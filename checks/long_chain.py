"""Truncated dynamics on a longer qubit chain: the twelve-qubit truncation example of chapter 5.

For the chain Hamiltonian H = sum_u (sigma^z_u sigma^z_{u+1} + (1/2) sigma^x_u sigma^x_{u+1}) on
n qubits and the observable a = sigma^x_0, computes for each time t and each region
X_r = {0, ..., r} the truncation error  eps_r(t) = ||A(t) - P_{X_r} A(t)||  (operator norm),
where A(t) = e^{itH} a e^{-itH} and P_X is the conditional expectation (normalized partial trace
over the complement, re-embedded), against the walk bound 2||a|| sum_k omega_k(t) of chapter 5
and the bounded-geometry bound 2||a|| |dY| (vt)^r e^{vt}/r! (v = 2 g l p with g = 4 terms per
site, l = 1, p = 2, rho = 1, so v = 16).

Resumable: every (t, r) point is written to the checkpoint JSON as soon as it is computed; an
interrupted run resumes from it. Dense linear algebra in dimension 2^n: n = 12 (4096) takes of
the order of an hour on four cores at two threads; n = 13 several hours.

Without options it runs quickly, on six qubits at t = 0.5 and 1. The example of the notes is the
run below; its checkpoint is kept, and checks/long_chain_figure.py draws the figure from it.

Usage (from the repository root):
    python checks/long_chain.py
    python checks/long_chain.py --n 12 --times 0.5 1 2 3 --out checks/data/long-chain-n12.json
"""
from __future__ import annotations

import argparse
import json
import os
import time
from pathlib import Path

os.environ.setdefault("OMP_NUM_THREADS", "2")
os.environ.setdefault("MKL_NUM_THREADS", "2")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "2")

import numpy as np  # noqa: E402

SX = np.array([[0, 1], [1, 0]], dtype=complex)
SZ = np.array([[1, 0], [0, -1]], dtype=complex)
I2 = np.eye(2, dtype=complex)


def site_op(n: int, u: int, m: np.ndarray) -> np.ndarray:
    """m at the site u (site 0 is the leftmost tensor factor), identity elsewhere."""
    out = np.array([[1.0 + 0j]])
    for v in range(n):
        out = np.kron(out, m if v == u else I2)
    return out


def chain_terms(n: int):
    """The terms (support, strength) and the Hamiltonian of the chapter's chain."""
    terms = []
    H = np.zeros((2 ** n, 2 ** n), dtype=complex)
    for u in range(n - 1):
        zz = site_op(n, u, SZ) @ site_op(n, u + 1, SZ)
        xx = site_op(n, u, SX) @ site_op(n, u + 1, SX)
        H += zz + 0.5 * xx
        terms.append(([u, u + 1], 1.0))
        terms.append(([u, u + 1], 0.5))
    return terms, H


def cond_exp(M: np.ndarray, n: int, X: list[int]) -> np.ndarray:
    """P_X M: normalized partial trace over the complement of X, re-embedded."""
    rest = sorted(u for u in range(n) if u not in X)
    T = M.reshape([2] * (2 * n))
    # trace out the complement sites from the highest down: with m sites left, site u has the
    # row axis u and the column axis m + u, and removing the highest pair leaves the lower
    # axes in place
    m = n
    for u in reversed(rest):
        T = np.trace(T, axis1=u, axis2=m + u)
        m -= 1
    red = T.reshape(2 ** m, 2 ** m) / 2 ** len(rest)
    # re-embed: identity on the complement; X need not be a prefix in general, but here X is
    # a prefix {0, ..., r}, so the embedding is red (x) 1
    assert X == list(range(len(X))), "X must be a prefix {0, ..., r} in this script"
    return np.kron(red, np.eye(2 ** len(rest), dtype=complex))


def opnorm(M: np.ndarray) -> float:
    return float(np.linalg.norm(M, 2))


def site_matrix(n: int, terms) -> np.ndarray:
    h = np.zeros((n, n))
    for S, k in terms:
        for u in S:
            for v in S:
                h[u, v] += k
    return h


def walk_bound(n: int, terms, X: list[int], Y: list[int], t: float) -> float:
    """2 * sum_{y in boundary Y} sum_{x in X cap T} (e^{2th} - 1)_{yx}, with ||a|| = 1."""
    h = site_matrix(n, terms)
    w, V = np.linalg.eigh(h)
    E = (V * np.exp(2 * t * w)) @ V.T - np.eye(n)
    dY = [y for y in Y if any(y in S and any(z not in Y for z in S) for S, _ in terms)]
    return 2.0 * float(sum(E[y, x] for y in dY for x in X))


def geometric_bound(n: int, terms, X: list[int], Y: list[int], r: int, t: float) -> float:
    """2 |dY| (v t)^r e^{v t} / r! with v = 2 g l p, g = 4, l = 1, p = 2."""
    from math import exp, factorial
    dY = [y for y in Y if any(y in S and any(z not in Y for z in S) for S, _ in terms)]
    v = 2 * 4 * 1.0 * 2
    return 2.0 * len(dY) * (v * t) ** r / factorial(r) * exp(v * t) if r >= 1 else float("nan")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=6)
    ap.add_argument("--times", type=float, nargs="+", default=[0.5, 1.0])
    ap.add_argument("--out", type=str, default="checks/out/long-chain.json")
    args = ap.parse_args()
    n = args.n
    out = Path(args.out)
    data = json.loads(out.read_text(encoding="utf-8")) if out.is_file() else {"n": n, "points": {}}
    assert data["n"] == n, "checkpoint belongs to another n"
    pts = data["points"]

    t0 = time.time()
    terms, H = chain_terms(n)
    a = site_op(n, 0, SX)
    print(f"n = {n}: diagonalizing H ({2 ** n} x {2 ** n}) ...", flush=True)
    w, V = np.linalg.eigh(H)
    print(f"  done in {time.time() - t0:.0f} s", flush=True)
    for t in args.times:
        key_t = f"{t:g}"
        U = (V * np.exp(1j * t * w)) @ V.conj().T
        At = U @ a @ U.conj().T
        del U
        for r in range(n):
            key = f"{key_t}:{r}"
            if key in pts:  # computed in an earlier run: report it as computed then
                q = pts[key]
                print(f"  t = {t:g}  r = {r:2d}  eps = {q['eps']:.3e}  walk = {q['walk_bound']:.3e}"
                      f"  geom = {q['geometric_bound']:.3e}  ({q['seconds']:.0f} s)", flush=True)
                continue
            X = list(range(r + 1))
            Y = [u for u in range(n) if u not in X]
            t1 = time.time()
            eps = opnorm(At - cond_exp(At, n, X)) if r < n - 1 else 0.0
            wb = walk_bound(n, terms, [0], Y, t) if Y else 0.0
            gb = geometric_bound(n, terms, [0], Y, r, t) if Y else 0.0
            pts[key] = {"t": t, "r": r, "eps": eps, "walk_bound": wb, "geometric_bound": gb,
                        "seconds": time.time() - t1}
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(json.dumps(data, indent=1), encoding="utf-8")
            print(f"  t = {t:g}  r = {r:2d}  eps = {eps:.3e}  walk = {wb:.3e}  geom = {gb:.3e}"
                  f"  ({time.time() - t1:.0f} s)", flush=True)
    print("done; checkpoint", out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
