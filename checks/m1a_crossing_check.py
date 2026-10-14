"""Numerical test of the boundary-crossing path class of the path-sum bound.

In the proof of the bound, the perturbation at each Duhamel step is the set of terms crossing the
boundary of the current probe region (meeting it and its complement). A path then satisfies:
S_{i_1} crosses Y; S_{i_{j+1}} crosses S_{i_j} (meets it and is not contained in it); first contact
with X at the last step. On the three-site chain H = Z_0 Z_1 + (1/2) X_1 X_2, observable X_0,
probe Z_2 (Y = {2}, X = {0}), the only such path is (S_2, S_1) with weight 1/2, so the crossing
bound is exactly 2 t^2 for every t, against the first-contact bound 4(e^t - 1 - t). The test:
is the exact commutator norm ||[X_0(t), Z_2]|| <= 2 t^2 on a fine grid? A violation would
refute the bound; agreement supports it (not a proof). The crossing path counts of the three-term
hypergraph of the reading guide and of one two-qubit term are checked exactly. Exits nonzero at a
failure.
"""
import numpy as np
from scipy.linalg import expm
from fractions import Fraction as Fr
from itertools import product

I2 = np.eye(2)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)


def on_sites(n, ops):
    out = np.array([[1.0 + 0j]])
    for j in range(n):
        out = np.kron(out, ops.get(j, I2))
    return out


def opnorm(M):
    return float(np.linalg.norm(M, 2))


def crossing_path_sum(terms, k, X, Y):
    """Exact count: first term crosses Y, consecutive terms cross the previous support,
    first contact with X at the last step."""
    def crosses(S, Z):
        return bool(S & Z) and not S <= Z
    total = Fr(0)
    for seq in product(range(len(terms)), repeat=k):
        Zs = [terms[i][0] for i in seq]
        if not crosses(Zs[0], Y):
            continue
        if any(not crosses(Zs[j + 1], Zs[j]) for j in range(k - 1)):
            continue
        if any(Zs[j] & X for j in range(k - 1)) or not (Zs[-1] & X):
            continue
        w = Fr(1)
        for i in seq:
            w *= terms[i][1]
        total += w
    return total


results = []


def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    results.append(cond)


print("== three-site chain: crossing paths ==")
terms3 = [(frozenset({0, 1}), Fr(1)), (frozenset({1, 2}), Fr(1, 2))]
counts = [crossing_path_sum(terms3, k, {0}, {2}) for k in range(1, 6)]
print("  P_k (crossing, first contact), k=1..5:", [str(c) for c in counts])
check("only the path (S_2, S_1) survives: P_2 = 1/2, others 0",
      counts == [Fr(0), Fr(1, 2), Fr(0), Fr(0), Fr(0)])

print("== exact commutator against the crossing bound 2 t^2 ==")
n = 3
H = on_sites(n, {0: Z, 1: Z}) + 0.5 * on_sites(n, {1: X, 2: X})
A, B = on_sites(n, {0: X}), on_sites(n, {2: Z})
worst_ratio = 0.0
viol = []
for t in np.linspace(0.01, 1.5, 150):
    U = expm(1j * t * H)
    At = U @ A @ U.conj().T
    nrm = opnorm(At @ B - B @ At)
    bound = 2 * t * t
    worst_ratio = max(worst_ratio, nrm / bound)
    if nrm > bound * (1 + 1e-9):
        viol.append((round(float(t), 3), nrm, bound))
print(f"  max ratio exact/bound on the grid: {worst_ratio:.6f}; violations: {viol[:5]}")
check("exact norm <= 2 t^2 on t in [0.01, 1.5]", not viol)

print("== three-term hypergraph of the reading guide: crossing counts ==")
termsH = [(frozenset({1, 2}), Fr(1)), (frozenset({1, 3}), Fr(1)), (frozenset({3, 4}), Fr(1))]
countsH = [crossing_path_sum(termsH, k, {4}, {1}) for k in range(1, 7)]
print("  P_k, k=1..6:", [str(c) for c in countsH])
check("three-term example: P_2 = 1, P_3 = 1 (S_1,S_2,S_3), P_4 = 1 (S_2,S_1,S_2,S_3)",
      countsH[:4] == [Fr(0), Fr(1), Fr(1), Fr(1)])

print("== two qubits, one term: unchanged ==")
terms2 = [(frozenset({0, 1}), Fr(1))]
check("one term: P_1 = 1 and no longer paths",
      [crossing_path_sum(terms2, k, {1}, {0}) for k in range(1, 4)] == [Fr(1), Fr(0), Fr(0)])

print(f"\n{sum(results)} of {len(results)} checks pass")
raise SystemExit(0 if all(results) else 1)
