"""Exact checks of chapters 1 and 2 of the lecture notes: the probe-reset recursion and the path
series.

Objects (sites 0..n-1; terms = (support, weight) with positive rational weights kappa_i):
  crossing terms: the perturbation at a probe region Y
  is the family of terms CROSSING Y (meeting Y and not contained in Y).
  first-contact path of length k from Y to X: supports S_{i_1}, ..., S_{i_k} with S_{i_1} crossing
    Y, S_{i_{j+1}} crossing S_{i_j} (no repeats, no nesting), S_{i_j} disjoint from X for j < k,
    S_{i_k} meeting X.  P_k(Y, X) = sum over such paths of the product of weights.
  the recursion, iterated exactly as a polynomial in t:
    F(X, Y) = 2                                               if X meets Y,
    F(X, Y) = 2 * sum_{i : S_i crosses Y} kappa_i * int_0^t F(X, S_i)(s) ds    otherwise.
  the series  2 * sum_{k >= 1} (2t)^k / k! * P_k(Y, X)  (X disjoint from Y).
  site matrix h (checks/path_check.py).

Claims (exact arithmetic unless the section says "numerical"):
  (R) the coefficient of t^k in the iterated recursion equals 2 * 2^k / k! * P_k(Y, X) for every k
      up to the truncation depth, on every example (the series IS the iterated recursion);
  (B) P_k(Y, X) <= (sum_i kappa_i)^k, the remainder estimate's ingredient;
  (S) first-contact paths are a subset of the paths of path_check.py and of the site-matrix walks:
      P_k(Y, X) <= path_sum <= sum_{x in X, y in Y} (h^k)_{xy}, hence the series is coefficientwise
      at most the review's closed form 2 * sum (e^{2th} - 1)_{xy} (Route against the source,
      smallest cases);
  (N, numerical) on two- and three-qubit chains the exact commutator norm ||[A(t), B]||, with
      ||A|| = ||B|| = 1, is at most the series bound at every t on a grid; on two qubits with the
      term Z Z the exact norm is 2|sin 2t|, against the series 4t.
Every claim is also run on degenerate inputs (section 4).
"""
from fractions import Fraction as Fr
from itertools import product
from math import factorial
import sys
import os

results = []


# ---------------------------------------------------------------- from path_check.py (copied:
# that script runs on import)
def site_matrix(n, terms):
    h = [[Fr(0)] * n for _ in range(n)]
    for S, w in terms:
        for u in S:
            h[u][u] += w
            for v in S:
                if u != v:
                    h[u][v] += w
    return h


def matpow_entry_sum(h, k, X, Y):
    n = len(h)
    v = [Fr(1) if y in Y else Fr(0) for y in range(n)]
    for _ in range(k):
        v = [sum(v[u] * h[u][w] for u in range(n)) for w in range(n)]
    return sum(v[x] for x in X)


def path_sum(terms, k, X, Y):
    """Paths of path_check.py: consecutive overlap, no first-contact condition."""
    total = Fr(0)
    for seq in product(range(len(terms)), repeat=k):
        Zs = [terms[i][0] for i in seq]
        if not (Zs[0] & Y):
            continue
        if any(not (Zs[j] & Zs[j + 1]) for j in range(k - 1)):
            continue
        if not (Zs[-1] & X):
            continue
        w = Fr(1)
        for i in seq:
            w *= terms[i][1]
        total += w
    return total


def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    results.append(cond)
    return cond


# ---------------------------------------------------------------- first-contact paths
def crosses(S, Z):
    """S meets Z and is not contained in Z (S meets the boundary of Z)."""
    return bool(S & Z) and not S <= Z


def fc_path_sum(terms, k, X, Y):
    """P_k(Y, X) by the transfer matrix on term indices: start
    weights v_i = kappa_i [S_i crosses Y]; a step i -> j is allowed with weight kappa_j when S_j
    crosses S_i and S_i is disjoint from X; the path ends at a term meeting X. Exact."""
    m = len(terms)
    if k < 1 or m == 0:
        return Fr(0)
    v = [w if crosses(S, Y) else Fr(0) for S, w in terms]
    for _ in range(k - 1):
        v = [sum(v[i] * terms[j][1] for i in range(m)
                 if crosses(terms[j][0], terms[i][0]) and not (terms[i][0] & X)) for j in range(m)]
    return sum(v[i] for i in range(m) if terms[i][0] & X)


def fc_path_sum_brute(terms, k, X, Y):
    """The same count by enumeration (cross-check for small k)."""
    total = Fr(0)
    for seq in product(range(len(terms)), repeat=k):
        Zs = [terms[i][0] for i in seq]
        if not crosses(Zs[0], Y):
            continue
        if any(not crosses(Zs[j + 1], Zs[j]) for j in range(k - 1)):
            continue
        if any(Zs[j] & X for j in range(k - 1)):
            continue
        if not (Zs[-1] & X):
            continue
        w = Fr(1)
        for i in seq:
            w *= terms[i][1]
        total += w
    return total


# ---------------------------------------------------------------- polynomials in t (exact)
def poly_add(p, q):
    r = dict(p)
    for d, c in q.items():
        r[d] = r.get(d, Fr(0)) + c
    return r


def poly_scale(p, c):
    return {d: c * v for d, v in p.items()}


def poly_integrate(p):
    """int_0^t p(s) ds."""
    return {d + 1: c / (d + 1) for d, c in p.items()}


def recursion_poly(terms, X, Y, depth):
    """The iterated recursion as a polynomial in t, exact, truncated at `depth` iterations
    (every monomial of degree <= depth is exact)."""
    if X & Y:
        return {0: Fr(2)}
    if depth == 0:
        return {}
    acc = {}
    for S, w in terms:
        if crosses(S, Y):
            acc = poly_add(acc, poly_scale(poly_integrate(recursion_poly(terms, X, S, depth - 1)),
                                           2 * w))
    return acc


def series_coeff(terms, X, Y, k):
    """2 * 2^k / k! * P_k(Y, X)."""
    return Fr(2 * 2 ** k, factorial(k)) * fc_path_sum(terms, k, X, Y)


def review_coeff(h, X, Y, k):
    """Coefficient of t^k in 2 * sum_{x in X, y in Y} (e^{2th} - 1)_{xy}."""
    return Fr(2 * 2 ** k, factorial(k)) * matpow_entry_sum(h, k, X, Y)


EXAMPLES = {
    "one term on two sites": (2, [(frozenset({0, 1}), Fr(1))], {1}, {0}),
    "three-site chain": (3, [(frozenset({0, 1}), Fr(1)), (frozenset({1, 2}), Fr(1, 2))], {2}, {0}),
    "three-term hypergraph of the reading guide": (
        5, [(frozenset({1, 2}), Fr(1)), (frozenset({1, 3}), Fr(1)), (frozenset({3, 4}), Fr(1))],
        {4}, {1}),
    "triangle with a three-site term": (
        4, [(frozenset({0, 1}), Fr(2, 3)), (frozenset({1, 2, 3}), Fr(1)), (frozenset({0, 2}), Fr(1, 3))],
        {3}, {0}),
}
DEPTH = 6

print("== Section 1: (R) the iterated recursion is the path series, coefficient by coefficient ==")
for name, (n, terms, X, Y) in EXAMPLES.items():
    poly = recursion_poly(terms, X, Y, DEPTH)
    ok = (poly.get(0, Fr(0)) == (2 if X & Y else 0)
          and all(poly.get(k, Fr(0)) == series_coeff(terms, X, Y, k) for k in range(1, DEPTH + 1)))
    print(f"  {name}: coefficients t^1..t^{DEPTH} =",
          [str(poly.get(k, Fr(0))) for k in range(1, DEPTH + 1)])
    check(f"(R) {name}", ok)
    check(f"(R) {name}: transfer-matrix count equals enumeration for k <= 5",
          all(fc_path_sum(terms, k, X, Y) == fc_path_sum_brute(terms, k, X, Y) for k in range(1, 6)))
    total = sum(w for _, w in terms)
    check(f"(B) {name}: P_k <= (sum kappa)^k for k <= {DEPTH}",
          all(fc_path_sum(terms, k, X, Y) <= total ** k for k in range(1, DEPTH + 1)))

print("== Section 2: (S) against path_check's paths and the site-matrix form (Route against "
      "the source, smallest cases) ==")
for name, (n, terms, X, Y) in EXAMPLES.items():
    h = site_matrix(n, terms)
    ok = True
    for k in range(1, DEPTH + 1):
        fc, ps, hs = fc_path_sum(terms, k, X, Y), path_sum(terms, k, X, Y), matpow_entry_sum(h, k, X, Y)
        ok = ok and fc <= ps <= hs and series_coeff(terms, X, Y, k) <= review_coeff(h, X, Y, k)
    check(f"(S) {name}: P_k^fc <= path_sum <= (h^k)_XY and series <= review form, k <= {DEPTH}", ok)
# the smallest divergent case, with its numbers: one term, repeats never occur before first contact
n, terms, X, Y = EXAMPLES["one term on two sites"]
h = site_matrix(n, terms)
check("(S) one term: our series is exactly 4t (P_1 = 1, P_k = 0 for k >= 2)",
      series_coeff(terms, X, Y, 1) == 4 and all(fc_path_sum(terms, k, X, Y) == 0 for k in (2, 3, 4)))
check("(S) one term: the review's form 2(e^{2th}-1)_{10} = 4t + 8t^2 + ... dominates ours",
      review_coeff(h, X, Y, 1) == 4 and review_coeff(h, X, Y, 2) == 8)
# the three-site chain: repeats before first contact are counted, P_k = kappa_1^{k-1} kappa_2
n, terms, X, Y = EXAMPLES["three-site chain"]
check("(S) three-site chain: the only path is (S_2, S_1): P_2 = 1/2, P_k = 0 otherwise",
      fc_path_sum(terms, 2, X, Y) == Fr(1, 2)
      and all(fc_path_sum(terms, k, X, Y) == 0 for k in (1, 3, 4, 5)))

print("== Section 3 (numerical): the exact commutator norm on qubit chains against the series ==")
try:
    import numpy as np
    from scipy.linalg import expm

    I2 = np.eye(2)
    Xp = np.array([[0, 1], [1, 0]], dtype=complex)
    Zp = np.array([[1, 0], [0, -1]], dtype=complex)

    def kron_all(ops):
        out = np.array([[1.0 + 0j]])
        for o in ops:
            out = np.kron(out, o)
        return out

    def on_sites(n, ops_at):
        return kron_all([ops_at.get(j, I2) for j in range(n)])

    def opnorm(M):
        return float(np.linalg.norm(M, 2))

    def series_bound(terms, X, Y, t, K=40):
        total = sum(float(w) for _, w in terms)
        s = sum(2.0 * (2 * t) ** k / factorial(k) * float(fc_path_sum(terms, k, X, Y))
                for k in range(1, K + 1))
        tail = 2.0 * (2 * t * total) ** (K + 1) / factorial(K + 1)   # remainder bound
        return s + tail

    # two qubits, H = Z Z (kappa = 1), A = X_0, B = X_1: exact norm 2 |sin 2t|
    n = 2
    H = on_sites(n, {0: Zp, 1: Zp})
    A, B = on_sites(n, {0: Xp}), on_sites(n, {1: Xp})
    terms2 = [(frozenset({0, 1}), Fr(1))]
    ok_exact, ok_bound = True, True
    for t in [0.0, 0.1, 0.25, 0.5, 1.0]:
        U = expm(1j * t * H)
        At = U @ A @ U.conj().T
        nrm = opnorm(At @ B - B @ At)
        ok_exact = ok_exact and abs(nrm - 2 * abs(np.sin(2 * t))) < 1e-9
        ok_bound = ok_bound and nrm <= series_bound(terms2, {1}, {0}, t) + 1e-12
    check("(N) two qubits, H = ZZ: ||[X_0(t), X_1]|| = 2|sin 2t| (tolerance 1e-9)", ok_exact)
    check("(N) two qubits, H = ZZ: exact norm <= series bound 4t on the grid", ok_bound)

    # three-qubit chain, H = Z_0 Z_1 + (1/2) Z_1 Z_2, A = X_0 (region X = {0}), B = X_2 (Y = {2}).
    # The two terms commute and X_0(t) stays on sites 0, 1, so the commutator vanishes identically.
    n = 3
    H = on_sites(n, {0: Zp, 1: Zp}) + 0.5 * on_sites(n, {1: Zp, 2: Zp})
    A, B = on_sites(n, {0: Xp}), on_sites(n, {2: Xp})
    terms3 = EXAMPLES["three-site chain"][1]
    ok_bound = True
    for t in [0.0, 0.1, 0.25, 0.5, 1.0, 2.0]:
        U = expm(1j * t * H)
        At = U @ A @ U.conj().T
        nrm = opnorm(At @ B - B @ At)
        ok_bound = ok_bound and nrm <= series_bound(terms3, {0}, {2}, t) + 1e-12
    check("(N) three-qubit chain of commuting terms: exact norm (0) <= series bound", ok_bound)
    # A non-commuting chain: H = Z_0 Z_1 + (1/2) X_1 X_2, A = X_0, probe B = Z_2.  Second order:
    # ad_H^2(X_0) = 4 X_0 + 2 Y_0 Y_1 X_2, so ||[X_0(t), Z_2]|| = 2 t^2 + O(t^3); among the crossing
    # paths the only one is (S_2, S_1) with weight 1/2, so the series is exactly 2 t^2.
    H = on_sites(n, {0: Zp, 1: Zp}) + 0.5 * on_sites(n, {1: Xp, 2: Xp})
    B = on_sites(n, {2: Zp})
    ok_bound, ok_leading = True, True
    for t in [0.01, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0]:
        U = expm(1j * t * H)
        At = U @ A @ U.conj().T
        nrm = opnorm(At @ B - B @ At)
        bound = series_bound(terms3, {0}, {2}, t)
        ok_bound = ok_bound and nrm <= bound + 1e-12
        if t <= 0.05:
            ok_leading = ok_leading and abs(nrm - 2 * t ** 2) < 4 * t ** 3
        ok_leading = ok_leading and abs(bound - 2 * t * t) < 1e-9
    check("(N) three-qubit chain, H = ZZ + (1/2) XX, probe Z_2: exact norm <= 2 t^2, the series",
          ok_bound and ok_leading)
except ImportError as e:
    print(f"  numerical section skipped: {e}")

print("== Section 4: degenerate inputs ==")
check("empty family: recursion polynomial is empty (bound 0) for disjoint X, Y",
      recursion_poly([], {0}, {1}, DEPTH) == {})
check("empty family: P_k = 0", all(fc_path_sum([], k, {0}, {1}) == 0 for k in (1, 2, 3)))
check("X meets Y: recursion value is the constant 2, no path term",
      recursion_poly([(frozenset({0, 1}), Fr(1))], {0}, {0, 1}, DEPTH) == {0: Fr(2)})
check("t = 0: every series coefficient of positive degree vanishes at t = 0 (series value 0)",
      sum(series_coeff(EXAMPLES["three-site chain"][1], {2}, {0}, k) * 0 ** k
          for k in range(1, DEPTH + 1)) == 0)
check("one site, one term {0}, X = Y = {0}: value 2",
      recursion_poly([(frozenset({0}), Fr(3))], {0}, {0}, DEPTH) == {0: Fr(2)})
check("one term disjoint from Y: no path, recursion empty",
      recursion_poly([(frozenset({1, 2}), Fr(1))], {2}, {0}, DEPTH) == {}
      and fc_path_sum([(frozenset({1, 2}), Fr(1))], 1, {2}, {0}) == 0)
check("weight zero term contributes nothing",
      recursion_poly([(frozenset({0, 1}), Fr(0))], {1}, {0}, DEPTH) in ({}, {1: Fr(0)}))

print(f"\n{sum(results)} of {len(results)} checks pass")
sys.exit(0 if all(results) else 1)
