"""Checks of chapter 3 of the lecture notes: the closed forms of the path series.

Objects: as in checks/m1a_check.py (crossing path class).  A path from Y to X is a sequence of
term indices i_1..i_k with S_{i_1} crossing Y (meeting Y and its complement), S_{i_{j+1}} crossing
S_{i_j}, S_{i_j} disjoint from X for j < k, S_{i_k} meeting X.  P_k(Y,X) = sum over paths of the
product of the kappa's.  Site matrix h_uv = sum of kappa_i over terms containing u and v
(u != v), h_uu = sum of kappa_i over terms containing u.  Series bound
C_{X,Y}(t) = 2 sum_k (2t)^k P_k / k!.

Sections (exact rational arithmetic unless marked numerical):
 1. closed form (i):  P_k(Y,X) <= sum_{x in X, y in Y} (h^k)_{xy}, k = 1..5, on the examples of
    m1a_check.py, on 600 random small hypergraphs with random disjoint X, Y, and on degenerate
    inputs (empty family, X meets Y, Y = all sites, a term with kappa = 0).  Records the fraction
    of strict inequalities and the minimal ratio at k = 2.
 2. why paths and not union-chains: a four-term hypergraph on three sites (smallest witness of the
    random search of path_check.py section 2) on which union-chains exceed sum (h^k)_{xy} at k = 4
    (507/8 > 121/2); paths do not.  The unit-weight four-edge chain is NOT a counterexample.
 3. closed form (ii) (numerical): F(r) = e^{-mu r}/(1+r)^2 on the chain {0..39}; C_F, the
    reproducing bound (F^k)_{xy} <= C_F^{k-1} F(d(x,y)) for k = 2, 3, the norm ||F||, and
    h_xy <= ||Phi||_F F(d(x,y)) for the nearest-neighbour family kappa = 1 on {j, j+1}.
 4. closed form (iii): nearest-neighbour chain, kappa <= l, degree g = 2: (h^k)_{xy} = 0 for
    k < d(x,y), (h^k)_{xy} <= (c g l)^k with the smallest c found for k <= 8 (c = 2 is tested),
    and 2 sum_{k >= r} (2t)^k (c g l)^k / k! <= 2 (2 c g l t)^r e^{2 c g l t} / r! at
    t = 0.1, 0.5, 1 (numerical, tolerance 1e-12 relative).  The review's Proposition 3.5 is
    C_uv(t) <= K (4(g-1) h t)^r / r!, K = 1/(1 - 2/e) (stated, not proved here); we compare our
    C_{u,v}(t) = 2 sum_k (2t)^k P_k/k! against 2 K (4(g-1) h t)^r / r! (the factor 2 converts the
    review's C, half the supremum, to ours) on the chain, h = 1, r = 1..6, t in {0.1, 0.5, 1}.
    Violations are printed as findings and do not count as failed checks.
 5. closed form (iv), the review's Example 3.6: (ct)^r/r! <= e^{-mu r}(e^{mu v t} - 1) with
    v = e^{mu} c / mu, checked numerically for c = 1, mu in {0.5, 1}, r = 1..10, t in {0.1, 1, 3}.
 6. time reversal (numerical): ||[A(t),B]|| = ||[A,B(-t)]|| (B(-t) = e^{-iHt} B e^{iHt}) holds;
    ||[A(t),B]|| = ||[A(-t),B]|| fails on some example; the series bound depends on |t| only,
    and bounds both signs.
"""
from fractions import Fraction as Fr
from itertools import product
from math import factorial, exp, e as E
import random
import sys

results = []


def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    results.append(bool(cond))
    return cond


# ------------------------------------------------ helpers (copied from m1a_check.py / path_check.py;
# those scripts run on import)
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


def crosses(S, Z):
    return bool(S & Z) and not S <= Z


def fc_path_sum(terms, k, X, Y):
    m = len(terms)
    if k < 1 or m == 0:
        return Fr(0)
    v = [w if crosses(S, Y) else Fr(0) for S, w in terms]
    for _ in range(k - 1):
        v = [sum(v[i] * terms[j][1] for i in range(m)
                 if crosses(terms[j][0], terms[i][0]) and not (terms[i][0] & X)) for j in range(m)]
    return sum(v[i] for i in range(m) if terms[i][0] & X)


def fc_path_sum_brute(terms, k, X, Y):
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


def chain_sum(terms, k, X, Y):
    """Union chains with first contact with X at step k (path_check.py)."""
    total = Fr(0)
    for seq in product(range(len(terms)), repeat=k):
        Zs = [terms[i][0] for i in seq]
        union = set(Y)
        ok = True
        for j, Z in enumerate(Zs):
            if not (Z & union):
                ok = False
                break
            union |= Z
            hits = bool(union & X)
            if (hits and j < k - 1) or (j == k - 1 and not hits):
                ok = False
                break
        if not ok:
            continue
        w = Fr(1)
        for i in seq:
            w *= terms[i][1]
        total += w
    return total


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

# ================================================================ Section 1
print("== Section 1: closed form (i), P_k <= sum_{x,y} (h^k)_{xy}, k = 1..5 ==")
for name, (n, terms, X, Y) in EXAMPLES.items():
    h = site_matrix(n, terms)
    check(f"(i) {name}: P_k <= (h^k)_XY for k = 1..5",
          all(fc_path_sum(terms, k, X, Y) <= matpow_entry_sum(h, k, X, Y) for k in range(1, 6)))

random.seed(20261005)
cases, bad, strict2, tot2, ratios2, zero2, brute_bad = 0, 0, 0, 0, [], 0, 0
for trial in range(600):
    n = random.randint(3, 6)
    m = random.randint(2, 5)
    terms = [(frozenset(random.sample(range(n), random.randint(1, 3))),
              Fr(random.randint(1, 4), random.randint(1, 3))) for _ in range(m)]
    X = set(random.sample(range(n), random.randint(1, 2)))
    rest = [s for s in range(n) if s not in X]
    Y = set(random.sample(rest, random.randint(1, min(2, len(rest)))))
    h = site_matrix(n, terms)
    for k in range(1, 6):
        cases += 1
        P, H = fc_path_sum(terms, k, X, Y), matpow_entry_sum(h, k, X, Y)
        if P > H:
            bad += 1
            print("  FAIL case", n, [(sorted(S), str(w)) for S, w in terms], X, Y, k)
        if k == 2:
            tot2 += 1
            if P < H:
                strict2 += 1
            if P > 0:
                ratios2.append(P / H)
            else:
                zero2 += 1
        if k <= 3 and P != fc_path_sum_brute(terms, k, X, Y):
            brute_bad += 1
check(f"(i) {cases} random (hypergraph, k) cases, k <= 5: no violation", bad == 0)
check("(i) transfer-matrix count equals enumeration on the random cases for k <= 3", brute_bad == 0)
print(f"  k = 2 over {tot2} random cases: strict in {strict2} ({100.0 * strict2 / tot2:.1f}%), "
      f"P_2 = 0 in {zero2}, minimal ratio P_2 / sum (h^2)_XY over P_2 > 0: "
      f"{min(ratios2)} = {float(min(ratios2)):.5f}")

# degenerate inputs
T = [(frozenset({0, 1}), Fr(1)), (frozenset({1, 2}), Fr(2))]
h3 = site_matrix(3, T)
check("(i) empty family: P_k = 0 = (h^k)_XY for k = 1..5",
      all(fc_path_sum([], k, {2}, {0}) == 0 == matpow_entry_sum(site_matrix(3, []), k, {2}, {0})
          for k in range(1, 6)))
check("(i) X meets Y: P_k <= (h^k)_XY for k = 1..5",
      all(fc_path_sum(T, k, {1}, {1, 0}) <= matpow_entry_sum(h3, k, {1}, {1, 0}) for k in range(1, 6))
      and all(fc_path_sum(T, k, {0, 1}, {1}) <= matpow_entry_sum(h3, k, {0, 1}, {1})
              for k in range(1, 6)))
check("(i) Y = all sites: no term crosses Y, P_k = 0",
      all(fc_path_sum(T, k, {2}, {0, 1, 2}) == 0 for k in range(1, 6)))
Tz = [(frozenset({0, 1}), Fr(0)), (frozenset({1, 2}), Fr(2))]
hz = site_matrix(3, Tz)
check("(i) a term with kappa = 0: inequality holds and the zero term adds nothing",
      all(fc_path_sum(Tz, k, {2}, {0}) <= matpow_entry_sum(hz, k, {2}, {0}) for k in range(1, 6))
      and all(fc_path_sum(Tz, k, {2}, {0}) == 0 for k in range(1, 6)))

# ================================================================ Section 2
print("== Section 2: union-chains exceed sum (h^k)_xy; paths do not ==")
# Smallest witness of the random search of path_check.py section 2 (seed 20261004): four terms on
# three sites.  The unit-weight four-edge chain is NOT a counterexample (checked below).
n = 3
terms = [(frozenset({1}), Fr(3)), (frozenset({1}), Fr(2)), (frozenset({0, 2}), Fr(1)),
         (frozenset({0, 1}), Fr(3, 2))]
X, Y = {2}, {0}
h = site_matrix(n, terms)
viol = []
for k in range(1, 7):
    cs, ps, hs = chain_sum(terms, k, X, Y), fc_path_sum(terms, k, X, Y), matpow_entry_sum(h, k, X, Y)
    print(f"  four terms on three sites, k = {k}: union-chains = {cs}, paths = {ps}, (h^k)_XY = {hs}")
    if cs > hs:
        viol.append(k)
check(f"union-chains exceed (h^k)_XY (k in {viol}); at k = 4: 507/8 > 121/2",
      chain_sum(terms, 4, X, Y) == Fr(507, 8) and matpow_entry_sum(h, 4, X, Y) == Fr(121, 2))
check("paths stay within (h^k)_XY on the same hypergraph, k = 1..6",
      all(fc_path_sum(terms, k, X, Y) <= matpow_entry_sum(h, k, X, Y) for k in range(1, 7)))
ch4 = [(frozenset({j, j + 1}), Fr(1)) for j in range(4)]
h4 = site_matrix(5, ch4)
check("the unit-weight four-edge chain (path_check.py section 3) is not a counterexample, k <= 6",
      all(chain_sum(ch4, k, {4}, {0}) <= matpow_entry_sum(h4, k, {4}, {0}) for k in range(1, 7)))

# ================================================================ Section 3
print("== Section 3 (numerical): closed form (ii), decay functions ==")
try:
    import numpy as np
    from scipy.linalg import expm
except ImportError as ex:
    np = None
    print(f"  numerical sections skipped: {ex}")

if np is not None:
    n = 40
    idx = np.arange(n)
    D = np.abs(idx[:, None] - idx[None, :]).astype(float)
    for mu in (0.5, 1.0):
        def Ff(r, mu=mu):
            return np.exp(-mu * r) / (1.0 + r) ** 2
        Fm = Ff(D)
        F2 = Fm @ Fm
        F3 = Fm @ Fm @ Fm
        CF = float(np.max(F2 / Fm))
        normF = float(Fm.sum(axis=1).max())
        full = 2 * sum(float(Ff(float(r))) for r in range(0, 4000)) - 1
        print(f"  mu = {mu}: C_F = {CF:.6f}, ||F|| = sup_x sum_y F(d(x,y)) = {normF:.6f} "
              f"(infinite chain {full:.6f})")
        check(f"(ii) mu = {mu}: (F^2)_xy <= C_F F(d) on the chain", np.all(F2 <= CF * Fm * (1 + 1e-12)))
        check(f"(ii) mu = {mu}: (F^3)_xy <= C_F^2 F(d)", np.all(F3 <= CF ** 2 * Fm * (1 + 1e-12)))
        check(f"(ii) mu = {mu}: ||F|| finite (chain value <= infinite-chain value)",
              normF <= full + 1e-12)
        hh = np.zeros((n, n))
        for j in range(n - 1):
            for u in (j, j + 1):
                for v in (j, j + 1):
                    hh[u, v] += 1.0
        PhiF = float(np.max(hh / Fm))
        print(f"  mu = {mu}: ||Phi||_F (nearest neighbour, kappa = 1) = {PhiF:.6f}; "
              f"4 e^mu = {4 * exp(mu):.6f}")
        check(f"(ii) mu = {mu}: h_xy <= ||Phi||_F F(d), ||Phi||_F = max(2, 1/F(1)) = 4 e^mu",
              abs(PhiF - 4 * exp(mu)) < 1e-9 and np.all(hh <= PhiF * Fm * (1 + 1e-12)))

# ================================================================ Section 4
print("== Section 4: closed form (iii), bounded degree ==")
n = 40
g = 2
cmin_by_ell = {}
for ell in (Fr(1), Fr(3, 2)):
    terms = [(frozenset({j, j + 1}), ell) for j in range(n - 1)]
    h = site_matrix(n, terms)
    Hk = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    zero_ok, cmin, maxes = True, 0.0, []
    for k in range(1, 9):
        Hk = [[sum(h[i][a] * Hk[a][j] for a in range(max(0, i - 1), min(n, i + 2)))
               for j in range(n)] for i in range(n)]
        mx = max(max(row) for row in Hk)
        maxes.append(mx)
        for i in range(n):
            for j in range(n):
                if k < abs(i - j) and Hk[i][j] != 0:
                    zero_ok = False
        cmin = max(cmin, float(mx) ** (1.0 / k) / (g * float(ell)))
    cmin_by_ell[ell] = cmin
    check(f"(iii) l = {ell}: (h^k)_xy = 0 for k < d(x,y), k <= 8", zero_ok)
    c2 = all(maxes[k - 1] <= (2 * g * ell) ** k for k in range(1, 9))
    print(f"  l = {ell}: smallest c with (h^k)_xy <= (c g l)^k for k <= 8: {cmin:.6f} "
          f"(per-k maxima {[str(m_) for m_ in maxes[:4]]} ...)")
    check(f"(iii) l = {ell}: c = 2 suffices exactly for k <= 8 (smallest c = {cmin:.4f})", c2)
    check(f"(iii) l = {ell}: smallest c lies in (1, 2)", 1 < cmin < 2)

if np is not None:
    cdata = cmin_by_ell[Fr(1)]

    def tail_sum(a, r, K=400):
        tl = [1.0]
        for k in range(1, K + 1):
            tl.append(tl[-1] * a / k)
        return sum(tl[r:])

    ok_tail = True
    for cval in (2.0, cdata):
        for ell in (1.0, 1.5):
            for t in (0.1, 0.5, 1.0):
                a = 2 * t * cval * g * ell
                for r in range(1, 11):
                    lhs = 2 * tail_sum(a, r)
                    rhs = 2 * a ** r * exp(a) / factorial(r)
                    if lhs > rhs * (1 + 1e-12):
                        ok_tail = False
    check("(iii) 2 sum_{k>=r}(2t)^k (cgl)^k/k! <= 2 (2cglt)^r e^{2cglt}/r!, r = 1..10, "
          "t in {0.1, 0.5, 1}, c in {2, data}, l in {1, 3/2}", ok_tail)

    # review's Proposition 3.5 against our series on the chain, h = 1 (kappa = 1), g = 2
    Kc = 1.0 / (1.0 - 2.0 / E)
    N = 70
    edges = [frozenset({j, j + 1}) for j in range(N - 1)]
    m = len(edges)
    Kmax = 80

    def series_value(u, v, t):
        Xs, Ys = frozenset({u}), frozenset({v})
        vec = np.array([1.0 if crosses(S, Ys) else 0.0 for S in edges])
        Tm = np.zeros((m, m))
        for i, Si in enumerate(edges):
            if Si & Xs:
                continue
            for j, Sj in enumerate(edges):
                if crosses(Sj, Si):
                    Tm[i, j] = 1.0
        endv = np.array([1.0 if S & Xs else 0.0 for S in edges])
        tot = 0.0
        for k in range(1, Kmax + 1):
            tot += 2.0 * (2 * t) ** k / factorial(k) * float(vec @ endv)
            vec = vec @ Tm
        return tot

    print("  review's Prop 3.5 (g = 2, h = 1, K = %.5f): our series vs 2 K (4(g-1)ht)^r / r!" % Kc)
    viol = []
    u0 = 30
    vals = {}
    for t in (0.1, 0.5, 1.0):
        for r in range(1, 7):
            ours = series_value(u0, u0 + r, t)
            vals[(t, r)] = ours
            rev = 2 * Kc * (4 * (g - 1) * 1.0 * t) ** r / factorial(r)
            print(f"    t = {t}, r = {r}: ours = {ours:.6g}, 2K(4t)^r/r! = {rev:.6g}, "
                  f"ratio = {ours / rev:.4g}")
            if ours > rev:
                viol.append((t, r, ours, rev))
    if viol:
        print(f"  FINDING: our path series exceeds 2 K (4(g-1)ht)^r/r! in {len(viol)} of 18 cases: "
              + "; ".join(f"(t={a}, r={b})" for a, b, _, _ in viol)
              + "; not counted as a failed check")
    else:
        print("  no violation of 2 K (4(g-1)ht)^r/r! by the path series in the 18 cases")
    check("(iii) path series on the chain is finite and positive in all 18 cases computed",
          all(np.isfinite(v_) and v_ > 0 for v_ in vals.values()))

# ================================================================ Section 5
print("== Section 5 (numerical): the review's Example 3.6 ==")
ok5, cnt5, worst = True, 0, 0.0
for mu in (0.5, 1.0):
    c = 1.0
    v = exp(mu) * c / mu
    for r in range(1, 11):
        for t in (0.1, 1.0, 3.0):
            lhs = (c * t) ** r / factorial(r)
            rhs = exp(-mu * r) * (exp(mu * v * t) - 1.0)
            cnt5 += 1
            worst = max(worst, lhs / rhs)
            if lhs > rhs * (1 + 1e-12):
                ok5 = False
                print("  FAIL", mu, r, t, lhs, rhs)
print(f"  {cnt5} cases; largest lhs/rhs = {worst:.4f}")
check("(iv) (ct)^r/r! <= e^{-mu r}(e^{mu v t} - 1), v = e^mu c/mu, c = 1, mu in {0.5, 1}, "
      "r = 1..10, t in {0.1, 1, 3}: holds in all cases", ok5)

# ================================================================ Section 6
print("== Section 6 (numerical): time reversal ==")
if np is not None:
    I2 = np.eye(2)
    Xp = np.array([[0, 1], [1, 0]], dtype=complex)
    Yp = np.array([[0, -1j], [1j, 0]], dtype=complex)
    Zp = np.array([[1, 0], [0, -1]], dtype=complex)

    def on_sites(nq, ops_at):
        out = np.array([[1.0 + 0j]])
        for j in range(nq):
            out = np.kron(out, ops_at.get(j, I2))
        return out

    def opnorm(M):
        return float(np.linalg.norm(M, 2))

    def series_bound(terms, X, Y, t, K=40):
        t = abs(t)
        total = sum(float(w) for _, w in terms)
        s = sum(2.0 * (2 * t) ** k / factorial(k) * float(fc_path_sum(terms, k, X, Y))
                for k in range(1, K + 1))
        return s + 2.0 * (2 * t * total) ** (K + 1) / factorial(K + 1)

    def comm_norms(H, A, B, t):
        Up, Um = expm(1j * t * H), expm(-1j * t * H)
        At, Amt = Up @ A @ Up.conj().T, Um @ A @ Um.conj().T
        Bmt = Um @ B @ Um.conj().T        # B(-t) = e^{-iHt} B e^{iHt}

        def c(P, Q):
            return opnorm(P @ Q - Q @ P)
        return c(At, B), c(Amt, B), c(A, Bmt)

    terms3 = EXAMPLES["three-site chain"][1]
    examples = {
        "two qubits, H = ZZ, A = X_0, B = X_1": (
            on_sites(2, {0: Zp, 1: Zp}), on_sites(2, {0: Xp}), on_sites(2, {1: Xp}),
            [(frozenset({0, 1}), Fr(1))], {0}, {1}),
        "three qubits, H = ZZ + (1/2) XX, A = X_0, B = Z_2": (
            on_sites(3, {0: Zp, 1: Zp}) + 0.5 * on_sites(3, {1: Xp, 2: Xp}),
            on_sites(3, {0: Xp}), on_sites(3, {2: Zp}), terms3, {0}, {2}),
        "three qubits, H = ZZ + (1/2) XX + (7/10) X_1 + (3/10) Z_0, A = Y_0, B = Z_2": (
            on_sites(3, {0: Zp, 1: Zp}) + 0.5 * on_sites(3, {1: Xp, 2: Xp})
            + 0.7 * on_sites(3, {1: Xp}) + 0.3 * on_sites(3, {0: Zp}),
            on_sites(3, {0: Yp}), on_sites(3, {2: Zp}),
            terms3 + [(frozenset({1}), Fr(7, 10)), (frozenset({0}), Fr(3, 10))], {0}, {2}),
    }
    for name, (H, A, B, terms, XA, YB) in examples.items():
        rev_ok, bound_ok, maxdiff = True, True, 0.0
        for t in (0.1, 0.25, 0.5, 1.0, 2.0):
            cp, cm, cB = comm_norms(H, A, B, t)
            rev_ok = rev_ok and abs(cp - cB) < 1e-9
            maxdiff = max(maxdiff, abs(cp - cm))
            bp, bm = series_bound(terms, XA, YB, t), series_bound(terms, XA, YB, -t)
            bound_ok = bound_ok and bp == bm and cp <= bp + 1e-12 and cm <= bm + 1e-12 \
                and cB <= bp + 1e-12
        print(f"  {name}: max_t | ||[A(t),B]|| - ||[A(-t),B]|| | = {maxdiff:.3e}")
        check(f"(time reversal) {name}: ||[A(t),B]|| = ||[A,B(-t)]|| (tolerance 1e-9)", rev_ok)
        check(f"(time reversal) {name}: series bound equal for t and -t and bounds both", bound_ok)
    # generic two-qubit example: random Hermitian H (kappa = ||H|| = 1 on {0,1}), random A on qubit 0,
    # B on qubit 1, all normalised to operator norm 1 (fixed seed)
    rng = np.random.default_rng(1)

    def herm(sz):
        M_ = rng.normal(size=(sz, sz)) + 1j * rng.normal(size=(sz, sz))
        M_ = M_ + M_.conj().T
        return M_ / opnorm(M_)
    Hg = herm(4)
    Ag, Bg = np.kron(herm(2), I2), np.kron(I2, herm(2))
    rev_ok, bound_ok, maxdiff = True, True, 0.0
    for t in (0.3, 1.0, 2.0):
        cp, cm, cB = comm_norms(Hg, Ag, Bg, t)
        rev_ok = rev_ok and abs(cp - cB) < 1e-9
        maxdiff = max(maxdiff, abs(cp - cm))
        bp = series_bound([(frozenset({0, 1}), Fr(1))], {0}, {1}, t)
        bound_ok = bound_ok and cp <= bp + 1e-12 and cm <= bp + 1e-12
    print(f"  generic two-qubit Hermitian H: max_t | ||[A(t),B]|| - ||[A(-t),B]|| | = {maxdiff:.3e}")
    check("(time reversal) generic two-qubit example: ||[A(t),B]|| = ||[A,B(-t)]|| (tolerance 1e-9)",
          rev_ok)
    check("(time reversal) generic two-qubit example: both signs within the series bound", bound_ok)
    check("(time reversal) ||[A(t),B]|| = ||[A(-t),B]|| fails on the generic example "
          "(difference > 1e-3); it held to 1e-9 on the Pauli examples above", maxdiff > 1e-3)

print(f"\n{sum(results)} of {len(results)} checks pass")
sys.exit(0 if all(results) else 1)
