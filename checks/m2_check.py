"""Checks of chapter 4 of the lecture notes: the qudit instance.

Objects: sites {0..n-1}, local dimension d, configuration basis ordered lexicographically (site 0
most significant).  embed(X, m)[s, s'] = m[s|X, s'|X] if s, s' agree off X, else 0.  A Hamiltonian
is a finite family of terms (S_i, Phi_i = embed(S_i, m_i)), m_i Hermitian; a(t) = e^{itH} a e^{-itH},
L a = i[H, a].  Site matrix h_uv = sum over terms containing u, v of ||Phi_i|| (operator norm),
boundary dY = Y meet union of the S_i crossing Y.  Closed form (i):
||[a(t), b]|| <= 2||a|| ||b|| ([X meet Y nonempty] + sum_{y in dY, x in X meet T} (e^{2th} - 1)_{yx}).

Sections (exact rational arithmetic where marked exact, otherwise numerical):
 1. local algebras (exact; n = 4, d = 2 and n = 3, d = 3): embed is a unital *-homomorphism,
    isotony, causality (disjoint supports commute), nontriviality (range characterization),
    non-commuting pairs on overlapping supports.
 2. derivation generators (n = 3, d = 2, random terms): expm(tL) a = e^{itH} a e^{-itH},
    ||e^{itH}|| = 1, G1 mechanism ||[Phi, c]|| <= ||Phi|| N_S(c), N_S(c) <= 2||c||, sharpness of 2.
 3. two-qubit witness H = X0 X1 and the three-qubit chain of checks/m1a_check.py: exact [i[H,a],b], exact
    a(t), ||[a(t), b]|| = 2|sin 2t|, closed form (i) dominates, ratios recorded.
 4. role exchange and time reversal: ||[a(t),b]|| = ||[a,b(-t)]||; t -> -t fails on an example;
    closed form (i) with roles exchanged, and the minimum of the two bounds.
 5. the F-norm as the F-bound (exact on a chain of 8 sites): ||Phi||_F, C_F(Lambda) for 8, 16, 32
    sites against 2^alpha ||F||, exponential weighting, closed form (ii) dominates (i).
 6. reproducing constants on Z^D grids: chain of 20 (alpha = 2) and 6 x 6 grid (alpha = 3).
"""
from fractions import Fraction as Fr
from itertools import product, combinations
import math
import random
import sys

import numpy as np

random.seed(20261006)
np.random.seed(20261006)

results = []


def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    results.append(bool(cond))
    return cond


# ------------------------------------------------------------------ helpers
def ridx(s, X, d):
    r = 0
    for i in X:
        r = r * d + s[i]
    return r


def embed(n, d, X, m, zero):
    """embed(X, m) as a nested list; X a sorted list of sites, m a d^|X| square array."""
    X = sorted(X)
    cfg = list(product(range(d), repeat=n))
    rest = [i for i in range(n) if i not in X]
    N = len(cfg)
    M = [[zero] * N for _ in range(N)]
    rs = [ridx(s, X, d) for s in cfg]
    for a, s in enumerate(cfg):
        for b, sp in enumerate(cfg):
            if all(s[i] == sp[i] for i in rest):
                M[a][b] = m[rs[a]][rs[b]]
    return M


def embed_within(X, Y, m, d, zero):
    Ys = sorted(Y)
    return embed(len(Ys), d, [Ys.index(x) for x in sorted(X)], m, zero)


def mmul(A, B):
    N = len(A)
    Bt = list(zip(*B))
    return [[sum((A[i][k] * Bt[j][k] for k in range(N) if A[i][k] != 0), Fr(0))
             for j in range(N)] for i in range(N)]


def dag(A):
    return [list(r) for r in zip(*A)]  # real rational entries: adjoint = transpose


def eye(N):
    return [[Fr(int(i == j)) for j in range(N)] for i in range(N)]


def rand_rat_matrix(N):
    return [[Fr(random.randint(-5, 5), random.randint(1, 4)) for _ in range(N)] for _ in range(N)]


def in_range(M, n, d, X):
    """M in the range of embed(X, .): zero when s, s' differ off X, and depends only on s|X, s'|X."""
    X = sorted(X)
    cfg = list(product(range(d), repeat=n))
    rest = [i for i in range(n) if i not in X]
    seen = {}
    for a, s in enumerate(cfg):
        for b, sp in enumerate(cfg):
            if any(s[i] != sp[i] for i in rest):
                if M[a][b] != 0:
                    return False
            else:
                key = (ridx(s, X, d), ridx(sp, X, d))
                if key in seen and seen[key] != M[a][b]:
                    return False
                seen[key] = M[a][b]
    return True


def shift(d):
    """generalised sigma^x (cyclic shift); for d = 2 it is sigma^x."""
    return [[Fr(int((i + 1) % d == j)) for j in range(d)] for i in range(d)]


def zdiag(d):
    return [[Fr(i if i == j else 0) if d > 2 else Fr((1, -1)[i] if i == j else 0)
             for j in range(d)] for i in range(d)]


def rand_subset(n, lo=1):
    k = random.randint(lo, n)
    return sorted(random.sample(range(n), k))


# numerical helpers
SX = np.array([[0, 1], [1, 0]], dtype=complex)
SY = np.array([[0, -1j], [1j, 0]], dtype=complex)
SZ = np.array([[1, 0], [0, -1]], dtype=complex)
I2 = np.eye(2, dtype=complex)


def kron(*ms):
    out = np.eye(1, dtype=complex)
    for m in ms:
        out = np.kron(out, m)
    return out


def op(n, d, X, m):
    return np.array(embed(n, d, X, m, 0j), dtype=complex)


def opnorm(M):
    return np.linalg.norm(M, 2)


def comm(A, B):
    return A @ B - B @ A


def U(H, t):
    w, V = np.linalg.eigh(H)
    return (V * np.exp(1j * t * w)) @ V.conj().T


def evolve(H, a, t):
    Ut = U(H, t)
    return Ut @ a @ Ut.conj().T


def rand_herm(N):
    A = np.random.randn(N, N) + 1j * np.random.randn(N, N)
    return (A + A.conj().T) / 2


def rand_op(N):
    return np.random.randn(N, N) + 1j * np.random.randn(N, N)


def site_matrix(n, supports, kappas):
    h = np.zeros((n, n))
    for S, k in zip(supports, kappas):
        for u in S:
            for v in S:
                h[u, v] += float(k)
    return h


def crosses(S, Z):
    return bool(set(S) & set(Z)) and not set(S) <= set(Z)


def expm_sym(h, s):
    w, V = np.linalg.eigh(h)
    return (V * np.exp(s * w)) @ V.T


def closed_i(h, supports, t, X, Y):
    """2 ([X meet Y] + sum_{y in dY, x in X meet T} (e^{2|t|h} - 1)_{yx}), ||a|| = ||b|| = 1."""
    X, Y = set(X), set(Y)
    T = set().union(*map(set, supports)) if supports else set()
    dY = Y & set().union(set(), *[set(S) for S in supports if crosses(S, Y)])
    M = expm_sym(h, 2 * abs(t)) - np.eye(len(h))
    tot = float(bool(X & Y)) + sum(M[y, x] for y in dY for x in X & T)
    return 2 * tot


# ------------------------------------------------------------------ section 1
def section1():
    print("-- section 1: local algebras (exact)")
    for (n, d) in [(4, 2), (3, 3)]:
        tag = f"n={n},d={d}: "
        Nfull = d ** n
        Lam = list(range(n))
        ok_h = ok_dag = ok_unit = True
        for _ in range(4):
            X = rand_subset(n)
            k = d ** len(X)
            m, mp = rand_rat_matrix(k), rand_rat_matrix(k)
            e = lambda mm: embed(n, d, X, mm, Fr(0))
            ok_h &= e(mmul(m, mp)) == mmul(e(m), e(mp))
            ok_dag &= e(dag(m)) == dag(e(m))
            ok_unit &= e(eye(k)) == eye(Nfull)
        check(tag + "(a) embed multiplicative", ok_h)
        check(tag + "(a) embed *-preserving", ok_dag)
        check(tag + "(a) embed unital", ok_unit)
        # additivity as well
        X = rand_subset(n)
        k = d ** len(X)
        m, mp = rand_rat_matrix(k), rand_rat_matrix(k)
        s_ = [[a + b for a, b in zip(r1, r2)] for r1, r2 in zip(m, mp)]
        E_ = lambda mm: embed(n, d, X, mm, Fr(0))
        check(tag + "(a) embed additive",
              E_(s_) == [[a + b for a, b in zip(r1, r2)] for r1, r2 in zip(E_(m), E_(mp))])
        ok = True
        for _ in range(5):
            Y = rand_subset(n, 2)
            sub = [x for x in Y if random.random() < 0.5] or [Y[0]]
            m = rand_rat_matrix(d ** len(sub))
            ok &= embed(n, d, sub, m, Fr(0)) == embed(
                n, d, Y, embed_within(sub, Y, m, d, Fr(0)), Fr(0))
        check(tag + "(b) isotony X in Y: embed(X,m) = embed(Y, embed_within(X,Y,m))", ok)
        ok, cnt = True, 0
        while cnt < 10:
            X = rand_subset(n - 1)
            rest = [i for i in Lam if i not in X]
            Y = sorted(random.sample(rest, random.randint(1, len(rest))))
            m, mp = rand_rat_matrix(d ** len(X)), rand_rat_matrix(d ** len(Y))
            A, B = embed(n, d, X, m, Fr(0)), embed(n, d, Y, mp, Fr(0))
            ok &= mmul(A, B) == mmul(B, A)
            cnt += 1
        check(tag + "(c) causality: disjoint supports commute (10 pairs)", ok)
        ok_range = all(in_range(embed(n, d, X, rand_rat_matrix(d ** len(X)), Fr(0)), n, d, X)
                       for X in [rand_subset(n) for _ in range(5)])
        check(tag + "(d) embed(X, .) lands in the characterised range", ok_range)
        ok_nt = True
        for r in range(1, n):
            for X in combinations(Lam, r):
                j = [i for i in Lam if i not in X][0]
                M = embed(n, d, [j], shift(d), Fr(0))
                ok_nt &= not in_range(M, n, d, list(X))
        check(tag + "(d) every X != Lambda: a one-site shift off X is outside the range", ok_nt)
        if d == 2:
            M = embed(n, d, [1], shift(2), Fr(0))
            check(tag + "(d) example: sigma^x on site 1 is not in the range for X = {0}",
                  not in_range(M, n, d, [0]) and in_range(M, n, d, [1]))
        ok = True
        for X, Y in [([0, 1], [1, 2]), ([0], [0, 3 % n]), ([1, 2], [0, 2])]:
            j = min(set(X) & set(Y))
            Zm = zdiag(d) if d == 2 else [[Fr(int(i == j2 and i == 0)) for j2 in range(d)]
                                         for i in range(d)]
            A = embed(n, d, X, embed_within([j], X, shift(d), d, Fr(0)), Fr(0))
            B = embed(n, d, Y, embed_within([j], Y, Zm, d, Fr(0)), Fr(0))
            ok &= mmul(A, B) != mmul(B, A)
        check(tag + "(e) overlapping supports: shift and diagonal projector on the shared "
              "site do not commute", ok)


# ------------------------------------------------------------------ section 2
def build_h3():
    n, d = 3, 2
    m1, m2 = rand_herm(4), rand_herm(4)
    P1, P2 = op(n, d, [0, 1], m1), op(n, d, [1, 2], m2)
    return n, d, [[0, 1], [1, 2]], [P1, P2]


N3, D3, SUP3, TERMS3 = None, None, None, None


def section2():
    global N3, D3, SUP3, TERMS3
    print("-- section 2: derivation generators (numerical)")
    N3, D3, SUP3, TERMS3 = build_h3()
    H = sum(TERMS3)
    Nn = 8
    a = rand_op(Nn)
    Lmat = 1j * (np.kron(H, np.eye(Nn)) - np.kron(np.eye(Nn), H.T))  # vec = row-major
    w, V = np.linalg.eigh(-1j * Lmat)  # L = i K, K Hermitian
    ok = True
    for t in (0.3, 1.0, -0.7):
        eL = (V * np.exp(1j * t * w)) @ V.conj().T
        lhs = (eL @ a.reshape(-1)).reshape(Nn, Nn)
        ok &= np.max(np.abs(lhs - evolve(H, a, t))) < 1e-10
    check("(a) expm(tL) a = e^{itH} a e^{-itH}, t = 0.3, 1.0, -0.7", ok)
    check("(b) ||e^{itH}|| = 1",
          all(abs(opnorm(U(H, t)) - 1) < 1e-12 for t in (0.3, 1.0, -0.7)))
    ok_eq = ok_N = True
    for P, S in zip(TERMS3, SUP3):
        kap = opnorm(P)
        c = rand_op(Nn)
        lhs = opnorm(comm(P, c))
        ok_eq &= abs(lhs - kap * opnorm(comm(c, P / kap))) < 1e-10
        Nlb = opnorm(comm(c, P / kap))
        for _ in range(30):
            b = op(3, 2, S, rand_op(4))
            b = b / opnorm(b)
            Nlb = max(Nlb, opnorm(comm(c, b)))
        ok_N &= (lhs <= kap * Nlb + 1e-10) and (Nlb <= 2 * opnorm(c) + 1e-10)
    check("(c) G1 mechanism ||[Phi,c]|| = ||Phi|| ||[c, Phi/||Phi||]|| (tautology, equality)",
          ok_eq)
    check("(c) ||[Phi,c]|| <= ||Phi|| N_S(c) and N_S(c) (sampled from below) <= 2||c||", ok_N)
    Phi = kron(SX, SX)
    c = kron(SZ, I2)
    check("(d) sharpness: ||[Phi, c]|| = 2||Phi|| ||c|| for sigma^z_0 vs sigma^x_0 sigma^x_1",
          abs(opnorm(comm(Phi, c)) - 2 * opnorm(Phi) * opnorm(c)) < 1e-12)
    check("(d) ||L_i c|| <= 2||Phi_i|| ||c|| on random c",
          all(opnorm(comm(P, (c2 := rand_op(8)))) <= 2 * opnorm(P) * opnorm(c2) + 1e-10
              for P in TERMS3 for _ in range(10)))


# ------------------------------------------------------------------ section 3
def section3():
    print("-- section 3: two-qubit witness and three-qubit chain")
    H = kron(SX, SX)
    a, b = kron(SZ, I2), kron(I2, SZ)
    check("(a) [a, b] = 0", opnorm(comm(a, b)) == 0)
    La = 1j * comm(H, a)
    check("(b) i[H, sigma^z_0] = 2 sigma^y x sigma^x", np.max(np.abs(La - 2 * kron(SY, SX))) < 1e-12)
    C = comm(La, b)
    check("(b) [i[H,a], b] = -4i sigma^y x sigma^y != 0",
          np.max(np.abs(C + 4j * kron(SY, SY))) < 1e-12 and opnorm(C) > 1)
    print("     [i[H,a],b] =")
    for row in C:
        print("       " + "  ".join(f"{z.real:+.0f}{z.imag:+.0f}i" for z in row))
    ok_a = ok_n = True
    ts = (0.1, 0.3, math.pi / 4, 1.0)
    for t in ts:
        at = a @ (math.cos(2 * t) * np.eye(4) - 1j * math.sin(2 * t) * H)
        ok_a &= np.max(np.abs(at - evolve(H, a, t))) < 1e-12
        ok_n &= abs(opnorm(comm(evolve(H, a, t), b)) - 2 * abs(math.sin(2 * t))) < 1e-12
    check("(c) a(t) = sigma^z_0 (cos 2t - i sin 2t H)", ok_a)
    check("(c) ||[a(t), b]|| = 2|sin 2t| at t = 0.1, 0.3, pi/4, 1.0", ok_n)
    h = np.ones((2, 2))
    sup = [[0, 1]]
    ok = ok_f = True
    print("     closed form (i) for the witness: t, exact norm, bound e^{4t}-1, ratio")
    for t in ts:
        ex = 2 * abs(math.sin(2 * t))
        bd = closed_i(h, sup, t, [0], [1])
        ok_f &= abs(bd - (math.exp(4 * t) - 1)) < 1e-10
        ok &= bd >= ex - 1e-12
        print(f"       t={t:.4f}  exact={ex:.6f}  bound={bd:.6f}  ratio={bd / ex:.4f}")
    check("(d) closed form (i) equals e^{4t} - 1 (entry (e^{2th}-1)_{10} = (e^{4t}-1)/2)", ok_f)
    check("(d) e^{4t} - 1 >= 2|sin 2t| at the four times", ok)
    # three-qubit chain
    Hc = kron(SZ, SZ, I2) + 0.5 * kron(I2, SX, SX)
    a, b = kron(SX, I2, I2), kron(I2, I2, SZ)
    hc = np.array([[1, 1, 0], [1, 1.5, 0.5], [0, 0.5, 0.5]])
    check("(e) site matrix of the chain from the term norms",
          np.allclose(site_matrix(3, [[0, 1], [1, 2]], [1, 0.5]), hc))
    ok_x = ok_b = True
    print("     chain: t, exact norm, bound, ratio")
    for t in (0.2, 0.5, 1.0):
        ex = opnorm(comm(evolve(Hc, a, t), b))
        formula = 0.8 * (1 - math.cos(math.sqrt(5) * t))
        bd = closed_i(hc, [[0, 1], [1, 2]], t, [0], [2])
        ok_x &= abs(ex - formula) < 1e-10
        ok_b &= bd >= ex
        print(f"       t={t}  exact={ex:.6f}  (4/5)(1-cos)={formula:.6f}  bound={bd:.6f}")
    check("(e) exact norm: ||[a(t), b]|| = (4/5)(1 - cos sqrt5 t)", ok_x)
    check("(e) closed form (i) dominates the chain norm at t = 0.2, 0.5, 1", ok_b)


# ------------------------------------------------------------------ section 4
def section4():
    print("-- section 4: role exchange and time reversal (numerical)")
    H = sum(TERMS3)
    kap = [opnorm(P) for P in TERMS3]
    h = site_matrix(3, SUP3, kap)
    a = op(3, 2, [0], rand_op(2))
    b = op(3, 2, [2], rand_op(2))
    a, b = a / opnorm(a), b / opnorm(b)
    ok = True
    for t in (0.3, 1.0):
        lhs = opnorm(comm(evolve(H, a, t), b))
        rhs = opnorm(comm(a, evolve(H, b, -t)))
        ok &= abs(lhs - rhs) < 1e-10
    check("(a) ||[a(t), b]|| = ||[a, b(-t)]|| at t = 0.3, 1.0", ok)
    found = None
    for _ in range(50):
        a2 = op(3, 2, [0], rand_op(2))
        b2 = op(3, 2, [2], rand_op(2))
        a2, b2 = a2 / opnorm(a2), b2 / opnorm(b2)
        p = opnorm(comm(evolve(H, a2, 0.7), b2))
        q = opnorm(comm(evolve(H, a2, -0.7), b2))
        if abs(p - q) > 1e-3:
            found = (p, q)
            break
    check("(b) ||[a(t), b]|| = ||[a(-t), b]|| fails on an example", found is not None)
    if found:
        print(f"     example t = 0.7: ||[a(t),b]|| = {found[0]:.6f}, ||[a(-t),b]|| = {found[1]:.6f}")
    ok1 = ok2 = ok3 = True
    for t in (0.3, 1.0, -0.5, -1.0):
        ex = opnorm(comm(evolve(H, a, t), b))
        b1 = closed_i(h, SUP3, t, [0], [2])   # sum over dY, X meet T
        b2 = closed_i(h, SUP3, t, [2], [0])   # roles exchanged: dX, Y meet T
        ok1 &= b1 >= ex - 1e-10
        ok2 &= b2 >= ex - 1e-10
        ok3 &= min(b1, b2) >= ex - 1e-10
    check("(c) closed form (i) dominates at t = 0.3, 1.0, -0.5, -1.0", ok1)
    check("(c) closed form (i) with roles exchanged (|t|) dominates", ok2)
    check("(c) the minimum of the two bounds dominates", ok3)


# ------------------------------------------------------------------ section 5, 6
def Fpoly(n, alpha=2):
    return [[Fr(1, (1 + abs(x - y)) ** alpha) for y in range(n)] for x in range(n)]


def CF_exact(F):
    n = len(F)
    best = Fr(0)
    for x in range(n):
        for y in range(n):
            s = sum(F[x][z] * F[z][y] for z in range(n)) / F[x][y]
            best = max(best, s)
    return best


def section5():
    print("-- section 5: F-norm as F-bound (exact on chains)")
    n = 8
    kappas = [Fr(random.randint(1, 8), 4) for _ in range(n - 1)]
    supports = [(j, j + 1) for j in range(n - 1)]
    h = [[Fr(0)] * n for _ in range(n)]
    for S, k in zip(supports, kappas):
        for u in S:
            for v in S:
                h[u][v] += k
    F = Fpoly(n)
    NF = max(h[x][y] / F[x][y] for x in range(n) for y in range(n))
    check("(a) h_xy <= ||Phi||_F F(x,y) for all x,y", all(h[x][y] <= NF * F[x][y]
                                                       for x in range(n) for y in range(n)))
    nsy = max(sum(k for S, k in zip(supports, kappas) if x in S and y in S) / F[x][y]
              for x in range(n) for y in range(n))
    check("(a) ||Phi||_F equals sup (1/F(d(x,y))) sum_{Z containing x,y} ||Phi(Z)||", nsy == NF)
    print(f"     ||Phi||_F = {NF} = {float(NF):.6f}")
    CF8 = None
    ok = True
    for L in (8, 16, 32):
        FL = Fpoly(L)
        C = CF_exact(FL)
        nF = max(sum(r) for r in FL)
        ok &= C <= 4 * nF
        print(f"     chain {L}: C_F = {float(C):.6f}, ||F|| = {float(nF):.6f}, "
              f"2^alpha ||F|| = {float(4 * nF):.6f}")
        if L == 8:
            CF8 = C
    check("(b) C_F(Lambda) <= 2^alpha ||F|| for chains of 8, 16, 32 (alpha = 2)", ok)
    ok = True
    for L in (8, 32):
        FL = np.array([[float(v) for v in r] for r in Fpoly(L)])
        C = float(CF_exact(Fpoly(L)))
        for mu in (0.5, 1.0):
            idx = np.arange(L)
            Fm = np.exp(-mu * np.abs(idx[:, None] - idx[None, :])) * FL
            ok &= bool(np.all(Fm @ Fm <= C * Fm * (1 + 1e-12)))
    check("(c) F_mu * F_mu <= C_F F_mu with the same C_F (mu = 0.5, 1; chains 8, 32)", ok)
    Fn = np.array([[float(v) for v in r] for r in F])
    C, N = float(CF8), float(NF)
    hn = np.array([[float(v) for v in r] for r in h])
    sup = [list(S) for S in supports]
    ok = True
    for t in (0.1, 0.5):
        b1 = closed_i(hn, sup, t, [0], [5, 6, 7])
        # dY = {5}, X meet T = {0}
        b2 = 2 * (math.exp(2 * N * C * t) - 1) / C * Fn[5, 0]
        print(f"     t={t}: closed (i) = {b1:.6g}, closed (ii) = {b2:.6g}")
        ok &= b2 >= b1
    check("(d) closed form (ii) dominates closed form (i), X = {0}, Y = {5,6,7}, t = 0.1, 0.5", ok)


def section6():
    print("-- section 6: reproducing property on Z^D grids")

    def stats(points, alpha):
        P = np.array(points)
        dist = np.abs(P[:, None, :] - P[None, :, :]).sum(-1)
        F = (1.0 + dist) ** (-alpha)
        C = ((F @ F) / F).max()
        return C, F.sum(1).max()

    C, nF = stats([(i,) for i in range(20)], 2)
    print(f"     chain 20, alpha=2: C_F = {C:.6f}, ||F|| = {nF:.6f}, 2^alpha ||F|| = {4 * nF:.6f}")
    check("chain of 20, alpha = 2: C_F <= 2^alpha ||F||", C <= 4 * nF)
    C, nF = stats([(i, j) for i in range(6) for j in range(6)], 3)
    print(f"     grid 6x6, alpha=3: C_F = {C:.6f}, ||F|| = {nF:.6f}, 2^alpha ||F|| = {8 * nF:.6f}")
    check("6x6 grid, alpha = 3: C_F <= 2^alpha ||F||", C <= 8 * nF)


section1()
section2()
section3()
section4()
section5()
section6()

print(f"m2_check: {sum(results)} of {len(results)} checks passed")
if not all(results):
    sys.exit(1)
