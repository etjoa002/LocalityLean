"""Checks of chapter 5 of the lecture notes: local approximation and open systems.

Objects: sites {0..n-1}, local dimension d, configuration basis ordered lexicographically (site 0
most significant).  embed(X, m) as in m2_check.  The twirl P_X(M) = |G|^-1 sum_g U_g M U_g^* over the
Pauli-Weyl group G on the complement of X (clock Z_u, shift X_u, all X^a Z^b), and the conditional
expectation E_X(M)[s,s'] = [s ~_X s'] d^-|X^c| sum_eta M[(s|X, eta), (s'|X, eta)].
N_Y(M) = sup{||[M,b]|| : b local to Y, ||b|| <= 1} is estimated from below by 50 random b plus the
Weyl unitaries on Y.  Walk bound (closed form (i) of m2_check, T = union of supports):
2||a|| sum_{y in dY, x in X} (e^{2th} - 1)_{yx}, h the site matrix.

Sections (exact rational arithmetic where marked exact, otherwise numerical):
 1. twirl = conditional expectation (exact for d = 2, numerical for d = 3), locality, identity on
    local matrices, idempotence, bimodule property, unitality, Hermiticity, contractivity.
 2. the local-approximation estimate: ||M - E_X M|| <= max_g ||[M, U_g]|| <= N_{X^c}(M),
    the converse ||[M,b]|| <= 2||M - E_X M|| ||b||, strict and extremal cases.
 3. truncated dynamics on a three-qubit and a five-qubit chain: eps_r(t) against the walk bound.
 4. Lindblad generators (n = 3, d = 2): unital, contractive, positive, vanishing on S^c, G1 through
    the twirl, G2, nonzero commutator, walk bound with kappa_i = ||L_{S_i}||.
 5. degenerate inputs: X = Lambda, X = empty, K = 0, t = 0.
"""
from fractions import Fraction as Fr
from itertools import product
import random
import sys

import numpy as np

random.seed(20261007)
np.random.seed(20261007)

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


def op(n, d, X, m):
    return np.array(embed(n, d, X, m, 0j), dtype=complex)


def opx(n, d, X, m):
    return np.array(embed(n, d, X, m, Fr(0)), dtype=object)


def in_range(M, n, d, X, tol=1e-10):
    """M is local to X: zero when s, s' differ off X, depends only on (s|X, s'|X)."""
    X = sorted(X)
    cfg = list(product(range(d), repeat=n))
    rest = [i for i in range(n) if i not in X]
    seen = {}
    for a, s in enumerate(cfg):
        for b, sp in enumerate(cfg):
            if any(s[i] != sp[i] for i in rest):
                if abs(M[a][b]) > tol:
                    return False
            else:
                key = (ridx(s, X, d), ridx(sp, X, d))
                if key in seen and abs(seen[key] - M[a][b]) > tol:
                    return False
                seen.setdefault(key, M[a][b])
    return True


def opnorm(M):
    return np.linalg.norm(M, 2)


def comm(A, B):
    return A @ B - B @ A


def rand_cmat(k):
    return np.random.randn(k, k) + 1j * np.random.randn(k, k)


def rand_herm(k):
    A = rand_cmat(k)
    return (A + A.conj().T) / 2


def rand_local(n, d, X):
    return op(n, d, X, rand_cmat(d ** len(X)))


def cond_exp(M, n, d, X, scale=None):
    """E_X(M) by partial trace over the complement of X, re-embedded (works for object arrays)."""
    N = d ** n
    T = M.reshape([d] * (2 * n))
    if scale is None:
        scale = 1.0 / d
    for u in range(n):
        if u in X:
            continue
        tr = np.trace(T, axis1=u, axis2=n + u)
        new = np.zeros(T.shape, dtype=T.dtype)
        for j in range(d):
            idx = [slice(None)] * (2 * n)
            idx[u] = j
            idx[n + u] = j
            new[tuple(idx)] = tr * scale
        T = new
    return T.reshape(N, N)


def weyl_site(n, d, u, exact=False):
    if exact:
        sx = [[Fr(int(i == (j + 1) % d)) for j in range(d)] for i in range(d)]
        zz = [[Fr((1, -1)[i]) if i == j else Fr(0) for j in range(d)] for i in range(d)]
        return opx(n, d, [u], sx), opx(n, d, [u], zz)
    w = np.exp(2j * np.pi / d)
    sx = np.array([[1.0 if i == (j + 1) % d else 0.0 for j in range(d)] for i in range(d)],
                  dtype=complex)
    zz = np.diag([w ** k for k in range(d)])
    return op(n, d, [u], sx), op(n, d, [u], zz)


def weyl_group(n, d, sites, exact=False):
    """All U_g = prod_u X_u^a Z_u^b over the given sites."""
    N = d ** n
    if exact:
        one = np.array([[Fr(int(i == j)) for j in range(N)] for i in range(N)], dtype=object)
    else:
        one = np.eye(N, dtype=complex)
    out = [one]
    for u in sites:
        Xu, Zu = weyl_site(n, d, u, exact)
        loc = []
        Xa = one
        for a in range(d):
            Zb = one
            for b in range(d):
                loc.append(Xa @ Zb)
                Zb = Zb @ Zu
            Xa = Xa @ Xu
        out = [U @ V for U in out for V in loc]
    return out


def twirl(M, n, d, X, exact=False):
    G = weyl_group(n, d, [u for u in range(n) if u not in X], exact)
    acc = None
    for U in G:
        term = U @ M @ (U.T if exact else U.conj().T)
        acc = term if acc is None else acc + term
    return acc * (Fr(1, len(G)) if exact else 1.0 / len(G))


def Nsamp(M, n, d, Y):
    """Sampled lower estimate of N_Y(M), and the max over the Weyl unitaries on Y."""
    vals = [opnorm(comm(M, U)) for U in weyl_group(n, d, list(Y))]
    wmax = max(vals)
    if len(Y) > 0:
        for _ in range(50):
            b = rand_local(n, d, list(Y))
            vals.append(opnorm(comm(M, b)) / opnorm(b))
    return max(vals), wmax


def expm_gen(A):
    """exp(A) by scaling and squaring with a Taylor series."""
    nrm = np.linalg.norm(A, 1)
    s = max(0, int(np.ceil(np.log2(max(nrm, 1e-16)))) + 2)
    B = A / 2 ** s
    R = np.eye(A.shape[0], dtype=complex)
    term = np.eye(A.shape[0], dtype=complex)
    for k in range(1, 30):
        term = term @ B / k
        R = R + term
    for _ in range(s):
        R = R @ R
    return R


def heis(H, a, t):
    w, V = np.linalg.eigh(H)
    U = (V * np.exp(1j * t * w)) @ V.conj().T
    return U @ a @ U.conj().T


def site_matrix(n, terms):
    h = np.zeros((n, n))
    for S, k in terms:
        for u in S:
            for v in S:
                h[u, v] += k
    return h


def walk_sum(n, terms, X, Y, t):
    h = site_matrix(n, terms)
    w, V = np.linalg.eigh(h)
    E = (V * np.exp(2 * t * w)) @ V.T - np.eye(n)
    dY = [y for y in Y if any(y in S and any(z not in Y for z in S) for S, _ in terms)]
    return sum(E[y, x] for y in dY for x in X)


SX = np.array([[0, 1], [1, 0]], dtype=complex)
SZ = np.array([[1, 0], [0, -1]], dtype=complex)


# ------------------------------------------------------------------ section 1
print("-- 1. twirl = conditional expectation")
n, d = 3, 2
N = d ** n
SUBS = [[0], [1], [0, 2], [], [0, 1, 2]]
for X in SUBS:
    Mx = np.array([[Fr(random.randint(-5, 5), random.randint(1, 4)) for _ in range(N)]
                   for _ in range(N)], dtype=object)
    P = twirl(Mx, n, d, X, exact=True)
    E = cond_exp(Mx, n, d, X, scale=Fr(1, d))
    check(f"1a exact d=2: twirl = E_X, X={X}", (P == E).all())
for X in SUBS:
    M = rand_cmat(N)
    check(f"1a numeric d=2: twirl = E_X, X={X}",
          np.allclose(twirl(M, n, 2, X), cond_exp(M, n, 2, X), atol=1e-12))
M3 = rand_cmat(27)
for X in [[0], [0, 2], []]:
    check(f"1a numeric d=3: twirl = E_X, X={X}",
          np.allclose(twirl(M3, 3, 3, X), cond_exp(M3, 3, 3, X), atol=1e-12))
ok = {k: True for k in "bcdef"}
for X in SUBS:
    M = rand_cmat(N)
    E = cond_exp(M, n, d, X)
    ok["b"] &= in_range(E, n, d, X)
    loc = op(n, d, X, rand_cmat(d ** len(X)))
    ok["c"] &= np.allclose(cond_exp(loc, n, d, X), loc, atol=1e-12)
    ok["d"] &= np.allclose(cond_exp(E, n, d, X), E, atol=1e-12)
    a, b = rand_local(n, d, X), rand_local(n, d, X)
    ok["e"] &= np.allclose(cond_exp(a @ M @ b, n, d, X), a @ E @ b, atol=1e-12)
    ok["f"] &= np.allclose(cond_exp(np.eye(N), n, d, X), np.eye(N), atol=1e-12)
check("1b E_X(M) is local to X (all five X)", ok["b"])
check("1c E_X is the identity on matrices local to X", ok["c"])
check("1d E_X o E_X = E_X", ok["d"])
check("1e bimodule: E_X(a M b) = a E_X(M) b for a, b local to X", ok["e"])
check("1f E_X(1) = 1", ok["f"])
okh, okn = True, True
for _ in range(20):
    X = random.choice(SUBS)
    M = rand_cmat(N)
    EH = cond_exp(M + M.conj().T, n, d, X)
    okh &= np.allclose(EH, EH.conj().T, atol=1e-12)
    okn &= opnorm(cond_exp(M, n, d, X)) <= opnorm(M) + 1e-10
check("1g E_X preserves Hermiticity (20 random M)", okh)
check("1h ||E_X(M)|| <= ||M|| (20 random M)", okn)

# ------------------------------------------------------------------ section 2
print("-- 2. local-approximation estimate")
oka = okb = okc = okm = True
for X in [[0], [1], [0, 2], [0, 1]]:
    Y = [u for u in range(n) if u not in X]
    G = weyl_group(n, d, Y)
    for _ in range(3):
        M = rand_cmat(N)
        E = cond_exp(M, n, d, X)
        dist = opnorm(M - E)
        Ns, wmax = Nsamp(M, n, d, Y)
        oka &= dist <= wmax + 1e-10
        okb &= dist <= Ns + 1e-10
        av = sum(comm(M, U) @ U.conj().T for U in G) / len(G)
        okm &= np.allclose(M - E, av, atol=1e-12)
        for b in [rand_local(n, d, Y) for _ in range(50)] + G:
            okc &= opnorm(comm(M, b)) <= 2 * dist * opnorm(b) + 1e-10
check("2a ||M - E_X M|| <= max_g ||[M,U_g]|| (X in {0},{1},{0,2},{0,1}; 3 M each)", oka)
check("2a' M - P_X(M) = avg_g [M,U_g] U_g^*", okm)
check("2b ||M - E_X M|| <= N_{X^c}(M) sampled", okb)
check("2c ||[M,b]|| <= 2 ||M - E_X M|| ||b|| for 50 random b and the Weyl unitaries", okc)
M = rand_cmat(N)
dist = opnorm(M - cond_exp(M, n, d, [0]))
Ns, wmax = Nsamp(M, n, d, [1, 2])
print(f"   2d random M, X={{0}}: ||M-E M|| = {dist:.6f}, N sampled = {Ns:.6f}, "
      f"max_g = {wmax:.6f}, 2||M-EM|| = {2 * dist:.6f}")
check("2d strict case: ||M - E_X M|| < N_{X^c}(M) sampled", dist < Ns - 1e-9)
for X in [[0], [1, 2]]:
    Y = [u for u in range(n) if u not in X]
    u = Y[0]
    Mu = op(n, d, [u], SX)
    dist = opnorm(Mu - cond_exp(Mu, n, d, X))
    Ns, wmax = Nsamp(Mu, n, d, Y)
    print(f"   2d M = X_{u}, X={X}: ||M-E M|| = {dist:.6f}, N sampled = {Ns:.6f}")
    check(f"2d M = X_{u} off X={X}: ||M-EM|| = 1, N = 2 = 2||M-EM|| (factor 2 attained)",
          abs(dist - 1) < 1e-10 and abs(Ns - 2) < 1e-10)
Ml = op(n, d, [0], rand_cmat(2))
Ns, wmax = Nsamp(Ml, n, d, [1, 2])
check("2d trivial equality, M local to X: ||M-EM|| = 0 = N",
      Ns < 1e-10 and opnorm(Ml - cond_exp(Ml, n, d, [0])) < 1e-12)

# ------------------------------------------------------------------ section 3
print("-- 3. truncated dynamics, eps_r(t) = ||A(t) - E_{X_r} A(t)||")
ZZ = np.kron(SZ, SZ)
XXm = np.kron(SX, SX)
chains = {
    "3-chain": (3, [([0, 1], 1.0, ZZ), ([1, 2], 0.5, XXm)]),
    "5-chain": (5, [([i, i + 1], 1.0, ZZ) for i in range(4)]
                + [([i, i + 1], 0.5, XXm) for i in range(4)]),
}
for name, (nn, tl) in chains.items():
    H = sum(op(nn, 2, S, c * m) for S, c, m in tl)
    terms = [(S, opnorm(c * m)) for S, c, m in tl]
    a = op(nn, 2, [0], SX)
    okb = okl = True
    row = []
    for r in [0, 1, 2, nn - 1]:
        Xr = [u for u in range(nn) if u <= r]
        Y = [u for u in range(nn) if u not in Xr]
        for t in [0.1, 0.3, 1.0]:
            At = heis(H, a, t)
            E = cond_exp(At, nn, 2, Xr)
            eps = opnorm(At - E)
            bound = 2 * opnorm(a) * walk_sum(nn, terms, [0], Y, t)
            okb &= eps <= bound + 1e-10
            okl &= in_range(E, nn, 2, Xr)
            if r == nn - 1:
                okl &= eps < 1e-10
            row.append((r, t, eps, bound))
    for r, t, eps, bound in row:
        rat = eps / bound if bound > 1e-14 else float('nan')
        print(f"   3 {name} r={r} t={t}: eps = {eps:.3e}, bound = {bound:.3e}, ratio = {rat:.3e}")
    check(f"3 {name}: eps_r(t) <= walk bound for r in 0,1,2,Lambda and t in 0.1,0.3,1.0", okb)
    check(f"3 {name}: E_{{X_r}}(A(t)) local to X_r, error 0 when X_r = Lambda", okl)

# ------------------------------------------------------------------ section 4
print("-- 4. Lindblad generators")
n, d, N = 3, 2, 8
Id = np.eye(N, dtype=complex)


def make_term(S, nk=2):
    Hs = op(n, d, S, 0.25 * rand_herm(2 ** len(S)))
    Ks = [op(n, d, S, 0.2 * rand_cmat(2 ** len(S))) for _ in range(nk)]
    return Hs, Ks


def lind(Hs, Ks, a):
    out = 1j * comm(Hs, a)
    for K in Ks:
        KK = K.conj().T @ K
        out = out + K.conj().T @ a @ K - 0.5 * (KK @ a + a @ KK)
    return out


def superop(Hs, Ks):
    S = 1j * (np.kron(Hs, Id) - np.kron(Id, Hs.T))
    for K in Ks:
        KK = K.conj().T @ K
        S = S + np.kron(K.conj().T, K.T) - 0.5 * (np.kron(KK, Id) + np.kron(Id, KK.T))
    return S


def apply_super(S, a):
    return (S @ a.reshape(-1)).reshape(N, N)


terms4 = {tuple(S): make_term(S) for S in ([0, 1], [1, 2])}
Ltot = sum(superop(*terms4[S]) for S in terms4)
Wall = weyl_group(n, d, [0, 1, 2])
sample_a = [rand_cmat(N) for _ in range(200)] + Wall + [Id]


def super_norm(S, extra=()):
    return max(opnorm(apply_super(S, a)) / opnorm(a) for a in sample_a + list(extra))


okU = okC = okP = True
worst = 0.0
for t in [0.2, 1.0, 3.0]:
    T = expm_gen(t * Ltot)
    okU &= np.allclose(apply_super(T, Id), Id, atol=1e-9)
    mx = max(opnorm(apply_super(T, a)) / opnorm(a) for a in sample_a)
    worst = max(worst, mx)
    okC &= mx <= 1 + 1e-9 and abs(opnorm(apply_super(T, Id)) - 1) < 1e-9
    for _ in range(10):
        A = rand_cmat(N)
        Q = apply_super(T, A @ A.conj().T)
        okP &= np.linalg.eigvalsh((Q + Q.conj().T) / 2)[0] >= -1e-9
print(f"   4a max sampled ||exp(tL)(a)||/||a|| over t in 0.2,1,3: {worst:.6f}")
check("4a exp(tL)(1) = 1 for t in 0.2, 1, 3", okU)
check("4a sampled ||exp(tL)||_{op->op} <= 1, equal to 1 at the identity", okC)
check("4a exp(tL) maps random PSD to PSD", okP)

okb = okmech = okineq = okexpl = True
rows = []
for S in ([0, 1], [1, 2]):
    Hs, Ks = terms4[tuple(S)]
    Sc = [u for u in range(n) if u not in S]
    for _ in range(3):
        okb &= opnorm(lind(Hs, Ks, rand_local(n, d, Sc))) < 1e-10
    kap_e = 2 * opnorm(Hs) + 2 * sum(opnorm(K) ** 2 for K in Ks)
    SS = superop(Hs, Ks)
    for _ in range(5):
        c = rand_cmat(N)
        dc = c - cond_exp(c, n, d, Sc)
        okmech &= np.allclose(lind(Hs, Ks, c), lind(Hs, Ks, dc), atol=1e-10)
        Ns, wmax = Nsamp(c, n, d, S)
        Lnorm = super_norm(SS, extra=[c, dc])
        lhs = opnorm(lind(Hs, Ks, c))
        okineq &= lhs <= Lnorm * Ns + 1e-10
        okexpl &= lhs <= kap_e * Ns + 1e-10
        rows.append((S, lhs, Lnorm, kap_e, Ns))
for S, lhs, Ln, ke, Ns in rows[:2] + rows[5:7]:
    print(f"   4c S={S}: ||L_S(c)|| = {lhs:.4f}, ||L_S|| sampled = {Ln:.4f}, "
          f"explicit kappa = {ke:.4f}, N_S(c) = {Ns:.4f}, ratio lhs/(||L_S|| N_S) = "
          f"{lhs / (Ln * Ns):.4f}")
check("4b L_S(c) = 0 for c local to S^c (S = {0,1}, {1,2})", okb)
check("4c mechanism L_S(c) = L_S(c - E_{S^c}(c)) to 1e-10", okmech)
check("4c ||L_S(c)|| <= ||L_S|| N_S(c) (||L_S|| sampled, including c and c-E c)", okineq)
check("4c ||L_S(c)|| <= (2||H_S|| + 2 sum ||K_j||^2) N_S(c)", okexpl)

okd = True
for S in ([1, 2], [0, 1]):
    Hs, Ks = terms4[tuple(S)]
    for Z in ([0], [2], [1]):
        out = lind(Hs, Ks, rand_local(n, d, Z))
        okd &= in_range(out, n, d, sorted(set(Z) | set(S)))
check("4d G2: L_S(c) local to Z union S (Z in {0},{2},{1}; S in {1,2},{0,1})", okd)

a0 = op(n, d, [0], SX)
b2 = op(n, d, [2], SX)
c0 = opnorm(comm(apply_super(expm_gen(0 * Ltot), a0), b2))
c5 = opnorm(comm(apply_super(expm_gen(0.5 * Ltot), a0), b2))
print(f"   4e ||[exp(tL)(X_0), X_2]|| at t=0: {c0:.3e}, at t=0.5: {c5:.6f}")
check("4e [exp(tL)(sx_0), sx_2] = 0 at t=0, nonzero at t=0.5", c0 < 1e-12 and c5 > 1e-6)

kap_s, kap_x = [], []
for S in ([0, 1], [1, 2]):
    Hs, Ks = terms4[tuple(S)]
    kap_s.append((S, super_norm(superop(Hs, Ks))))
    kap_x.append((S, 2 * opnorm(Hs) + 2 * sum(opnorm(K) ** 2 for K in Ks)))
aa, bb = op(n, d, [0], SX), op(n, d, [2], SZ)
okf = okfe = okfl = True
for t in [0.3, 1.0]:
    lhs = opnorm(comm(apply_super(expm_gen(t * Ltot), aa), bb))
    bs = 2 * walk_sum(n, kap_s, [0], [2], t)
    be = 2 * walk_sum(n, kap_x, [0], [2], t)
    okf &= lhs <= bs + 1e-10
    okfe &= lhs <= be + 1e-10
    okfl &= be >= bs
    print(f"   4f t={t}: ||[T_t(a),b]|| = {lhs:.5f}, bound(kappa sampled {kap_s[0][1]:.3f},"
          f"{kap_s[1][1]:.3f}) = {bs:.5f}, bound(explicit {kap_x[0][1]:.3f},{kap_x[1][1]:.3f}) = "
          f"{be:.5f}")
check("4f walk bound with kappa_i = ||L_{S_i}|| (sampled) dominates ||[exp(tL)(a), b]||", okf)
check("4f walk bound with explicit kappa dominates ||[exp(tL)(a), b]||", okfe)
check("4f explicit-kappa bound >= sampled-kappa bound", okfl)

# ------------------------------------------------------------------ section 5
print("-- 5. degenerate inputs")
M = rand_cmat(8)
check("5 X = Lambda: E is the identity", np.allclose(cond_exp(M, 3, 2, [0, 1, 2]), M))
check("5 X = empty: E(M) = tr(M)/d^n 1",
      np.allclose(cond_exp(M, 3, 2, []), np.trace(M) / 8 * np.eye(8)))
Hs = op(3, 2, [0, 1], rand_herm(4))
Lh = superop(Hs, [])
a = rand_cmat(8)
check("5 K = 0: exp(tL) a = e^{itH} a e^{-itH}",
      np.allclose(apply_super(expm_gen(0.7 * Lh), a), heis(Hs, a, 0.7), atol=1e-9))
check("5 K = 0: L a = i[H, a]", np.allclose(apply_super(Lh, a), 1j * comm(Hs, a)))
check("5 t = 0: exp(0 L) = identity and A(0) = a",
      np.allclose(apply_super(expm_gen(0 * Ltot), a), a) and np.allclose(heis(Hs, a, 0.0), a))
check("5 Weyl group sizes d^(2k)",
      len(weyl_group(3, 2, [0, 1])) == 16 and len(weyl_group(3, 3, [0])) == 9)

# ------------------------------------------------------------------ summary
npass = sum(results)
print(f"m3_check: {npass} of {len(results)} checks passed")
sys.exit(0 if npass == len(results) else 1)
