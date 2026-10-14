"""Checks of chapter 7 of the lecture notes: harmonic bosons on a finite chain.

Phase space V = R^n (+) R^n, vectors f = (f^q, f^p), sigma(f, g) = f^T J g, J = [[0, I], [-I, 0]].
Hamiltonian H = (1/2) xi^T M xi, xi = (q, p), M = diag(A, I), A_xx = w^2 + 2 lam (w^2 + lam at the two
ends), A_{x,x+-1} = -lam; this is H = (1/2) sum_x [p_x^2 + w^2 q_x^2 + lam (q_x - q_{x+1})^2]
(the factor 1/2 is part of the convention).  Flow xi' = J M xi, T_t = exp(tK), K = J M.
Weyl relation W(f) W(g) = exp(-i sigma(f,g)/2) W(f+g), alpha_t(W(f)) = W(T_t f).
Block (y, x) of a 2n x 2n matrix: rows (y, n+y), columns (x, n+x); block norm = operator norm.
Site matrix h_{yx} = ||K_{yx}||; v = ||h||_inf (maximal row sum).

Sections (exact = to 1e-10, numerical = marked):
 1-3. K Hamiltonian, T_t symplectic, one-parameter group, sigma invariant.
 4.   |1 - e^{-i s}| = 2|sin(s/2)| <= |s|.
 5-6. entrywise bound ||(e^{tK})_{yx}|| <= (e^{th})_{yx}; power bound ||(K^m)_{yx}|| <= (h^m)_{yx}.
 7.   the commutator bound chain for f at site 0, g at site y.
 8.   light cone: decay per site (numerical, least squares of the log over y = 3..7).
 9.   comparison with the velocity of Nachtergaele-Raz-Schlein-Sims (2009), Theorem 3.1.
 10.  the chain at w = 0, lam = 1 (numbers only).
 16.  degenerate cases: no coupling (lam = 0), the zero label, a chain of one site.
"""
import math
import sys

import numpy as np
from scipy.linalg import expm

np.random.seed(20261007)
results = []
TOL = 1e-10


def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    results.append(bool(cond))
    return cond


def chain(n, w, lam):
    A = np.zeros((n, n))
    for x in range(n):
        A[x, x] = w ** 2 + (2 if 0 < x < n - 1 else 1) * lam
        if x + 1 < n:
            A[x, x + 1] = A[x + 1, x] = -lam
    Z = np.zeros((n, n))
    M = np.block([[A, Z], [Z, np.eye(n)]])
    J = np.block([[Z, np.eye(n)], [-np.eye(n), Z]])
    return A, M, J, J @ M


def blk(T, y, x, n):
    return T[np.ix_([y, n + y], [x, n + x])]


def site_matrix(K, n):
    return np.array([[np.linalg.norm(blk(K, y, x, n), 2) for x in range(n)] for y in range(n)])


n, w, lam = 8, 1.0, 1.0
A, M, J, KH = chain(n, w, lam)
K = KH.T   # generator acting on Weyl labels: K = K_H^T, K_H = J M Hamilton's matrix
I2 = np.eye(2 * n)


def sig(f, g):
    return f @ J @ g


ts = [0.25, 0.5, 1.0, 2.0]
h = site_matrix(K, n)
v = np.abs(h).sum(axis=1).max()
print(f"n = {n}, omega = {w}, lambda = {lam}, H = (1/2) xi^T M xi; h row sums = "
      f"{np.round(h.sum(axis=1), 4).tolist()}, v = ||h||_inf = {v:.6f}")

# ------------------------------------------------------------------ 1-3
print("-- 1. K Hamiltonian, T_t symplectic")
e1 = np.abs(K.T @ J + J @ K).max()
check(f"1a K^T J + J K = 0 (max entry {e1:.2e})", e1 < TOL)
e1b = max(np.abs(expm(t * K).T @ J @ expm(t * K) - J).max() for t in ts + [3.7])
check(f"1b T_t^T J T_t = J, t in 0.25..3.7 (max entry {e1b:.2e})", e1b < TOL)
print("-- 2. one-parameter group")
e2 = max(np.abs(expm(s * K) @ expm(t * K) - expm((s + t) * K)).max()
         for s in [0.3, 1.1] for t in [0.7, 2.0])
check(f"2a T_s T_t = T_(s+t) (max entry {e2:.2e})", e2 < TOL)
check("2b T_0 = I", np.abs(expm(0 * K) - I2).max() < TOL)
e2c = max(np.abs(expm(t * K) - expm(t * KH).T).max() for t in ts)
check(f"2c K = K_H^T is Hamiltonian (K^T J + J K = 0) and T_t(K) = T_t(K_H)^T (max entry {e2c:.2e})",
      np.abs(K.T @ J + J @ K).max() < TOL and e2c < TOL)
print("-- 3. sigma invariant")
e3 = 0.0
for t in ts:
    T = expm(t * K)
    for _ in range(20):
        f, g = np.random.randn(2 * n), np.random.randn(2 * n)
        e3 = max(e3, abs(sig(T @ f, T @ g) - sig(f, g)))
check(f"3 sigma(T_t f, T_t g) = sigma(f, g), 80 random pairs (max error {e3:.2e})", e3 < TOL)

# ------------------------------------------------------------------ 4
print("-- 4. Weyl commutator norm")
s = np.linspace(-20, 20, 4001)
lhs = np.abs(1 - np.exp(-1j * s))
mid = 2 * np.abs(np.sin(s / 2))
e4 = np.abs(lhs - mid).max()
check(f"4a |1 - e^(-i s)| = 2|sin(s/2)| on 4001 points (max error {e4:.2e})", e4 < TOL)
check("4b 2|sin(s/2)| <= |s| on the same points", (mid <= np.abs(s) + TOL).all())

# ------------------------------------------------------------------ 5
print("-- 5. entrywise bound")
worst, where = 0.0, None
ok5 = True
for t in ts:
    T = expm(t * K)
    E = expm(t * h)
    for y in range(n):
        for x in range(n):
            a, b = np.linalg.norm(blk(T, y, x, n), 2), E[y, x]
            ok5 &= a <= b + TOL
            if b > 1e-12 and a / b > worst:
                worst, where = a / b, (t, y, x)
check(f"5 ||(e^(tK))_(yx)|| <= (e^(th))_(yx), t in {ts}, all 64 (y,x); largest ratio "
      f"{worst:.6f} at (t, y, x) = {where}", ok5)

# ------------------------------------------------------------------ 6
print("-- 6. power bound")
ok6, worst6 = True, 0.0
Km, hm = np.eye(2 * n), np.eye(n)
for m in range(1, 7):
    Km, hm = Km @ K, hm @ h
    for y in range(n):
        for x in range(n):
            a, b = np.linalg.norm(blk(Km, y, x, n), 2), hm[y, x]
            ok6 &= a <= b + TOL * max(1, b)
            if b > 1e-12:
                worst6 = max(worst6, a / b)
check(f"6 ||(K^m)_(yx)|| <= (h^m)_(yx), m = 1..6, all (y,x); largest ratio {worst6:.6f}", ok6)

# ------------------------------------------------------------------ 7
print("-- 7. commutator bound chain, f at site 0, g at site y")
print("   columns: exact 2|sin(s/2)|, |s|, ||f|| ||g|| (e^(th))_(y0), "
      "||f|| ||g|| (vt)^y/y! e^(vt), ratio |s| / exact")
ok7 = True
for t in [0.5, 1.0, 2.0]:
    T = expm(t * K)
    E = expm(t * h)
    for y in range(1, 8):
        f = np.zeros(2 * n)
        g = np.zeros(2 * n)
        f[[0, n]] = np.random.randn(2)
        g[[y, n + y]] = np.random.randn(2)
        sg = sig(T @ f, g)
        c = 2 * abs(math.sin(sg / 2))
        nf, ng = np.linalg.norm(f), np.linalg.norm(g)
        b3 = nf * ng * E[y, 0]
        b4 = nf * ng * (v * t) ** y / math.factorial(y) * math.exp(v * t)
        ok7 &= c <= abs(sg) + TOL and abs(sg) <= b3 + TOL and b3 <= b4 + TOL * max(1, b4)
        rat = abs(sg) / c if c > 0 else float('nan')
        print(f"   t={t} y={y}: {c:.4e}  {abs(sg):.4e}  {b3:.4e}  {b4:.4e}  {rat:.6f}")
check("7 2|sin(s/2)| <= |s| <= ||f|| ||g|| (e^(th))_(y0) <= ||f|| ||g|| (vt)^y/y! e^(vt)", ok7)

# ------------------------------------------------------------------ 8
print("-- 8. light cone at t = 1 (numerical)")
t = 1.0
T = expm(t * K)
E = expm(t * h)
sup = np.array([np.linalg.norm(blk(T, y, 0, n), 2) for y in range(n)])
print("   y: sup over unit f,g of |sigma(T f, g)| = ||T_(y0)||, (e^(th))_(y0):")
for y in range(n):
    print(f"   y={y}: {sup[y]:.4e}  {E[y, 0]:.4e}")
ys = np.arange(3, 8)
sl_ex = np.polyfit(ys, np.log(sup[3:8]), 1)[0]
sl_b = np.polyfit(ys, np.log(E[3:8, 0]), 1)[0]
print(f"   decay per site (slope of log, y = 3..7): exact {sl_ex:.4f}, bound {sl_b:.4f}")
check("8 both sequences decrease in y for y = 3..7 and the exact one is below the bound",
      (np.diff(sup[3:8]) < 0).all() and (np.diff(E[3:8, 0]) < 0).all()
      and (sup <= E[:, 0] + TOL).all())

# ------------------------------------------------------------------ 9
print("-- 9. velocity against Nachtergaele-Raz-Schlein-Sims (2009), Theorem 3.1")
c = math.sqrt(w ** 2 + 4 * lam)
mus = np.linspace(0.05, 10, 20000)
vmin = (c * np.maximum(2 / mus, np.exp(mus / 2 + 1))).min()
vmu1 = c * max(2.0, math.exp(1.5))
print(f"   c = {c:.6f}, 4c = {4 * c:.6f}, v(mu=1) = c max(2, e^1.5) = {vmu1:.6f}, "
      f"min over mu = {vmin:.6f}, our v = ||h||_inf = {v:.6f}")
check("9 min over mu of c max(2/mu, e^(mu/2+1)) <= 4c", vmin <= 4 * c + 1e-9)
check("9 our v = 5 = ||h||_inf for omega = lambda = 1", abs(v - 5) < TOL)

# ------------------------------------------------------------------ 10
print("-- 10. chain at omega = 0, lambda = 1 (numbers only)")
A0, M0, J0, K0 = chain(n, 0.0, 1.0)
K0 = K0.T
h0 = site_matrix(K0, n)
v0 = h0.sum(axis=1).max()
T0 = expm(K0)
E0 = expm(h0)
print(f"   v = {v0:.4f}; t = 1; blocks (e^K)_(y0) as [[a, b], [c, d]], ||block||, (e^h)_(y0), "
      f"v^y/y! e^v:")
ok10 = True
for y in range(n):
    B = blk(T0, y, 0, n)
    nb = np.linalg.norm(B, 2)
    ok10 &= nb <= E0[y, 0] + TOL
    print(f"   y={y}: {np.round(B, 5).tolist()}  {nb:.4e}  {E0[y, 0]:.4e}  "
          f"{v0 ** y / math.factorial(y) * math.exp(v0):.4e}")
check("10 entrywise bound also holds at omega = 0", ok10)

# ------------------------------------------------------------------ 11
print("-- 11. doubled-index form on Lambda' = Lambda x {q, p}")
absK = np.abs(K)
vp = absK.sum(axis=1).max()
print(f"   v' = max row sum of |K| = {vp:.6f} (omega^2 + 4 lambda = {w ** 2 + 4 * lam:.6f}); "
      f"q-row sums {absK[:n].sum(axis=1).tolist()}, p-row sums {absK[n:].sum(axis=1).tolist()}")
ok11 = True
for t in ts + [-tt for tt in ts]:
    ok11 &= (np.abs(expm(t * K)) <= expm(abs(t) * absK) + TOL).all()
check("11a |(e^(tK))_(ab)| <= (e^(|t||K|))_(ab), all a, b in Lambda', t = +-0.25, 0.5, 1, 2", ok11)
check("11b v' = omega^2 + 4 lambda", abs(vp - (w ** 2 + 4 * lam)) < TOL)
okr = True
for t in ts:
    Eabs = expm(t * absK)
    for a in range(2 * n):
        for b in range(2 * n):
            r = abs(a % n - b % n)
            okr &= Eabs[b, a] <= (vp * t) ** r / math.factorial(r) * math.exp(vp * t) + TOL
check("11c (e^(t|K|))_(ba) <= (v't)^r/r! e^(v't), r = |x - y| (sites of a, b), all a, b, t", okr)


def bar(b):
    return (b + n) % 2 * 0 + (b + n) % (2 * n)


def sigma_bounds(T, Eabs, f, g, Xp):
    """|sigma(Tf,g)|, sum_b |(Tf)_b||g_bbar|, sum_{b,a in X'} E_ba |f_a||g_bbar|."""
    s_ = abs(sig(T @ f, g))
    b1_ = sum(abs((T @ f)[b]) * abs(g[bar(b)]) for b in range(2 * n))
    b2_ = sum(Eabs[b, a] * abs(f[a]) * abs(g[bar(b)]) for b in range(2 * n) for a in Xp)
    return s_, b1_, b2_


ok11d = True
fg = {}
for t in [0.5, 1.0, 2.0]:
    T = expm(t * K)
    Eabs = expm(t * absK)
    for y in range(1, 8):
        f = np.zeros(2 * n)
        g = np.zeros(2 * n)
        f[[0, n]] = np.random.randn(2)
        g[[y, n + y]] = np.random.randn(2)
        fg[(t, y)] = (f, g)
        s_, b1_, b2_ = sigma_bounds(T, Eabs, f, g, [0, n])
        ok11d &= s_ <= b1_ + TOL and b1_ <= b2_ + TOL * max(1, b2_)
check("11d |sigma(T f, g)| <= sum_b |(Tf)_b||g_bbar| <= sum_(b,a) (e^(|t||K|))_(ba)|f_a||g_bbar|, "
      "f at 0, g at y = 1..7, t in 0.5, 1, 2", ok11d)
print("   t = 1: y, doubled-index bound, block-Euclidean bound of check 7, ratio")
T = expm(K)
Eabs = expm(absK)
Eh = expm(h)
rat11 = []
for y in range(1, 8):
    f, g = fg[(1.0, y)]
    b2_ = sigma_bounds(T, Eabs, f, g, [0, n])[2]
    b3_ = np.linalg.norm(f) * np.linalg.norm(g) * Eh[y, 0]
    rat11.append(b2_ / b3_)
    print(f"   y={y}: {b2_:.4e}  {b3_:.4e}  {b2_ / b3_:.4f}")
check("11e ratio doubled/block-Euclidean at t = 1 lies in (0, 2] (printed above)",
      all(0 < r_ <= 2 + 1e-9 for r_ in rat11))

# ------------------------------------------------------------------ 12
print("-- 12. symplectic rescaling q -> c q, p -> p / c")


def rescale(c):
    S = np.diag(np.r_[c * np.ones(n), np.ones(n) / c])
    Kc = np.linalg.inv(S) @ K @ S
    return S, Kc


ok12a = ok12b = ok12c = True
for c in [0.5, 1.0, math.sqrt(5), 2.0, 3.0, 5.0]:
    S, Kc = rescale(c)
    Si = np.linalg.inv(S)
    ok12a &= np.abs(S.T @ J @ S - J).max() < TOL
    for t in ts:
        ok12b &= np.abs(expm(t * Kc) - Si @ expm(t * K) @ S).max() < TOL * max(1, c ** 2)
    for _ in range(5):
        f, g = np.random.randn(2 * n), np.random.randn(2 * n)
        T = expm(0.7 * K)
        ok12c &= abs(sig(T @ f, g) - sig(expm(0.7 * Kc) @ Si @ f, Si @ g)) < TOL * max(1, c ** 2)
check("12a S^T J S = J, S = diag(c I, I/c)", ok12a)
check("12b T^c_t = S^(-1) T_t S, K_c = S^(-1) K S", ok12b)
check("12c sigma(T_t f, g) = sigma(T^c_t S^(-1) f, S^(-1) g)", ok12c)
print("   v'(c) = max row sum of |K_c|:")
vc = {}
for c in [0.5, 1.0, math.sqrt(5), 2.0, 3.0, 5.0, 5 ** 0.25, 5 ** -0.25]:
    vc[c] = np.abs(rescale(c)[1]).sum(axis=1).max()
    print(f"   c = {c:.6f}: v'(c) = {vc[c]:.6f}")
cs = np.linspace(0.2, 6, 58001)
vs = np.array([max((w ** 2 + 4 * lam) / c ** 2, c ** 2) for c in cs])
cmin = cs[vs.argmin()]
print(f"   scan: min v'(c) = {vs.min():.6f} at c = {cmin:.5f}; sqrt(omega^2+4lambda) = "
      f"{math.sqrt(5):.6f}, (omega^2+4lambda)^(-1/4) = {5 ** -0.25:.6f}, "
      f"(omega^2+4lambda)^(1/4) = {5 ** 0.25:.6f}")
print("   closed form: v'(c) = max((omega^2+4 lambda)/c^2, c^2) (rows q and p); scan agrees with table:",
      all(abs(vc[c] - max(5 / c ** 2, c ** 2)) < 1e-9 for c in vc))
check("12d min over c of v'(c) = sqrt(omega^2+4 lambda) = 2.236", abs(vs.min() - math.sqrt(5)) < 1e-3)
check("12e minimiser is c = (omega^2+4 lambda)^(+1/4) for S = diag(c I, I/c) "
      "(not c = sqrt(omega^2+4 lambda))", abs(cmin - 5 ** 0.25) < 1e-3)
okb = True
print("   t = 1: y, unscaled bound (11), rescaled c = sqrt5, rescaled c = 5^(1/4)")
rows = []
for c in [math.sqrt(5), 5 ** 0.25]:
    S, Kc = rescale(c)
    Si = np.linalg.inv(S)
    Ec = expm(np.abs(Kc))
    col = []
    for y in range(1, 8):
        f, g = fg[(1.0, y)]
        s_ = abs(sig(expm(K) @ f, g))
        _, _, bc = sigma_bounds(None, Ec, Si @ f, Si @ g, [0, n]) if False else (
            0, 0, sum(Ec[b, a] * abs((Si @ f)[a]) * abs((Si @ g)[bar(b)])
                      for b in range(2 * n) for a in [0, n]))
        okb &= s_ <= bc + TOL * max(1, bc)
        col.append(bc)
    rows.append(col)
for i, y in enumerate(range(1, 8)):
    f, g = fg[(1.0, y)]
    ub = sigma_bounds(expm(K), expm(absK), f, g, [0, n])[2]
    print(f"   y={y}: {ub:.4e}  {rows[0][i]:.4e}  {rows[1][i]:.4e}")
check("12f rescaled bound dominates |sigma(T_1 f, g)|, c = sqrt5 and c = 5^(1/4), y = 1..7", okb)

# ------------------------------------------------------------------ 13
print("-- 13. witness for the true dynamics (label generator K = K_H^T)")
fp, gp = np.zeros(2 * n), np.zeros(2 * n)
fp[n + 0], gp[n + 1] = 1.0, 1.0
fq, gq = np.zeros(2 * n), np.zeros(2 * n)
fq[0], gq[1] = 1.0, 1.0
sKp, sKq = sig(K @ fp, gp), sig(K @ fq, gq)
print(f"   sigma(K f, g), f = delta_(0,p), g = delta_(1,p): {sKp:.6f} (lambda = {lam})")
print(f"   sigma(K f', g'), f' = delta_(0,q), g' = delta_(1,q): {sKq:.6f}")
ok13p = ok13q = True
for t in [0.01, 0.1, 0.5]:
    T = expm(t * K)
    sp_, sq_ = sig(T @ fp, gp), sig(T @ fq, gq)
    print(f"   t = {t}: sigma(T_t f, g) = {sp_:.6e} (/t = {sp_ / t:.6f}); "
          f"sigma(T_t f', g') = {sq_:.6e} (/t^3 = {sq_ / t ** 3:.6f}, lambda/6 = {lam / 6:.6f})")
    ok13p &= abs(sp_) > 0
    if t <= 0.1:
        ok13q &= abs(abs(sq_) / t ** 3 - lam / 6) < 0.05 * lam / 6
check("13a sigma(K f, g) = lambda for the momentum pair", abs(sKp - lam) < TOL)
check("13b |sigma(T_t f, g)| > 0 for t = 0.01, 0.1, 0.5 (momentum pair)", ok13p)
check("13c sigma(K f', g') = 0 for the position pair", abs(sKq) < TOL)
check("13d |sigma(T_t f', g')| = lambda t^3/6 (1 + O(t^2)) for t = 0.01, 0.1 (within 5%)", ok13q)

# ------------------------------------------------------------------ 14
print("-- 14. sharper light-cone form")
vv = math.sqrt(5)
ok14, worst14 = True, 0.0
for t in [0.5, 1.0, 2.0]:
    x = vv * t
    for r in range(1, 9):
        tail = sum(x ** m / math.factorial(m) for m in range(r, 120))
        for mu in [0.0, 0.5, 1.0, 2.0]:
            rhs = math.exp(-mu * r) * math.expm1(math.exp(mu) * x)
            ok14 &= tail <= rhs * (1 + 1e-12)
            worst14 = max(worst14, tail / rhs)
check(f"14 sum_(m>=r) (vt)^m/m! <= e^(-mu r)(e^(e^mu vt) - 1), v = sqrt5, t in 0.5,1,2, r = 1..8, "
      f"mu in 0,0.5,1,2 (largest ratio {worst14:.6f})", ok14)

# ------------------------------------------------------------------ 15
print("-- 15. time normalisation, source Hamiltonian H_s = 2 H")
Ks = (J @ (2 * M)).T
e15 = max(np.abs(expm(t * Ks) - expm(2 * t * K)).max() for t in ts)
check(f"15a T^(s)_t = T_(2t), flow of H_s (max entry {e15:.2e})", e15 < TOL)
vres = math.sqrt(w ** 2 + 4 * lam)
src_min = (vres * np.maximum(2 / mus, np.exp(mus / 2 + 1))).min()
print(f"   our cone velocity in source time: 2 e v_rescaled = {2 * math.e * vres:.6f} "
      f"(v_rescaled = {vres:.6f}); source min over mu of c max(2/mu, e^(mu/2+1)) = {src_min:.6f}; "
      f"4c = {4 * vres:.6f}")
kk = np.linspace(0, math.pi, 200001)
gam = np.sqrt(w ** 2 + 4 * lam * np.sin(kk / 2) ** 2)
gp_ = np.gradient(gam, kk)
vg = gp_.max()
print(f"   dispersion gamma(k) = sqrt(w^2 + 4 lam sin^2(k/2)); max group velocity "
      f"{vg:.6f} at k = {kk[gp_.argmax()]:.4f} (our time), {2 * vg:.6f} (source time)")
ev = np.sort(np.sqrt(np.linalg.eigvalsh(A)))
ex = np.sort(np.sqrt(w ** 2 + 4 * lam * np.sin(np.pi * np.arange(n) / (2 * n)) ** 2))
check("15b open-chain frequencies sqrt(eig A) = gamma(k_j), k_j = pi j / n, j = 0..n-1",
      np.abs(ev - ex).max() < TOL)
check("15c max group velocity <= v_rescaled and <= the walk-bound cone speed e v_rescaled",
      vg <= vres + 1e-9)

# ------------------------------------------------------------------ 16
print("-- 16. degenerate cases")
# (a) No coupling: every site evolves alone, so the off-diagonal blocks of e^(tK) and of e^(th)
# vanish, and labels on different sites keep a zero symplectic form at every time.
Ad, Md, Jd, Kd = chain(n, w, 0.0)
Kd = Kd.T
hd = site_matrix(Kd, n)
ok16a = np.abs(hd - np.diag(np.diag(hd))).max() < TOL
for t in ts:
    Td, Ed = expm(t * Kd), expm(t * hd)
    for y in range(1, n):
        ok16a &= np.linalg.norm(blk(Td, y, 0, n), 2) < TOL and abs(Ed[y, 0]) < TOL
    f = np.zeros(2 * n)
    g = np.zeros(2 * n)
    f[0], f[n] = 1.0, 0.5
    g[3], g[n + 3] = -0.7, 1.0
    ok16a &= abs(sig(Td @ f, g)) < TOL
check("16a lam = 0: h and e^(th) diagonal, (e^(tK))_(y0) = 0 for y != 0, sigma(T_t f, g) = 0 "
      "for f at site 0 and g at site 3", ok16a)
# (b) The zero label: sigma(T_t 0, g) = 0 and the bound's right side is 0.
ok16b = all(abs(sig(expm(t * K) @ np.zeros(2 * n), np.random.randn(2 * n))) < TOL for t in ts)
check("16b f = 0 gives sigma(T_t f, g) = 0 for random g", ok16b)
# (c) One site (a single oscillator, A = w^2 + lam): the flow is symplectic and the entrywise bound holds.
A1, M1, J1, K1 = chain(1, w, lam)
K1 = K1.T
h1 = site_matrix(K1, 1)
ok16c = True
for t in ts:
    T1 = expm(t * K1)
    ok16c &= np.abs(T1.T @ J1 @ T1 - J1).max() < TOL
    ok16c &= np.linalg.norm(T1, 2) <= expm(t * h1)[0, 0] + TOL
check("16c one site: T_t symplectic and ||e^(tK)|| <= e^(th)", ok16c)

# ------------------------------------------------------------------ summary
npass = sum(results)
print(f"m5_check: {npass} of {len(results)} checks passed")
sys.exit(0 if npass == len(results) else 1)
