"""Small-t expansion and closed form of the three-site chain's exact commutator.

Claim under test: for H = Z_0 Z_1 + (1/2) X_1 X_2, the exact norm
||[e^{iHt} X_0 e^{-iHt}, Z_2]|| = 2 t^2 - (5/6) t^4 + O(t^6), so the ratio to the path-sum
bound 2 t^2 is 1 - (5/12) t^2, equal to 0.99996 at t = 0.01 and decreasing in t; the norm is
(4/5)(1 - cos(sqrt(5) t)) exactly.
Checked numerically: the t^4 coefficient is extracted from (2t^2 - norm)/t^4 at small t, and the
closed form and the decrease of the ratio are checked on the grid of checks/m1a_crossing_check.py.
Exits nonzero at a failure.
"""
import numpy as np
from scipy.linalg import expm

I2 = np.eye(2)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)


def on_sites(n, ops):
    out = np.array([[1.0 + 0j]])
    for j in range(n):
        out = np.kron(out, ops.get(j, I2))
    return out


H = on_sites(3, {0: Z, 1: Z}) + 0.5 * on_sites(3, {1: X, 2: X})
A = on_sites(3, {0: X})
B = on_sites(3, {2: Z})


def norm_comm(t):
    U = expm(1j * t * H)
    At = U @ A @ U.conj().T
    return np.linalg.norm(At @ B - B @ At, 2)


ok = True
for t in (0.02, 0.01, 0.005):
    c4 = (2 * t**2 - norm_comm(t)) / t**4
    print(f"t = {t}: (2t^2 - norm)/t^4 = {c4:.5f}  (claim 5/6 = {5/6:.5f})")
    ok &= abs(c4 - 5 / 6) < 0.01

ts = np.linspace(0.01, 1.5, 150)
norms = np.array([norm_comm(t) for t in ts])
ratios = norms / (2 * ts**2)
# closed form: the strings X_0, Y_0 Z_1, Y_0 Y_1 X_2 span an
# invariant space of ad_H, and the commutator with Z_2 has norm (4/5)(1 - cos(sqrt(5) t)).
closed = 0.8 * (1 - np.cos(np.sqrt(5) * ts))
dev = float(np.max(np.abs(norms - closed)))
print(f"closed form (4/5)(1 - cos sqrt5 t): max deviation on the grid {dev:.2e}")
ok &= dev < 1e-10
print(f"ratio at t = 0.01: {ratios[0]:.6f}; max ratio {ratios.max():.6f}; "
      f"decreasing on the grid: {bool(np.all(np.diff(ratios) < 0))}")
ok &= ratios.max() < 1 and bool(np.all(np.diff(ratios) < 0))
print("PASS" if ok else "FAIL", ": t^4 coefficient -5/6, ratio below 1 and decreasing")
raise SystemExit(0 if ok else 1)
