"""Numerical calibration of TwistedLadderParity.lean (2026-07-29).

Checks, on the two-clock kernel I_{r,m}(xi) = int_{-1}^{1} Phi(x) U_r(x) U_m(x) e^{-2pi i x xi c} dx
with Phi(x) = sqrt(1-x^2) (even orbital profile), c = 0.7 (irrational-ish scale):

  A. two-clock reflection:  I(-xi) = (-1)^{r+m} I(xi)
  B. channel law, even weights v(xi)=1/(1+xi^2):  window sum == 0 iff r+m odd
     (control: r+m even must be NONZERO)
  C. flipped channel, odd weights v(xi)=xi/(1+xi^2):  window sum == 0 iff r+m even
     (control: r+m odd must be NONZERO)

Method law: controls aggregated by MAX over the window; residuals normalized by the
max term magnitude.
"""
import numpy as np
from numpy.polynomial import chebyshev

def chebU(r, x):
    # second-kind via recurrence, matching the Lean def
    if r == 0:
        return np.ones_like(x)
    if r == 1:
        return 2 * x
    um2, um1 = np.ones_like(x), 2 * x
    for _ in range(2, r + 1):
        um2, um1 = um1, 2 * x * um1 - um2
    return um1

# Gauss-Legendre quadrature on [-1,1]
NODES, WTS = np.polynomial.legendre.leggauss(400)
C = 0.7

def I_rm(r, m, xi):
    x = NODES
    f = np.sqrt(np.clip(1 - x**2, 0, None)) * chebU(r, x) * chebU(m, x) * np.exp(-2j * np.pi * x * xi * C)
    return np.sum(WTS * f)

N = 25
xis = np.arange(-N, N + 1)

print("A. two-clock reflection residuals max over r,m<=5, xi<=10:")
resA = 0.0
for r in range(6):
    for m in range(6):
        for xi in range(11):
            lhs = I_rm(r, m, -xi)
            rhs = (-1) ** (r + m) * I_rm(r, m, xi)
            scale = max(abs(lhs), abs(rhs), 1e-300)
            resA = max(resA, abs(lhs - rhs) / scale if scale > 1e-14 else abs(lhs - rhs))
print(f"   max rel residual = {resA:.3e}")

def window_sum(r, m, v):
    return sum(v(xi) * I_rm(r, m, xi) for xi in xis)

def term_scale(r, m, v):
    return max(abs(v(xi) * I_rm(r, m, xi)) for xi in xis)

v_even = lambda xi: 1.0 / (1 + xi**2)
v_odd = lambda xi: xi / (1 + xi**2)

print("B. even weights: |sum|/maxterm  (predict ~0 for r+m ODD, control r+m EVEN nonzero)")
for (r, m) in [(1, 0), (2, 1), (3, 2), (5, 4), (2, 0), (3, 1), (4, 2), (6, 4)]:
    s, sc = window_sum(r, m, v_even), term_scale(r, m, v_even)
    tag = "ZERO-CHANNEL" if (r + m) % 2 == 1 else "CONTROL"
    print(f"   r={r} m={m} r+m={'odd ' if (r+m)%2 else 'even'} |S|/max = {abs(s)/sc:.3e}  [{tag}]")

print("C. odd weights: |sum|/maxterm  (predict ~0 for r+m EVEN, control r+m ODD nonzero)")
for (r, m) in [(2, 0), (3, 1), (4, 2), (6, 4), (1, 0), (2, 1), (3, 2), (5, 4)]:
    s, sc = window_sum(r, m, v_odd), term_scale(r, m, v_odd)
    tag = "ZERO-CHANNEL" if (r + m) % 2 == 0 else "CONTROL"
    print(f"   r={r} m={m} r+m={'odd ' if (r+m)%2 else 'even'} |S|/max = {abs(s)/sc:.3e}  [{tag}]")
