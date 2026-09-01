# att567 — THE ZERO-FLOW ODE (pre-registered).
# Exact law: d/dU Xi_U(z) = 2*Phi(U)*cos(zU)  (FTC at the extent boundary), so a
# stage zero moves by  zdot = -2*Phi(U)*cos(z_e U) / Xi_U'(z_e).
# TEST: localize the escort at U = 1.00, 1.01, 1.02 (Newton); compare ODE
# velocity at U=1.01 with the central difference (z(1.02)-z(1.00))/0.02.
# DECISION (registered): relative error < 15% CONFIRM; > 50% REFUTE (bug or
# wrong zero).  PREDICTION: CONFIRM, Im zdot > 0 (dive), |zdot| = O(10..100).
from mpmath import mp, mpf, mpc, exp, cos, sin, pi, quad, findroot
mp.dps = 32
NM = 8
def Phi(u):
    a = abs(u); s = mpf(0)
    for n in range(1, NM + 1):
        nn = mpf(n * n)
        s += (2 * pi**2 * nn * nn * exp(9 * a / 2) - 3 * pi * nn * exp(5 * a / 2)) * exp(-pi * nn * exp(2 * a))
    return 4 * s
def XiU(z, U, xosc=40):
    npts = max(6, int(float(xosc) * float(U) / 3.0))
    pts = [U * mpf(k) / npts for k in range(npts + 1)]
    return 2 * quad(lambda u: Phi(u) * cos(z * u), pts)
def XiUprime(z, U):
    npts = max(6, int(40.0 * float(U) / 3.0))
    pts = [U * mpf(k) / npts for k in range(npts + 1)]
    return -2 * quad(lambda u: u * Phi(u) * sin(z * u), pts)

z0 = mpc(32.3, 1.2)   # seed inside att566's T1 localization box
zs = {}
for U in [mpf('1.00'), mpf('1.01'), mpf('1.02')]:
    ze = findroot(lambda z: XiU(z, U), z0, tol=1e-24)
    zs[float(U)] = ze
    print(f"U={float(U):.2f}  z_e = {mp.nstr(ze, 12)}   |Xi_U(z_e)| = {mp.nstr(abs(XiU(ze,U)),3)}")
    z0 = ze  # track continuously

zm = (zs[1.02] - zs[1.00]) / mpf('0.02')
U1 = mpf('1.01'); ze1 = zs[1.01]
zdot = -2 * Phi(U1) * cos(ze1 * U1) / XiUprime(ze1, U1)
relerr = abs(zdot - zm) / abs(zm)
print(f"measured  dz/dU = {mp.nstr(zm, 8)}")
print(f"ODE       dz/dU = {mp.nstr(zdot, 8)}")
print(f"relative error  = {float(relerr):.4f}   ->",
      "CONFIRM" if relerr < 0.15 else ("REFUTE" if relerr > 0.5 else "MARGINAL"))
print(f"Im zdot = {mp.nstr(zdot.imag, 6)} (dive iff > 0)")
