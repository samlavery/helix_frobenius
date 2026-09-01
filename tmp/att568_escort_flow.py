# att568 — zero-flow ODE, take 2 (pre-registered amendments):
# (a) ESCORT: multi-seed Newton, REJECT |Im z|<0.05 (axis capture); U=1.00,1.005,1.01.
# (b) REAL-ZERO flow: finer steps U=1.005,1.0075,1.01 -> central diff at 1.0075 vs ODE.
# DECISION (same): <15% CONFIRM, >50% REFUTE, else MARGINAL.  ODE exact => predict CONFIRM
# for (b) with fine steps; (a) escort dive Im zdot > 0.
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
def XiUp(z, U):
    npts = max(6, int(40.0 * float(U) / 3.0))
    pts = [U * mpf(k) / npts for k in range(npts + 1)]
    return -2 * quad(lambda u: u * Phi(u) * sin(z * u), pts)
def hunt(U, seeds):
    for s in seeds:
        try:
            z = findroot(lambda w: XiU(w, U), s, tol=1e-24)
            if abs(z.imag) > 0.05:
                return z
        except Exception:
            pass
    return None
print("(a) escort:")
seeds = [mpc(31.5,1.0), mpc(32.5,1.2), mpc(33.2,1.0), mpc(32.0,0.9), mpc(33.8,1.3)]
tr = {}
for U in [mpf('1.00'), mpf('1.005'), mpf('1.01')]:
    z = hunt(U, seeds)
    tr[float(U)] = z
    print(f"  U={float(U):.3f}  escort = {mp.nstr(z,10) if z else 'NOT FOUND'}")
    if z: seeds = [z] + seeds
if tr[1.00] and tr[1.01] and tr[1.005]:
    zm = (tr[1.01] - tr[1.00]) / mpf('0.01')
    U1 = mpf('1.005'); z1 = tr[1.005]
    zo = -2 * Phi(U1) * cos(z1 * U1) / XiUp(z1, U1)
    re = abs(zo - zm) / abs(zm)
    print(f"  measured dz/dU = {mp.nstr(zm,7)}\n  ODE      dz/dU = {mp.nstr(zo,7)}")
    print(f"  relerr = {float(re):.4f} ->", "CONFIRM" if re<0.15 else ("REFUTE" if re>0.5 else "MARGINAL"))
print("(b) real zero, fine steps:")
z0 = mpc(30.9, 0)
rr = {}
for U in [mpf('1.005'), mpf('1.0075'), mpf('1.01')]:
    z = findroot(lambda w: XiU(w, U), z0, tol=1e-24)
    rr[float(U)] = z; z0 = z
    print(f"  U={float(U):.4f}  x = {mp.nstr(z.real,10)}")
zm = (rr[1.01] - rr[1.005]) / mpf('0.005')
U1 = mpf('1.0075'); z1 = rr[1.0075]
zo = -2 * Phi(U1) * cos(z1 * U1) / XiUp(z1, U1)
re = abs(zo - zm) / abs(zm)
print(f"  measured dz/dU = {mp.nstr(zm,7)}\n  ODE      dz/dU = {mp.nstr(zo,7)}")
print(f"  relerr = {float(re):.4f} ->", "CONFIRM" if re<0.15 else ("REFUTE" if re>0.5 else "MARGINAL"))
