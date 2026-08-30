#!/usr/bin/env python3
"""C3 batch 11 numerics, part 2 — high-precision hostile scan and counterexample closure.

NONRIGOROUS CONTROLS ONLY.

Part 1 (tmp/c3b11_num.py) scanned Q(x,y) = A A' + B B' by double-precision quadrature and
reported "negatives" from x ~ 30 upward.  Those were ARTEFACTS: |M(y+ix)|^2 fell to ~1e-24,
i.e. |M| ~ 1e-12, which is exactly the absolute noise floor of a double-precision quadrature
whose integrand has scale ~1.  This file redoes the scan through the exact identification

      M(z) = 2 * xi(1/2 + z)          (established to 8 digits in part 1, N2b)

so that Q(x,y) = 4 * Re[ xi'(s) * conj(xi(s)) ],  s = 1/2 + y + i x,  computed in mpmath.

Sections:
  M1  calibration: quadrature Q vs mpmath Q, and where the quadrature noise floor bites
  M2  HOSTILE SCAN in mpmath: x in 0..150 dense + zero-ordinate neighbourhoods, y in 1e-6..5
  M3  the y -> 0+ edge: Q(x,y)/y -> L1(x) = Xi'(x)^2 - Xi(x) Xi''(x)  (Laguerre expression)
  M4  counterexample kernel closed form, and the Gaussian-mixture class
"""
import math
import mpmath as mp

mp.mp.dps = 30


def xi(s):
    return s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def logDeriv_xi(s):
    """xi'/xi (s) = 1/s + 1/(s-1) - (1/2)log pi + (1/2)psi(s/2) + zeta'/zeta (s).

    Computed from the closed form rather than by numerical differentiation: one zeta, one
    zeta', one digamma per point, with no cancellation."""
    return (1 / s + 1 / (s - 1) - mp.log(mp.pi) / 2 + mp.digamma(s / 2) / 2
            + mp.zeta(s, derivative=1) / mp.zeta(s))


def Qmp(x, y):
    """Q(x,y) = Re[M'(z) conj M(z)] = |M|^2 * Re[xi'/xi](s),  z = y+ix, s = 1/2+z.

    Returns (Q, |M|^2) with M = 2 xi(1/2 + .).  sign(Q) = sign(Re[xi'/xi])."""
    if x == 0:
        x = 1e-6                     # avoid the s = 1 pole of zeta at (x,y) = (0, 1/2)
    s = mp.mpf(1) / 2 + mp.mpf(y) + 1j * mp.mpf(x)
    v = xi(s)
    nrm = 4 * abs(v) ** 2
    return nrm * mp.re(logDeriv_xi(s)), nrm


print("=" * 78)
print("M1  calibration of the double-precision quadrature against mpmath")
print("=" * 78)
import numpy as np


def gl(n, a, b):
    q, w = np.polynomial.legendre.leggauss(n)
    return 0.5 * (b - a) * q + 0.5 * (b + a), 0.5 * (b - a) * w


NMAX = 60
TMAX = 2.6
TN, TW = gl(4000, 0.0, TMAX)


def Phi(t):
    a = np.abs(np.asarray(t, dtype=float))
    e2 = np.exp(2.0 * a)
    s = np.zeros_like(a)
    for n in range(1, NMAX + 1):
        s += (2.0 * math.pi ** 2 * n ** 4 * np.exp(4.5 * a)
              - 3.0 * math.pi * n ** 2 * np.exp(2.5 * a)) * np.exp(-math.pi * n * n * e2)
    return 4.0 * s


PHIT = Phi(TN)


def Qquad(x, y):
    ch, sh = np.cosh(y * TN), np.sinh(y * TN)
    c, s = np.cos(x * TN), np.sin(x * TN)
    A = 2.0 * np.sum(TW * ch * PHIT * c)
    Ap = 2.0 * np.sum(TW * TN * sh * PHIT * c)
    B = 2.0 * np.sum(TW * sh * PHIT * s)
    Bp = 2.0 * np.sum(TW * TN * ch * PHIT * s)
    return A * Ap + B * Bp, A * A + B * B


for x in [0.0, 5.0, 14.134725142, 20.0, 30.0, 40.0, 46.1, 60.0]:
    qq, nq = Qquad(x, 0.5)
    qm, nm = Qmp(x, 0.5)
    print(f"x={x:12.6f} y=0.5   quad Q={qq: .6e}  |M|^2={nq: .6e}")
    print(f"{'':22}mpmath Q={float(qm): .6e}  |M|^2={float(nm): .6e}"
          f"   -> quadrature |M|^2 error {abs(nq-float(nm)):.2e}")

print()
print("=" * 78)
print("M2  HOSTILE SCAN (mpmath, 30 dps):  Q(x,y) = A A' + B B'  must be >= 0")
print("=" * 78)
ZEROS = [14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
         37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478,
         52.970321478, 56.446247697, 59.347044003, 60.831778525, 65.112544048,
         67.079810529, 69.546401711, 72.067157674, 75.704690699, 77.144840069,
         79.337375020, 82.910380854, 84.735492981, 87.425274613, 88.809111208,
         92.491899271, 94.651344041, 95.870634228, 98.831194218, 101.317851006,
         103.725538040, 105.446623052, 107.168611184, 111.029535543, 111.874659177,
         114.320220915, 116.226680321, 118.790782866, 121.370125002, 122.946829294,
         124.256818554, 127.516683880, 129.578704200, 131.087688531, 133.497737203,
         134.756509753, 138.116042055, 139.736208952, 141.123707404, 143.111845808,
         146.000982487, 147.422765343, 150.053520421]
xs = [i * 0.5 for i in range(0, 301)]           # 0 .. 150 step 0.5
for g in ZEROS:
    for d in (-0.05, -0.01, -0.001, 0.0, 0.001, 0.01, 0.05):
        xs.append(g + d)
ys = [1e-6, 1e-4, 1e-2, 0.1, 0.25, 0.49, 0.5, 0.51, 1.0, 2.0, 3.5, 5.0]

nneg = 0
tot = 0
worst = (mp.inf, None)
for x in xs:
    for y in ys:
        q, nrm = Qmp(x, y)
        tot += 1
        r = q / nrm if nrm > 0 else q
        if r < worst[0]:
            worst = (r, (x, y, q, nrm))
        if q < 0:
            nneg += 1
            if nneg <= 15:
                print(f"  NEGATIVE  x={x:.6f} y={y:.6g}  Q={float(q):.6e}  |M|^2={float(nrm):.6e}")
print(f"  scanned {tot} (x,y) pairs;  negatives found: {nneg}")
print(f"  min of Q/|M|^2 = {float(worst[0]):.8e}  at x={worst[1][0]:.6f}, y={worst[1][1]:.6g}")
print("  CORRECTED NORMALISATION (batch 12): Q = Re[M' conj M] = (1/2) d/dy |M|^2, so")
print("     Q/|M|^2 = (1/2) d/dy log|M|^2 = d/dy log|M| = Re[xi'/xi](1/2+y+ix).")
print("  (Batch 11 printed '2 * d/dy log|M|' here; that factor 2 was wrong.  The scan itself")
print("   is unaffected: only the sign of Q was ever used, and Q = |M|^2 * Re[xi'/xi] exactly.)")
print("  NOTE on the x=0 row: Qmp substitutes x = 1e-6 when x == 0.  The closed-form")
print("  log-derivative 1/s + 1/(s-1) - (1/2)log pi + (1/2)psi(s/2) + zeta'/zeta(s) has a")
print("  REMOVABLE singularity at s = 1: the pole of 1/(s-1) cancels against the pole of")
print("  zeta'/zeta(s) = -1/(s-1) + O(1).  Each summand is separately singular there, so the")
print("  point (x,y) = (0, 1/2) is evaluated as a numerical limit at x = 1e-6, NOT at x = 0.")

print()
print("=" * 78)
print("M3  the y -> 0+ edge:   Q(x,y)/y  ->  L1(x) = Xi'(x)^2 - Xi(x) Xi''(x)")
print("    (Xi(x) = 2 xi(1/2+ix), real on the real axis)")
print("=" * 78)


def Xi(x):
    return mp.re(2 * xi(mp.mpf(1) / 2 + 1j * mp.mpf(x)))


def L1(x):
    d1 = mp.diff(Xi, x, 1)
    d2 = mp.diff(Xi, x, 2)
    return d1 ** 2 - Xi(x) * d2


for x in [0.0, 3.0, 7.0, 14.134725142, 14.5, 21.022039639, 25.010857580, 40.0]:
    y = mp.mpf('1e-8')
    q, _ = Qmp(x, y)
    print(f"  x={x:12.6f}   Q/y = {float(q / y): .10e}   L1(x) = {float(L1(x)): .10e}")

negL = 0
mnL = (mp.inf, None)
for i in range(0, 601):
    x = i * 0.25
    v = L1(x)
    if v < 0:
        negL += 1
        if negL <= 10:
            print(f"  L1 NEGATIVE at x={x:.4f}: {float(v):.6e}")
    if v < mnL[0]:
        mnL = (v, x)
print(f"  L1 scanned on x in [0,150] step 0.25: negatives = {negL};"
      f"  min L1 = {float(mnL[0]):.6e} at x={mnL[1]:.4f}")

print()
print("=" * 78)
print("M4  COUNTEREXAMPLE CLOSURE (generic positive even kernels)")
print("=" * 78)
print("  (a)  Phi_c(t) = e^{-t^2}(2 + cos 2t) > 0, even, Schwartz.")
print("       M_c(z) = int e^{zt} Phi_c(t) dt = sqrt(pi) e^{z^2/4} (2 + e^{-1} cos z).")
b0 = mp.acosh(2 * mp.e)
z0 = mp.pi + 1j * b0
Mc = lambda z: mp.sqrt(mp.pi) * mp.e ** (z ** 2 / 4) * (2 + mp.e ** (-1) * mp.cos(z))
print(f"       zero at z0 = {mp.nstr(z0, 15)};  M_c(z0) = {mp.nstr(Mc(z0), 8)}")
print(f"       |M_c(i*Im z0)|  = {mp.nstr(abs(Mc(1j*b0)), 10)}   (>0, on the imaginary axis)")
print(f"       |M_c(z0)|       = {mp.nstr(abs(Mc(z0)), 10)}   (=0, OFF the imaginary axis)")
print("       => F(lam)=|M_c(lam + i*Im z0)|^2/4 is >0 at lam=0 and =0 at lam=Re z0=pi,")
print("          so F DECREASES somewhere on (0,pi): the target FAILS for Phi_c.")
print("       Explicit negative sample of the leaf functional Q_c(x0,y):")
x0 = float(b0)


def Qc(x, y):
    z = mp.mpf(y) + 1j * mp.mpf(x)
    v = Mc(z)
    d = mp.diff(Mc, z)
    return mp.re(d * mp.conj(v))


for y in [2.4, 2.6, 2.8, 3.0, 3.1]:
    print(f"         x0={x0:.10f}  y={y:.2f}   Q_c = {float(Qc(x0, y)): .8e}")

print()
print("  (b)  Gaussian mixtures (= complete monotonicity of Phi(sqrt(.))): Phi_g(t)=e^{-t^2}+e^{-4t^2}")
Mg = lambda z: mp.sqrt(mp.pi) * mp.e ** (z ** 2 / 4) + mp.sqrt(mp.pi) / 2 * mp.e ** (z ** 2 / 16)
# zeros: e^{3 z^2/16} = -1/2  =>  3z^2/16 = -log 2 + i pi (2k+1)
for k in (0, -1):
    w = (-mp.log(2) + 1j * mp.pi * (2 * k + 1)) * 16 / 3
    zz = mp.sqrt(w)
    print(f"       zero z = {mp.nstr(zz, 12)}   M_g(z) = {mp.nstr(Mg(zz), 6)}"
          f"   Re z = {float(mp.re(zz)):.6f} != 0")
zz = mp.sqrt((-mp.log(2) + 1j * mp.pi) * 16 / 3)
xg, yg = float(mp.im(zz)), float(mp.re(zz))
print(f"       so with x = Im z = {xg:.6f}: |M_g(i x)|^2 = {float(abs(Mg(1j*mp.im(zz)))**2):.6e} > 0")
print(f"                              but |M_g({yg:.4f} + i x)|^2 = "
      f"{float(abs(Mg(zz))**2):.6e} = 0")


def Qg(x, y):
    z = mp.mpf(y) + 1j * mp.mpf(x)
    v = Mg(z)
    d = mp.diff(Mg, z)
    return mp.re(d * mp.conj(v))


for y in [0.5 * yg, 0.7 * yg, 0.85 * yg, 0.95 * yg]:
    print(f"         x={xg:.6f}  y={y:.4f}   Q_g = {float(Qg(xg, y)): .8e}")
print("       A Gaussian mixture has cosine transform = positive mixture of Gaussians,")
print("       hence NO zeros on the imaginary axis; being entire of order 2 and non-vanishing")
print("       only if it is a single Gaussian, it MUST have off-axis zeros. So for every")
print("       Gaussian-mixture kernel except a single Gaussian the target FAILS.")
