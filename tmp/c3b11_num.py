#!/usr/bin/env python3
"""C3 batch 11 numerics.

NONRIGOROUS CONTROLS ONLY.  Nothing here is a proof; every claim that matters is
compiled in tmp/c3b11_*.lean.

What this checks:
  (N1)  the four-moment identity
          T(x,y) := int_{u>0} u sinh(2yu) C(x,u) du  ==  (1/4)(A A' + B B')
        against a direct 2D quadrature of the (u,p) integral;
  (N2)  the two-square identity
          F(x,lam) := int_{u>0} cosh(2 lam u) C(x,u) du == (1/4)(A^2 + B^2)
        and the exact Xi identification  A + iB = 4*xi(1/2 + y + ix);
  (N3)  hostile sign scan of A A' + B B' over x in 0..150 (incl. zero ordinates)
        and y in 1e-6..5;
  (N4)  a GENERIC positive even kernel Phi_c(t) = e^{-t^2}(2 + cos 2t) for which the
        same functional is provably NEGATIVE somewhere -- the counterexample that
        says positivity of the kernel alone cannot decide the sign.
"""
import math
import numpy as np

# ---------------------------------------------------------------- the kernel
NMAX = 60


def Phi(t):
    """riemannXiKernel(t) = 4 * sum_{n>=1} (2 pi^2 n^4 e^{9t/2} - 3 pi n^2 e^{5t/2}) e^{-pi n^2 e^{2t}}.

    Even in t (riemannXiKernel_neg), so evaluate at |t|."""
    a = np.abs(np.asarray(t, dtype=float))
    e2 = np.exp(2.0 * a)
    s = np.zeros_like(a)
    for n in range(1, NMAX + 1):
        s += (2.0 * math.pi ** 2 * n ** 4 * np.exp(4.5 * a)
              - 3.0 * math.pi * n ** 2 * np.exp(2.5 * a)) * np.exp(-math.pi * n * n * e2)
    return 4.0 * s


# fine Gauss-Legendre nodes on [0, TMAX]; Phi(t) ~ exp(-pi e^{2t}) kills t > 2.2
TMAX = 2.6


def gl(n, a, b):
    x, w = np.polynomial.legendre.leggauss(n)
    return 0.5 * (b - a) * x + 0.5 * (b + a), 0.5 * (b - a) * w


TN, TW = gl(4000, 0.0, TMAX)
PHIT = Phi(TN)


def moments(x, y):
    """A = cosMom(cosh(y.)Phi), A' = cosMom(t sinh(y.)Phi),
       B = sinMom(sinh(y.)Phi), B' = sinMom(t cosh(y.)Phi).
       Each is an integral over all of R; parity folds it onto (0,TMAX) with factor 2."""
    ch = np.cosh(y * TN)
    sh = np.sinh(y * TN)
    c = np.cos(x * TN)
    s = np.sin(x * TN)
    A = 2.0 * np.sum(TW * ch * PHIT * c)
    Ap = 2.0 * np.sum(TW * TN * sh * PHIT * c)
    B = 2.0 * np.sum(TW * sh * PHIT * s)
    Bp = 2.0 * np.sum(TW * TN * ch * PHIT * s)
    return A, Ap, B, Bp


def Q(x, y):
    """The leaf functional  A A' + B B' = Re[ M'(y+ix) conj M(y+ix) ]."""
    A, Ap, B, Bp = moments(x, y)
    return A * Ap + B * Bp


# ------------------------------------------------- (N1) direct 2D quadrature
PN, PW = gl(3000, -4.0, 4.0)


def cellDensity(x, u):
    return np.sum(PW * Phi(u + PN) * Phi(u - PN) * np.cos(2.0 * x * PN))


UN, UW = gl(400, 0.0, 3.0)


def _cd_row(x):
    return np.array([cellDensity(x, uu) for uu in UN])


def target_direct(x, y, vals=None):
    if vals is None:
        vals = _cd_row(x)
    return np.sum(UW * UN * np.sinh(2.0 * y * UN) * vals)


def F_direct(x, lam, vals=None):
    if vals is None:
        vals = _cd_row(x)
    return np.sum(UW * np.cosh(2.0 * lam * UN) * vals)


print("=" * 78)
print("N1/N2  identity checks:  T = (1/4)(AA'+BB')   and   F = (1/4)(A^2+B^2)")
print("=" * 78)
for (x, y) in [(0.0, 0.7), (1.0, 0.3), (3.0, 1.0), (14.134725, 0.4), (7.0, 0.05)]:
    A, Ap, B, Bp = moments(x, y)
    vals = _cd_row(x)
    t_mom = 0.25 * (A * Ap + B * Bp)
    t_dir = target_direct(x, y, vals)
    f_mom = 0.25 * (A * A + B * B)
    f_dir = F_direct(x, y, vals)
    print(f"x={x:10.6f} y={y:6.3f}  T_mom={t_mom: .10e}  T_dir={t_dir: .10e}"
          f"  relerr={abs(t_mom-t_dir)/max(abs(t_dir),1e-300):.2e}")
    print(f"{'':24}F_mom={f_mom: .10e}  F_dir={f_dir: .10e}"
          f"  relerr={abs(f_mom-f_dir)/max(abs(f_dir),1e-300):.2e}")

# ------------------------------------------------- (N2b) the Xi identification
try:
    import mpmath as mp
    mp.mp.dps = 25
    print()
    print("=" * 78)
    print("N2b  A + iB  vs  4*xi(1/2 + y + i x)      xi(s)=s(s-1)/2 pi^{-s/2}Gamma(s/2)zeta(s)")
    print("=" * 78)

    def xi(s):
        return s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

    for (x, y) in [(0.0, 0.0), (1.0, 0.0), (14.134725142, 0.0), (5.0, 0.8), (21.022, 0.25)]:
        A, Ap, B, Bp = moments(x, y)
        z = xi(mp.mpf(1) / 2 + mp.mpf(y) + 1j * mp.mpf(x))
        print(f"x={x:12.6f} y={y:5.2f}  A+iB = {A: .8e} {B:+.8e}i   "
              f"4xi = {float(mp.re(4*z)): .8e} {float(mp.im(4*z)):+.8e}i")
except Exception as e:  # pragma: no cover
    print("mpmath unavailable:", e)

# ------------------------------------------------- (N3) hostile sign scan
print()
print("=" * 78)
print("N3  HOSTILE SCAN of  Q(x,y) = A A' + B B'   (target sign, must be >= 0)")
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
xs = list(np.linspace(0.0, 150.0, 1501))
for g in ZEROS:
    for d in (-0.05, -0.01, -0.002, 0.0, 0.002, 0.01, 0.05):
        xs.append(g + d)
ys = [1e-6, 1e-5, 1e-4, 1e-3, 0.01, 0.03, 0.05, 0.1, 0.2, 0.3, 0.4, 0.49, 0.5, 0.51,
      0.6, 0.8, 1.0, 1.5, 2.0, 3.0, 4.0, 5.0]
worst = (math.inf, None)
nneg = 0
tot = 0
for x in xs:
    for y in ys:
        A, Ap, B, Bp = moments(x, y)
        q = A * Ap + B * Bp
        tot += 1
        nrm = A * A + B * B
        r = q / nrm if nrm > 0 else q
        if r < worst[0]:
            worst = (r, (x, y, q, nrm))
        if q < 0:
            nneg += 1
            if nneg <= 20:
                print(f"  NEGATIVE  x={x:.6f} y={y:.6g}  Q={q:.6e}  |M|^2={nrm:.6e}")
print(f"  scanned {tot} (x,y) pairs;  negatives found: {nneg}")
print(f"  minimum of Q/|M|^2 = {worst[0]:.6e} at x={worst[1][0]:.6f}, y={worst[1][1]:.6g}")

# ------------------------------------------------- (N4) generic-kernel counterexample
print()
print("=" * 78)
print("N4  COUNTEREXAMPLE on a generic positive even kernel")
print("    Phi_c(t) = e^{-t^2} (2 + cos 2t) > 0, even.")
print("    M_c(z) = sqrt(pi) e^{z^2/4} (2 + e^{-1} cos z);  zeros at z = pi +- i*arccosh(2e)")
print("=" * 78)
CT, CW = gl(6000, 0.0, 9.0)


def Phic(t):
    return np.exp(-t * t) * (2.0 + np.cos(2.0 * t))


PHIC = Phic(CT)


def moments_c(x, y):
    ch, sh = np.cosh(y * CT), np.sinh(y * CT)
    c, s = np.cos(x * CT), np.sin(x * CT)
    A = 2.0 * np.sum(CW * ch * PHIC * c)
    Ap = 2.0 * np.sum(CW * CT * sh * PHIC * c)
    B = 2.0 * np.sum(CW * sh * PHIC * s)
    Bp = 2.0 * np.sum(CW * CT * ch * PHIC * s)
    return A, Ap, B, Bp


b0 = math.acosh(2.0 * math.e)     # cos z = -2e  =>  z = pi + i b0
x0, y0 = b0, math.pi
print(f"  predicted zero of M_c at  z = {y0:.6f} + {x0:.6f} i   (y=Re z, x=Im z)")
A, Ap, B, Bp = moments_c(x0, y0)
print(f"  |M_c(y0+i x0)|^2 = {A*A+B*B:.6e}   (should be ~0)")
A, Ap, B, Bp = moments_c(x0, 0.0)
print(f"  |M_c(i x0)|^2    = {A*A+B*B:.6e}   (strictly positive)")
print("  scan of Q_c(x0, y):")
neg = []
for y in np.linspace(0.0, 3.6, 61):
    A, Ap, B, Bp = moments_c(x0, y)
    q = A * Ap + B * Bp
    if q < 0:
        neg.append((y, q, A * A + B * B))
for (y, q, n) in neg[:12]:
    print(f"    y={y:.4f}  Q_c={q: .6e}   |M_c|^2={n:.6e}   <-- NEGATIVE")
print(f"  total negative y-samples on [0,3.6]: {len(neg)} / 61")

print()
print("=" * 78)
print("N5  Gaussian-mixture / complete-monotonicity control")
print("    Phi_g(t) = e^{-t^2} + e^{-4 t^2}  (a Gaussian mixture: Phi_g(sqrt(.)) completely monotone)")
print("=" * 78)


def Phig(t):
    return np.exp(-t * t) + np.exp(-4.0 * t * t)


PHIG = Phig(CT)


def moments_g(x, y):
    ch, sh = np.cosh(y * CT), np.sinh(y * CT)
    c, s = np.cos(x * CT), np.sin(x * CT)
    A = 2.0 * np.sum(CW * ch * PHIG * c)
    Ap = 2.0 * np.sum(CW * CT * sh * PHIG * c)
    B = 2.0 * np.sum(CW * sh * PHIG * s)
    Bp = 2.0 * np.sum(CW * CT * ch * PHIG * s)
    return A, Ap, B, Bp


negg = 0
mn = (math.inf, None)
for x in np.linspace(0.0, 12.0, 121):
    for y in np.linspace(0.0, 4.0, 41):
        A, Ap, B, Bp = moments_g(x, y)
        q = A * Ap + B * Bp
        if q < 0:
            negg += 1
        if q < mn[0]:
            mn = (q, (x, y))
print(f"  negatives: {negg} / {121*41};  min Q_g = {mn[0]:.6e} at x={mn[1][0]:.4f}, y={mn[1][1]:.4f}")
print("  A Gaussian mixture has cosine transform = positive mixture of Gaussians > 0 on R,")
print("  so it has NO zeros on the imaginary axis at all; the two-sided Laplace transform")
print("  M_g(z) = sqrt(pi)(e^{z^2/4} + e^{z^2/16}/2) is zero-free on C, so Q_g >= 0 holds for a")
print("  reason that CANNOT transfer to Phi_Xi (whose transform must have zeros).")
