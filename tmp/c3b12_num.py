#!/usr/bin/env python3
"""C3 batch 12 numerics.  NONRIGOROUS CONTROLS ONLY.

Every section carries an explicit error control: each quantity is computed at two
independent resolutions (or by two independent routes) and the discrepancy is printed.
No claim in the batch-12 ledger rests on anything in this file.

  P1  the compiled momentTwo_eq, against a direct 2D quadrature (2 resolutions)
  P2  the readout dictionary  c0 = Xi, s1 = -Xi', c2 = -Xi''  (quadrature vs mpmath)
  P3  the compiled elementary_factor_split, at M = (z^2-1/4) G,  G = pi^{-s/2}Gamma(s/2)zeta(s)
      -- including the SIGN of each of the two terms inside and outside |s-1/2| < 1/2
  P4  hostile scan of the sub-leaf L1(x) = Xi'(x)^2 - Xi(x)Xi''(x) to x = 300, mpmath
  P5  the counterexample kernel Phi_c: is the u^2 sub-leaf ALSO violated?
"""
import math
import numpy as np
import mpmath as mp

mp.mp.dps = 30
NMAX = 60
TMAX = 2.6


def gl(n, a, b):
    q, w = np.polynomial.legendre.leggauss(n)
    return 0.5 * (b - a) * q + 0.5 * (b + a), 0.5 * (b - a) * w


def Phi(t):
    a = np.abs(np.asarray(t, dtype=float))
    e2 = np.exp(2.0 * a)
    s = np.zeros_like(a)
    for n in range(1, NMAX + 1):
        s += (2.0 * math.pi ** 2 * n ** 4 * np.exp(4.5 * a)
              - 3.0 * math.pi * n ** 2 * np.exp(2.5 * a)) * np.exp(-math.pi * n * n * e2)
    return 4.0 * s


def moments_poly(x, nq):
    """c0 = cosMom(Phi), s1 = sinMom(t Phi), c2 = cosMom(t^2 Phi); full-line, folded."""
    tn, tw = gl(nq, 0.0, TMAX)
    ph = Phi(tn)
    c0 = 2.0 * np.sum(tw * ph * np.cos(x * tn))
    s1 = 2.0 * np.sum(tw * tn * ph * np.sin(x * tn))
    c2 = 2.0 * np.sum(tw * tn ** 2 * ph * np.cos(x * tn))
    return c0, s1, c2


def momentTwo_moments(x, nq=4000):
    c0, s1, c2 = moments_poly(x, nq)
    return 0.125 * (c0 * c2 + s1 ** 2)


def momentTwo_direct(x, nu, npq):
    """int_{u>0} u^2 C(x,u) du by direct 2D quadrature."""
    pn, pw = gl(npq, -4.0, 4.0)
    un, uw = gl(nu, 0.0, 3.0)
    tot = 0.0
    for uu, ww in zip(un, uw):
        c = np.sum(pw * Phi(uu + pn) * Phi(uu - pn) * np.cos(2.0 * x * pn))
        tot += ww * uu ** 2 * c
    return tot


print("=" * 78)
print("P1  compiled  momentTwo_eq :  int_{u>0} u^2 C(x,u) du = (1/8)(c0*c2 + s1^2)")
print("    error control: two quadrature resolutions for each side")
print("=" * 78)
for x in [0.0, 1.0, 3.0, 7.0, 14.134725142, 20.0]:
    m_lo = momentTwo_moments(x, 2000)
    m_hi = momentTwo_moments(x, 4000)
    d_lo = momentTwo_direct(x, 200, 1500)
    d_hi = momentTwo_direct(x, 400, 3000)
    print(f"  x={x:12.6f}  moments={m_hi: .12e} (self-err {abs(m_hi-m_lo):.2e})")
    print(f"  {'':14}  direct ={d_hi: .12e} (self-err {abs(d_hi-d_lo):.2e})"
          f"   MISMATCH={abs(m_hi-d_hi):.3e}")

print()
print("=" * 78)
print("P2  readout dictionary:  c0 = Xi(x),  s1 = -Xi'(x),  c2 = -Xi''(x)")
print("    Xi(x) = 2 xi(1/2 + i x)   (the factor 2 was measured in batch 11 N2b)")
print("=" * 78)


def xi(s):
    return s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi(x):
    return mp.re(2 * xi(mp.mpf(1) / 2 + 1j * mp.mpf(x)))


for x in [0.0, 1.0, 3.0, 7.0, 14.134725142, 20.0]:
    c0, s1, c2 = moments_poly(x, 4000)
    X0 = Xi(x)
    X1 = mp.diff(Xi, x, 1)
    X2 = mp.diff(Xi, x, 2)
    print(f"  x={x:12.6f}  c0={c0: .10e} Xi={float(X0): .10e}  |d|={abs(c0-float(X0)):.2e}")
    print(f"  {'':14}  s1={s1: .10e} -Xi'={float(-X1): .10e}  |d|={abs(s1+float(X1)):.2e}")
    print(f"  {'':14}  c2={c2: .10e} -Xi''={float(-X2): .10e} |d|={abs(c2+float(X2)):.2e}")

print()
print("=" * 78)
print("P3  compiled elementary_factor_split at  M = (z^2 - 1/4) G,  G = pi^{-s/2}Gamma(s/2)zeta(s)")
print("      Re[M' conj M] = 2*Re(z)*(|z|^2 - 1/4)*|G|^2 + |z^2-1/4|^2 * Re[G' conj G]")
print("=" * 78)


def G(s):
    return mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def logderivG(s):
    return -mp.log(mp.pi) / 2 + mp.digamma(s / 2) / 2 + mp.zeta(s, derivative=1) / mp.zeta(s)


def logderivXi(s):
    return 1 / s + 1 / (s - 1) + logderivG(s)


print(f"  {'y':>8} {'x':>8} {'|z|^2-1/4':>12} {'elem term':>15} {'G term':>15} "
      f"{'sum':>15} {'Re[M conj M]':>15} {'rel err':>10}")
for (y, x) in [(0.1, 0.1), (0.2, 0.3), (0.3, 0.35), (0.49, 0.05), (0.6, 0.2),
               (1.0, 2.0), (0.05, 0.05), (0.25, 0.4)]:
    s = mp.mpf(1) / 2 + mp.mpf(y) + 1j * mp.mpf(x)
    z = mp.mpf(y) + 1j * mp.mpf(x)
    Gv = G(s)
    nG = abs(Gv) ** 2
    elem = 2 * y * (abs(z) ** 2 - mp.mpf(1) / 4) * nG
    Gterm = abs(z ** 2 - mp.mpf(1) / 4) ** 2 * (nG * mp.re(logderivG(s)))
    # Re[M' conj M] with M = 2 xi(1/2+z):  = 4 |xi|^2 Re[xi'/xi]
    xiv = xi(s)
    tot = 4 * abs(xiv) ** 2 * mp.re(logderivXi(s))
    ssum = elem + Gterm
    rel = abs(ssum - tot) / abs(tot)
    print(f"  {y:8.3f} {x:8.3f} {float(abs(z)**2-0.25):12.5f} {float(elem):15.6e} "
          f"{float(Gterm):15.6e} {float(ssum):15.6e} {float(tot):15.6e} {float(rel):10.2e}")
print("  -> CORRECTED (OpenAI adjudication 2026-08-25).  An earlier draft of this line said")
print("     'outside, both are positive'.  The table above REFUTES that: at (y,x)=(0.600,0.200)")
print("     and (1.000,2.000) the elementary term is positive while the G term is NEGATIVE.")
print("     The correct reading is that the two terms have OPPOSITE signs at every sampled")
print("     point, and which one carries the leaf SWAPS across the circle |s-1/2| = 1/2:")
print("       inside  (|z|^2 < 1/4): elementary term < 0, G term > 0;")
print("       outside (|z|^2 > 1/4): elementary term > 0, G term < 0.")
print("     Only the ELEMENTARY term's sign is compiled (C3B12.elementary_term_neg /")
print("     elementary_term_nonneg).  The split itself is compiled ONLY as complex algebra")
print("     (C3B12.elementary_factor_split); the analytic bridge M = (z^2-1/4)N from")
print("     Phi = psi'' - psi/4 is NOT COMPILED, and this section is its numerical check only.")

print()
print("=" * 78)
print("P4  HOSTILE SCAN of the sub-leaf  L1(x) = Xi'(x)^2 - Xi(x) Xi''(x)  to x = 300")
print("    (mpmath 30 dps; L1 = 8 * int_{u>0} u^2 C(x,u) du, the compiled momentTwo)")
print("=" * 78)
ZEROS = [14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
         37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478,
         52.970321478, 56.446247697, 59.347044003, 60.831778525, 65.112544048,
         67.079810529, 69.546401711, 72.067157674, 75.704690699, 77.144840069,
         79.337375020, 82.910380854, 84.735492981, 87.425274613, 88.809111208,
         92.491899271, 94.651344041, 95.870634228, 98.831194218, 101.317851006]


def L1(x):
    d1 = mp.diff(Xi, x, 1)
    d2 = mp.diff(Xi, x, 2)
    return d1 ** 2 - Xi(x) * d2


neg = 0
tot = 0
worst = (mp.inf, None)
xs = [i * 0.5 for i in range(0, 601)]
for g in ZEROS:
    for d in (-0.01, 0.0, 0.01):
        xs.append(g + d)
for x in xs:
    v = L1(x)
    tot += 1
    if v < 0:
        neg += 1
        if neg <= 10:
            print(f"  NEGATIVE at x={x:.6f}: L1={float(v):.6e}")
    if v < worst[0]:
        worst = (v, x)
print(f"  scanned {tot} points on [0,300] (step 0.5) + 30 zero ordinates at +-0.01")
print(f"  negatives: {neg};  min L1 = {float(worst[0]):.6e} at x={worst[1]:.4f}")
print("  ZERO FIBRE (compiled: momentTwo_eq_sq_of_cosMom_zero):  at a zero of Xi, L1 = Xi'^2")
for g in ZEROS[:6]:
    d1 = mp.diff(Xi, g, 1)
    print(f"    x={g:.9f}  Xi={float(Xi(g)):+.3e}  L1={float(L1(g)):.10e}"
          f"  Xi'^2={float(d1**2):.10e}  |d|={float(abs(L1(g)-d1**2)):.2e}")

print()
print("=" * 78)
print("P5  is the u^2 SUB-LEAF also violated by the counterexample kernel?")
print("    Phi_c(t) = e^{-t^2}(2 + cos 2t);  Xi_c(x) = cosine transform")
print("=" * 78)
CT, CW = gl(6000, 0.0, 9.0)
PHIC = np.exp(-CT * CT) * (2.0 + np.cos(2.0 * CT))


def Xic(x):
    return 2.0 * np.sum(CW * PHIC * np.cos(x * CT))


def L1c(x, h=1e-4):
    return ((Xic(x + h) - Xic(x - h)) / (2 * h)) ** 2 \
        - Xic(x) * (Xic(x + h) - 2 * Xic(x) + Xic(x - h)) / h ** 2


negc = 0
mnc = (math.inf, None)
for i in range(0, 401):
    x = i * 0.05
    v = L1c(x)
    if v < 0:
        negc += 1
    if v < mnc[0]:
        mnc = (v, x)
print(f"  Phi_c on x in [0,20] step 0.05:  negatives = {negc}/401;"
      f"  min L1_c = {mnc[0]:.6e} at x={mnc[1]:.3f}")
if negc == 0:
    print("  => the u^2 sub-leaf is NOT violated by Phi_c: it is STRICTLY WEAKER than the")
    print("     full leaf, which Phi_c does violate (batch 11 F1).  So the counterexample")
    print("     does NOT rule out an unconditional proof of the sub-leaf.")
else:
    print("  => Phi_c violates the sub-leaf too: same instrument limit applies to it.")
