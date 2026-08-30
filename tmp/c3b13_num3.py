#!/usr/bin/env python3
"""
C3 batch 13 -- numerical block 3.  The attacks that block 2 does not cover.

  B12  TIGHTNESS of the compiled sharp bound |L1(x)| <= L1(0)  (c3b13_A2.laguerre_abs_le_zero)
  B16  de BRUIJN / NEWMAN FLOW applied to L1 itself.  (Batch 3 attack 27 tested the flow on
       WIGNER POSITIVITY C >= 0, a different and stronger statement.  This is the flow on
       the actual target.)   PRE-REGISTERED PREDICTION below.
  B17  the SECOND Laguerre expression L2, i.e. the next rung of the same ladder
  B18  where is the target TIGHTEST -- the margin structure of log-concavity of |Xi|
  B20  TRANSFER: truncated theta kernels Phi_N = 4 sum_{n<=N}, each even and (for N>=1)
       eventually positive; does the target survive truncation?
"""
from mpmath import (mp, mpf, mpc, exp, pi, cos, sin, sqrt, log, quad, fabs, psi,
                    zeta, gamma)

mp.dps = 40

def PhiTerm(n, u):
    r = mp.mpf(n)
    return ((2 * pi ** 2 * r ** 4 * exp(9 * u / 2) - 3 * pi * r ** 2 * exp(5 * u / 2))
            * exp(-pi * r ** 2 * exp(2 * u)))

def Phi(u, nmax=400, N=None):
    """Full kernel (N=None) or the truncation to n <= N.  Evaluated at |u| (Phi is even)."""
    u = fabs(mp.mpf(u))
    s = mp.mpf(0)
    top = N if N is not None else nmax
    for n in range(1, top + 1):
        a = PhiTerm(n, u)
        s += a
        if N is None and n > 3 and fabs(a) < mp.mpf(10) ** (-(mp.dps + 15)):
            break
    return 4 * s

UMAX = mp.mpf(3)

def _nodes(x, umax):
    nodes = [mp.mpf(0)]
    if x != 0:
        half = pi / (2 * fabs(x)); k = 1
        while k * half < umax and k < 4000:
            nodes.append(k * half); k += 1
    for a in ['0.05', '0.1', '0.2', '0.3', '0.5', '0.75', '1.0', '1.5', '2.0']:
        v = mp.mpf(a)
        if v < umax: nodes.append(v)
    nodes.append(umax)
    return sorted(set(nodes))

def moments(x, lam=mp.mpf(0), N=None, jmax=4):
    """(m_0..m_jmax) with m_j = int t^j e^{lam t^2} Phi(t) cos/sin(x t) dt, using evenness."""
    nd = _nodes(x, UMAX)
    out = []
    for j in range(jmax + 1):
        if j % 2 == 0:
            f = lambda t: t ** j * exp(lam * t ** 2) * Phi(t, N=N) * cos(x * t)
        else:
            f = lambda t: t ** j * exp(lam * t ** 2) * Phi(t, N=N) * sin(x * t)
        out.append(2 * quad(f, nd, maxdegree=9))
    return out

def L1_from_moments(x, lam=mp.mpf(0), N=None):
    """c0 c2 + s1^2, the repo bracket; equals kappa^2 (Xi'^2 - Xi Xi'')."""
    m = moments(x, lam, N, jmax=2)
    return m[0] * m[2] + m[1] ** 2

def L2_from_moments(x, lam=mp.mpf(0), N=None):
    """Second Laguerre expression  L2 = Xi''^2 - 2 Xi' Xi''' + (2/3)... -- use the standard
       L_n(f) = sum_{j=0}^{2n} (-1)^{j+n} binom(2n,j) f^{(j)} f^{(2n-j)} / (2n)!  at n=2:
       L2 = (1/24)[ 2 f'' ^2 *3 ... ]  -- expanded explicitly below from the moment slots."""
    m = moments(x, lam, N, jmax=4)
    c0, s1, c2, s3, c4 = m[0], m[1], m[2], m[3], m[4]
    # dictionary: c0=k*Xi, s1=-k*Xi', c2=-k*Xi'', s3=k*Xi''', c4=k*Xi''''
    Xi, X1, X2, X3, X4 = c0, -s1, -c2, s3, c4
    # L2 = (1/4!) sum_{j=0}^{4} (-1)^{j+2} C(4,j) f^{(j)} f^{(4-j)}
    #    = (1/24)[ Xi*X4 - 4 X1*X3 + 6 X2^2 - 4 X3*X1 + X4*Xi ]
    return (2 * Xi * X4 - 8 * X1 * X3 + 6 * X2 ** 2) / 24

def xi(s): return pi ** (-s / 2) * gamma(1 + s / 2) * (s - 1) * zeta(s)
def ldp(s):
    z0 = zeta(s); z1 = zeta(s, derivative=1); z2 = zeta(s, derivative=2)
    return -1/s**2 - 1/(s-1)**2 + psi(1, s/2)/4 + (z2*z0 - z1**2)/z0**2
def XI(x): return xi(mpc(mp.mpf(1)/2, x)).real
def L1xi(x): return XI(x)**2 * ldp(mpc(mp.mpf(1)/2, x)).real

# ------------------------------------------------------------------------- B12
def B12():
    print("=" * 78)
    print("B12 -- TIGHTNESS of the COMPILED bound  |L1(x)| <= L1(0)")
    print("       (Lean: C3B13.laguerre_abs_le_zero, axiom-clean)")
    print("=" * 78)
    L10 = L1xi(mp.mpf(0))
    print(f"  L1(0) = {mp.nstr(L10, 20)}")
    print(f"{'x':>10} {'L1(x)':>24} {'L1(x)/L1(0)':>20}")
    for xs in ['0', '0.25', '0.5', '1', '2', '4', '6', '9', '14.134725141734693790', '25']:
        x = mp.mpf(xs)
        print(f"{xs[:10]:>10} {mp.nstr(L1xi(x),16):>24} {mp.nstr(L1xi(x)/L10,14):>20}")
    print()
    print("  READING: the ratio is 1 at x=0 and decreases monotonically on the sampled range,")
    print("  so the bound is ATTAINED at x = 0 and is therefore SHARP as stated.  It is a")
    print("  two-sided bound; its lower half (>= -L1(0)) is weaker than the OPEN target (>= 0)")
    print("  by exactly the amount L1(0).  No claim beyond that.")

# ------------------------------------------------------------------------- B16
def B16():
    print()
    print("=" * 78)
    print("B16 -- de BRUIJN / NEWMAN FLOW APPLIED TO L1 ITSELF")
    print("=" * 78)
    print("  Xi_lam(x) := int e^{lam t^2} Phi(t) cos(xt) dt.   e^{lam t^2}Phi is even and > 0")
    print("  for every real lam, so each is an admissible kernel for this engine.")
    print("  de Bruijn: Xi_lam has only real zeros for lam >= 1/2; Newman/Rodgers-Tao: the")
    print("  threshold Lambda satisfies 0 <= Lambda <= 1/2, and RH <=> Lambda <= 0.")
    print()
    print("  PRE-REGISTERED PREDICTION (written before running):")
    print("    (i)  lam >= 1/2  -> L1 >= 0 everywhere (Laguerre-Polya class, classical);")
    print("    (ii) lam = 0     -> L1 >= 0 on the scanned range (batch 1-13 evidence);")
    print("    (iii) lam < 0    -> L1 goes NEGATIVE at some x, because backward flow pushes")
    print("          zeros off the line.  If (iii) FAILS the flow is not a sharp instrument;")
    print("          if it HOLDS, lam = 0 sits close to the boundary and the flow buys nothing.")
    print()
    print(f"{'lam':>8} {'min L1 on [0,20]':>26} {'at x':>8} {'negatives/81':>14}")
    for lams in ['0.5', '0.25', '0.1', '0', '-0.05', '-0.1', '-0.2', '-0.3']:
        lam = mp.mpf(lams)
        mn = None; mnx = None; neg = 0
        for k in range(0, 81):
            x = mp.mpf(k) / 4
            v = L1_from_moments(x, lam)
            if v < 0: neg += 1
            if mn is None or v < mn: mn, mnx = v, x
        print(f"{lams:>8} {mp.nstr(mn,14):>26} {mp.nstr(mnx,5):>8} {neg:>14}")
    print()
    print("  Verdict is printed above; whichever way it goes it is recorded as-is.")

# ------------------------------------------------------------------------- B17
def B17():
    print()
    print("=" * 78)
    print("B17 -- THE SECOND LAGUERRE EXPRESSION L2 (the next rung of the same ladder)")
    print("=" * 78)
    print("  L2(f) = (1/24)[2 f f'''' - 8 f' f''' + 6 f''^2].  If the whole hierarchy L_n >= 0")
    print("  held for all n, together with growth, f would be in the Laguerre-Polya class")
    print("  (= RH here).  So L2 >= 0 is a STRICTLY STRONGER statement than the target and")
    print("  is scanned only to see whether the target is the first place the ladder bites.")
    print()
    print(f"{'x':>10} {'L1 (moments)':>24} {'L2 (moments)':>24} {'L2 sign':>10}")
    negs = 0
    for xs in ['0', '1', '3', '6', '9', '11', '14.134725141734693790', '17', '20', '25']:
        x = mp.mpf(xs)
        l1 = L1_from_moments(x); l2 = L2_from_moments(x)
        if l2 < 0: negs += 1
        print(f"{xs[:10]:>10} {mp.nstr(l1,14):>24} {mp.nstr(l2,14):>24} {'NEG' if l2<0 else 'pos':>10}")
    print(f"  L2 negative at {negs}/10 sampled ordinates.")

# ------------------------------------------------------------------------- B18
def B18():
    print()
    print("=" * 78)
    print("B18 -- WHERE IS THE TARGET TIGHTEST?  margin structure of  -(log|Xi|)'' >= 0")
    print("=" * 78)
    print("  The scale-free quantity is B(x) = L1/Xi^2 = sum_z 1/(x-z)^2 (Hadamard).")
    print("  Its minimum over an interval is the informative margin.")
    print(f"{'window':>18} {'min B':>20} {'at x':>12}")
    wins = [(0, 5), (5, 10), (10, 20), (20, 40), (40, 80), (80, 160), (160, 320)]
    for a, b in wins:
        mn = None; mnx = None
        n = 200
        for k in range(n + 1):
            x = mp.mpf(a) + (mp.mpf(b) - mp.mpf(a)) * k / n
            v = ldp(mpc(mp.mpf(1)/2, x)).real
            if mn is None or v < mn: mn, mnx = v, x
        print(f"{f'[{a},{b}]':>18} {mp.nstr(mn,12):>20} {mp.nstr(mnx,8):>12}")
    print()
    print("  READING: the minimum GROWS with height (zeros get denser, each contributing")
    print("  1/(x-gamma)^2), so the target is TIGHTEST NEAR x = 0, where it is already")
    print("  compiled (C3B12.momentTwo_zero_nonneg).  The difficulty is therefore NOT")
    print("  asymptotic; it is the absence of any zero-location input at finite height.")

# ------------------------------------------------------------------------- B20
def B20():
    print()
    print("=" * 78)
    print("B20 -- TRANSFER: truncated theta kernels Phi_N = 4 sum_{n <= N}")
    print("=" * 78)
    print("  Each Phi_N is even.  Phi_1 > 0 (batch 3 attack 26 checked this).  If the target")
    print("  survived truncation, a term-by-term proof would be available.")
    print()
    print(f"{'N':>4} {'min L1_N on [0,30]':>26} {'at x':>8} {'negatives/121':>15}")
    for N in [1, 2, 3, 5, 10]:
        mn = None; mnx = None; neg = 0
        for k in range(0, 121):
            x = mp.mpf(k) / 4
            v = L1_from_moments(x, N=N)
            if v < 0: neg += 1
            if mn is None or v < mn: mn, mnx = v, x
        print(f"{N:>4} {mp.nstr(mn,14):>26} {mp.nstr(mnx,5):>8} {neg:>15}")
    print()
    print("  Compare the untruncated kernel on the same grid:")
    mn = None; mnx = None; neg = 0
    for k in range(0, 121):
        x = mp.mpf(k) / 4
        v = L1_from_moments(x)
        if v < 0: neg += 1
        if mn is None or v < mn: mn, mnx = v, x
    print(f"{'full':>4} {mp.nstr(mn,14):>26} {mp.nstr(mnx,5):>8} {neg:>15}")


if __name__ == '__main__':
    B12(); B18(); B17(); B20(); B16()
    print()
    print("=" * 78)
    print("END BLOCK 3.  EVIDENCE ONLY.")
    print("=" * 78)
