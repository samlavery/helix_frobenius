#!/usr/bin/env python3
"""
C3 batch 13 -- numerical block 5.  ADJUDICATION of the B20 truncation finding.

B20 reported: the even extension of the FIRST theta term, Phi_1(u) = 4*term_1(|u|),
violates the target (28/121 negatives on [0,30], min -1.47e-8 at x = 19.75), while N = 2
does not.  Before that is recorded as "no termwise proof can work", TWO confounds must be
ruled out:

  (C1) PRECISION.  L1 = c0 c2 + s1^2 is a cancelling combination.  Recompute at dps 30 / 60
       / 90 with two different quadrature node sets.  If the value moves, REJECT.

  (C2) THE CORNER.  The FULL Phi is smooth at 0 (its evenness is the Jacobi reflection, an
       identity, not an imposition).  A TRUNCATED sum is NOT even, so "Phi_N(|u|)" imposes
       evenness and creates a CORNER of size 2*Phi_N'(0+).  A corner makes the transform
       decay like 1/x^2 instead of exponentially, which by itself can flip L1 at large x.
       So the violation may be an artefact of the extension, NOT of the truncation.
       Measure Phi_N'(0+) for N = 1,2,3 and compare with the full kernel's 0.

  (C3) INDEPENDENT ROUTE.  By the Hadamard calculus of B9, L1 < 0 near x = g requires a
       zero of the transform at g -+ i*delta with delta small.  Locate the complex zero of
       Xi_1 nearest the real axis near x = 19.75 and check it predicts the observed sign.
"""
from mpmath import mp, mpf, mpc, exp, pi, cos, sin, sqrt, log, quad, fabs, findroot

def term(n, u):
    r = mp.mpf(n)
    return ((2 * pi ** 2 * r ** 4 * exp(9 * u / 2) - 3 * pi * r ** 2 * exp(5 * u / 2))
            * exp(-pi * r ** 2 * exp(2 * u)))

def dterm(n, u):
    """d/du term(n,u), exactly."""
    r = mp.mpf(n)
    A = 2 * pi ** 2 * r ** 4 * exp(9 * u / 2) - 3 * pi * r ** 2 * exp(5 * u / 2)
    dA = 9 * pi ** 2 * r ** 4 * exp(9 * u / 2) - mpf(15) / 2 * pi * r ** 2 * exp(5 * u / 2)
    E = exp(-pi * r ** 2 * exp(2 * u))
    dE = E * (-2 * pi * r ** 2 * exp(2 * u))
    return dA * E + A * dE

def PhiN(u, N, nmax=400):
    u = fabs(mp.mpf(u))
    s = mp.mpf(0)
    top = N if N is not None else nmax
    for n in range(1, top + 1):
        a = term(n, u)
        s += a
        if N is None and n > 3 and fabs(a) < mp.mpf(10) ** (-(mp.dps + 15)):
            break
    return 4 * s

UMAX = mp.mpf(3)

def nodeset(x, umax, variant=0):
    nodes = [mp.mpf(0)]
    if x != 0:
        half = pi / (2 * fabs(x)); k = 1
        while k * half < umax and k < 6000:
            nodes.append(k * half); k += 1
    extra = (['0.05','0.1','0.2','0.3','0.5','0.75','1.0','1.5','2.0'] if variant == 0
             else ['0.03','0.07','0.13','0.25','0.4','0.6','0.9','1.2','1.8','2.4'])
    for a in extra:
        v = mp.mpf(a)
        if v < umax: nodes.append(v)
    nodes.append(umax)
    return sorted(set(nodes))

def L1N(x, N, variant=0, umax=UMAX):
    nd = nodeset(x, umax, variant)
    c0 = 2 * quad(lambda t: PhiN(t, N) * cos(x * t), nd, maxdegree=10)
    s1 = 2 * quad(lambda t: t * PhiN(t, N) * sin(x * t), nd, maxdegree=10)
    c2 = 2 * quad(lambda t: t ** 2 * PhiN(t, N) * cos(x * t), nd, maxdegree=10)
    return c0 * c2 + s1 ** 2, c0, s1, c2

print("=" * 78)
print("C1 -- PRECISION ADJUDICATION of the N=1 violation at x = 19.75")
print("=" * 78)
print(f"{'dps':>6} {'nodes':>8} {'L1_1(19.75)':>26} {'c0':>16} {'s1':>16} {'c2':>16}")
vals = []
for dps in [30, 60, 90]:
    for variant in [0, 1]:
        mp.dps = dps
        v, c0, s1, c2 = L1N(mp.mpf('19.75'), 1, variant)
        vals.append(v)
        print(f"{dps:>6} {('A' if variant==0 else 'B'):>8} {mp.nstr(v,16):>26}"
              f" {mp.nstr(c0,10):>16} {mp.nstr(s1,10):>16} {mp.nstr(c2,10):>16}")
mp.dps = 60
spread = max(vals) - min(vals)
print(f"\n  spread across 6 (dps, nodeset) settings = {mp.nstr(spread, 6)}")
print(f"  value scale                              = {mp.nstr(fabs(vals[0]), 6)}")
print(f"  VERDICT: {'STABLE - the negative sign survives' if fabs(spread) < fabs(vals[0])/10 else 'UNSTABLE - REJECT'}")

print()
print("=" * 78)
print("C2 -- THE CORNER.  Phi_N'(0+) for the truncations, against the full kernel's 0.")
print("=" * 78)
mp.dps = 40
print("  The FULL kernel is even as an IDENTITY (Jacobi reflection), so Phi'(0) = 0 and")
print("  there is no corner.  A truncation is not even; forming Phi_N(|u|) imposes")
print("  evenness and creates a corner of size 2*Phi_N'(0+).")
print()
print(f"{'N':>4} {'Phi_N(0)':>20} {'Phi_N-prime(0+)':>22} {'corner/value':>16}")
for N in [1, 2, 3, 5, 10, 40]:
    v = 4 * sum(term(n, mp.mpf(0)) for n in range(1, N + 1))
    d = 4 * sum(dterm(n, mp.mpf(0)) for n in range(1, N + 1))
    print(f"{N:>4} {mp.nstr(v,12):>20} {mp.nstr(d,12):>22} {mp.nstr(fabs(d)/fabs(v),8):>16}")
print()
print("  READING: if Phi_N-prime(0+) -> 0 as N grows, the corner vanishes with N and the")
print("  N=1 violation CANNOT be separated from the corner artefact by this data alone.")

print()
print("=" * 78)
print("C3 -- INDEPENDENT ROUTE: the complex zero of Xi_1 nearest the real axis")
print("=" * 78)
print("  B9's Hadamard calculus: L1 < 0 near x = g requires a transform zero at g -+ i delta")
print("  with 2/delta^2 exceeding the other zeros' contribution.  Locate it.")
mp.dps = 30

def Xi1(z):
    """Transform of the even extension of the first theta term, at COMPLEX z."""
    nd = [mp.mpf(0), mpf('0.05'), mpf('0.1'), mpf('0.2'), mpf('0.3'), mpf('0.5'),
          mpf('0.75'), mpf('1.0'), mpf('1.5'), mpf('2.0'), UMAX]
    return 2 * quad(lambda t: PhiN(t, 1) * cos(z * t), nd, maxdegree=10)

try:
    z0 = findroot(Xi1, mpc('19.75', '-0.5'))
    print(f"  nearest zero found: z = {mp.nstr(z0, 12)}")
    d = fabs(z0.imag)
    print(f"  |Im z| = delta = {mp.nstr(d, 10)}   ->  pair contributes -2/delta^2 ="
          f" {mp.nstr(-2/d**2, 10)} at x = Re z")
    v, _, _, _ = L1N(mp.mpf(z0.real), 1)
    print(f"  measured L1_1(Re z) = {mp.nstr(v, 12)}  ({'NEGATIVE, as predicted' if v < 0 else 'POSITIVE - prediction MISSED'})")
except Exception as e:
    print(f"  root find failed: {e}")
    print("  (recorded as a failed cross-check, not as a confirmation)")

print()
print("=" * 78)
print("END BLOCK 5.")
print("=" * 78)
