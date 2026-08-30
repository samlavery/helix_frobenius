#!/usr/bin/env python3
"""
C3 batch 13 -- numerical block 4.  COVERAGE of the two COMPILED fibres.

  Fibre S (small readout)   C3B13.momentTwo_nonneg_of_thickened
        c2(0)*|c0(x)| <= s1(x)^2
  Fibre L (large readout)   C3B13.momentTwo_nonneg_of_large_readout
        Jbar a <= a^2 * (1/4) * c0(x)^2 ,   Jbar a = int_{(0,inf)} |u^2-a^2| C(0,u) du

Everything is in the REPO normalisation (c0 = cosMom riemannXiKernel = 2*xi(1/2+ix)).
Two independent routes are used for Jbar: direct quadrature, and the closed form
        Jbar a = a^2 (2 m0(a) - M0) - (2 m2(a) - M),
with M0 = int_{(0,inf)} C(0,u)du = (1/4)c0(0)^2 and M = int_{(0,inf)} u^2 C(0,u)du
= (1/8)c0(0)c2(0).  Disagreement between the routes REJECTS the formula.
"""
from mpmath import mp, mpf, mpc, exp, pi, cos, sin, sqrt, log, quad, fabs, psi, zeta, gamma

mp.dps = 30

def Phi(u, nmax=400):
    u = fabs(mp.mpf(u))
    e2u = exp(2 * u); e92 = exp(9 * u / 2); e52 = exp(5 * u / 2)
    s = mp.mpf(0)
    for n in range(1, nmax + 1):
        r = mp.mpf(n)
        a = (2 * pi ** 2 * r ** 4 * e92 - 3 * pi * r ** 2 * e52) * exp(-pi * r ** 2 * e2u)
        s += a
        if n > 3 and fabs(a) < mp.mpf(10) ** (-(mp.dps + 15)):
            break
    return 4 * s

UMAX = mp.mpf(3)

def xi(s): return pi ** (-s / 2) * gamma(1 + s / 2) * (s - 1) * zeta(s)
def c0(x): return 2 * xi(mpc(mp.mpf(1) / 2, x)).real          # kappa = 2, verified in B0

def C0(u):
    """cellDensity 0 u = int_p Phi(u+p)Phi(u-p) dp  >= 0."""
    u = mp.mpf(u)
    f = lambda p: Phi(u + p) * Phi(u - p)
    lim = UMAX + fabs(u)
    return quad(f, [-lim, -fabs(u), 0, fabs(u), lim], maxdegree=7)

def main():
    print("=" * 78)
    print("B21 -- COVERAGE of the two compiled fibres")
    print("=" * 78)
    # anchors
    c00 = c0(mp.mpf(0))
    # c2(0) = int t^2 Phi = -kappa*Xi''(0); take it from quadrature (route Q)
    c20 = 2 * quad(lambda t: t ** 2 * Phi(t) * mp.mpf(1), [0, mpf('0.1'), mpf('0.3'),
                                                          mpf('0.7'), mpf('1.5'), UMAX],
                   maxdegree=9)
    M0 = quad(C0, [0, mpf('0.05'), mpf('0.1'), mpf('0.2'), mpf('0.4'), mpf('0.8'),
                   mpf('1.5'), mpf('3'), mpf('6')], maxdegree=7)
    M = quad(lambda u: u ** 2 * C0(u), [0, mpf('0.05'), mpf('0.1'), mpf('0.2'), mpf('0.4'),
                                        mpf('0.8'), mpf('1.5'), mpf('3'), mpf('6')],
             maxdegree=7)
    print(f"  c0(0)          = {mp.nstr(c00, 18)}")
    print(f"  c2(0)          = {mp.nstr(c20, 18)}")
    print("  CONTROL: batch-12 identities  M0 = (1/4)c0(0)^2  and  M = (1/8)c0(0)c2(0)")
    print(f"    M0 (quadrature) = {mp.nstr(M0,16)}   (1/4)c0(0)^2 = {mp.nstr(c00**2/4,16)}"
          f"   reldiff {mp.nstr(fabs(M0-c00**2/4)/M0,4)}")
    print(f"    M  (quadrature) = {mp.nstr(M,16)}   (1/8)c0(0)c2(0) = {mp.nstr(c00*c20/8,16)}"
          f"   reldiff {mp.nstr(fabs(M-c00*c20/8)/M,4)}")
    print()
    print("  Jbar(a), two independent routes:")
    print(f"{'a':>8} {'Jbar direct':>20} {'Jbar closed form':>20} {'reldiff':>10}"
          f" {'threshold T=4J/a^2':>22}")
    best = None
    nodes = lambda a: sorted(set([mpf(0), mpf('0.05'), mpf('0.1'), a, mpf('0.2'), mpf('0.4'),
                                  mpf('0.8'), mpf('1.5'), mpf('3'), mpf('6')]))
    for asx in ['0.10','0.15','0.20','0.25','0.30','0.40','0.50','0.75','1.00']:
        a = mpf(asx)
        Jd = quad(lambda u: fabs(u ** 2 - a ** 2) * C0(u), nodes(a), maxdegree=7)
        m0a = quad(C0, [0, min(a, mpf('0.05')), a], maxdegree=7)
        m2a = quad(lambda u: u ** 2 * C0(u), [0, min(a, mpf('0.05')), a], maxdegree=7)
        Jc = a ** 2 * (2 * m0a - M0) - (2 * m2a - M)
        rd = fabs(Jd - Jc) / fabs(Jd)
        T = 4 * Jd / a ** 2
        if best is None or T < best[1]:
            best = (a, T)
        print(f"{asx:>8} {mp.nstr(Jd,12):>20} {mp.nstr(Jc,12):>20} {mp.nstr(rd,3):>10}"
              f" {mp.nstr(T,12):>22}")
    a_opt, T_min = best
    print()
    print(f"  best a = {mp.nstr(a_opt,6)},  threshold T_min = {mp.nstr(T_min,12)}")
    print(f"  c0(0)^2 = {mp.nstr(c00**2,12)}   ->  fibre L is NONEMPTY: {T_min < c00**2}")
    if T_min < c00 ** 2:
        need = sqrt(T_min)
        print(f"  fibre L covers exactly  {{ x : |c0(x)| >= {mp.nstr(need,12)} }}")
        # find the x where |c0| drops below need
        lo, hi = mpf(0), mpf(30)
        for _ in range(80):
            mid = (lo + hi) / 2
            if fabs(c0(mid)) >= need: lo = mid
            else: hi = mid
        print(f"  => an INTERVAL  |x| <= {mp.nstr(lo,10)}  (|c0| is decreasing there)")
    print()
    print("  Coverage on a grid x in [0,60] step 0.05 (1201 points):")
    covS = 0; covL = 0; covB = 0
    # s1(x) = -kappa*Xi'(x): get by exact differentiation of xi
    def s1(x):
        h = mpf(10) ** (-15)
        return -(c0(x + h) - c0(x - h)) / (2 * h)
    for k in range(0, 1201):
        x = mpf(k) / 20
        cx = c0(x)
        S = (c20 * fabs(cx) <= s1(x) ** 2)
        L = (T_min <= cx ** 2)
        if S: covS += 1
        if L: covL += 1
        if S or L: covB += 1
    print(f"    fibre S (small readout) : {covS}/1201 ({100.0*covS/1201:.2f}%)")
    print(f"    fibre L (large readout) : {covL}/1201 ({100.0*covL/1201:.2f}%)")
    print(f"    S or L (compiled union) : {covB}/1201 ({100.0*covB/1201:.2f}%)")
    print()
    print("  HONEST READING: the compiled union covers a neighbourhood of x = 0 -- which")
    print("  §B18 identifies as the TIGHTEST point of the target -- plus specks at the first")
    print("  zero.  It leaves the bulk of the line open.  No claim beyond the measured count.")

if __name__ == '__main__':
    main()
    print()
    print("=" * 78)
    print("END BLOCK 4.  EVIDENCE ONLY.")
    print("=" * 78)
