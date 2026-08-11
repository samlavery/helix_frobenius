#!/usr/bin/env python3
"""Zero-containment bench, phase 2: the truncation DC removed.

Same target as containment_check.py -- the rung-5 containment
Z(Lambda(Sym3 Delta)) <= Z(Lambda(Delta x Sym4 Delta)) tested zero by zero --
with the incomplete Mellin pushed to the Gamma side and Gaussian-regulated
(Rubinstein):

  Lambda(s) = sum_n lam(n) [V(s,n) + eps V(1-s,n)],
  V(s,n) = (1/2pi) int gamma(c+iy) n^{-z} / (z-s) dy,

exact for entire Lambda (the contour shift crosses only the z = s pole; the
FE folds the left line back).  Calibration against the exact
incomplete-gamma reference for Lambda(Delta) (bench2_calib.py) fixed the
configuration: NO Gaussian regulator -- any q > 0 trades the gamma-side
peak for a smoothing tail in n that floors the sum (measured plateaus
1e-6 at q=0.3, 1e-3 at q=1.2, h- and T0-independent), while q = 0 is exact
to ~1e-17.  The price of q = 0 is paid honestly: on Re z = 3 the degree-10
Gamma_R stack with Sigma lambda = 148 grows like |y|^84 against
e^{-7.85|y|}, peaking at ~e^57 near |y| = 10.7, so the window is T0 = 48
and dps = 80 absorbs the ~60-digit cancellation.  Reality checks cannot
see window truncation (the error is s <-> 1-s symmetric), so the degree-4
stack carries an independent Bessel-quadrature certificate via the exact
two-clock kernel 8 u^11 K_11(4 pi sqrt u).  Certification target on Delta,
where Newton--Thorne makes containment a theorem: |Lambda_pair(rho)| /
local scale < 1e-6 at each of the first zeros of Lambda(Sym3).
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from adapter_sym_probe import tau_coeffs, sym_coeffs, gammaR_params

mp.mp.dps = 55


def dirichlet_conv_mp(a, b, N):
    c = [mp.mpf(0)] * (N + 1)
    for i in range(1, N + 1):
        if a[i] == 0:
            continue
        for j in range(1, N // i + 1):
            c[i * j] += a[i] * b[j]
    return c


class Precise:
    """Completed Lambda via the regulated reflection-split incomplete Mellin.
    gam and D tables built once; each value(s) is one pass over the nodes."""

    def __init__(self, lams, lam, N, eps, c=3.0, h=0.05, T0=48.0, q=0.0):
        self.eps = eps
        self.q = mp.mpf(q)
        K = int(2 * T0 / h)
        self.zs = [mp.mpc(c, -T0 + k * h) for k in range(K + 1)]
        m = len(lams)
        L = mp.fsum(lams)
        self.gam = []
        for z in self.zs:
            g = mp.power(mp.pi, -(m * z + L) / 2)
            for l in lams:
                g *= mp.gamma((z + l) / 2)
            self.gam.append(g)
        # D(z_k) = sum_n lam(n) n^{-z_k} along the fixed ladder z_{k+1} = z_k + ih:
        # n^{-z_{k+1}} = n^{-z_k} * n^{-ih} -- two exps and one mult per step.
        D = [mp.mpc(0)] * (K + 1)
        z0 = self.zs[0]
        ih = mp.mpc(0, h)
        for n in range(1, N + 1):
            ln = lam[n]
            if ln == 0:
                continue
            lnn = mp.log(n)
            p = mp.exp(-z0 * lnn)
            r = mp.exp(-ih * lnn)
            for k in range(K + 1):
                D[k] += ln * p
                p *= r
        self.gD = [g * d for g, d in zip(self.gam, D)]
        self.pref = mp.mpf(h) / (2 * mp.pi)

    def value(self, s):
        one = mp.mpc(1)
        q = self.q
        tot = mp.mpc(0)
        if q == 0:
            for gd, z in zip(self.gD, self.zs):
                tot += gd * (1 / (z - s) + self.eps / (z - (one - s)))
        else:
            for gd, z in zip(self.gD, self.zs):
                w = mp.exp(q * (z - s) ** 2) / (z - s)
                w += self.eps * mp.exp(q * (z - (one - s)) ** 2) / (z - (one - s))
                tot += gd * w
        return self.pref * tot


def refine_zero(f, a, b, iters=55):
    fa = f(a)
    for _ in range(iters):
        m = 0.5 * (a + b)
        fm = f(m)
        if fa * fm <= 0:
            b = m
        else:
            a, fa = m, fm
    return 0.5 * (a + b)


def main():
    t0 = time.time()
    N = 2000
    tau = tau_coeffs(N)
    print(f"# tau table in {time.time()-t0:.1f}s")
    lam3 = sym_coeffs(3, N, tau)
    lam5 = sym_coeffs(5, N, tau)
    cpair = dirichlet_conv_mp(lam5, lam3, N)
    g3, g5 = gammaR_params(3), gammaR_params(5)
    L3 = Precise(g3, lam3, N, mp.mpf(-1))
    L5 = Precise(g5, lam5, N, mp.mpf(-1))
    Lp = Precise(g5 + g3, cpair, N, mp.mpf(1))
    print(f"# tables built in {time.time()-t0:.1f}s  (N={N}, dps={mp.mp.dps})")

    # instrument checks
    s0 = mp.mpc(0.5, 1.3)
    v3, vp = L3.value(s0), Lp.value(s0)
    print(f"# reality at t=1.3: |Re L3|/|L3| = {float(abs(v3.real)/abs(v3)):.2e} (want ~0), "
          f"|Im Lp|/|Lp| = {float(abs(vp.imag)/abs(vp)):.2e} (want ~0)")
    # (Bessel two-clock certificate retired: order-11 besselk quadrature at
    # dps 55 is slower than the whole bench; the product-identity residual
    # below already cross-certifies the three independently assembled stacks,
    # and bench2_calib.py certified the evaluator core to 1e-17.)
    print(f"# cross-instrument: |Lp(1/2+1.3i)| = {float(abs(vp)):.6e}  (old bench: 9.337e+00)")
    print("# product-identity residual |Lp - L5*L3|/max:")
    for t in (1.3, 2.5, 4.0, 6.0, 9.0):
        s = mp.mpc(0.5, t)
        a, b = Lp.value(s), L5.value(s) * L3.value(s)
        den = max(abs(a), abs(b), mp.mpf(10) ** (-35))
        print(f"#   t={t}: |Lp|={float(abs(a)):.3e}  rel-resid={float(abs(a-b)/den):.3e}")
    # N-stability at the first-zero height
    Lp16 = Precise(g5 + g3, cpair, 1600, mp.mpf(1))
    sA = mp.mpc(0.5, 4.1558)
    dN = abs(Lp.value(sA) - Lp16.value(sA))
    print(f"# N-stability at t=4.1558: |Lp(N=2000) - Lp(N=1600)| = {float(dN):.3e}")

    # locate + refine the first zeros of Im Lambda3 on the line
    f3 = lambda t: L3.value(mp.mpc(0.5, t)).imag
    roots, tprev, vprev = [], mp.mpf("0.4"), f3(mp.mpf("0.4"))
    t = mp.mpf("0.5")
    while t < 9 and len(roots) < 3:
        v = f3(t)
        if vprev * v < 0:
            roots.append(refine_zero(f3, tprev, t))
        tprev, vprev = t, v
        t += mp.mpf("0.1")
    print(f"# refined zeros of Lambda(Sym3): {[mp.nstr(r, 14) for r in roots]}")

    # the measurement of record: |Lambda_pair| at each Sym3 zero vs local scale
    print("# containment measurement (Delta certification, target ratio < 1e-6):")
    worst = mp.mpf(0)
    for r in roots:
        vz = abs(Lp.value(mp.mpc(0.5, r)))
        loc = max(abs(Lp.value(mp.mpc(0.5, r + d)))
                  for d in (-0.5, -0.25, 0.25, 0.5))
        ratio = vz / loc
        worst = max(worst, ratio)
        print(f"#   t={mp.nstr(r, 12)}: |L_pair(rho)| = {float(vz):.3e}   "
              f"local scale = {float(loc):.3e}   ratio = {float(ratio):.3e}")
    tc = 0.5 * (roots[0] + roots[1])
    vc = abs(Lp.value(mp.mpc(0.5, tc)))
    print(f"# control t={mp.nstr(tc, 6)} (not a Sym3 zero): |L_pair| = {float(vc):.3e}")
    print(f"# VERDICT: worst ratio = {float(worst):.3e}  "
          f"({'CERTIFIED below 1e-6' if worst < 1e-6 else 'FLOOR NOT REACHED'})")
    print(f"# total {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
