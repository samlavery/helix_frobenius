#!/usr/bin/env python3
"""The convergence matrix: 32 denominator zeros x 4 coefficient cutoffs.

Decision (Sam, 2026-08-10): before any new form or Sym^6, make the Sym^5
measurement difficult to dismiss on the SAME form (LMFDB 1.0.1.1.1).

Per denominator zero rho_j of Lambda(Sym3 f), per cutoff M in
{250,500,750,1000}:
  - displacement of the NUMERATOR's local zero, d_j(M) = -g(0)/g'(0)
    (g = the real-valued line restriction of Lambda_pair; secant slope from
    +/-0.05) -- evidence the numerator HAS a zero there, not merely that it
    is small;
  - normalized residual R_j(M) = |g(0)| / local scale (max |g| at +/-0.25,
    +/-0.5);
  - at M=1000 a +/-delta profile tests the expected local linear crossing.
Scaling readout: containment predicts d_j(M) -> 0 systematically in M; a
truncation floor shows its scaling law; non-containment converges to a
nonzero displacement.

rho_j error propagation: zeros located with the degree-4 Lambda3 (effective
conductor ~7, so M=1000 is rounding-grade); the M=500 evaluation at rho_j
over the local slope bounds the zero displacement from truncation.

NEGATIVE CONTROL (design law: the machinery must SEE a pole where theory
puts one): Neururer--Oliver prove Lambda(Sym2 f)/xi has infinitely many
poles -- non-containment. Same machinery, numerator Lambda(Sym2 f) at the
first Riemann zeros: expected O(1) residual ratios and displacements that
do NOT shrink.  (Odd Maass f: Sym2 channels are sgn^2 = trivial, so
gamma(Sym2) = GammaR(s+2iR) GammaR(s) GammaR(s-2iR), eps = +1.)
"""
import sys, os, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from maass_containment import load_data, sym_coeffs_from_ap
from containment_bench2 import dirichlet_conv_mp

mp.mp.dps = 45

RIEMANN_ZEROS = ["14.134725141734693790", "21.022039638771554993",
                 "25.010857580145688763", "30.424876125859513210",
                 "32.935061587739189691"]


class PreciseSnap:
    """Regulator-free contour evaluator with D-table snapshots at several
    coefficient cutoffs (one ladder pass over n)."""

    def __init__(self, lams, lam, cutoffs, eps, h, T0, c=3.0):
        self.eps = eps
        K = int(2 * T0 / h)
        self.zs = [mp.mpc(c, -T0 + k * h) for k in range(K + 1)]
        m = len(lams)
        L = mp.fsum(lams)
        gam = []
        for z in self.zs:
            g = mp.power(mp.pi, -(m * z + L) / 2)
            for l in lams:
                g *= mp.gamma((z + l) / 2)
            gam.append(g)
        D = [mp.mpc(0)] * (K + 1)
        self.gD = {}
        z0 = self.zs[0]
        ih = mp.mpc(0, h)
        cuts = sorted(cutoffs)
        ci = 0
        for n in range(1, cuts[-1] + 1):
            ln = lam[n]
            if ln != 0:
                lnn = mp.log(n)
                p = mp.exp(-z0 * lnn)
                r = mp.exp(-ih * lnn)
                for k in range(K + 1):
                    D[k] += ln * p
                    p *= r
            if ci < len(cuts) and n == cuts[ci]:
                self.gD[cuts[ci]] = [g * d for g, d in zip(gam, D)]
                ci += 1
        self.pref = mp.mpf(h) / (2 * mp.pi)

    def value(self, s, M):
        one = mp.mpc(1)
        tot = mp.mpc(0)
        for gd, z in zip(self.gD[M], self.zs):
            tot += gd * (1 / (z - s) + self.eps / (z - (one - s)))
        return self.pref * tot


def find_zeros(f, t0, tmax, step, want):
    roots, tprev, vprev = [], mp.mpf(t0), f(mp.mpf(t0))
    t = mp.mpf(t0) + step
    while t < tmax and len(roots) < want:
        v = f(t)
        if vprev * v < 0:
            a, b, fa = tprev, t, vprev
            for _ in range(38):
                mmid = 0.5 * (a + b)
                fm = f(mmid)
                if fa * fm <= 0:
                    b = mmid
                else:
                    a, fa = mmid, fm
            roots.append(0.5 * (a + b))
        tprev, vprev = t, v
        t += step
    return roots


def main():
    t0 = time.time()
    R, a, emax = load_data()
    N = 1000
    lam2 = sym_coeffs_from_ap(2, N, a)
    lam3 = sym_coeffs_from_ap(3, N, a)
    lam5 = sym_coeffs_from_ap(5, N, a)
    cpair = dirichlet_conv_mp(lam5, lam3, N)
    i = mp.mpc(0, 1)
    g3 = [1 + i * m * R for m in (3, 1, -1, -3)]
    g5 = [1 + i * m * R for m in (5, 3, 1, -1, -3, -5)]
    g2 = [i * 2 * R, mp.mpc(0), -i * 2 * R]

    # ---- denominator zeros (degree 4; effective conductor ~7)
    L3 = PreciseSnap(g3, lam3, [500, 1000], mp.mpf(1), h=0.03, T0=float(3 * R) + 47)
    f3 = lambda t: L3.value(mp.mpc(0.5, t), 1000).real
    roots = find_zeros(f3, 0.3, 35.0, mp.mpf("0.05"), 32)
    t_top = float(roots[-1])
    print(f"# {len(roots)} zeros of Lambda(Sym3 f): first {mp.nstr(roots[0],10)}, "
          f"last {mp.nstr(roots[-1],10)}  [{time.time()-t0:.0f}s]")
    # rho_j truncation displacement: |L3^(500)(rho)| / slope
    rho_err = []
    for r in roots:
        sl = (f3(r + mp.mpf("0.05")) - f3(r - mp.mpf("0.05"))) / mp.mpf("0.1")
        v5 = L3.value(mp.mpc(0.5, r), 500).real
        rho_err.append(abs(v5 / sl) if sl != 0 else mp.mpf(0))
    print(f"# rho_j truncation displacement (M=500 vs 1000): max = "
          f"{float(max(rho_err)):.2e}")

    # ---- the pair, snapshots at four cutoffs
    Lp = PreciseSnap(g5 + g3, cpair, [250, 500, 750, 1000], mp.mpf(-1),
                     h=0.025, T0=float(5 * R) + t_top + 13)
    print(f"# pair tables built  [{time.time()-t0:.0f}s]")
    gP = lambda t, M: Lp.value(mp.mpc(0.5, t), M).imag

    def displacement(r, M, dsec=mp.mpf("0.05")):
        gz = gP(r, M)
        sl = (gP(r + dsec, M) - gP(r - dsec, M)) / (2 * dsec)
        return (-gz / sl if sl != 0 else mp.mpf(0)), gz, sl

    print("# zero          M=250 d      M=500 d      M=750 d      M=1000 d     "
          "R(1000)   lin")
    ds = {M: [] for M in (250, 500, 750, 1000)}
    for r in roots:
        row = []
        for M in (250, 500, 750, 1000):
            d, gz, sl = displacement(r, M)
            ds[M].append(abs(d))
            row.append(d)
        # M=1000 profile: local scale and linearity of the crossing
        loc = max(abs(gP(r + d0, 1000)) for d0 in
                  (mp.mpf("-0.5"), mp.mpf("-0.25"), mp.mpf("0.25"), mp.mpf("0.5")))
        Rj = abs(gP(r, 1000)) / loc
        _, _, sl = displacement(r, 1000)
        wide = (gP(r + mp.mpf("0.1"), 1000) - gP(r - mp.mpf("0.1"), 1000)) / mp.mpf("0.2")
        lin = abs(wide / sl) if sl != 0 else mp.mpf(0)
        print(f"# t={mp.nstr(r,10):13} " +
              " ".join(f"{float(x):+.3e}" for x in row) +
              f"  {float(Rj):.2e}  {float(lin):.3f}")
    print("# scaling summary (median |d_j(M)| over the 32 zeros):")
    med = {}
    for M in (250, 500, 750, 1000):
        v = sorted(ds[M])
        med[M] = v[len(v) // 2]
        print(f"#   M={M:4}: median |d| = {float(med[M]):.3e}")
    for M in (250, 500, 750):
        print(f"#   ratio med|d({M})|/med|d(1000)| = {float(med[M]/med[1000]):.2f}")

    # ---- NEGATIVE CONTROL: Lambda(Sym2 f) at Riemann zeros (N--O: no containment)
    L2 = PreciseSnap(g2, lam2, [500, 1000], mp.mpf(1), h=0.025,
                     T0=float(2 * R) + 34 + 13)
    print(f"# control tables built  [{time.time()-t0:.0f}s]")
    g2f = lambda t, M: L2.value(mp.mpc(0.5, t), M).real
    print("# NEGATIVE CONTROL: Lambda(Sym2 f) at Riemann zeros "
          "(theory: containment FAILS):")
    for rs in RIEMANN_ZEROS:
        r = mp.mpf(rs)
        gz = g2f(r, 1000)
        loc = max(abs(g2f(r + d0, 1000)) for d0 in
                  (mp.mpf("-0.5"), mp.mpf("-0.25"), mp.mpf("0.25"), mp.mpf("0.5")))
        sl = (g2f(r + mp.mpf("0.05"), 1000) - g2f(r - mp.mpf("0.05"), 1000)) / mp.mpf("0.1")
        d1000 = -gz / sl if sl != 0 else mp.mpf(0)
        gz5 = g2f(r, 500)
        sl5 = (g2f(r + mp.mpf("0.05"), 500) - g2f(r - mp.mpf("0.05"), 500)) / mp.mpf("0.1")
        d500 = -gz5 / sl5 if sl5 != 0 else mp.mpf(0)
        print(f"#   t={rs[:10]}: ratio = {float(abs(gz)/loc):.3e}   "
              f"d(500) = {float(d500):+.3e}   d(1000) = {float(d1000):+.3e}")
    print(f"# total {time.time()-t0:.0f}s")


if __name__ == '__main__':
    main()
