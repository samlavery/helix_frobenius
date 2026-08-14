"""ADVERSARIAL VERIFICATION of attempt 016, part 3.

K.  WHAT IS THE +1% EXCESS JUST ABOVE tau=1?  DC first: it is either
    (i) a broadband commodity on (1,3)  -- the thing the attempt was hunting, or
    (ii) the PEDESTAL of the tau=1 lattice line, i.e. the finite-d relaxation of
         Var(u_{k+d}-u_k-d) toward its saturated value -- Berry's number-variance
         saturation, the SAME classical object as the line, hence not new.
    (ii) predicts: the excess is confined to |tau-1| <~ 1/d_sat with d_sat ~ L/log2,
    i.e. a width shrinking like 1/L, and it should NOT be present around tau=2,3
    with the same weight (the line at tau=2 is dead).
L.  spot-checks of the record's remaining quoted numbers: NULL C medians, corr(K,D),
    the Fejer number, the precision claim at the height where Zrs is WORST (T=1e3).
"""
import numpy as np, os, sys
from math import log, pi, sqrt, exp
HERE = os.path.dirname(os.path.abspath(__file__))
def P(*a): print(*a); sys.stdout.flush()

def theta_asym(t):
    t = np.asarray(t, float)
    return (t/2*np.log(t/(2*pi)) - t/2 - pi/8 + 1/(48*t) + 7/(5760*t**3)
            + 31/(80640*t**5) + 127/(430080*t**7))

def K_direct(u, taus, blk=512):
    u = np.asarray(u, float); taus = np.asarray(taus, float)
    out = np.empty(len(taus))
    for i in range(0, len(taus), blk):
        ph = 2.0*np.pi*np.multiply.outer(taus[i:i+blk], u)
        out[i:i+blk] = (np.cos(ph).sum(1)**2 + np.sin(ph).sum(1)**2)/len(u)
    return out

HEIGHTS = [1e3, 1e4, 1e5, 1e6, 1e7]
D = {}
for T in HEIGHTS:
    g = np.load(os.path.join(HERE, f"att010_zeros_{T:.0e}.npy"))
    u = theta_asym(g)/pi; u -= u[0]
    D[T] = dict(g=g, u=u, U=float(u[-1]), n=len(u), L=log(0.5*(g[0]+g[-1])/(2*pi)))

WHICH = sys.argv[1] if len(sys.argv) > 1 else 'KL'

if 'K' in WHICH:
    P("="*104)
    P("K.  PROFILE OF THE EXCESS AROUND tau = 1, 2, 3.  Mean K in narrow shells |tau-m|.")
    P("    Poisson pipeline baseline is 1.0005 +- 0.0015 (60 draws), single-draw sd 0.0112.")
    P("="*104)
    SH = [(0.01, 0.03), (0.03, 0.06), (0.06, 0.10), (0.10, 0.20), (0.20, 0.40),
          (0.40, 0.70), (0.70, 1.00)]
    for m in (1, 2, 3):
        P(f"\n  shells around tau = {m}   (upper side only; entries are <K>)")
        P(f"  {'T':>9}{'L':>7}{'log2/L':>9}" + "".join(f"{f'{a:.2f}-{b:.2f}':>12}" for a, b in SH))
        for T in HEIGHTS:
            d = D[T]; U = d['U']
            taus = np.arange(1, int(3.0*U))/U
            if 'K' not in d:
                d['K'] = K_direct(d['u'], taus); d['taus'] = taus
            line = f"  {T:>9.0e}{d['L']:>7.2f}{log(2)/d['L']:>9.3f}"
            for a, b in SH:
                s = (d['taus'] > m+a) & (d['taus'] < m+b)
                line += f"{(d['K'][s].mean() if s.sum() > 30 else float('nan')):>12.4f}"
            P(line)
    P("\n  (i) broadband commodity  => excess roughly flat across all shells and around 2,3.")
    P("  (ii) pedestal of the tau=1 line => excess ONLY in the inner shells at tau=1,")
    P("       shrinking in width like 1/L, and ABSENT at tau=2,3 where the line is dead.")

    P("\n  K2.  INTEGRATED excess above 1.00 in (1.0,1.3) vs (1.3,3.0), and the same at tau=2.")
    P(f"  {'T':>9}{'int(1.0,1.3)':>14}{'int(1.3,3.0)':>14}{'int(2.0,2.3)':>14}{'int(2.3,3.0)':>14}")
    for T in HEIGHTS:
        d = D[T]; row = f"  {T:>9.0e}"
        for lo, hi in ((1.0, 1.3), (1.3, 3.0), (2.0, 2.3), (2.3, 3.0)):
            s = (d['taus'] > lo+0.002) & (d['taus'] < hi)
            row += f"{(d['K'][s].mean()-1)*(hi-lo):>14.5f}"
        P(row)

    P("\n  K3.  SURROGATE with the SAME S values but iid (kills S-correlations, keeps the line):")
    rng = np.random.default_rng(11)
    P(f"  {'T':>9}{'zeta (1.00,1.15)':>19}{'iid-S surrogate':>18}{'zeta (1.15,3.0)':>18}{'surr':>10}")
    for T in HEIGHTS:
        d = D[T]; n = d['n']
        r = np.arange(n) - d['u']; r -= r.mean()
        us = np.sort(np.arange(n) - rng.permutation(r)); us -= us[0]; UU = float(us[-1])
        ts = np.arange(1, int(3.0*UU))/UU
        Ks = K_direct(us, ts)
        row = f"  {T:>9.0e}"
        for lo, hi in ((1.002, 1.15), (1.15, 3.0)):
            sz = (d['taus'] > lo) & (d['taus'] < hi)
            ss = (ts > lo) & (ts < hi)
            row += f"{d['K'][sz].mean():>19.4f}{Ks[ss].mean():>18.4f}" if lo < 1.1 else \
                   f"{d['K'][sz].mean():>18.4f}{Ks[ss].mean():>10.4f}"
        P(row)

if 'L' in WHICH:
    P("\n" + "="*104)
    P("L.  SPOT-CHECKS of the record's remaining quoted numbers.")
    P("="*104)
    def primes_upto(X):
        X = int(X); s = np.ones(X+1, dtype=bool); s[:2] = False
        for p in range(2, int(X**0.5)+1):
            if s[p]: s[p*p::p] = False
        return np.nonzero(s)[0].astype(np.int64)
    XCAP = int(1e8); pr = primes_upto(XCAP); lg = np.log(pr.astype(float))
    E = np.arange(0, 3.0+1e-9, 0.05); MID = 0.5*(E[:-1]+E[1:])
    P("\n  L1. NULL C: median K/D and median |K/D-1| on 0.2<tau<0.95, and corr(K,D).")
    P(f"  {'T':>9}{'median K/D':>13}{'median|K/D-1|':>15}{'corr(K,D)':>12}{'median K/tau':>14}")
    for T in HEIGHTS:
        d = D[T]; L = d['L']
        tt = [lg/L]; ww = [lg*lg/pr.astype(float)]; k = 2
        while True:
            msk = pr.astype(float)**k <= XCAP
            if not msk.any(): break
            tt.append(k*lg[msk]/L); ww.append(lg[msk]**2/(pr[msk].astype(float)**k)); k += 1
        h, _ = np.histogram(np.concatenate(tt), bins=E, weights=np.concatenate(ww))
        Dp = h/(L*L*0.05)
        U = d['U']; taus = np.arange(1, int(3.0*U))/U
        K = d['K'] if 'K' in d else K_direct(d['u'], taus)
        idx = np.digitize(taus, E)-1
        bm = np.array([K[idx == b].mean() if (idx == b).sum() else np.nan for b in range(len(MID))])
        sel = (MID > 0.2) & (MID < 0.95)
        P(f"  {T:>9.0e}{np.nanmedian(bm[sel]/Dp[sel]):>13.4f}"
          f"{np.nanmedian(np.abs(bm[sel]/Dp[sel]-1)):>15.4f}"
          f"{np.corrcoef(bm[sel], Dp[sel])[0,1]:>12.4f}"
          f"{np.nanmedian(bm[sel]/MID[sel]):>14.4f}")

    P("\n  L2. FEJER: convolve min(|tau|,1) with the boxcar kernel sin^2(pi x U)/(pi^2 x^2 U).")
    for Uw in (4000.0, 5166.0):
        x = np.arange(-800000, 800001)/(80.0*Uw)      # +-10000/U in tau, fine step
        ker = np.where(np.abs(x) < 1e-15, Uw, np.sin(pi*x*Uw)**2/(pi*pi*x*x*Uw))
        ker = ker/ker.sum()
        for tg in (1.0, 1.05, 1.10):
            v = float(np.dot(ker, np.minimum(np.abs(tg-x), 1.0)))
            P(f"    U={Uw:.0f}  tau={tg:.2f}:  Fejer-smoothed = {v:.6f}   "
              f"deviation from min(tau,1) = {v-min(tg,1.0):+.2e}")

    P("\n  L3. PRECISION at the height where Riemann-Siegel is WORST (T=1e3).")
    P("      Measured |Z| at their cached zeros there is 3.6e-6, so the POSITIONAL")
    P("      uncertainty is ~|Z|/|Z'| ~ 6e-7, i.e. 60x LARGER than the 1e-8 jitter they")
    P("      tested, not 100x smaller.  Re-test with jitter 1e-6 and 1e-5.")
    rng = np.random.default_rng(5)
    P(f"  {'T':>9}{'K(1) exact':>12}{'j=1e-8':>10}{'j=1e-6':>10}{'j=1e-5':>10}"
      f"{'<K>1.05-3 exact':>17}{'j=1e-6':>10}{'j=1e-5':>10}")
    for T in HEIGHTS:
        d = D[T]; row = f"  {T:>9.0e}{float(K_direct(d['u'],[1.0])[0]):>12.4f}"
        outs = {}
        for j in (1e-8, 1e-6, 1e-5):
            gp = d['g'] + rng.normal(0, j, d['n'])
            up = theta_asym(gp)/pi; up -= up[0]; UU = float(up[-1])
            tt = np.arange(1, int(3.0*UU))/UU
            Kp = K_direct(up, tt)
            outs[j] = (float(K_direct(up, [1.0])[0]), Kp[(tt > 1.05) & (tt < 3)].mean())
            row += f"{outs[j][0]:>10.3f}"
        s = (d['taus'] > 1.05) & (d['taus'] < 3.0)
        row += f"{d['K'][s].mean():>17.4f}{outs[1e-6][1]:>10.4f}{outs[1e-5][1]:>10.4f}"
        P(row)

P("\ndone.")
