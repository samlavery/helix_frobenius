"""ATTEMPT 030, stage 4 -- WHAT THE THRESHOLD ACTUALLY SCALES WITH, and what produces it.

Stage 2 already refuted BOTH pre-registered mechanisms as stated:
  (W) "n* is the same for every L-function"        -- refuted, n* spreads 3.1-6.6x
  (R) "n* = gamma_1^2 log m_1"                     -- refuted, n*/(gamma_1^2 log m_1) spreads
                                                      2.1-4.6x and chi_-3/chi_5 come out in the
                                                      WRONG ORDER (21 vs 41, predicted 45 vs 31)
so this stage measures the exponent instead of assuming it, and identifies the object.

 A. EXPONENT.  n_half(chi) := the smallest n at which the sliding oscillation amplitude
    A(n) = rms(detrended lambda^arith on [n, 2n]) / n^{1/4} first reaches f * plateau and stays.
    Regress log n_half on log gamma_1 over the four specimens -> exponent p.
    PRE-REGISTERED DECISION RULE: p >= 1.6 supports the resonance law n = gamma_1^2 log m;
    p <= 1.3 refutes it.  Reported for f = 0.3, 0.5, 0.7 and window ratios 1.5, 2, 3 so the
    exponent's own spread is visible.

 B. IDENTIFICATION.  Zero-parameter test of the rival object.  lambda_n = sum_gamma
    [2 - 2 cos(2 n arctan(1/(2 gamma)))], so the LOWEST ZEROS contribute pure cosines in n of
    period 2 pi gamma_1 (= 88.8, 50.5, 41.8, 30.8 for the four specimens).  Model the
    oscillation by the FIRST K zeros only, K = 1,2,3,5,10 -- no fitted parameters at all --
    and score it against lambda_n^arith on the same windows where the prime-Laguerre model
    scored badly.  If the small-n oscillation IS the lowest zeros' cosine, the threshold is
    "when the lowest zero has completed enough cycles to survive the detrend", i.e. n prop
    gamma_1, and it says nothing about primes.

 C. matched filter, PHASE FIXED: the m-tone in lambda^arith = -sum_m ... is
    -a_m n^{1/4} cos(omega_m sqrt n - 3pi/4) with a_m = Lambda(m) chi(m)/(sqrt(pi) sqrt m
    (log m)^{3/4}), so arg A = pi/4 when chi(m)=+1 and -3pi/4 when chi(m)=-1.  Stage 3 used
    +pi/4 for every specimen, which is wrong for chi(m_1) = -1; corrected here.

STATED NULL (pre-registered before this stage)
  N7  p >= 1.6  (the gamma_1^2 resonance law survives a direct exponent measurement)
  N8  the first-K-zeros model does NOT explain the sub-threshold oscillation: R^2 < 0.5 for
      every K on the windows below n_half.
"""
import sys, os, math, time
import numpy as np
from mpmath import mp, mpf, mpc

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from att030_zeta import prime_powers, line_prediction_zeta, score, detrend
from att030_dirichlet import CHARS, chi_line_prediction, Lchi
def P(*a): print(*a); sys.stdout.flush()

def zeros_of(q, a, chi, T=60.0):
    mp.dps = 25
    def Z(t):
        s = mpc(mpf(1)/2, t)
        th = (t/2)*mp.log(mpf(q)/mp.pi) + mp.im(mp.loggamma((mpf(1)/2+a+mpc(0, t))/2))
        return mp.re(mp.expj(th)*Lchi(s, q, chi))
    ts = np.arange(0.02, T, 0.02); out = []; prev = Z(mpf(0.02))
    for t in ts[1:]:
        cur = Z(mpf(t))
        if prev*cur < 0:
            out.append(float(mp.findroot(Z, (mpf(t-0.02), mpf(t)), solver='bisect',
                                         tol=mpf(10)**-18)))
        prev = cur
    return np.array(out)

def zero_model(gammas, nmax):
    n = np.arange(1, nmax+1, dtype=float)
    ph = 2*np.arctan(1.0/(2*np.asarray(gammas, float)))
    return (2.0 - 2.0*np.cos(np.outer(n, ph))).sum(axis=1)

def amp_curve(Y, nmax, ratio=2.0, npts=260):
    grid = np.unique(np.round(np.exp(np.linspace(math.log(10), math.log(nmax/ratio),
                                                 npts))).astype(int))
    ns, As = [], []
    for n0 in grid:
        n1 = int(n0*ratio)
        if n1 > nmax or n1-n0 < 8: continue
        nv = np.arange(n0, n1+1, dtype=float)
        Yd = detrend(nv, Y[n0-1:n1])
        ns.append(n0); As.append(Yd.std()/(0.5*(n0+n1))**0.25)
    return np.array(ns, float), np.array(As)

def n_half(ns, As, frac, plateau_from=700):
    pl = np.median(As[ns >= plateau_from]) if (ns >= plateau_from).any() else As[-5:].mean()
    thr = frac*pl
    for i in range(len(ns)):
        if As[i] >= thr and np.all(As[i:] >= 0.55*thr):
            return ns[i], pl
    return float('nan'), pl

def matched(Y, omega, V=8.0, step=0.25, nmax=2500, vstart=5.0):
    n = np.arange(1, len(Y)+1, dtype=float); v = np.sqrt(n); g = Y/n**0.25
    out = []; v0 = max(vstart - V/2, 0.0)
    while v0 + V <= math.sqrt(nmax):
        k = (v >= v0) & (v <= v0+V)
        if k.sum() > 30:
            vv = v[k]; gg = g[k]
            w = 0.5 - 0.5*np.cos(2*math.pi*(vv-v0)/V)
            A = 2*np.sum(w*gg*np.exp(-1j*omega*vv)*np.gradient(vv))/(V*0.5)
            out.append((v0+V/2, abs(A), np.angle(A)))
        v0 += step
    return np.array(out)

if __name__ == "__main__":
    t0 = time.time(); P(__doc__); P("="*104)
    NMAX = 2500
    names = ['zeta'] + list(CHARS)
    g1 = {'zeta': 14.134725141734693, 'chi_-3': 8.039737155681467,
          'chi_5': 6.648453344727715, 'chi_8': 4.899973997007036}
    m1 = {'zeta': 2, 'chi_-3': 2, 'chi_5': 2, 'chi_8': 3}
    chival = {'zeta': 1, 'chi_-3': CHARS['chi_-3'][2](2), 'chi_5': CHARS['chi_5'][2](2),
              'chi_8': CHARS['chi_8'][2](3)}
    Ys = {'zeta': np.load(os.path.join(HERE, 'att030_Yzeta_r997.npy'))[:NMAX]}
    Os = {'zeta': line_prediction_zeta(NMAX, 32)}
    for nm, (q, a, chi) in CHARS.items():
        Ys[nm] = np.load(os.path.join(HERE, f'att030_Y_{nm}.npy'))[:NMAX]
        Os[nm] = chi_line_prediction(NMAX, 32, q, chi)

    P("A. EXPONENT of the amplitude turn-on in gamma_1")
    P(f"  {'spec':>8}{'gamma_1':>9}{'plateau':>9}" +
      "".join(f"{'n_h(f=%.1f)'%f:>13}" for f in (0.3, 0.5, 0.7)))
    NH = {}
    for nm in names:
        ns, As = amp_curve(Ys[nm], NMAX, 2.0)
        row = f"  {nm:>8}{g1[nm]:>9.4f}"
        vals = []
        for f in (0.3, 0.5, 0.7):
            nh, pl = n_half(ns, As, f)
            vals.append(nh)
        row += f"{pl:>9.4f}" + "".join(f"{v:>13.0f}" for v in vals)
        NH[nm] = vals; P(row)
    P("\n  log-log regression  log n_half = p log gamma_1 + c   (4 specimens)")
    x = np.log([g1[nm] for nm in names])
    for j, f in enumerate((0.3, 0.5, 0.7)):
        y = np.log([NH[nm][j] for nm in names])
        p_, c_ = np.polyfit(x, y, 1)
        pr = np.corrcoef(x, y)[0, 1]
        sp2 = max(NH[nm][j]/g1[nm]**2 for nm in names)/min(NH[nm][j]/g1[nm]**2 for nm in names)
        sp1 = max(NH[nm][j]/g1[nm] for nm in names)/min(NH[nm][j]/g1[nm] for nm in names)
        sp0 = max(NH[nm][j] for nm in names)/min(NH[nm][j] for nm in names)
        P(f"    f={f}:  p = {p_:+.3f}   r = {pr:+.4f}   |  spread of n_h/gamma_1^2 = {sp2:.2f}x"
          f"   n_h/gamma_1 = {sp1:.2f}x   n_h = {sp0:.2f}x")
    P("\n  same, window ratio 1.5 and 3.0 (robustness of the exponent to the window):")
    for ratio in (1.5, 3.0):
        vals = {}
        for nm in names:
            ns, As = amp_curve(Ys[nm], NMAX, ratio)
            vals[nm] = n_half(ns, As, 0.5)[0]
        y = np.log([vals[nm] for nm in names]); p_, _ = np.polyfit(x, y, 1)
        P(f"    ratio {ratio}:  n_half = " + "  ".join(f"{nm}={vals[nm]:.0f}" for nm in names)
          + f"    p = {p_:+.3f}")

    P("\n" + "="*104)
    P("B. IDENTIFICATION: the first K zeros, ZERO fitted parameters")
    Z = {'zeta': np.load(os.path.join(HERE, 'att019_zeros_to20k.npy'))[:12]}
    for nm, (q, a, chi) in CHARS.items():
        Z[nm] = zeros_of(q, a, chi, 60.0)[:12]
    for nm in names:
        P(f"  {nm}: first zeros {['%.4f'%g for g in Z[nm][:6]]}   "
          f"period 2*pi*gamma_1 = {2*math.pi*Z[nm][0]:.1f}")
    wins = [(20,40),(40,80),(80,160),(160,320),(320,640)]
    for K in (1, 2, 3, 5, 10):
        P(f"\n  K = {K} lowest zeros -- R^2 of lambda_n^arith against the zero model")
        P(f"  {'window':>13}" + "".join(f"{n:>12}" for n in names) +
          "     [same windows, prime model M=32 in brackets]")
        for lo, hi in wins:
            nv = np.arange(lo, hi+1, dtype=float); row = f"  [{lo:>4},{hi:>4}]"
            extra = ""
            for nm in names:
                ZM = zero_model(Z[nm][:K], NMAX)
                R2, *_ = score(nv, Ys[nm][lo-1:hi], ZM[lo-1:hi])
                R2p, *_ = score(nv, Ys[nm][lo-1:hi], Os[nm][lo-1:hi])
                row += f"{R2:>12.4f}"; extra += f"{R2p:>9.3f}"
            P(row + "   [" + extra + " ]")

    P("\n" + "="*104)
    P("C. matched filter with the CORRECT phase (pi/4 if chi(m_1)=+1, -3pi/4 if -1)")
    for nm in names:
        m = m1[nm]; om = 2*math.sqrt(math.log(m))
        a_pred = math.log(m)/(math.sqrt(math.pi)*math.sqrt(m)*math.log(m)**0.75)
        target = math.pi/4 if chival[nm] > 0 else math.pi/4 - math.pi
        M = matched(Ys[nm], om, 8.0, 0.5, NMAX, vstart=5.0)
        hit = None
        for v0, aa, ph in M:
            d = abs(((ph - target + math.pi) % (2*math.pi)) - math.pi)
            if aa/a_pred >= 0.5 and d <= 0.5: hit = v0; break
        P(f"  {nm:>8} m_1={m} chi={chival[nm]:+d} target arg={target:+.4f} "
          f"a_pred={a_pred:.4f}: turn-on sqrt(n)={hit}  n={hit*hit if hit else None}   "
          f"(gamma_1^2 log m_1 = {g1[nm]**2*math.log(m):.0f}, 2 pi gamma_1 = "
          f"{2*math.pi*g1[nm]:.0f})")
        s = "     "
        for v0, aa, ph in M[:9]:
            d = abs(((ph - target + math.pi) % (2*math.pi)) - math.pi)
            s += f"[n={v0*v0:.0f} r={aa/a_pred:.2f} dphi={d:.2f}] "
        P(s)
    P(f"\n[{time.time()-t0:.0f}s] stage 4 done")
