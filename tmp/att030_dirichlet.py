"""ATTEMPT 030, stage 2 -- THE DECISIVE TEST.  Does the attempt-015 threshold move with gamma_1?

Attempt 015 found the dyadic R^2 of  lambda_n^arith  against the truncated Bombieri-Lagarias
prime-Laguerre sum crossing from -3.78 to +0.9501 between n=160 and n=320, and named the
crossing  n* = gamma_1^2 log 2 = 199.79 * 0.69315 = 138.5.

TWO MECHANISMS PREDICT A NUMBER NEAR 138 ON ZETA AND THEY DISAGREE OFF ZETA.

 (R) RESONANCE.  Szego 8.22.1:  e^{-x/2} L_{n-1}^{(1)}(x) ~ n^{1/4} x^{-3/4}
     cos(2 sqrt(nx) - 3pi/4)/sqrt(pi).  Against the prime fluctuation, whose density carries
     the frequencies gamma, stationary phase gives  d/dx[2 sqrt(nx)] = gamma  i.e.
                                n = gamma^2 * log m .
     Equivalently, in n:  the zero gamma oscillates in n with local period 2 pi gamma while the
     m-tone has local period 2 pi sqrt(n / log m); they lock at n = gamma^2 log m.
     PREDICTION: the smallest prime power m_1 with chi(m_1) != 0 switches on at
                                n* = gamma_1(chi)^2 log m_1 ,
     which MOVES between L-functions because gamma_1 does.

 (W) WINDOW/DETREND ABSORPTION.  The m-tone completes
     c = (sqrt(ratio)-1) sqrt(n) * 2 sqrt(log m) / (2 pi)  cycles per window [n, ratio*n];
     a 4-parameter detrend absorbs it while c < ~1.3.  The frequencies 2 sqrt(log m) are
     PROPERTIES OF THE LAGUERRE POLYNOMIAL, identical for every L-function.
     PREDICTION: n* is the SAME for every L-function.

SPECIMENS (real primitive characters; the arithmetic part is
   lambda_n^{arith,chi} = -sum_m Lambda(m) chi(m)/m L_{n-1}^{(1)}(log m), no counterterm since
   sum Lambda(m)chi(m)/m converges):
     zeta         q=1   m_1 = 2
     chi_-3       q=3   odd    m_1 = 2
     chi_5        q=5   even   m_1 = 2
     chi_8        q=8   even   m_1 = 3   (chi_8(2) = 0 -- a second, independent handle)

CONTOUR VALIDITY, computed BEFORE running: the image of a zero beta+i gamma lies in |z|<r iff
   beta^2 + gamma^2 < 1/(1-r^2).  Radius is chosen per specimen so that 1/(1-r^2) < gamma_1^2,
   hence UNCONDITIONAL given only the (finitely verifiable) location of the lowest zeros.

STATED NULL (pre-registered, before the run)
   N2:  n*(chi) does NOT track gamma_1(chi)^2 log m_1 -- specifically, the ratio
        n*(chi) / (gamma_1(chi)^2 log m_1) is NOT constant to within a factor 1.5 across the
        four specimens, and/or n*(chi) is constant across specimens (mechanism W).
   Rejecting N2 requires n*(chi)/(gamma_1^2 log m_1) constant within 1.5x while gamma_1^2 log m_1
   itself spans a factor >= 2.5 across the specimens.
POSITIVE CONTROL that fails by MISSING STRUCTURE: random frequencies with the true amplitudes.
"""
import sys, os, math, time
import numpy as np
from mpmath import mp, mpf, mpc

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from att030_zeta import (mpfft, taylor_coeffs, laguerre1_dot, laguerre0, prime_powers,
                         detrend, score, line_prediction_zeta)
def P(*a):
    print(*a); sys.stdout.flush()

CHARS = {
    'chi_-3': (3, 1, lambda n: 0 if n % 3 == 0 else (1 if n % 3 == 1 else -1)),
    'chi_5':  (5, 0, lambda n: 0 if n % 5 == 0 else (1 if n % 5 in (1, 4) else -1)),
    'chi_8':  (8, 0, lambda n: 0 if n % 2 == 0 else (1 if n % 8 in (1, 7) else -1)),
}

def Lchi(s, q, chi):
    return sum(chi(a)*mp.zeta(s, mpf(a)/q) for a in range(1, q)) * mp.power(q, -s)

def dLchi(s, q, chi):
    S0 = sum(chi(a)*mp.zeta(s, mpf(a)/q) for a in range(1, q))
    S1 = sum(chi(a)*mp.zeta(s, mpf(a)/q, 1) for a in range(1, q))
    return mp.power(q, -s)*(S1 - mp.log(q)*S0)

def first_zero(q, a, chi):
    """lowest positive ordinate of L(s,chi) on the critical line, by sign changes of
       Z_chi(t) = e^{i theta}(L(1/2+it)),  theta = (t/2)log(q/pi) + arg Gamma((1/2+a+it)/2)."""
    mp.dps = 30
    def Z(t):
        s = mpc(mpf(1)/2, t)
        th = (t/2)*mp.log(mpf(q)/mp.pi) + mp.im(mp.loggamma((mpf(1)/2+a+mpc(0, t))/2))
        return mp.re(mp.expj(th)*Lchi(s, q, chi))
    ts = np.arange(0.05, 20.0, 0.05)
    prev = Z(mpf(0.05)); out = []
    for t in ts[1:]:
        cur = Z(mpf(t))
        if prev*cur < 0:
            out.append(float(mp.findroot(Z, (mpf(t-0.05), mpf(t)), solver='bisect',
                                         tol=mpf(10)**-20)))
            if len(out) >= 3: break
        prev = cur
    return out

def h_arith_chi(z, q, chi):
    s = 1/(1-z)
    return (dLchi(s, q, chi)/Lchi(s, q, chi)) * s**2

def chi_line_prediction(nmax, M, q, chi):
    ms, lam = prime_powers(M)
    w = np.array([chi(int(m)) for m in ms], float)
    k = w != 0
    return -laguerre1_dot(np.log(ms[k]), (lam[k]*w[k])/ms[k], nmax)

def crossing(Y, O, nmax, ratio=2.0, basis='orig', lo=8, hi=None, thresh=0.5):
    hi = hi or int(nmax/ratio)
    grid = np.unique(np.round(np.exp(np.linspace(math.log(lo), math.log(hi), 220))).astype(int))
    for n0 in grid:
        n1 = int(n0*ratio)
        if n1 > nmax or n1-n0 < 8: continue
        ns = np.arange(n0, n1+1, dtype=float)
        R2, *_ = score(ns, Y[n0-1:n1], O[n0-1:n1], basis)
        if R2 >= thresh:
            ok = True
            for mfac in (1.3, 1.8, 2.6):
                n2 = int(n0*mfac); n3 = int(n2*ratio)
                if n3 > nmax: continue
                ns2 = np.arange(n2, n3+1, dtype=float)
                R22, *_ = score(ns2, Y[n2-1:n3], O[n2-1:n3], basis)
                if R22 < thresh: ok = False; break
            if ok: return n0
    return None

if __name__ == "__main__":
    t0 = time.time(); P(__doc__); P("="*104)
    NMAX = 2500

    P("first zeros (own scan + bisection, dps 30):")
    g1 = {'zeta': 14.134725141734693}
    for nm, (q, a, chi) in CHARS.items():
        zz = first_zero(q, a, chi)
        g1[nm] = zz[0]
        P(f"   {nm:>7}  q={q} a={a}   first three ordinates {['%.6f'%x for x in zz]}")
    P(f"   zeta                       first ordinate 14.134725")

    # radius per specimen: need 1/(1-r^2) < gamma_1^2
    rad = {}
    for nm in ('zeta',) + tuple(CHARS):
        g = g1[nm]
        rmax = math.sqrt(max(0.0, 1 - 1.0/(g*g)))
        r = math.floor(rmax*1000)/1000 - 0.001
        rad[nm] = r
        P(f"   {nm:>7}: gamma_1 = {g:.6f}  -> unconditional radius r <= {rmax:.5f}, using r = {r}"
          f"   (r^{NMAX} = {r**NMAX:.2e})")

    Ys = {}
    Ys['zeta'] = np.load(os.path.join(HERE, 'att030_Yzeta_r997.npy'))[:NMAX]
    for nm, (q, a, chi) in CHARS.items():
        cache = os.path.join(HERE, f'att030_Y_{nm}.npy')
        if not os.path.exists(cache):
            P(f"\n   contour for {nm}: r={rad[nm]}, N=8192, dps=60 ... [{time.time()-t0:.0f}s]")
            cz = taylor_coeffs(lambda z, q=q, chi=chi: h_arith_chi(z, q, chi),
                               str(rad[nm]), 8192, 70, NMAX)
            np.save(cache, np.array([float(c.real) for c in cz]))
            P(f"      max |Im c| = {float(max(abs(c.imag) for c in cz)):.3e} "
              f"[{time.time()-t0:.0f}s]")
        Ys[nm] = np.load(cache)
        # gate: lambda_1^arith,chi must equal -L'/L(1,chi)  (n=1 coefficient, independent check)
        mp.dps = 40
        ref = float(dLchi(mpf(1), q, chi)/Lchi(mpf(1), q, chi))
        P(f"   {nm}: lambda_1^arith = {Ys[nm][0]:.12f}   direct L'/L(1,chi) = {ref:.12f}   "
          f"diff {abs(Ys[nm][0]-ref):.2e}")

    P("\n" + "="*104)
    P("dyadic R^2, M = 32, basis {1,log n,sqrt n,n}, ZERO free parameters")
    Os = {'zeta': line_prediction_zeta(NMAX, 32)}
    for nm, (q, a, chi) in CHARS.items():
        Os[nm] = chi_line_prediction(NMAX, 32, q, chi)
    wins = [(10,20),(20,40),(40,80),(80,160),(160,320),(320,640),(640,1250),(1250,2500)]
    names = ['zeta'] + list(CHARS)
    P(f"  {'window':>14}" + "".join(f"{n:>13}" for n in names))
    for lo, hi in wins:
        ns = np.arange(lo, hi+1, dtype=float)
        row = f"  [{lo:>4},{hi:>5}]"
        for nm in names:
            R2, *_ = score(ns, Ys[nm][lo-1:hi], Os[nm][lo-1:hi]); row += f"{R2:>13.4f}"
        P(row)

    P("\ndetrended amplitude  rms(Yd)/n^{1/4}  (the amplitude TURN-ON, basis-light)")
    P(f"  {'window':>14}" + "".join(f"{n:>13}" for n in names))
    for lo, hi in wins:
        ns = np.arange(lo, hi+1, dtype=float)
        row = f"  [{lo:>4},{hi:>5}]"
        for nm in names:
            _, _, sy, _ = score(ns, Ys[nm][lo-1:hi], Os[nm][lo-1:hi])
            row += f"{sy/(0.5*(lo+hi))**0.25:>13.4f}"
        P(row)

    P("\n" + "="*104)
    P("THE TEST.  crossing point n* (R^2 >= 0.5 and staying), several window ratios and bases")
    m1 = {'zeta': 2, 'chi_-3': 2, 'chi_5': 2, 'chi_8': 3}
    P(f"  {'spec':>8}{'gamma_1':>10}{'m_1':>5}{'pred g1^2 log m1':>18}"
      f"{'n*(r=2,orig)':>14}{'n*(r=3,orig)':>14}{'n*(r=2,p3)':>13}{'n*(r=2,lin)':>13}")
    tab = {}
    for nm in names:
        pred = g1[nm]**2*math.log(m1[nm])
        a1 = crossing(Ys[nm], Os[nm], NMAX, 2.0, 'orig')
        a2 = crossing(Ys[nm], Os[nm], NMAX, 3.0, 'orig')
        a3 = crossing(Ys[nm], Os[nm], NMAX, 2.0, 'p3')
        a4 = crossing(Ys[nm], Os[nm], NMAX, 2.0, 'lin')
        tab[nm] = (pred, a1, a2, a3, a4)
        P(f"  {nm:>8}{g1[nm]:>10.4f}{m1[nm]:>5}{pred:>18.1f}"
          f"{str(a1):>14}{str(a2):>14}{str(a3):>13}{str(a4):>13}")
    P("\n  ratio n*/(gamma_1^2 log m_1)  -- must be CONSTANT within 1.5x to reject N2:")
    for col, lab in ((1,'r=2,orig'), (2,'r=3,orig'), (3,'r=2,p3'), (4,'r=2,lin')):
        vals = [tab[nm][col]/tab[nm][0] if tab[nm][col] else float('nan') for nm in names]
        sp = max(vals)/min(vals) if all(v == v for v in vals) else float('nan')
        P(f"    {lab:>10}: " + "  ".join(f"{nm}={v:.3f}" for nm, v in zip(names, vals))
          + f"    spread = {sp:.2f}x")
    P("\n  same for the rival: n* itself (mechanism W says these are EQUAL across specimens):")
    for col, lab in ((1,'r=2,orig'), (2,'r=3,orig'), (3,'r=2,p3'), (4,'r=2,lin')):
        vals = [tab[nm][col] for nm in names]
        sp = max(vals)/min(vals)
        P(f"    {lab:>10}: " + "  ".join(f"{nm}={v}" for nm, v in zip(names, vals))
          + f"    spread = {sp:.2f}x")

    P("\nPOSITIVE CONTROL: random frequencies, true amplitudes, window [320,640]")
    rng = np.random.default_rng(302)
    for nm in names:
        q = 1 if nm == 'zeta' else CHARS[nm][0]
        chi = (lambda n: 1) if nm == 'zeta' else CHARS[nm][2]
        ms, lam = prime_powers(32)
        w = np.array([chi(int(m)) for m in ms], float); k = w != 0
        amps = (lam[k]*w[k])/ms[k]
        lo, hi = 320, 640; ns = np.arange(lo, hi+1, dtype=float)
        R2t, *_ = score(ns, Ys[nm][lo-1:hi], Os[nm][lo-1:hi])
        cs = []
        for _ in range(100):
            xs = rng.uniform(math.log(2), math.log(32), size=k.sum())
            Oc = -laguerre1_dot(xs, amps, hi)
            a_, *_ = score(ns, Ys[nm][lo-1:hi], Oc[lo-1:hi]); cs.append(a_)
        cs = np.array(cs)
        P(f"  {nm:>8}  TRUE {R2t:+.4f}   control median {np.median(cs):+.4f}  "
          f"99th {np.percentile(cs,99):+.4f}  max {cs.max():+.4f}")
    P(f"\n[{time.time()-t0:.0f}s] stage 2 done")
