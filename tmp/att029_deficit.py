"""ATTEMPT 029 -- can the gap between two Landau sums READ OFF-LINE CONTENT?

PAIRING.  house = the adaptive (Landau-variable) instrument of attempt 026, calibrated on zeta
to median obs/pred 1.0003 with phase +-1.000 pi, plus the Speiser/argument-principle census.
classical = Landau (1911) / Gonek (1993) in its FULL form  sum_rho x^rho, and the argument
principle.  MECHANISM: the instrument is blind to beta by construction; the SIZE of what it
misses is the measurement.

================== DC FIRST: the deficit in closed form, before any estimate ==================
Landau, FULL and unconditional:      sum_{rho: gamma in (T1,T2]} n^rho = -(W/2pi) Lambda_f(n) + E.
Ordinate-only instrument:            a_ord(n) := (2pi/W) sum_gamma n^{i gamma}.
Beta-weighted:                       a_bet(n) := (2pi/W) sum_rho n^{beta-1/2} n^{i gamma}
                                              = n^{-1/2}(2pi/W) sum_rho n^rho = -Lambda_f(n)/sqrt n.
DEFICIT      Delta(n) := a_ord(n) / (-Lambda_f(n)/sqrt n)  -  1
EXACT        Delta(n)  =  (2pi/W) sum_rho (1 - n^{beta_rho - 1/2}) n^{i gamma_rho} / (-Lambda_f(n)/sqrt n)
so Delta is EXACTLY a weighted census of off-line mass.  Now evaluate the common mode.

FACT 1 (the functional equation kills the first order).  A self-dual FE with real coefficients
pairs rho <-> 1-rho, so off-line zeros occur AT THE SAME ORDINATE in pairs beta = 1/2 +- d.
Summing the weight over such a pair:
        (1 - n^{+d}) + (1 - n^{-d})  =  2 - 2 cosh(d log n)  =  -(d log n)^2 - (d log n)^4/12 - ...
THE LINEAR TERM CANCELS IDENTICALLY.  For any function with a self-dual FE the ordinate-only
Landau deficit is SECOND ORDER in the off-line displacement.

FACT 2 (no FE pairing => first order survives).  For a zero set with no rho<->1-rho symmetry
(zeta-prime), 1 - n^{d} = -d log n + O(d^2): first order, hence O(1/d) times more sensitive.

FACT 3 (missing zeros => ZEROTH order).  If a fraction f of zeros is simply OMITTED from the
ordinate sum -- which is exactly what a critical-line sign-change census does to off-line zeros
-- then E[a_ord] = (1-f) a_bet and  Delta = -f, with NO d-suppression at all.

So the three regimes are  O(1) : O(d) : O(d^2)  and they are pre-registered as H-C : H-B : H-A.

======================== PRE-REGISTERED NULLS (written before running) ========================
NULL-0 (the campaign's stated null).  Delta does not track off-line content: either zeta shows
    a Delta as large as DH's, or DH's Delta is at zeta's level, or the beta-weighted version
    fails to restore the prediction.  Then the deficit carries no location information.
NULL-1 (instrument).  zeta, 22491 zeros, W = 19985: median |Delta| > 0.01.  -> instrument broken.
NULL-2 (thinning positive control).  Deleting a uniformly random fraction f of zeta's zeros does
    NOT give Delta = -f within the measured scatter.  -> Fact 3 is wrong.
NULL-3 (zeta-prime positive control).  The beta-weighted sum does NOT restore the prediction
    (median obs/pred < 0.5) while the ordinate-only sum sits near it.  -> the control fails by
    cancellation rather than by missing structure, and nothing is learned.
NULL-4 (DH).  The DH on-line-census deficit Delta_online is NOT -f_off = -0.1065 +- 3 sigma.
NULL-5 (DH, the real question).  Delta_all (off-line zeros restored to the ordinate sum) is as
    large as Delta_online, i.e. Fact 1's quadratic suppression does not happen.

=========================== VALIDITY CRITERIA, computed BEFORE running ========================
V1  Gonek error.  |E| = O(sqrt n log n loglog n) absolutely, so the RELATIVE error on a(n) is
        r(n,W) = 2pi C sqrt n log n loglog n * sqrt n /(W Lambda(n)) ~ 2pi C n loglog n / W.
    Require r < 0.1 => n_max ~ W/(60 loglog n).  Printed per specimen before any measurement.
V2  Detection threshold.  With measured scatter sigma(Delta), a fraction f of MISSING zeros is
    seen at 3 sigma iff f >= 3 sigma (Fact 3).  For FE-paired off-line zeros at displacement d
    (Fact 1) the incoherent prediction is
        |Delta| ~ (4 pi/W) (cosh(d log n) - 1) sqrt(f N/2) sqrt n / Lambda(n),
    which is compared against 3 sigma to give f_min(d,n).  Both printed as numbers.

RESTATEMENT CHECK (rule 2).  Unfolding Delta: it is the log-n Fourier mode of the difference
between the ordinate-counting measure and the beta-weighted measure.  Classically that
difference is the off-line correction term in Littlewood's lemma / Selberg's formula for S(t).
So Delta is NOT a new object; it is that correction read mode by mode.  Claimed novelty: none.
The deliverable is the SENSITIVITY, i.e. Facts 1-3 with numbers attached.
"""
import numpy as np, math, sys, os
from math import log, sqrt, pi, cosh

def P(*a): print(*a); sys.stdout.flush()
TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'

def vonm(n):
    m = n; p = 2
    while p*p <= m:
        if m % p == 0:
            while m % p == 0: m //= p
            return log(p) if m == 1 else 0.0
        p += 1
    return log(m) if m > 1 else 0.0

PP = [n for n in range(2, 2000) if vonm(n) > 0]

def a_of(gam, n, W, w=None):
    """(2pi/W) sum_gamma w n^{i gamma}."""
    e = np.exp(1j*gam*log(n))
    if w is not None: e = e*w
    return e.sum()/(W/(2*pi))

def rel_err_bound(n, W):
    """V1: relative Gonek error, C = 1."""
    return 2*pi*sqrt(n)*log(n)*log(log(n)+1.0)*sqrt(n)/(W*vonm(n)) if vonm(n) > 0 else float('nan')

# ============================================================ STAGE 1: zeta calibration
def stage1():
    P("="*100)
    P("STAGE 1 -- zeta calibration.  0% off-line.  Delta must be ~0 and its SCATTER is the")
    P("           denominator of every sensitivity statement below.")
    g = np.load(TMP+'att019_zeros_to20k.npy')
    W = g[-1]-g[0]; N = len(g)
    P(f"  {N} zeros, gamma in [{g[0]:.2f},{g[-1]:.2f}], W = {W:.1f}")
    P(f"  V1: n_max with relative Gonek error < 0.1 (C=1):")
    for n in (2,3,5,11,31,101,211,401):
        if vonm(n) > 0:
            P(f"      n={n:>4}  r(n,W) = {rel_err_bound(n,W):.4f}")
    NS = [n for n in PP if rel_err_bound(n, W) < 0.10]
    P(f"  -> admissible n (r<0.10): {NS[0]}..{NS[-1]}, {len(NS)} values")
    D = []
    for n in NS:
        a = a_of(g, n, W); pred = -vonm(n)/sqrt(n)
        D.append(a.real/pred - 1)
    D = np.array(D)
    P(f"  Delta(n) over admissible n: median {np.median(D):+.5f}  mean {D.mean():+.5f}  "
      f"std {D.std():.5f}  max|.| {np.abs(D).max():.5f}")
    P(f"  NULL-1 (median |Delta| > 0.01): median|Delta| = {np.median(np.abs(D)):.5f}  "
      f"-> {'NULL HOLDS (broken)' if np.median(np.abs(D))>0.01 else 'null refuted, instrument sound'}")
    # scatter vs W, per n
    P("\n  scatter of Delta vs window width (sub-windows of the same set):")
    P(f"  {'window':>16}{'#zeros':>8}{'W':>8}{'#n adm':>8}{'median':>10}{'sigma':>10}{'3sigma':>9}")
    SIG = {}
    for lo, hi in ((14,500),(14,1000),(14,2500),(14,5000),(14,10000),(14,20000)):
        sub = g[(g>=lo)&(g<=hi)]
        if len(sub) < 50: continue
        Ws = sub[-1]-sub[0]
        ns = [n for n in PP if rel_err_bound(n, Ws) < 0.10]
        if len(ns) < 4: continue
        d = np.array([ (a_of(sub,n,Ws).real)/(-vonm(n)/sqrt(n)) - 1 for n in ns])
        SIG[Ws] = d.std()
        P(f"  {f'[{lo},{hi}]':>16}{len(sub):>8}{Ws:>8.0f}{len(ns):>8}{np.median(d):>10.4f}"
          f"{d.std():>10.4f}{3*d.std():>9.4f}")
    return g, W, NS, D, SIG

# ============================================================ STAGE 2: thinning control
def stage2(g, W, NS):
    P("\n"+"="*100)
    P("STAGE 2 -- POSITIVE CONTROL for Fact 3.  Delete a uniformly random fraction f of zeta's")
    P("           zeros (fails by MISSING STRUCTURE -- fewer zeros -- never by cancellation).")
    P("           PREDICTION: Delta = -f exactly, at ZEROTH order in any displacement.")
    rng = np.random.default_rng(29)
    P(f"  {'f':>7}{'pred Delta':>12}{'obs median':>12}{'obs mean':>11}{'sigma':>9}{'obs/pred':>10}")
    rows = []
    for f in (0.0, 0.02, 0.05, 0.1065, 0.20, 0.40):
        meds = []
        for trial in range(8):
            keep = rng.random(len(g)) >= f
            sub = g[keep]
            d = np.array([(a_of(sub,n,W).real)/(-vonm(n)/sqrt(n)) - 1 for n in NS])
            meds.append(np.median(d))
        meds = np.array(meds)
        r = meds.mean()/(-f) if f > 0 else float('nan')
        rows.append((f, meds.mean(), meds.std()))
        P(f"  {f:>7.4f}{-f:>12.4f}{np.median(meds):>12.4f}{meds.mean():>11.4f}{meds.std():>9.4f}{r:>10.4f}")
    P("  NULL-2 refuted iff obs/pred ~ 1.00 for every f > 0.")
    return rows

# ============================================================ STAGE 3: zeta-prime
def stage3():
    P("\n"+"="*100)
    P("STAGE 3 -- zeta-prime.  ~100% off-line, NO rho<->1-rho pairing (Fact 2: FIRST order).")
    P("           This is the positive control for the beta-weighting: ordinate-only must FAIL")
    P("           BY MISSING THE BETAs, and supplying them must RESTORE the prediction.")
    sys.path.insert(0, TMP)
    from att014_afe import zprime_coeffs
    C = zprime_coeffs(2.6)
    for tag, fn in (('1e5','att014_zpz_1e+05.npy'), ('1e6','att014_zpz_1e+06.npy'),
                    ('1e7','att014_zpz_1e+07.npy')):
        r = np.load(TMP+fn)
        gam = r.imag; bet = r.real
        W = gam.max()-gam.min(); Tc = (gam.max()+gam.min())/2
        # GATE: density must be (1/2pi) log(T/4pi), not log(T/2pi)
        n_pred4 = W/(2*pi)*log(Tc/(4*pi)); n_pred2 = W/(2*pi)*log(Tc/(2*pi))
        P(f"\n  T={tag}: {len(r)} zeros, W={W:.1f}")
        P(f"    GATE density: found {len(r)}, log(T/4pi) count {n_pred4:.0f} "
          f"(ratio {len(r)/n_pred4:.4f}), log(T/2pi) count {n_pred2:.0f} (ratio {len(r)/n_pred2:.4f})")
        P(f"    beta-1/2: median {np.median(bet-0.5):.5f} mean {(bet-0.5).mean():.5f} "
          f"max {(bet-0.5).max():.4f}  [all > 0 => no FE pairing]")
        items = sorted(((float(k), v, k) for k, v in C.items() if 0.3 < log(float(k)) < 2.0),
                       key=lambda z: z[0])
        P(f"    {'r':>10}{'lam':>8}{'c_r':>10}{'pred':>10}{'a_ord':>11}{'ord/pred':>10}"
          f"{'a_bet':>11}{'bet/pred':>10}")
        ro, rb = [], []
        for x, c, k in items:
            if abs(c) < 0.05: continue
            pred = -c/sqrt(x)
            ao = a_of(gam, x, W).real
            ab = a_of(gam, x, W, w=x**(bet-0.5)).real
            ro.append(ao/pred); rb.append(ab/pred)
            P(f"    {str(k):>10}{log(x):>8.4f}{c:>10.4f}{pred:>10.4f}{ao:>11.4f}{ao/pred:>10.3f}"
              f"{ab:>11.4f}{ab/pred:>10.3f}")
        ro = np.array(ro); rb = np.array(rb)
        P(f"    -> ordinate-only  median obs/pred {np.median(ro):.4f}  => Delta_ord = {np.median(ro)-1:+.4f}")
        P(f"    -> beta-weighted  median obs/pred {np.median(rb):.4f}  => Delta_bet = {np.median(rb)-1:+.4f}")
        P(f"    NULL-3 refuted iff beta-weighted >> ordinate-only and beta-weighted ~ 1.")

# ============================================================ STAGE 4: DH on-line census deficit
CHI4 = {1: 1.0, 2: 0.0, 3: 0.0, 4: -1.0, 0: 0.0}     # Re chi(n), chi quartic mod 5, chi(2)=i
def lam_eff_dh(n):
    """Lambda(n) Re chi(n).  Derived, not fitted: on the line f = A L_chi + Abar L_chibar is a
    sum of two phasors of equal modulus, so arg f BISECTS -> S_f = (S_chi + S_chibar)/2, i.e.
    the Landau coefficient is (Lambda chi + Lambda chibar)/2 = Lambda(n) Re chi(n).
    No free constant.  Signed: NEGATIVE-real sums at n=1 mod 5, POSITIVE at n=4 mod 5, zero else."""
    return vonm(n)*CHI4[n % 5]

def stage4():
    P("\n"+"="*100)
    P("STAGE 4 -- Davenport-Heilbronn, ON-LINE census only (Fact 3 regime).")
    P("           prime side Lambda_eff(n) = Lambda(n) Re chi(n) -- derived by the bisector")
    P("           argument above, NO free constant, and SIGNED (+ at n=4 mod 5).")
    for tag, fn, U in (('1e5 W=1800','att011_z_DH_1e+05_1800.npy', 3234.7),
                       ('1e6 W=3000','att011_z_DH_1e+06_3000.npy', 6485.4)):
        g = np.load(TMP+fn); W = g[-1]-g[0]; N = len(g)
        f_off = 1 - N/U
        P(f"\n  DH {tag}: {N} on-line zeros in [{g[0]:.1f},{g[-1]:.1f}], W={W:.1f}")
        P(f"    census: expected total {U:.1f}, found on-line {N} -> f_off = {f_off:.4f}")
        NS = [n for n in PP if lam_eff_dh(n) != 0 and rel_err_bound(n, W) < 0.10]
        NZ = [n for n in PP if lam_eff_dh(n) == 0 and vonm(n) > 0 and rel_err_bound(n, W) < 0.10]
        P(f"    admissible n (r<0.10): live {NS}  dead {NZ}")
        P(f"    {'n':>5}{'n%5':>5}{'Lam_eff':>10}{'pred':>10}{'Re a':>10}{'|Im a|':>9}"
          f"{'obs/pred':>10}{'phase/pi':>10}")
        rs = []
        for n in NS:
            a = a_of(g, n, W); pred = -lam_eff_dh(n)/sqrt(n)
            rs.append(a.real/pred)
            ph = math.atan2(a.imag, a.real)/pi
            P(f"    {n:>5}{n%5:>5}{lam_eff_dh(n):>10.4f}{pred:>10.4f}{a.real:>10.4f}"
              f"{abs(a.imag):>9.4f}{a.real/pred:>10.3f}{ph:>10.3f}")
        rs = np.array(rs)
        P(f"    -> median obs/pred {np.median(rs):.4f}  IQR {np.percentile(rs,25):.4f}-"
          f"{np.percentile(rs,75):.4f}  => Delta_online = {np.median(rs)-1:+.4f}")
        P(f"    -> PREDICTED by Fact 3: Delta = -f_off = {-f_off:+.4f}")
        LF = np.load(TMP+'att011_lamfull_DH.npy')
        P(f"    dead lines under Lambda_eff (n = 2,3 mod 5) -- compared against BOTH candidate")
        P(f"    prime sides: Lambda_eff = 0 (bisector law) and the true Lambda_f of -f'/f.")
        P(f"    {'n':>5}{'n%5':>5}{'Lam_f':>10}{'pred_f':>10}{'Re a':>10}{'|Im a|':>9}{'a/pred_f':>10}")
        for n in NZ:
            a = a_of(g, n, W); pf = -LF[n]/sqrt(n)
            P(f"    {n:>5}{n%5:>5}{LF[n]:>10.4f}{pf:>10.4f}{a.real:>10.4f}{abs(a.imag):>9.4f}"
              f"{(a.real/pf if pf!=0 else float('nan')):>10.3f}")
        P(f"    NULL-4 refuted iff Delta_online = -f_off within scatter.")

if __name__ == "__main__":
    P(__doc__)
    g, W, NS, D, SIG = stage1()
    stage2(g, W, NS)
    stage3()
    stage4()
    # ---------------- V2: the sensitivity statement, from the measured scatter
    P("\n"+"="*100)
    P("V2 -- SENSITIVITY (test D).  sigma from STAGE 1's scatter at each W.")
    P("  Fact 3 regime (MISSING zeros):  f detectable at 3 sigma iff f >= 3 sigma.")
    for Ws, s in sorted(SIG.items()):
        P(f"    W = {Ws:>7.0f}   sigma = {s:.5f}   3-sigma f_min = {3*s:.5f}")
    P("\n  Fact 1 regime (FE-PAIRED off-line zeros at displacement d, all ordinates used):")
    Wl = 19985.0; Nl = 22491; sl = SIG[max(SIG)]
    P(f"    at W={Wl:.0f}, N={Nl}, sigma={sl:.5f}:  need"
      f"  (4pi/W)(cosh(d log n)-1) sqrt(f N/2) sqrt n/Lambda(n) >= 3 sigma")
    P(f"    {'n':>6}{'d=0.02':>10}{'d=0.05':>10}{'d=0.10':>10}{'d=0.20':>10}{'d=0.50':>10}   (f_min)")
    for n in (2, 11, 31, 101, 211, 401):
        row = []
        for d in (0.02, 0.05, 0.10, 0.20, 0.50):
            k = (4*pi/Wl)*(cosh(d*log(n))-1)*sqrt(Nl/2)*sqrt(n)/vonm(n)
            fm = (3*sl/k)**2 if k > 0 else float('inf')
            row.append(f"{fm:>10.3g}" if fm <= 1 else f"{'>1':>10}")
        P(f"    {n:>6}" + "".join(row))
    P("\n  (f_min > 1 means: even a 100%-off-line spectrum at that displacement is invisible.)")
