"""ATTEMPT 029, stage 5 -- the DECISIVE arm: Davenport-Heilbronn with its OFF-LINE zeros
LOCATED, so that a_ord (ordinates only) and a_beta (beta-weighted) can be compared on the
SAME zero set of an FE-SYMMETRIC specimen with 10.6% off-line content.

WHY THIS IS THE TEST.  Stage 4 measured only the on-line census sum, which is Fact 3 (missing
zeros, ZEROTH order).  Fact 1 -- the claim that a self-dual functional equation makes the
ordinate-only deficit SECOND order in the off-line displacement -- can only be tested with the
off-line ordinates in hand.  And stage 4 turned up an anomaly demanding exactly this data: the
on-line sum has strong COHERENT lines at n = 2, 3 mod 5, where the bisector law Lambda Re chi
predicts zero (a(2) = +0.49/+0.54 across two windows, ~ +Lambda(2)/sqrt 2, empirically tracking
+2 Lambda(n) Im chi(n)/n^{3/2}).  Either DH's prime side is not Lambda Re chi, or those lines
are cancelled by the off-line zeros -- which would be the first coherent arithmetic ever
attributed to off-line zeros here.

PRE-REGISTERED, before running:
G1  CENSUS GATE.  #on-line + 2*#off-line-pairs must equal round(delta theta_f/pi) within the
    Turing slack (|S| <~ 2).  If it does not, the zero set is incomplete and every number below
    is void.  theta_f(t) = (t/2)log(5/pi) + Im log Gamma(3/4 + it/2); density (1/2pi)log(5t/2pi).
G2  PHASE GATE.  Z_f(t) = e^{i theta_f(t)} f(1/2+it) must be real to ~1e-10.
G3  PAIRING GATE.  Every located off-line zero must have a partner at 1 - beta, SAME gamma
    (self-dual FE).  Median |beta + beta' - 1| must be ~0.

NULL-5 (pre-registered).  Delta_all := a_ord_all/a_beta - 1 is as large as Delta_online, i.e.
    the FE's quadratic suppression (Fact 1) does not happen.  Then the ordinate sum's deficit
    is a genuine O(1) location readout and the route is OPEN.
NULL-6 (pre-registered).  a_beta does NOT equal -Lambda_f(n)/sqrt n for the TRUE Lambda_f of
    -f'/f.  Then Landau's theorem is not usable for DH (attempt 011's D2 suspicion), every
    ratio here is against an unknown prime side, and the DH arm is BROKEN, not negative.
NULL-7 (the anomaly).  a_off(n) at n = 2,3 mod 5 is INCOHERENT (|a_off| ~ the sqrt(N_off)
    floor), i.e. the off-line zeros carry no arithmetic of their own.

VALIDITY, computed before running: sigma(a(n)) ~ (2pi/W) sqrt(N_total) is the incoherent floor;
with W = 3000 and N ~ 3400 that is 0.122, so a coherent line must exceed 0.37 to be a 3-sigma
detection.  Printed as a number below.
"""
import numpy as np, math, sys, time, os
from math import log, sqrt, pi, cosh
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att014_dh_winding import dh, XI, AV

def P(*a): print(*a); sys.stdout.flush()
TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'
T0, T1 = 100.0, 3100.0

def vonm(n):
    m = n; p = 2
    while p*p <= m:
        if m % p == 0:
            while m % p == 0: m //= p
            return log(p) if m == 1 else 0.0
        p += 1
    return log(m) if m > 1 else 0.0

# ---------------------------------------------------------------- theta_f and Z_f
from scipy.special import loggamma
def theta_f(t):
    t = np.asarray(t, float)
    return (t/2)*log(5/pi) + np.imag(loggamma(0.75 + 0.5j*t))

def Zf(t, chunk=4000):
    t = np.asarray(t, float); out = np.empty(t.shape, float); ph = np.empty(t.shape, float)
    for i in range(0, len(t), chunk):
        tt = t[i:i+chunk]
        v = dh(0.5+1j*tt)[0]*np.exp(1j*theta_f(tt))
        out[i:i+chunk] = v.real; ph[i:i+chunk] = np.abs(v.imag)/(np.abs(v)+1e-300)
    return out, ph

def newton2d(seeds, iters=45, chunk=1500):
    """Complex Newton.  NB: diverging points are CLAMPED, never set to nan -- a single nan in a
    chunk makes dh()'s term count collapse to 40 (max(40, nan) == 40) and silently destroys the
    whole chunk.  That bug cost the first run of this stage."""
    z = np.array(seeds, complex)
    order = np.argsort(z.imag); z = z[order]
    for i in range(0, len(z), chunk):
        w = z[i:i+chunk]
        for _ in range(iters):
            f, fp = dh(w)
            step = np.where(np.abs(fp) > 1e-300, f/np.where(np.abs(fp) > 1e-300, fp, 1.0), 0.0)
            big = np.abs(step) > 0.5
            step = np.where(big, 0.5*step/np.where(big, np.abs(step), 1.0), step)
            w = w - step
            w = np.clip(w.real, 0.05, 4.0) + 1j*np.clip(w.imag, T0-5, T1+5)
        z[i:i+chunk] = w
    return z

def dedupe(z, tol=1e-6):
    z = z[np.isfinite(z)]
    if len(z) == 0: return z
    key = np.round(z.real/tol)*1e7 + np.round(z.imag/tol)
    _, idx = np.unique(key, return_index=True)
    return z[np.sort(idx)]

def lam_f_dh(N=200):
    a = np.zeros(N+1); ch = {1: 1.0, 2: XI, 3: -XI, 4: -1.0, 0: 0.0}
    for n in range(1, N+1): a[n] = ch[n % 5]
    L = np.zeros(N+1)
    for n in range(2, N+1):
        s = a[n]*log(n)
        for d in range(1, n):
            if n % d == 0 and d > 1: s -= L[d]*a[n//d]
        L[n] = s
    return L

CHI4RE = {1: 1.0, 2: 0.0, 3: 0.0, 4: -1.0, 0: 0.0}
CHI4IM = {1: 0.0, 2: 1.0, 3: -1.0, 4: 0.0, 0: 0.0}

if __name__ == "__main__":
    P(__doc__)
    W = T1-T0
    # ------------------------------------------------------------ G2 phase gate
    tt = np.linspace(T0, T1, 9)
    z, rel = Zf(tt)
    P(f"G2 PHASE GATE  max |Im(e^{{i theta}} f)|/|f| over 9 probes = {rel.max():.3e}   (must be ~0)")
    # ------------------------------------------------------------ on-line zeros
    t_ = time.time()
    NG = int((T1-T0)/0.02)
    grid = np.linspace(T0, T1, NG+1)
    Zg, _ = Zf(grid)
    sgn = np.sign(Zg); idx = np.where(sgn[:-1]*sgn[1:] < 0)[0]
    lo = grid[idx].copy(); hi = grid[idx+1].copy(); flo = Zg[idx].copy()
    for _ in range(52):
        mid = 0.5*(lo+hi); fm, _ = Zf(mid)
        b = (fm*flo > 0); lo = np.where(b, mid, lo); hi = np.where(b, mid, hi)
        flo = np.where(b, fm, flo)
    on = 0.5*(lo+hi)
    P(f"  on-line zeros by sign change (h=0.02): {len(on)}   [{time.time()-t_:.0f}s]")
    # ------------------------------------------------------------ off-line zeros
    # TARGETED SEEDS: between consecutive on-line zeros the expected count is
    # delta theta_f/pi; where that is ~3 instead of ~1 an off-line PAIR sits in the gap.
    t_ = time.time()
    ex = np.diff(theta_f(on))/pi
    gapidx = np.where(ex > 1.6)[0]
    mid = 0.5*(on[gapidx]+on[gapidx+1])
    P(f"  gaps between on-line zeros with expected count > 1.6: {len(gapidx)}"
      f"  (total excess {np.round((ex[gapidx]-1).sum(),1)})")
    tg = np.concatenate([mid + off for off in (-0.25, -0.08, 0.0, 0.08, 0.25)])
    tgrid = np.arange(T0+0.07, T1, 0.30)
    seeds = np.concatenate([(0.5+d) + 1j*tg for d in (0.03, 0.10, 0.22, 0.40, 0.70)] +
                           [(0.5+d) + 1j*tgrid for d in (0.08, 0.20, 0.45, 0.80)])
    P(f"  2D Newton from {len(seeds)} seeds ...")
    r = dedupe(newton2d(seeds))
    r = r[(r.imag > T0) & (r.imag < T1) & (np.abs(r.real-0.5) > 2e-5)]
    fv, fpv = dh(r)
    r = r[np.abs(fv) < 1e-7*np.maximum(np.abs(fpv), 1e-3)]
    r = dedupe(r, 1e-6)
    P(f"  off-line zeros located: {len(r)}   [{time.time()-t_:.0f}s]")
    # ------------------------------------------------------------ G3 pairing gate
    right = np.sort_complex(r[r.real > 0.5]); left = r[r.real < 0.5]
    P(f"G3 PAIRING GATE  #(beta>1/2) = {len(right)}   #(beta<1/2) = {len(left)}   (must be equal)")
    if len(right) and len(left):
        li = np.array(sorted(left, key=lambda z: z.imag))
        ri = np.array(sorted(right, key=lambda z: z.imag))
        m = min(len(li), len(ri))
        P(f"   median |beta_+ + beta_- - 1| = {np.median(np.abs(li[:m].real+ri[:m].real-1)):.2e}"
          f"   median |gamma_+ - gamma_-| = {np.median(np.abs(li[:m].imag-ri[:m].imag)):.2e}")
        P(f"   displacement d = beta-1/2 (right partners): median {np.median(ri.real-0.5):.4f}"
          f"  mean {np.mean(ri.real-0.5):.4f}  max {np.max(ri.real-0.5):.4f}")
    # ------------------------------------------------------------ G1 census gate
    Nth = (theta_f(T1)-theta_f(T0))/pi
    Ntot = len(on) + len(r)
    P(f"G1 CENSUS GATE  delta theta_f/pi = {Nth:.2f}   on-line {len(on)} + off-line {len(r)}"
      f" = {Ntot}   deficit {Nth-Ntot:+.2f}   (Turing slack |S| <~ 2)")
    f_off = len(r)/Nth
    P(f"   off-line FRACTION f_off = {f_off:.4f}")
    np.save(TMP+'att029_dh_on.npy', on); np.save(TMP+'att029_dh_off.npy', r)

    # ------------------------------------------------------------ the measurement
    gam_on = on; gam_off = r.imag; d_off = r.real - 0.5
    Ntotal = len(on)+len(r)
    floor = (2*pi/W)*sqrt(Ntotal)
    P(f"\nVALIDITY  incoherent floor sigma(a) = (2pi/W) sqrt(N) = {floor:.4f};"
      f"  3-sigma coherent line must exceed {3*floor:.4f}")
    LF = lam_f_dh(200)
    P(f"\n{'n':>4}{'n%5':>4}{'Lam_f':>9}{'pred_f':>9} | {'a_on':>8}{'a_off':>8}{'a_all':>8}"
      f"{'a_beta':>9} | {'all/pf':>8}{'bet/pf':>8} | {'LamRe':>8}{'pred_e':>8}{'on/pe':>7}")
    rows = []
    for n in range(2, 60):
        if vonm(n) == 0 and n not in (6,10,14,15,21,22,26,33,34,35,38,39,46,51,55,57,58): continue
        ln = log(n)
        e_on = np.exp(1j*gam_on*ln).sum()
        e_of = np.exp(1j*gam_off*ln).sum()                       # each member of the pair once
        e_bw = (np.exp(1j*gam_off*ln)*n**d_off).sum()
        k = (2*pi/W)
        a_on = k*e_on; a_off = k*e_of; a_all = a_on+a_off; a_bet = a_on + k*e_bw
        pf = -LF[n]/sqrt(n)
        le = vonm(n)*CHI4RE[n % 5]; pe = -le/sqrt(n)
        rows.append((n, a_on, a_off, a_all, a_bet, pf, pe))
        P(f"{n:>4}{n%5:>4}{LF[n]:>9.4f}{pf:>9.4f} | {a_on.real:>8.4f}{a_off.real:>8.4f}"
          f"{a_all.real:>8.4f}{a_bet.real:>9.4f} | "
          f"{(a_all.real/pf if pf else float('nan')):>8.3f}{(a_bet.real/pf if pf else float('nan')):>8.3f} | "
          f"{le:>8.4f}{pe:>8.4f}{(a_on.real/pe if pe else float('nan')):>7.3f}")

    # ------------------------------------------------------------ verdicts
    liv = [x for x in rows if x[6] != 0 and vonm(x[0]) > 0]
    dead = [x for x in rows if x[6] == 0 and vonm(x[0]) > 0 and x[0] % 5 in (2,3)]
    r_on = np.array([x[1].real/x[6] for x in liv])
    r_all = np.array([x[3].real/x[6] for x in liv])
    r_bet = np.array([x[4].real/x[6] for x in liv])
    P(f"\nAgainst the bisector prime side Lambda(n)Re chi(n)  (n = 1,4 mod 5, {len(liv)} lines):")
    P(f"   a_on  median {np.median(r_on):.4f}   Delta_online = {np.median(r_on)-1:+.4f}"
      f"   [Fact 3 predicts {-f_off:+.4f}]")
    P(f"   a_all median {np.median(r_all):.4f}   Delta_all    = {np.median(r_all)-1:+.4f}")
    P(f"   a_bet median {np.median(r_bet):.4f}   Delta_beta   = {np.median(r_bet)-1:+.4f}")
    ao = np.array([abs(x[2]) for x in dead]); an = np.array([abs(x[1]) for x in dead])
    aa = np.array([abs(x[3]) for x in dead])
    P(f"\nNULL-7, the n = 2,3 mod 5 anomaly ({[x[0] for x in dead]}):")
    P(f"   |a_on|  = {np.round(an,4)}")
    P(f"   |a_off| = {np.round(ao,4)}   (incoherent floor for {len(r)} off-line zeros: "
      f"{(2*pi/W)*sqrt(len(r)):.4f})")
    P(f"   |a_all| = {np.round(aa,4)}   -> cancellation iff |a_all| << |a_on|")
    r_bf = np.array([x[4].real/x[5] for x in rows if x[5] != 0])
    r_af = np.array([x[3].real/x[5] for x in rows if x[5] != 0])
    P(f"\nNULL-6, Landau with the TRUE Lambda_f: a_beta/pred_f median {np.median(r_bf):.4f}"
      f"  IQR {np.percentile(r_bf,25):.3f}-{np.percentile(r_bf,75):.3f}   (must be 1.00 if"
      f" Landau is usable for DH)")
    P(f"          a_all /pred_f median {np.median(r_af):.4f}")
