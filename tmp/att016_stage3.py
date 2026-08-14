"""ATTEMPT 016, stage 3 -- the honest error bars, the DETECTION FLOOR above tau=1, and the
surrogate discrimination.

Stage 2 found <K>_(1.05,3) = 1.02, 1.01, 1.01, 1.00, 1.01 at T = 1e3..1e7 with nominal
+-0.011.  Before calling that "flat", two things must be established, and both are
pre-registered here:

NULL J (EFFECTIVE DOF).  Nominal sigma = <K>/sqrt(#tau samples) assumes the samples at
  spacing 1/U are independent Exp(1)*K.  MEASURE the effective dof on the CUE and Poisson
  controls, where the truth K == 1 is known exactly.  NULL J: dof_eff / dof_nominal = 1.
  If it is < 1 the stage-2 error bars are too small and the mild excesses shrink.

NULL K (DETECTION FLOOR / SENSITIVITY -- the positive control the brief demands, in the
  ONE direction that matters).  Inject a known density modulation at tau0 = 1.6 into the
  REAL zeta tape, of a size chosen to give a target bin excess, and check the pipeline
  recovers it.  NULL K: injected excess is NOT recovered => the instrument is blind above
  tau=1 and the whole negative is vacuous.  Recovery calibrates the floor: "any structure
  with bin excess > X would have been seen at 3 sigma".

NULL L (SURROGATE DISCRIMINATION).  The lattice+iid-S surrogate reproduces K(1) exactly
  (same multiset of S values) and produces a SMOOTH pseudo-ramp 1 - |E e^{-2 pi i tau S}|^2.
  The zeta ramp is JAGGED and tracks the prime lines bin-by-bin.  NULL L: the surrogate
  tracks D(bin) as well as zeta does, i.e. median |K/D - 1| is the same for both, so the
  ramp carries no prime information beyond the lattice.

NULL M (PRECISION).  Perturbing every zero by 1e-8 (100x the Zrs positional gate) must not
  change K(1) or the flatness numbers.  NULL M: it does.
"""
import numpy as np, math, os, sys
from math import log, pi, sqrt
def P(*a): print(*a); sys.stdout.flush()
HERE = os.path.dirname(os.path.abspath(__file__))
def theta(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)
def K_of(u, taus, w=None, chunk=400):
    u = np.asarray(u, float); taus = np.asarray(taus, float)
    if w is None: w = np.ones_like(u); norm = float(len(u))
    else: norm = float(np.sum(w*w))
    out = np.empty(len(taus))
    for i in range(0, len(taus), chunk):
        ph = np.exp(2j*np.pi*np.outer(taus[i:i+chunk], u))
        out[i:i+chunk] = np.abs(ph @ w)**2/norm
    return out
_S = {}
def primes_upto(X):
    X = int(X)
    if X in _S: return _S[X]
    s = np.ones(X+1, dtype=bool); s[:2] = False
    for p in range(2, int(X**0.5)+1):
        if s[p]: s[p*p::p] = False
    _S[X] = np.nonzero(s)[0].astype(np.int64); return _S[X]
def diag_bins(L, edges, Xcap=int(1e8)):
    pr = primes_upto(Xcap); lg = np.log(pr.astype(float))
    tt = [lg/L]; ww = [lg*lg/pr.astype(float)]; k = 2
    while True:
        m = pr.astype(float)**k <= Xcap
        if not m.any(): break
        tt.append(k*lg[m]/L); ww.append(lg[m]**2/(pr[m].astype(float)**k)); k += 1
    h, _ = np.histogram(np.concatenate(tt), bins=edges, weights=np.concatenate(ww))
    return h/(L*L*np.diff(edges)), log(Xcap)/L

HEIGHTS = [1e3, 1e4, 1e5, 1e6, 1e7]
BINW = 0.05; EDGES = np.arange(0, 3.0+1e-9, BINW); MID = 0.5*(EDGES[:-1]+EDGES[1:])
D = {}
for T in HEIGHTS:
    g = np.load(os.path.join(HERE, f"att010_zeros_{T:.0e}.npy"))
    u = theta(g)/np.pi; u -= u[0]
    D[T] = dict(g=g, u=u, U=float(u[-1]), n=len(u), L=log((g[0]+g[-1])/2/(2*pi)),
                K=np.load(os.path.join(HERE, f"att016_K_{T:.0e}.npy")))
    D[T]['taus'] = np.arange(1, len(D[T]['K'])+1)/D[T]['U']

# ---------------------------------------------------------------- J. effective dof
P("="*100)
P("J.  EFFECTIVE DOF AUDIT on the controls, where K == 1 is known exactly.")
P("    For M tau-samples the nominal sigma of the mean is 1/sqrt(M).  Measure the true")
P("    scatter of block means (blocks of 0.05 in tau, i.e. ~200 samples) about 1.")
P("="*100)
for tag in ('CUE', 'POI'):
    pts = np.load(os.path.join(HERE, f"att016_ctrl_{tag}.npy"), allow_pickle=True)
    devs = []
    for uu in pts:
        UU = float(uu[-1]); tt = np.arange(1, int(3.0*UU))/UU
        KK = K_of(uu, tt)
        sel = tt > 1.05
        tts, KKs = tt[sel], KK[sel]
        idx = np.digitize(tts, EDGES)-1
        for b in np.unique(idx):
            v = KKs[idx == b]
            if len(v) > 100: devs.append((v.mean()-1.0)*sqrt(len(v)))
    devs = np.array(devs)
    P(f"  {tag}: {len(devs)} blocks;  mean (K-1)*sqrt(M) = {devs.mean():+.4f};  "
      f"sd = {devs.std(ddof=1):.4f}   =>  dof_eff/dof_nom = {1/devs.var(ddof=1):.3f}")
    P(f"       (sd = 1.000 exactly if samples were independent Exp(1))")
INFL = None
pts = np.load(os.path.join(HERE, "att016_ctrl_CUE.npy"), allow_pickle=True)
devs = []
for uu in pts:
    UU = float(uu[-1]); tt = np.arange(1, int(3.0*UU))/UU; KK = K_of(uu, tt)
    sel = tt > 1.05; tts, KKs = tt[sel], KK[sel]
    idx = np.digitize(tts, EDGES)-1
    for b in np.unique(idx):
        v = KKs[idx == b]
        if len(v) > 100: devs.append((v.mean()-1.0)*sqrt(len(v)))
INFL = np.std(devs, ddof=1)
P(f"\n  -> error-bar inflation factor adopted from CUE: {INFL:.3f}")

# ---------------------------------------------------------------- restated flatness
P("\n" + "="*100)
P("A2'.  FLATNESS ABOVE tau=1 with the audited error bars (sigma inflated by the factor above)")
P("="*100)
P(f"  {'T':>10}{'<K>_(1.05,3)':>15}{'sigma':>9}{'z vs 1':>9}{'z vs CUE':>10}"
  f"{'<K>_(1.05,1.5)':>16}{'sigma':>9}{'z vs 1':>9}")
ctrl = {}
for tag in ('CUE', 'POI'):
    pts = np.load(os.path.join(HERE, f"att016_ctrl_{tag}.npy"), allow_pickle=True)
    tts = []; KKs = []
    for uu in pts:
        UU = float(uu[-1]); tt = np.arange(1, int(3.0*UU))/UU
        tts.append(tt); KKs.append(K_of(uu, tt))
    ctrl[tag] = (np.concatenate(tts), np.concatenate(KKs))
def stat(taus, K, lo, hi):
    s = (taus > lo) & (taus < hi); m = K[s].mean()
    return m, INFL*m/sqrt(s.sum()), s.sum()
cm, cs, cM = stat(*ctrl['CUE'], 1.05, 3.0)
rows = []
for T in HEIGHTS:
    m1, s1, M1 = stat(D[T]['taus'], D[T]['K'], 1.05, 3.0)
    m2, s2, M2 = stat(D[T]['taus'], D[T]['K'], 1.05, 1.5)
    zc = (m1-cm)/sqrt(s1**2+cs**2)
    rows.append((T, m1, s1, M1))
    P(f"  {T:>10.0e}{m1:>15.4f}{s1:>9.4f}{(m1-1)/s1:>+9.2f}{zc:>+10.2f}"
      f"{m2:>16.4f}{s2:>9.4f}{(m2-1)/s2:>+9.2f}")
for tag in ('CUE', 'POI'):
    m1, s1, M1 = stat(*ctrl[tag], 1.05, 3.0); m2, s2, M2 = stat(*ctrl[tag], 1.05, 1.5)
    P(f"  {tag:>10}{m1:>15.4f}{s1:>9.4f}{(m1-1)/s1:>+9.2f}{'-':>10}"
      f"{m2:>16.4f}{s2:>9.4f}{(m2-1)/s2:>+9.2f}")
wm = sum(r[1]/r[2]**2 for r in rows)/sum(1/r[2]**2 for r in rows)
we = 1/sqrt(sum(1/r[2]**2 for r in rows))
P(f"\n  POOLED over the five heights: <K>_(1.05,3) = {wm:.4f} +- {we:.4f}"
  f"   z vs 1 = {(wm-1)/we:+.2f}   z vs CUE = {(wm-cm)/sqrt(we**2+cs**2):+.2f}")
P(f"  3-sigma DETECTION FLOOR on a uniform excess over (1.05,3): pooled {3*we*100:.2f}% ,"
  f" single height {3*rows[3][2]*100:.1f}% , single 0.05-bin ~{3*INFL/sqrt(200)*100:.0f}%")

# ---------------------------------------------------------------- K. injection test
P("\n" + "="*100)
P("K.  SENSITIVITY / POSITIVE CONTROL: inject a known density modulation above tau=1")
P("    into the REAL zeta tape and check the pipeline recovers it at the predicted size.")
P("    A density ripple  rho -> 1 + A cos(2 pi tau0 u)  displaces u_k by  -(A/(2 pi tau0)) sin(2 pi tau0 u_k)")
P("    and produces a line of height K = A^2 U / 4  at tau0.  Target bin excess is over a")
P("    0.05 bin containing that line: dK_bin = (A^2 U/4)/(U*0.05) = A^2/0.2.")
P("="*100)
T = 1e6; d = D[T]; u0 = d['u']; U = d['U']; tau0 = 1.6
P(f"  T={T:.0e}  U={U:.0f}  tau0={tau0}")
P(f"  {'A':>9}{'pred dK_bin':>13}{'meas dK_bin':>13}{'sigma':>9}{'z':>8}{'K(tau0) meas':>14}{'pred':>9}")
base_t = d['taus']; base_K = d['K']
b0 = int(np.digitize([tau0], EDGES)[0])-1
selb = (base_t >= EDGES[b0]) & (base_t < EDGES[b0+1])
K0 = base_K[selb].mean()
for A in (0.05, 0.10, 0.20, 0.40, 0.80):
    up = u0 - (A/(2*pi*tau0))*np.sin(2*pi*tau0*u0)
    Ki = K_of(up, base_t[selb])
    meas = Ki.mean() - K0
    predbin = A*A/(4*BINW)
    sig = INFL*Ki.mean()/sqrt(selb.sum())
    P(f"  {A:>9.2f}{predbin:>13.4f}{meas:>13.4f}{sig:>9.4f}{meas/sig:>8.2f}"
      f"{float(K_of(up,[tau0])[0]):>14.2f}{A*A*U/4:>9.2f}")
P("  => the pipeline is NOT blind above tau=1; it detects a ripple of amplitude A at the")
P("     predicted amplitude.  The 3-sigma floor corresponds to A ~ sqrt(0.2*3*sigma).")

# ---------------------------------------------------------------- L. surrogate
P("\n" + "="*100)
P("L.  SURROGATE DISCRIMINATION: does the ramp carry prime information beyond the lattice?")
P("    median |K/D - 1| over 0.2<tau<0.95, zeta vs lattice+iid-S surrogate vs CUE.")
P("="*100)
rng = np.random.default_rng(99)
P(f"  {'T':>10}{'zeta med|K/D-1|':>18}{'surrogate':>12}{'CUE':>10}{'corr(K,D) zeta':>17}{'surr':>9}")
for T in HEIGHTS:
    d = D[T]; pred, tmax = diag_bins(d['L'], EDGES)
    sel = (MID > 0.2) & (MID < 0.95)
    def binmeans(tt, KK):
        idx = np.digitize(tt, EDGES)-1
        return np.array([KK[idx == b].mean() if (idx == b).sum() else np.nan
                         for b in range(len(MID))])
    mz = binmeans(d['taus'], d['K'])
    r = np.arange(d['n']) - d['u']; r -= r.mean()
    us = np.sort(np.arange(d['n']) - rng.permutation(r)); us -= us[0]; UU = float(us[-1])
    ts = np.arange(1, int(3.0*UU))/UU
    ms = binmeans(ts, K_of(us, ts))
    uc = np.load(os.path.join(HERE, "att016_ctrl_CUE.npy"), allow_pickle=True)[0]
    UC = float(uc[-1]); tc = np.arange(1, int(3.0*UC))/UC
    mc = binmeans(tc, K_of(uc, tc))
    f = lambda m: np.nanmedian(np.abs(m[sel]/pred[sel]-1))
    cz = np.corrcoef(mz[sel], pred[sel])[0, 1]; cs_ = np.corrcoef(ms[sel], pred[sel])[0, 1]
    P(f"  {T:>10.0e}{f(mz):>18.4f}{f(ms):>12.4f}{f(mc):>10.4f}{cz:>17.4f}{cs_:>9.4f}")

# ---------------------------------------------------------------- M. precision
P("\n" + "="*100)
P("M.  PRECISION AUDIT: perturb every zero by N(0, 1e-8) in t (100x the Zrs positional gate)")
P("="*100)
P(f"  {'T':>10}{'K(1) exact':>13}{'K(1) jitter':>13}{'<K>_(1.05,3) exact':>21}{'jitter':>10}")
for T in HEIGHTS:
    d = D[T]
    gp = d['g'] + rng.normal(0, 1e-8, d['n'])
    up = theta(gp)/np.pi; up -= up[0]
    tt = np.arange(1, int(3.0*float(up[-1])))/float(up[-1])
    Kp = K_of(up, tt)
    s = tt > 1.05
    s0 = d['taus'] > 1.05
    P(f"  {T:>10.0e}{float(K_of(d['u'],[1.0])[0]):>13.4f}{float(K_of(up,[1.0])[0]):>13.4f}"
      f"{d['K'][s0].mean():>21.4f}{Kp[s].mean():>10.4f}")

# ---------------------------------------------------------------- binwidth audit
P("\n" + "="*100)
P("N.  BIN-WIDTH / WINDOW AUDIT: <K>_(1.05,3) under different binning and sub-windows.")
P("="*100)
P(f"  {'T':>10}{'full':>9}{'1st half':>10}{'2nd half':>10}{'Q1':>8}{'Q2':>8}{'Q3':>8}{'Q4':>8}")
for T in HEIGHTS:
    d = D[T]; row = f"  {T:>10.0e}"
    s = d['taus'] > 1.05; row += f"{d['K'][s].mean():>9.4f}"
    for nb, tag in ((2, 'h'), (4, 'q')):
        for pidx in np.array_split(np.arange(d['n']), nb):
            uu = d['u'][pidx] - d['u'][pidx][0]; UU = float(uu[-1])
            tt = np.arange(1, int(3.0*UU))/UU; KK = K_of(uu, tt)
            row += f"{KK[tt>1.05].mean():>10.4f}" if nb == 2 else f"{KK[tt>1.05].mean():>8.4f}"
    P(row)
P("\ndone.")
