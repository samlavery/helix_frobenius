"""ATTEMPT 016, stage 2 -- (i) the diagonal ABOVE tau=1, (ii) the tau=1 line zoom,
(iii) every artifact control the brief demands.

PRE-REGISTERED NULLS FOR THIS STAGE
-----------------------------------
NULL A2 (headline, restated sharply).  <K> over tau in (1.05, 3.00) equals 1.000 at every
  height, within 1/sqrt(dof) ~ 1.1%.  If so there is no extra information above tau=1.
NULL E (the off-diagonal).  Berry's diagonal D(tau) -> tau also above tau=1.  If the
  measured K stays at 1 while D climbs to tau, the off-diagonal terms cancel (tau-1)
  EXACTLY at these finite heights.  Null-E value if the off-diagonal does NOT act:
  K/D = 1 above tau=1 (i.e. K = tau).  Predicted if it does act: K/D = 1/tau.
NULL F (windowing).  A boxcar of length U convolves K with the NON-NEGATIVE Fejer kernel
  sin^2(pi tau U)/(pi^2 tau^2 U).  Convolving min(tau,1) with it gives a DIP just above
  tau=1, never a bump, and of depth O(log(U)/U) -- computed explicitly here.  So any bump
  near tau=1 above the Fejer curve is not the window.  NULL F value: measured near-1 shape
  = Fejer-smoothed min(tau,1).
NULL G (U-scaling of the tau=1 line).  If K(1) is Exp(1) noise it does not scale with U.
  If it is a coherent line, K(1) = c * U.  NULL G: slope 0 in U.
NULL H (taper).  Hann taper kills a boxcar sidelobe artifact, keeps a real line.
  NULL H: the line disappears under the taper.
NULL I (surrogate).  A lattice k - S_k with S resampled iid from the MEASURED S at zeros
  reproduces K(1) but NOT the ramp.  NULL I: it reproduces the ramp too (=> the line and
  the ramp are the same mechanism, and the line is not separate information).
"""
import numpy as np, math, os, sys, time
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

def diag_taus_wgts(L, Xcap):
    pr = primes_upto(Xcap); lg = np.log(pr.astype(float))
    taus = [lg/L]; wgts = [lg*lg/pr.astype(float)]; k = 2
    while True:
        m = pr.astype(float)**k <= Xcap
        if not m.any(): break
        taus.append(k*lg[m]/L); wgts.append(lg[m]**2/(pr[m].astype(float)**k)); k += 1
    return np.concatenate(taus), np.concatenate(wgts)

HEIGHTS = [1e3, 1e4, 1e5, 1e6, 1e7]
BINW = 0.05
EDGES = np.arange(0.0, 3.0+1e-9, BINW); MID = 0.5*(EDGES[:-1]+EDGES[1:])
def binned(taus, K, edges):
    idx = np.digitize(taus, edges)-1; nb = len(edges)-1
    m = np.full(nb, np.nan); c = np.zeros(nb, int)
    for b in range(nb):
        sel = K[idx == b]
        if len(sel): m[b] = sel.mean(); c[b] = len(sel)
    return m, np.where(c > 0, m/np.sqrt(np.maximum(c, 1)), np.nan), c

D = {}
for T in HEIGHTS:
    g = np.load(os.path.join(HERE, f"att010_zeros_{T:.0e}.npy"))
    u = theta(g)/np.pi; u -= u[0]; U = float(u[-1]); n = len(u)
    L = log((g[0]+g[-1])/2/(2*pi))
    ck = os.path.join(HERE, f"att016_K_{T:.0e}.npy")
    taus = np.arange(1, int(np.floor(3.0*U))+1)/U
    K = np.load(ck) if os.path.exists(ck) else K_of(u, taus)
    if not os.path.exists(ck): np.save(ck, K)
    D[T] = dict(g=g, u=u, U=U, n=n, L=L, taus=taus, K=K)

# ---------------------------------------------------------------- 0. census / sanity
P("="*104)
P("0.  CENSUS + INSTRUMENT SANITY.  u_k = theta(gamma_k)/pi = k - 3/2 - S(gamma_k) is EXACT,")
P("    so a MISSED zero makes k-u jump by 1 for all later k and var blows up.  Small var")
P("    (~0.1) is therefore an independent census gate.  W = window in t.")
P("="*104)
P(f"  {'T':>8}{'n':>7}{'U':>10}{'n-1-U':>9}{'L':>9}{'var(k-u)':>11}{'max|dev|':>10}"
  f"{'skew':>8}{'kurt':>8}{'Selberg v':>11}")
for T in HEIGHTS:
    d = D[T]; r = np.arange(d['n']) - d['u']; r -= r.mean()
    v = r.var(); sk = (r**3).mean()/v**1.5; ku = (r**4).mean()/v**2
    sv = (1/(2*pi*pi))*log(log((d['g'][0]+d['g'][-1])/2))
    P(f"  {T:>8.0e}{d['n']:>7}{d['U']:>10.1f}{d['n']-1-d['U']:>9.2f}{d['L']:>9.4f}"
      f"{v:>11.5f}{np.abs(r).max():>10.3f}{sk:>8.3f}{ku:>8.3f}{sv:>11.5f}")

try:
    import mpmath as mp
    mp.mp.dps = 30
    g6 = D[1e6]['g']
    err = max(abs(float(mp.siegeltheta(mp.mpf(float(x)))) - float(theta(np.array([x]))[0]))
              for x in g6[:5])
    zerr = max(abs(float(mp.siegelz(mp.mpf(float(x))))) for x in g6[:5])
    P(f"\n  theta asymptotic vs mpmath.siegeltheta at 5 zeros (T=1e6): max abs err = {err:.2e}")
    P(f"  |Z(gamma_k)| at those 5 cached zeros (should be ~0):        max = {zerr:.2e}")
except Exception as e:
    P(f"  mpmath check skipped: {e}")

# ---------------------------------------------------------------- 1. diagonal above tau=1
P("\n" + "="*104)
P("1.  NULL E -- Berry diagonal D(tau) ABOVE tau=1 vs measured K.")
P("    D(bin) = (1/w) sum_{n: log n/L in bin} Lambda(n)^2/(L^2 n), ALL prime powers n<=1e8.")
P("    NULL E (no off-diagonal): K/D = 1.   Off-diagonal acting: K/D = 1/tau.")
P("="*104)
XCAP = int(1e8)
for T in HEIGHTS:
    d = D[T]; taumax = log(XCAP)/d['L']
    tt, ww = diag_taus_wgts(d['L'], XCAP)
    h, _ = np.histogram(tt, bins=EDGES, weights=ww)
    pred = h/(d['L']**2*BINW)
    m, s, c = binned(d['taus'], d['K'], EDGES)
    hi = (MID > 1.0) & (MID < taumax)
    if not hi.any():
        P(f"  T={T:.0e}: sieve cap 1e8 reaches only tau<={taumax:.2f} -- no bins above 1."); continue
    P(f"\n  T={T:.0e}  L={d['L']:.4f}  diagonal valid to tau={taumax:.2f}")
    P(f"    {'bin':>12}{'K meas':>10}{'+-':>8}{'D(diag)':>10}{'tau':>8}{'K/D':>8}{'1/tau':>8}")
    for b in np.nonzero(hi)[0]:
        P(f"    {EDGES[b]:.2f}-{EDGES[b+1]:.2f}{m[b]:>10.4f}{s[b]:>8.4f}{pred[b]:>10.4f}"
          f"{MID[b]:>8.3f}{m[b]/pred[b]:>8.3f}{1/MID[b]:>8.3f}")
    sel = hi & (MID > 1.05)
    if sel.any():
        dof = c[sel].sum()
        P(f"    -> mean over 1.05<tau<{taumax:.2f}:  K={np.nansum(m[sel]*c[sel])/dof:.4f}"
          f" +- {np.nansum(m[sel]*c[sel])/dof/sqrt(dof):.4f} (dof={dof})   "
          f"D={np.nanmean(pred[sel]):.4f}   K/D={np.nansum(m[sel]*c[sel])/dof/np.nanmean(pred[sel]):.4f}")

# ---------------------------------------------------------------- 2. flatness above 1
P("\n" + "="*104)
P("2.  NULL A2 -- <K> over tau in (1.05,3.00), the sharp flatness test.  dof ~ 1.95*U.")
P("="*104)
P(f"  {'T':>10}{'<K>_(1.05,3)':>15}{'+-':>9}{'z vs 1':>9}{'<K>_(1.05,1.5)':>16}{'+-':>9}{'z':>8}")
for T in HEIGHTS + ['CUE', 'POI']:
    if T in ('CUE', 'POI'):
        f = os.path.join(HERE, f"att016_ctrl_{T}.npy")
        if not os.path.exists(f): continue
        pts = np.load(f, allow_pickle=True)
        Ks = []; ts = []
        for uu in pts:
            UU = float(uu[-1]); tt = np.arange(1, int(np.floor(3.0*UU))+1)/UU
            ts.append(tt); Ks.append(K_of(uu, tt))
        taus = np.concatenate(ts); K = np.concatenate(Ks)
    else:
        taus = D[T]['taus']; K = D[T]['K']
    for lo, hi_ in ((1.05, 3.0), (1.05, 1.5)):
        sel = (taus > lo) & (taus < hi_)
        mm = K[sel].mean(); ee = mm/sqrt(sel.sum())
        if lo == 1.05 and hi_ == 3.0:
            row = f"  {(('%.0e'%T) if not isinstance(T,str) else T):>10}{mm:>15.4f}{ee:>9.4f}{(mm-1)/ee:>+9.2f}"
        else:
            row += f"{mm:>16.4f}{ee:>9.4f}{(mm-1)/ee:>+8.2f}"
    P(row)

# ---------------------------------------------------------------- 3. Fejer, explicitly
P("\n" + "="*104)
P("3.  NULL F -- the explicit Fejer kernel of the finite window, and what it does at tau=1.")
P("="*104)
def fejer_smooth(Uw, grid):
    """(min(|tau|,1)) convolved with (1/U)|What|^2 = sin^2(pi x U)/(pi^2 x^2 U)."""
    x = np.arange(-40000, 40001)/(4.0*Uw)          # +-10 in tau, step 1/(4U)
    ker = np.where(np.abs(x) < 1e-14, Uw, np.sin(pi*x*Uw)**2/(pi*pi*x*x*Uw))
    ker /= ker.sum()
    out = []
    for tg in grid:
        out.append(float(np.dot(ker, np.minimum(np.abs(tg - x), 1.0))))
    return np.array(out)
Uw = 4000.0
grid = np.array([0.90, 0.95, 0.98, 0.99, 0.995, 1.0, 1.005, 1.01, 1.02, 1.05, 1.10, 1.20])
fs = fejer_smooth(Uw, grid)
P(f"  U={Uw:.0f}.  Fejer-smoothed min(tau,1):")
P("    " + "".join(f"{t:>9.3f}" for t in grid))
P("    " + "".join(f"{v:>9.4f}" for v in fs))
P(f"  max deviation from min(tau,1): {np.abs(fs-np.minimum(grid,1)).max():.4f}  "
  f"(at tau=1: {fs[5]:.4f} vs 1.000)")
P("  => the window can only DEPRESS K near tau=1 by <~0.05, and by construction cannot")
P("     manufacture a peak.  Any K(1) >> 1 is not the window.")

# ---------------------------------------------------------------- 4. tau=1 zoom + controls
P("\n" + "="*104)
P("4.  NULL B/G/H -- the tau=1 line: shape, exact location, U-scaling, taper.")
P("="*104)
for T in HEIGHTS:
    d = D[T]; u, U, n = d['u'], d['U'], d['n']
    fine = 1 + np.arange(-64, 65)/(16*U)
    Kf = K_of(u, fine)
    ipk = int(np.argmax(Kf))
    P(f"\n  T={T:.0e}   K(1)={K_of(u,[1.0])[0]:.3f}   peak {Kf[ipk]:.3f} at tau="
      f"{fine[ipk]:.9f}  (offset {(fine[ipk]-1)*U:+.3f} resolution cells)")
    half = Kf.max()/2
    ww = np.sum(Kf > half)/(16*U)
    P(f"    FWHM = {ww:.6f} in tau  =  {ww*U:.2f} resolution cells (1/U = {1/U:.2e});"
      f"  a coherent line has FWHM ~ 0.89/U")
    # U-scaling
    row = "    U-scaling of K(1):  "
    for nb in (1, 2, 4, 8):
        parts = np.array_split(np.arange(n), nb)
        vals = []
        for pidx in parts:
            uu = u[pidx] - u[pidx][0]
            vals.append(float(K_of(uu, [1.0])[0]))
        row += f"  U/{nb}: {np.mean(vals):8.2f}"
    P(row)
    # Hann taper
    hann = 0.5*(1 - np.cos(2*pi*u/U))
    kh = float(K_of(u, [1.0], w=hann)[0])
    kh_off = np.mean(K_of(u, np.linspace(1.3, 2.7, 400), w=hann))
    P(f"    Hann taper:  K(1)={kh:.3f}   <K>_(1.3,2.7)={kh_off:.3f}   ratio={kh/kh_off:.1f}")

# controls at tau=1
P("\n  controls (same pipeline):")
for tag in ('CUE', 'POI'):
    f = os.path.join(HERE, f"att016_ctrl_{tag}.npy")
    if not os.path.exists(f): continue
    for i, uu in enumerate(np.load(f, allow_pickle=True)):
        UU = float(uu[-1])
        fine = 1 + np.arange(-64, 65)/(16*UU)
        Kf = K_of(uu, fine)
        P(f"    {tag}{i+1}: K(1)={float(K_of(uu,[1.0])[0]):8.3f}   max on the zoom window="
          f"{Kf.max():8.3f}   (Exp(1) floor: 99th pct = 4.6)")

# ---------------------------------------------------------------- 5. surrogate
P("\n" + "="*104)
P("5.  NULL I -- lattice + resampled-S surrogate.  Reproduces the line, not the ramp?")
P("="*104)
rng = np.random.default_rng(4242)
for T in (1e5, 1e6, 1e7):
    d = D[T]; n = d['n']
    r = np.arange(n) - d['u']; r -= r.mean()
    us = np.arange(n) - rng.permutation(r)            # iid resample of the SAME S values
    us = np.sort(us); us -= us[0]; UU = float(us[-1])
    tt = np.arange(1, int(np.floor(3.0*UU))+1)/UU
    Ks = K_of(us, tt)
    m, s, c = binned(tt, Ks, EDGES)
    ramp = np.nanmedian(m[(MID > 0.2) & (MID < 0.95)]/MID[(MID > 0.2) & (MID < 0.95)])
    P(f"  T={T:.0e}:  surrogate K(1)={float(K_of(us,[1.0])[0]):8.3f}  (zeta {float(K_of(d['u'],[1.0])[0]):8.3f})"
      f"   median K/tau on the ramp = {ramp:.3f}  (zeta ~0.98, GUE 1.00)")

# ---------------------------------------------------------------- 6. the mass
P("\n" + "="*104)
P("6.  THE PAYOFF METRIC (pre-registered before looking): the tau=1 delta's INTEGRATED MASS")
P("    m = K(1)/n = |<e^{-2 pi i S}>|^2.  A band-limited certificate reads int K(tau) hhat(tau) dtau,")
P("    so a point mass contributes m*hhat(1), NOT K(1).  Ramp mass on (0,1) = 0.5 for scale.")
P("="*104)
P(f"  {'T':>10}{'K(1)':>10}{'n':>7}{'mass m':>10}{'(logT)^-2':>12}{'m*(logT)^2':>12}"
  f"{'m/0.5':>9}")
for T in HEIGHTS:
    d = D[T]; n = d['n']; k1 = float(K_of(d['u'], [1.0])[0]); m_ = k1/n
    lt = log((d['g'][0]+d['g'][-1])/2)
    P(f"  {T:>10.0e}{k1:>10.3f}{n:>7}{m_:>10.5f}{lt**-2:>12.5f}{m_*lt*lt:>12.4f}{m_/0.5:>9.4f}")
P("\ndone.")
