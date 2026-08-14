"""ATTEMPT 016 -- the theta-tape form factor K(tau) ABOVE tau = 1.

HOUSE:     the theta-tape form factor  K(tau) = |sum_k e^{2 pi i tau u_k}|^2 / n,
           u = theta(t)/pi  (density identically 1), calibrated in attempt 010 by the
           exact line law  K(tau_n) = U Lambda(n)^2 / (L^2 n)  at tau_n = log n / L.
CLASSICAL: Montgomery pair correlation / Berry's diagonal approximation
           (K(tau) = tau for tau<1, = 1 for tau>1), the Rudnick-Sarnak range
           k*lambda < 2, and the Bogomolny-Keating off-diagonal terms.

MECHANISM. Zeta23's ceiling 0.68185 exists because their certificate reads only
band-width lambda <= 1 data.  In form-factor language: tau > 1 is inaccessible to them.
The tape is the coordinate in which K is literally computable from a zero list, and the
attempt-010 line law fixes the amplitude normalisation with no free parameter.  So we
just LOOK at tau in (1,3) and find out what is there at finite height.

=====================  PRE-REGISTERED NULLS (rule 1)  =====================
NULL A (the task's stated null, the headline).
  K(tau) = 1, flat, for tau in (1,3), at every height, within error bars, and
  statistically indistinguishable from the CUE control.  Numerically: every bin mean
  in (1,3) lies within 3 sigma of 1.000 with sigma = K/sqrt(dof).

NULL B (the tau = 1 lattice line, my addition -- see DERIVATION below).
  K(1) = 1 + O(1/sqrt(dof)).  Equivalently |<e^{2 pi i u_k}>|^2 = 1/n, i.e. the
  fractional parts of theta(gamma_k)/pi are equidistributed.  Under NULL B the ratio
  K(1)/1 is ~1 and does NOT grow linearly with the window length U.

NULL C (the ramp below tau = 1; this is an INSTRUMENT CHECK, not a discovery -- Berry
  1988 diagonal approximation, and reporting it as new would be a restatement).
  binned K(tau) = tau for tau<1, and equals the closed-form summed prime-line content
  D(bin) = (1/width) sum_{n: log n/L in bin} Lambda(n)^2 / (L^2 n)  to within error.
  Failure of NULL C means the instrument is broken and the attempt is BROKEN.

NULL D (controls).  CUE(N) run through the identical pipeline gives K = min(tau,1)
  with no line at tau=1; Poisson gives K = 1 everywhere with no ramp.

=====================  DERIVATION of the tau=1 prediction (DC first, rule 4)  ==========
von Mangoldt:  N(t) = theta(t)/pi + 1 + S(t).  At the k-th zero (mid-value)
       u_k := theta(gamma_k)/pi = k - 3/2 - S(gamma_k)                      (EXACT)
so the tape positions are an EXACT INTEGER LATTICE displaced by -S.  Hence
       sum_k e^{2 pi i m u_k} = (-1)^m i^{...} * sum_k e^{-2 pi i m S(gamma_k)},
       K(m) = n * |<e^{-2 pi i m S}>|^2  +  (incoherent floor ~1).
If S at zeros were Gaussian with variance v,  <e^{-2 pi i m S}> = e^{-2 pi^2 m^2 v},
and with Selberg's v = (1/(2 pi^2)) log log T this gives the closed form

       K(1)  ~  n * (log T)^{-2} * e^{-2 c0},      K(2) ~ n * (log T)^{-8}  (dead).

This is a DC term -- it is computed exactly, not bounded.  It is NOT new mathematics:
it is von Mangoldt's counting formula plus Selberg's CLT rewritten as a form factor.
Claim no priority.  The QUESTION the campaign cares about is whether the line carries
usable MASS: the delta at tau=1 has integrated mass |<e^{-2 pi i S}>|^2, not K(1).

=====================  SELF-DECEPTION CONTROLS (mandatory)  ============================
(a) Fejer.  The finite window convolves K with (1/U)|What(tau)|^2 = sin^2(pi tau U)/(pi^2 tau^2 U).
    That kernel is NON-NEGATIVE, so smoothing the concave kink of min(tau,1) produces a
    DIP just above tau=1, never a bump.  Computed explicitly below.
(b) DC leakage.  The mean density contributes sin^2(pi tau U)/(pi^2 tau^2 n), which is
    EXACTLY ZERO on the tau-grid multiples of 1/U and <= 1/(pi^2 n) elsewhere.
(c) U-scaling.  A coherent line has K proportional to U; the Exp(1) noise floor does not.
    Split the zero list into halves/quarters and check the slope.
(d) Taper.  Repeat with a Hann taper; a boxcar artifact dies, a real line does not.
(e) Surrogate.  A lattice + resampled-S surrogate must reproduce the tau=1 line and must
    NOT reproduce the ramp (different mechanisms).
"""
import numpy as np, math, os, sys, time
from math import log, pi, sqrt

def P(*a): print(*a); sys.stdout.flush()
HERE = os.path.dirname(os.path.abspath(__file__))

def theta(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)

# ---------------------------------------------------------------- form factor
def K_of(u, taus, w=None, chunk=400):
    """K(tau) = |sum_k w_k e^{2 pi i tau u_k}|^2 / (sum w_k^2).  w=None -> boxcar."""
    u = np.asarray(u, float); taus = np.asarray(taus, float)
    if w is None:
        w = np.ones_like(u); norm = float(len(u))
    else:
        norm = float(np.sum(w*w))
    out = np.empty(len(taus))
    for i in range(0, len(taus), chunk):
        ph = np.exp(2j*np.pi*np.outer(taus[i:i+chunk], u))
        out[i:i+chunk] = np.abs(ph @ w)**2 / norm
    return out

def tape(g):
    u = theta(g)/np.pi
    u = u - u[0]
    return u, float(u[-1]), len(u)

# ---------------------------------------------------------------- prime lines
_SIEVE_CACHE = {}
def primes_upto(X):
    X = int(X)
    if X in _SIEVE_CACHE: return _SIEVE_CACHE[X]
    s = np.ones(X+1, dtype=bool); s[:2] = False
    for p in range(2, int(X**0.5)+1):
        if s[p]: s[p*p::p] = False
    pr = np.nonzero(s)[0].astype(np.int64)
    _SIEVE_CACHE[X] = pr
    return pr

def diagonal_bins(L, edges, Xcap=int(1e8)):
    """Per-bin Berry diagonal prediction  (1/width) sum_{n in bin} Lambda(n)^2/(L^2 n).
    Returns (pred, tau_max_valid).  Uses ALL prime powers n <= Xcap."""
    pr = primes_upto(Xcap)
    lg = np.log(pr.astype(float))
    tau = lg/L
    wgt = lg*lg/pr.astype(float)                     # Lambda^2/n for k=1
    taus = [tau]; wgts = [wgt]
    k = 2
    while True:
        m = pr.astype(float)**k <= Xcap
        if not m.any(): break
        pk = pr[m].astype(float)**k
        taus.append(k*lg[m]/L); wgts.append(lg[m]**2/pk)
        k += 1
    taus = np.concatenate(taus); wgts = np.concatenate(wgts)
    h, _ = np.histogram(taus, bins=edges, weights=wgts)
    width = np.diff(edges)
    return h/(L*L*width), log(Xcap)/L

# ---------------------------------------------------------------- controls
def cue_phases(N, rng):
    Z = (rng.standard_normal((N, N)) + 1j*rng.standard_normal((N, N)))/np.sqrt(2)
    Q, R = np.linalg.qr(Z)
    Q = Q*(np.diag(R)/np.abs(np.diag(R)))
    ev = np.linalg.eigvals(Q)
    ph = np.sort(np.angle(ev) % (2*np.pi))
    return N*ph/(2*np.pi)                            # unfolded, density 1 on [0,N)

# ---------------------------------------------------------------- main
HEIGHTS = [1e3, 1e4, 1e5, 1e6, 1e7]
BINW = 0.05
EDGES = np.arange(0.0, 3.0+1e-9, BINW)
MID = 0.5*(EDGES[:-1]+EDGES[1:])

def binned(taus, K, edges):
    idx = np.digitize(taus, edges)-1
    nb = len(edges)-1
    m = np.full(nb, np.nan); s = np.full(nb, np.nan); c = np.zeros(nb, int)
    for b in range(nb):
        sel = K[idx == b]
        if len(sel):
            m[b] = sel.mean(); c[b] = len(sel); s[b] = sel.mean()/sqrt(len(sel))
    return m, s, c

P("="*100)
P("ATTEMPT 016 -- K(tau) on (0,3):  is anything above tau = 1 at finite height?")
P("="*100)

DATA = {}
for T in HEIGHTS:
    g = np.load(os.path.join(HERE, f"att010_zeros_{T:.0e}.npy"))
    u, U, n = tape(g)
    L = log((g[0]+g[-1])/2/(2*np.pi))                # L at window CENTRE (att010 rule)
    # tau grid at spacing exactly 1/U  ->  samples ~independent (FFT-bin convention)
    M = int(np.floor(3.0*U))
    taus = np.arange(1, M+1)/U
    t0 = time.time()
    K = K_of(u, taus)
    DATA[T] = dict(g=g, u=u, U=U, n=n, L=L, taus=taus, K=K)
    P(f"  T={T:.0e}  zeros={n}  U={U:.2f}  n/U={n/U:.5f}  L(centre)={L:.4f}  "
      f"grid={M} pts  [{time.time()-t0:.1f}s]")

# ============================================================ 1. NULL C: the ramp
P("\n" + "="*100)
P("1.  NULL C -- INSTRUMENT CHECK below tau=1 (Berry diagonal; a CHECK, not a discovery)")
P("    binned K(tau)  vs  tau  vs  summed closed-form prime lines D(bin)")
P("="*100)
DIAG = {}
for T in HEIGHTS:
    d = DATA[T]
    pred, taumax = diagonal_bins(d['L'], EDGES)
    DIAG[T] = (pred, taumax)
    m, s, c = binned(d['taus'], d['K'], EDGES)
    P(f"\n  T={T:.0e}   L={d['L']:.4f}   diagonal sum valid for tau <= {taumax:.2f} "
      f"(prime powers to 1e8)")
    P(f"    {'bin':>12}{'dof':>6}{'K meas':>10}{'+-':>8}{'tau':>8}{'D(bin)':>10}{'K/tau':>8}{'K/D':>8}")
    for b in range(len(MID)):
        if MID[b] > 1.0: break
        P(f"    {EDGES[b]:.2f}-{EDGES[b+1]:.2f}{c[b]:>6}{m[b]:>10.4f}{s[b]:>8.4f}"
          f"{MID[b]:>8.3f}{pred[b]:>10.4f}{m[b]/MID[b]:>8.3f}"
          f"{(m[b]/pred[b] if pred[b]>0 else float('nan')):>8.3f}")
    sel = (MID > 0.2) & (MID < 0.95)
    P(f"    -> median K/tau on 0.2<tau<0.95 : {np.nanmedian(m[sel]/MID[sel]):.4f}"
      f"     median K/D : {np.nanmedian(m[sel]/pred[sel]):.4f}")

# ============================================================ 2. controls
P("\n" + "="*100)
P("2.  CONTROLS through the identical pipeline (NULL D)")
P("="*100)
rng = np.random.default_rng(20260812)
NC = 4000
cue_K = []
for r in range(3):
    t0 = time.time()
    x = cue_phases(NC, rng)
    uu = x - x[0]; UU = float(uu[-1])
    tt = np.arange(1, int(np.floor(3.0*UU))+1)/UU
    cue_K.append((tt, K_of(uu, tt), UU, NC))
    P(f"  CUE({NC}) sample {r+1} done [{time.time()-t0:.1f}s]  U={UU:.2f}")
poi = []
for r in range(3):
    UU = 4000.0
    xx = np.sort(rng.random(4000)*UU); uu = xx - xx[0]; UU2 = float(uu[-1])
    tt = np.arange(1, int(np.floor(3.0*UU2))+1)/UU2
    poi.append((tt, K_of(uu, tt), UU2, 4000))

def pool(runs):
    allm = []
    for tt, KK, UU, NN in runs:
        m, s, c = binned(tt, KK, EDGES)
        allm.append((m, c))
    M_ = np.array([a[0] for a in allm]); C_ = np.array([a[1] for a in allm])
    mm = np.nansum(M_*C_, 0)/np.nansum(C_, 0)
    cc = np.nansum(C_, 0)
    return mm, mm/np.sqrt(cc), cc
cue_m, cue_s, cue_c = pool(cue_K)
poi_m, poi_s, poi_c = pool(poi)

P(f"\n  {'bin':>12}{'CUE K':>10}{'+-':>8}{'min(tau,1)':>12}{'Poisson K':>12}{'+-':>8}")
for b in range(len(MID)):
    if b % 4: continue
    P(f"  {EDGES[b]:.2f}-{EDGES[b+1]:.2f}{cue_m[b]:>10.4f}{cue_s[b]:>8.4f}"
      f"{min(MID[b],1.0):>12.3f}{poi_m[b]:>12.4f}{poi_s[b]:>8.4f}")

# ============================================================ 3. above tau=1
P("\n" + "="*100)
P("3.  NULL A -- K(tau) for tau in (1,3) at every height, vs the CUE control")
P("="*100)
P(f"  {'bin':>12}" + "".join(f"{('T=%.0e'%T):>16}" for T in HEIGHTS) + f"{'CUE':>14}")
rows = {}
for T in HEIGHTS:
    d = DATA[T]; m, s, c = binned(d['taus'], d['K'], EDGES); rows[T] = (m, s, c)
for b in range(len(MID)):
    if MID[b] < 1.0: continue
    line = f"  {EDGES[b]:.2f}-{EDGES[b+1]:.2f}"
    for T in HEIGHTS:
        m, s, c = rows[T]
        line += f"{m[b]:>9.3f}+-{s[b]:<5.3f}"
    line += f"{cue_m[b]:>8.3f}+-{cue_s[b]:<5.3f}"
    P(line)

P("\n  3-sigma scan against the CUE control (bins with tau>1, excluding the tau=1 bin):")
hits = 0
for T in HEIGHTS:
    m, s, c = rows[T]
    for b in range(len(MID)):
        if MID[b] <= 1.05: continue
        sig = sqrt(s[b]**2 + cue_s[b]**2)
        z = (m[b]-cue_m[b])/sig
        if abs(z) > 3:
            hits += 1
            P(f"    T={T:.0e}  tau in [{EDGES[b]:.2f},{EDGES[b+1]:.2f}]  "
              f"K={m[b]:.4f} vs CUE {cue_m[b]:.4f}   z={z:+.2f}")
P(f"    total |z|>3 bins: {hits}  out of {len(HEIGHTS)*sum(1 for b in range(len(MID)) if MID[b]>1.05)}")

# ============================================================ 4. the tau=1 line
P("\n" + "="*100)
P("4.  NULL B -- the tau=1 lattice line  (u_k = k - 3/2 - S(gamma_k), exact)")
P("="*100)
P(f"  {'T':>8}{'n':>7}{'U':>10}{'K(1)':>10}{'K(2)':>9}{'K(3)':>9}"
  f"{'var S':>9}{'pred K(1)':>11}{'mass':>9}{'floor':>8}")
tau1 = {}
for T in HEIGHTS:
    d = DATA[T]; u, U, n = d['u'], d['U'], d['n']
    k1 = float(K_of(u, [1.0])[0]); k2 = float(K_of(u, [2.0])[0]); k3 = float(K_of(u, [3.0])[0])
    # S at the zeros, up to an additive constant: S_k = -(u_k - k) + const
    kk = np.arange(len(u))
    Sres = kk - u                      # = 3/2 + S_k - (const)   -> centre it
    Sres = Sres - Sres.mean()
    v = float(Sres.var())
    predG = n*math.exp(-4*pi*pi*v)     # Gaussian-S prediction
    mass = k1/n                        # |<e^{-2 pi i S}>|^2 = integrated delta mass
    tau1[T] = dict(k1=k1, k2=k2, k3=k3, v=v, predG=predG, mass=mass)
    P(f"  {T:>8.0e}{n:>7}{U:>10.1f}{k1:>10.3f}{k2:>9.3f}{k3:>9.3f}"
      f"{v:>9.4f}{predG:>11.3f}{mass:>9.5f}{1.0:>8.1f}")
P("\n  (K(2),K(3) predicted DEAD: Gaussian factor e^{-2 pi^2 m^2 v} with m=2,3.)")
P("  CUE control at the same three points:")
for r, (tt, KK, UU, NN) in enumerate(cue_K):
    x = None
for r in range(3):
    tt, KK, UU, NN = cue_K[r]
    uu = None
P("   (computed below on the stored CUE point sets)")

# recompute CUE K at tau=1,2,3 exactly -- need the point sets, so redo cheaply
rng2 = np.random.default_rng(777)
P(f"  {'ctrl':>10}{'n':>7}{'K(1)':>10}{'K(2)':>9}{'K(3)':>9}{'var S':>9}")
for r in range(3):
    x = cue_phases(NC, rng2)
    uu = x - x[0]
    kk = np.arange(len(uu))
    Sres = kk - uu; Sres = Sres - Sres.mean()
    P(f"  {'CUE'+str(r+1):>10}{len(uu):>7}{float(K_of(uu,[1.0])[0]):>10.3f}"
      f"{float(K_of(uu,[2.0])[0]):>9.3f}{float(K_of(uu,[3.0])[0]):>9.3f}{Sres.var():>9.4f}")
for r in range(2):
    UU = 4000.0
    xx = np.sort(rng2.random(4000)*UU); uu = xx-xx[0]
    kk = np.arange(len(uu)); Sres = kk-uu; Sres = Sres-Sres.mean()
    P(f"  {'Poisson'+str(r+1):>10}{len(uu):>7}{float(K_of(uu,[1.0])[0]):>10.3f}"
      f"{float(K_of(uu,[2.0])[0]):>9.3f}{float(K_of(uu,[3.0])[0]):>9.3f}{Sres.var():>9.4f}")

np.save(os.path.join(HERE, "att016_cache.npy"),
        np.array([{k: {kk: vv for kk, vv in v.items() if kk in ('U','n','L')}
                   for k, v in DATA.items()}], dtype=object))
P("\nstage 1 done.")
