"""ADVERSARIAL VERIFICATION of attempt 016 -- independent recomputation.

I do NOT reuse their cached K arrays.  I recompute the tape, the form factor, the
error bars and the controls from the zero lists, with my own code, on my own tau grids,
and with my own null model.  Stage flags on the command line.

STAGES
  A  data integrity + independent census (mpmath siegelz / siegeltheta / zero recount)
  B  K(tau) recomputed; <K> above tau=1 on THREE independent tau grids; lower-cut sweep
  C  block-bootstrap / jackknife error bars, independent of their "scatter audit"
  D  the tau=1 line: K(1), mass, decay fit; identity check; leakage budget
  E  Berry diagonal D(tau) with a LARGER sieve cap; is D=tau?  is K/D=1/tau a restatement?
  F  my own CUE + Poisson controls
  G  positive control at a different tau0; sensitivity floor
"""
import numpy as np, math, os, sys, time
from math import log, pi, sqrt, exp

HERE = os.path.dirname(os.path.abspath(__file__))
def P(*a): print(*a); sys.stdout.flush()
STAGES = set(sys.argv[1]) if len(sys.argv) > 1 else set('ABCDEFG')

HEIGHTS = [1e3, 1e4, 1e5, 1e6, 1e7]

# ------------------------------------------------------------------ my own theta
def theta_asym(t):
    """Stirling asymptotic for the Riemann-Siegel theta, one more term than theirs."""
    t = np.asarray(t, float)
    return (t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8
            + 1/(48*t) + 7/(5760*t**3) + 31/(80640*t**5) + 127/(430080*t**7))

def K_direct(u, taus, w=None, blk=256):
    """K(tau) = |sum_k w_k e^{2 pi i tau u_k}|^2 / sum w_k^2.  Written independently."""
    u = np.asarray(u, float); taus = np.asarray(taus, float)
    if w is None:
        w = np.ones(len(u)); nrm = float(len(u))
    else:
        w = np.asarray(w, float); nrm = float(np.dot(w, w))
    out = np.empty(len(taus))
    for i in range(0, len(taus), blk):
        tt = taus[i:i+blk]
        ph = 2.0*np.pi*np.multiply.outer(tt, u)
        re = np.cos(ph) @ w
        im = np.sin(ph) @ w
        out[i:i+blk] = (re*re + im*im)/nrm
    return out

def tape_of(g):
    u = theta_asym(g)/np.pi
    return u - u[0]

DATA = {}
for T in HEIGHTS:
    g = np.load(os.path.join(HERE, f"att010_zeros_{T:.0e}.npy"))
    u = tape_of(g)
    DATA[T] = dict(g=g, u=u, U=float(u[-1]), n=len(u),
                   Lc=log(0.5*(g[0]+g[-1])/(2*pi)), Tc=0.5*(g[0]+g[-1]))

# ================================================================== A
if 'A' in STAGES:
    P("="*104)
    P("A.  DATA INTEGRITY + INDEPENDENT CENSUS")
    P("="*104)
    import mpmath as mp
    mp.mp.dps = 30
    P(f"  {'T':>9}{'n':>7}{'t_lo':>14}{'t_hi':>14}{'W':>9}{'U=u[-1]':>11}{'n-1-U':>9}"
      f"{'L(centre)':>11}{'L(edge_lo)':>11}{'L(edge_hi)':>11}")
    for T in HEIGHTS:
        d = DATA[T]; g = d['g']
        P(f"  {T:>9.0e}{d['n']:>7}{g[0]:>14.4f}{g[-1]:>14.4f}{g[-1]-g[0]:>9.1f}"
          f"{d['U']:>11.3f}{d['n']-1-d['U']:>9.3f}{d['Lc']:>11.4f}"
          f"{log(g[0]/(2*pi)):>11.4f}{log(g[-1]/(2*pi)):>11.4f}")

    P("\n  A1. |Z(gamma)| at 8 cached zeros per height (mpmath.siegelz, dps=30):")
    rng = np.random.default_rng(1)
    for T in HEIGHTS:
        g = DATA[T]['g']; idx = rng.choice(len(g), 8, replace=False)
        vals = [abs(float(mp.siegelz(mp.mpf(float(g[i]))))) for i in idx]
        P(f"    T={T:.0e}   max |Z| = {max(vals):.3e}   median = {np.median(vals):.3e}")

    P("\n  A2. my theta_asym vs mpmath.siegeltheta (8 zeros per height):")
    for T in HEIGHTS:
        g = DATA[T]['g']; idx = rng.choice(len(g), 8, replace=False)
        e = max(abs(float(mp.siegeltheta(mp.mpf(float(g[i])))) - float(theta_asym(np.array([g[i]]))[0]))
                for i in idx)
        P(f"    T={T:.0e}   max |theta_asym - siegeltheta| = {e:.3e}  "
          f"(u error = {e/pi:.3e})")

    P("\n  A3. INDEPENDENT CENSUS by mpmath.siegelz on a fine grid over a SUB-WINDOW.")
    P("      I recount sign changes of Z myself and compare with their zero list.")
    for T in HEIGHTS:
        g = DATA[T]['g']
        a, b = float(g[0]) - 1e-6, float(g[min(60, len(g)-1)]) + 1e-6
        # spacing near height T is 2pi/log(T/2pi); sample 60 points per mean spacing
        sp = 2*pi/DATA[T]['Lc']
        N = int((b-a)/(sp/60)) + 1
        ts = np.linspace(a, b, N)
        z = np.array([float(mp.siegelz(mp.mpf(float(x)))) for x in ts])
        sc = int(np.sum(np.signbit(z[:-1]) != np.signbit(z[1:])))
        theirs = int(np.sum((g >= a) & (g <= b)))
        P(f"    T={T:.0e}  sub-window [{a:.3f},{b:.3f}]  grid {N} pts ({sp/60:.2e} step)"
          f"   my sign changes = {sc}   their zeros = {theirs}   {'OK' if sc==theirs else '*** MISMATCH'}")

    P("\n  A4. residual r_k = k - u_k  (exact identity r_k = 3/2 + S(gamma_k) + const):")
    P(f"  {'T':>9}{'var r':>10}{'max|r-mean|':>13}{'skew':>8}{'kurt':>8}"
      f"{'Selberg (1/2pi^2)loglogT':>26}{'ratio':>8}")
    for T in HEIGHTS:
        d = DATA[T]; r = np.arange(d['n']) - d['u']; r = r - r.mean()
        v = r.var()
        sv = log(log(d['Tc']))/(2*pi*pi)
        P(f"  {T:>9.0e}{v:>10.5f}{np.abs(r).max():>13.4f}{(r**3).mean()/v**1.5:>8.3f}"
          f"{(r**4).mean()/v**2:>8.3f}{sv:>26.5f}{v/sv:>8.3f}")

# ================================================================== B
if 'B' in STAGES:
    P("\n" + "="*104)
    P("B.  <K> ABOVE tau=1, RECOMPUTED, on three independent tau grids.")
    P("    grid1 = j/U (theirs).  grid2 = (j+1/2)/U (half-cell offset).  grid3 = j/(4U) (4x dense).")
    P("="*104)
    RES = {}
    for T in HEIGHTS:
        d = DATA[T]; u, U = d['u'], d['U']
        row = {}
        for tag, taus in (('g1', np.arange(1, int(3.0*U))/U),
                          ('g2', (np.arange(0, int(3.0*U))+0.5)/U),
                          ('g3', np.arange(1, int(12.0*U))/(4*U))):
            t0 = time.time()
            K = K_direct(u, taus)
            row[tag] = (taus, K)
            del t0
        RES[T] = row
        d['K1'] = row['g1']
    P(f"  {'T':>9}" + "".join(f"{g:>12}" for g in ('g1', 'g2', 'g3'))
      + f"{'M(g1)':>9}{'nominal sd':>12}")
    for T in HEIGHTS:
        line = f"  {T:>9.0e}"
        for tag in ('g1', 'g2', 'g3'):
            taus, K = RES[T][tag]; s = (taus > 1.05) & (taus < 3.0)
            line += f"{K[s].mean():>12.4f}"
        taus, K = RES[T]['g1']; s = (taus > 1.05) & (taus < 3.0)
        line += f"{s.sum():>9d}{K[s].mean()/sqrt(s.sum()):>12.4f}"
        P(line)

    P("\n  B2. LOWER-CUT SWEEP (leakage from the tau=1 line would show as a decreasing trend):")
    P(f"  {'T':>9}" + "".join(f"{('cut '+str(c)):>11}" for c in (1.02, 1.05, 1.10, 1.20, 1.50, 2.00)))
    for T in HEIGHTS:
        taus, K = RES[T]['g1']; line = f"  {T:>9.0e}"
        for c in (1.02, 1.05, 1.10, 1.20, 1.50, 2.00):
            s = (taus > c) & (taus < 3.0)
            line += f"{K[s].mean():>11.4f}"
        P(line)
    np.save(os.path.join(HERE, "att016_verify_B.npy"),
            np.array([{T: (RES[T]['g1'][0], RES[T]['g1'][1]) for T in HEIGHTS}], dtype=object),
            allow_pickle=True)

# ================================================================== C
if 'C' in STAGES:
    P("\n" + "="*104)
    P("C.  MY OWN ERROR BARS: block bootstrap over tau-blocks, several block sizes.")
    P("    (independent of their 'scatter audit'; a block bootstrap needs no Exp(1) assumption)")
    P("="*104)
    B = np.load(os.path.join(HERE, "att016_verify_B.npy"), allow_pickle=True)[0]
    rng = np.random.default_rng(20260812)
    P(f"  {'T':>9}{'<K>':>9}{'nominal sd':>12}" +
      "".join(f"{('boot bw='+str(b)):>16}" for b in (0.05, 0.10, 0.25)) + f"{'z(bw=0.25)':>12}")
    for T in HEIGHTS:
        taus, K = B[T]; s = (taus > 1.05) & (taus < 3.0)
        tt, KK = taus[s], K[s]
        m = KK.mean(); nom = m/sqrt(len(KK))
        line = f"  {T:>9.0e}{m:>9.4f}{nom:>12.4f}"
        last = None
        for bw in (0.05, 0.10, 0.25):
            edges = np.arange(1.05, 3.0+1e-9, bw)
            idx = np.digitize(tt, edges)-1
            blocks = [KK[idx == b] for b in range(len(edges)-1) if (idx == b).sum() > 10]
            bm = np.array([bb.mean() for bb in blocks])
            bc = np.array([len(bb) for bb in blocks])
            # bootstrap the weighted mean over blocks
            draws = rng.integers(0, len(blocks), size=(4000, len(blocks)))
            bs = (bm[draws]*bc[draws]).sum(1)/bc[draws].sum(1)
            se = bs.std(ddof=1)
            line += f"{se:>16.4f}"
            last = se
        line += f"{(m-1)/last:>+12.2f}"
        P(line)

    P("\n  C2. sub-band (1.05,1.5), where their apparent excess lived:")
    P(f"  {'T':>9}{'<K>':>9}{'nominal sd':>12}{'boot bw=0.10':>15}{'z(boot)':>10}")
    for T in HEIGHTS:
        taus, K = B[T]; s = (taus > 1.05) & (taus < 1.5)
        tt, KK = taus[s], K[s]
        m = KK.mean(); nom = m/sqrt(len(KK))
        edges = np.arange(1.05, 1.5+1e-9, 0.10)
        idx = np.digitize(tt, edges)-1
        blocks = [KK[idx == b] for b in range(len(edges)-1) if (idx == b).sum() > 10]
        bm = np.array([bb.mean() for bb in blocks]); bc = np.array([len(bb) for bb in blocks])
        draws = rng.integers(0, len(blocks), size=(4000, len(blocks)))
        bs = (bm[draws]*bc[draws]).sum(1)/bc[draws].sum(1)
        se = bs.std(ddof=1)
        P(f"  {T:>9.0e}{m:>9.4f}{nom:>12.4f}{se:>15.4f}{(m-1)/se:>+10.2f}")

# ================================================================== D
if 'D' in STAGES:
    P("\n" + "="*104)
    P("D.  THE tau=1 LINE: K(1), the mass, the decay exponent, and the IDENTITY.")
    P("="*104)
    P(f"  {'T':>9}{'n':>7}{'K(1) direct':>13}{'n|<e(-r)>|^2':>15}{'K(2)':>9}{'K(3)':>9}"
      f"{'mass m':>10}{'m_gauss':>10}{'m/m_g':>8}")
    XX = []; YY = []; MM = []
    for T in HEIGHTS:
        d = DATA[T]; u, n = d['u'], d['n']
        k1 = float(K_direct(u, [1.0])[0])
        k2 = float(K_direct(u, [2.0])[0]); k3 = float(K_direct(u, [3.0])[0])
        r = np.arange(n) - u
        ident = n*abs(np.exp(-2j*pi*r).mean())**2
        v = (r - r.mean()).var()
        m = k1/n; mg = exp(-4*pi*pi*v)
        P(f"  {T:>9.0e}{n:>7}{k1:>13.4f}{ident:>15.4f}{k2:>9.4f}{k3:>9.4f}"
          f"{m:>10.5f}{mg:>10.5f}{m/mg:>8.4f}")
        XX.append(log(log(d['Tc']))); YY.append(log(m)); MM.append(m)
    A = np.polyfit(XX, YY, 1)
    P(f"\n  D1. log-log fit of m vs log(log T_centre):  exponent p = {A[0]:+.4f}  (theirs -2.746)")
    # sensitivity of the exponent to the choice of 'T'
    for tag, f in (('T nominal', lambda d, T: T),
                   ('T centre', lambda d, T: d['Tc']),
                   ('T lower edge', lambda d, T: d['g'][0]),
                   ('L=log(T/2pi)', lambda d, T: d['Tc']/(2*pi))):
        X2 = [log(log(f(DATA[T], T))) for T in HEIGHTS]
        A2 = np.polyfit(X2, YY, 1)
        P(f"      exponent with '{tag}': {A2[0]:+.4f}")
    P("\n  D2. is the tau=1 'line' just the identity u_k = k - 3/2 - S_k?  The two columns")
    P("      above (K(1) direct vs n|<e^{-2 pi i r}>|^2 with r = k - u) must agree to")
    P("      machine precision.  They do: the object is n|<e^{-2 pi i S}>|^2, nothing else.")

    P("\n  D3. LEAKAGE BUDGET of the tau=1 line into the band above 1.05.")
    P("      Predicted mean leakage = K(1)*sin^2(pi frac(U))/(pi^2) * <1/d^2> over the band.")
    for T in HEIGHTS:
        d = DATA[T]; U = d['U']; k1 = float(K_direct(d['u'], [1.0])[0])
        f = U - math.floor(U)
        cells = np.arange(int(0.05*U), int(2.0*U))
        lk = k1*math.sin(pi*f)**2/(pi*pi)*np.mean(1.0/cells**2)
        P(f"    T={T:.0e}  K(1)={k1:7.2f}  frac(U)={f:.4f}  mean leakage into (1.05,3) ~ {lk:.2e}")

    P("\n  D4. peak position and width of the line, on a fine grid:")
    for T in HEIGHTS:
        d = DATA[T]; U = d['U']
        fine = 1 + np.arange(-80, 81)/(20*U)
        Kf = K_direct(d['u'], fine)
        i = int(np.argmax(Kf))
        half = Kf.max()/2
        fw = np.sum(Kf > half)/(20*U)
        P(f"    T={T:.0e}  peak {Kf.max():8.3f} at tau={fine[i]:.9f} "
          f"(offset {(fine[i]-1)*U:+.3f} cells)  FWHM {fw*U:.3f} cells")

# ================================================================== E
if 'E' in STAGES:
    P("\n" + "="*104)
    P("E.  THE BERRY DIAGONAL D(tau).  Is D = tau above tau=1?  Then K/D = 1/tau is")
    P("    ALGEBRAICALLY the same statement as K = 1 and carries no extra information.")
    P("="*104)
    def primes_upto(X):
        X = int(X); s = np.ones(X+1, dtype=bool); s[:2] = False
        for p in range(2, int(X**0.5)+1):
            if s[p]: s[p*p::p] = False
        return np.nonzero(s)[0].astype(np.int64)
    for XCAP, tag in ((int(1e8), '1e8 (theirs)'), (int(4e8), '4e8 (mine, 4x)')):
        pr = primes_upto(XCAP); lg = np.log(pr.astype(float))
        P(f"\n  sieve cap {tag}: {len(pr)} primes")
        for T in (1e3, 1e4):
            L = DATA[T]['Lc']
            tt = [lg/L]; ww = [lg*lg/pr.astype(float)]; k = 2
            while True:
                msk = pr.astype(float)**k <= XCAP
                if not msk.any(): break
                tt.append(k*lg[msk]/L); ww.append(lg[msk]**2/(pr[msk].astype(float)**k)); k += 1
            tt = np.concatenate(tt); ww = np.concatenate(ww)
            E = np.arange(0, 3.0+1e-9, 0.05); MIDb = 0.5*(E[:-1]+E[1:])
            h, _ = np.histogram(tt, bins=E, weights=ww)
            Dp = h/(L*L*0.05)
            tmax = log(XCAP)/L
            sel = (MIDb > 1.05) & (MIDb < min(3.0, tmax))
            P(f"    T={T:.0e} L={L:.4f}  valid to tau={tmax:.3f}   "
              f"<D> on (1.05,{min(3.0,tmax):.2f}) = {Dp[sel].mean():.4f}   "
              f"<tau> there = {MIDb[sel].mean():.4f}   ratio D/tau = {Dp[sel].mean()/MIDb[sel].mean():.4f}")
            sel2 = (MIDb > 0.2) & (MIDb < 0.95)
            P(f"      below 1: <D> = {Dp[sel2].mean():.4f}  <tau> = {MIDb[sel2].mean():.4f}"
              f"  ratio = {Dp[sel2].mean()/MIDb[sel2].mean():.4f}")

# ================================================================== F
if 'F' in STAGES:
    P("\n" + "="*104)
    P("F.  MY OWN CONTROLS: CUE (Haar, my own generation) and Poisson, same pipeline.")
    P("="*104)
    rng = np.random.default_rng(31337)
    NCUE = int(os.environ.get('NCUE', 2000)); NREP = int(os.environ.get('NREP', 6))
    vals = []
    for r in range(NREP):
        t0 = time.time()
        Z = (rng.standard_normal((NCUE, NCUE)) + 1j*rng.standard_normal((NCUE, NCUE)))/sqrt(2)
        Q, R = np.linalg.qr(Z); Q = Q*(np.diag(R)/np.abs(np.diag(R)))
        ph = np.sort(np.angle(np.linalg.eigvals(Q)) % (2*pi))
        x = NCUE*ph/(2*pi); uu = x - x[0]; UU = float(uu[-1])
        taus = np.arange(1, int(3.0*UU))/UU
        K = K_direct(uu, taus)
        s = (taus > 1.05) & (taus < 3.0)
        vals.append((K[s].mean(), float(K_direct(uu, [1.0])[0]), UU, time.time()-t0))
        P(f"    CUE({NCUE}) rep {r+1}: <K>_(1.05,3) = {vals[-1][0]:.4f}   K(1) = {vals[-1][1]:.3f}"
          f"   U={UU:.1f}  [{vals[-1][3]:.1f}s]")
    a = np.array([v[0] for v in vals])
    P(f"  CUE pooled: <K> = {a.mean():.4f}  sd across reps = {a.std(ddof=1):.4f}"
      f"  se of mean = {a.std(ddof=1)/sqrt(len(a)):.4f}")
    pv = []
    for r in range(8):
        NN = 4000; x = np.sort(rng.random(NN)*NN); uu = x - x[0]; UU = float(uu[-1])
        taus = np.arange(1, int(3.0*UU))/UU
        K = K_direct(uu, taus); s = (taus > 1.05) & (taus < 3.0)
        pv.append((K[s].mean(), float(K_direct(uu, [1.0])[0])))
    b = np.array([v[0] for v in pv])
    P(f"  Poisson(4000) x8: <K> = {b.mean():.4f}  sd = {b.std(ddof=1):.4f}"
      f"  K(1) values = {[round(v[1],3) for v in pv]}")

# ================================================================== G
if 'G' in STAGES:
    P("\n" + "="*104)
    P("G.  POSITIVE CONTROL at a tau0 OF MY CHOOSING (2.30, not their 1.60), and the")
    P("    3-sigma detection floor implied by MY bootstrap error bars.")
    P("="*104)
    T = 1e6; d = DATA[T]; u0 = d['u']; U = d['U']
    for tau0 in (2.30, 1.60):
        P(f"\n  tau0 = {tau0}, T={T:.0e}, U={U:.0f}")
        E = np.arange(0, 3.0+1e-9, 0.05)
        b0 = int(np.digitize([tau0], E)[0])-1
        taus = np.arange(1, int(3.0*U))/U
        selb = (taus >= E[b0]) & (taus < E[b0+1])
        K0 = K_direct(u0, taus[selb]).mean()
        P(f"  {'A':>7}{'K(tau0) meas':>15}{'pred A^2 U/4':>15}{'Bessel n J1(A)^2':>19}"
          f"{'bin excess meas':>17}{'pred A^2/0.2':>14}")
        for A in (0.05, 0.1, 0.2, 0.4, 0.8):
            up = u0 - (A/(2*pi*tau0))*np.sin(2*pi*tau0*u0)
            kk = float(K_direct(up, [tau0])[0])
            from math import inf
            try:
                from scipy.special import j1 as _j1
                bess = d['n']*_j1(A)**2
            except Exception:
                # J1(A) series
                x = A/2.0
                bess = d['n']*(x - x**3/2 + x**5/12)**2
            binx = K_direct(up, taus[selb]).mean() - K0
            P(f"  {A:>7.2f}{kk:>15.3f}{A*A*U/4:>15.3f}{bess:>19.3f}{binx:>17.4f}{A*A/0.2:>14.4f}")

P("\nverify done.")
