"""ATTEMPT 016, stage 4 -- the honest error bar for the ZETA data above tau=1.

Stage 3 measured the block-mean scatter on the CUE/Poisson controls (sd = 0.97 of nominal,
so nominal error bars are right THERE).  But above tau=1 at LOW height the zeta bin means
are NOT 200 Exp(1) samples: individual prime lines are still resolved (at T=1e3 one
resolution cell is ~1.3 integers wide near n = e^L, so primes are 5 cells apart and a bin
of 200 cells contains only ~50 lines).  A sum of ~50 heavy contributions has a LARGER
relative scatter than 200 Exp(1) draws.

NULL O (pre-registered).  The zeta block-mean scatter above tau=1, in units of the nominal
sigma, equals 1.00 at every height -- i.e. the stage-3 z-scores are honest.
If it is > 1 at low height, the low-height "excess" is an error-bar artifact and must be
retracted; the number to quote is z / (scatter factor).
"""
import numpy as np, os, sys
from math import log, pi, sqrt
def P(*a): print(*a); sys.stdout.flush()
HERE = os.path.dirname(os.path.abspath(__file__))
def theta(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)
BINW = 0.05; EDGES = np.arange(0, 3.0+1e-9, BINW); MID = 0.5*(EDGES[:-1]+EDGES[1:])
P("="*100)
P("O.  EMPIRICAL SCATTER of 0.05-blocks above tau=1, zeta vs CUE, in units of nominal sigma.")
P("    'lines/bin' = number of prime powers whose tau_n falls in a 0.05 bin at tau=1.5,")
P("    'cells/prime gap' = how many resolution cells (1/U) separate consecutive primes there.")
P("="*100)
P(f"  {'T':>10}{'L':>9}{'U':>8}{'cells/gap@1.5':>15}{'lines/bin@1.5':>15}"
  f"{'scatter/nominal':>17}{'z(1.05,3) raw':>15}{'corrected':>11}")
for T in (1e3, 1e4, 1e5, 1e6, 1e7):
    g = np.load(os.path.join(HERE, f"att010_zeros_{T:.0e}.npy"))
    u = theta(g)/np.pi; u -= u[0]; U = float(u[-1]); n = len(u)
    L = log((g[0]+g[-1])/2/(2*pi))
    K = np.load(os.path.join(HERE, f"att016_K_{T:.0e}.npy"))
    taus = np.arange(1, len(K)+1)/U
    sel = taus > 1.05
    idx = np.digitize(taus[sel], EDGES)-1
    Ks = K[sel]
    bm = []; bc = []
    for b in np.unique(idx):
        v = Ks[idx == b]
        if len(v) > 100: bm.append(v.mean()); bc.append(len(v))
    bm = np.array(bm); bc = np.array(bc)
    # scatter of block means about the LOCAL (running, 5-block) mean, in units of nominal
    glob = bm.mean()
    z = (bm - glob)*np.sqrt(bc)/glob
    scat = z.std(ddof=1)
    # arithmetic resolution at tau=1.5
    x = np.exp(1.5*L); gap = np.log(x)          # mean prime gap near x
    cells = gap*U/(x*L/x)  # = gap * U / (x * L / x)?  -> gap in tau units * U
    cells = (gap/x)*(x/x)  # placeholder
    dtau_per_int = 1.0/(x*L)                    # d tau = dn/(n L)
    cells_per_gap = gap*dtau_per_int*U
    lines_per_bin = BINW/(gap*dtau_per_int)
    m = Ks.mean(); sig = m/sqrt(sel.sum())
    P(f"  {T:>10.0e}{L:>9.4f}{U:>8.0f}{cells_per_gap:>15.2f}{lines_per_bin:>15.0f}"
      f"{scat:>17.3f}{(m-1)/sig:>+15.2f}{(m-1)/(sig*scat):>+11.2f}")
P("\n  (cells/gap >~ 1 means individual prime lines are RESOLVED above tau=1 and the")
P("   Exp(1) error model understates the scatter.)")
P("\n  Same for the (1.05,1.5) sub-band, where the stage-3 excess lived:")
P(f"  {'T':>10}{'<K>':>9}{'nominal z':>11}{'scatter/nom':>13}{'corrected z':>13}")
for T in (1e3, 1e4, 1e5, 1e6, 1e7):
    g = np.load(os.path.join(HERE, f"att010_zeros_{T:.0e}.npy"))
    u = theta(g)/np.pi; u -= u[0]; U = float(u[-1])
    K = np.load(os.path.join(HERE, f"att016_K_{T:.0e}.npy"))
    taus = np.arange(1, len(K)+1)/U
    sel = (taus > 1.05) & (taus < 1.5); Ks = K[sel]
    idx = np.digitize(taus[sel], EDGES)-1
    bm = []; bc = []
    for b in np.unique(idx):
        v = Ks[idx == b]
        if len(v) > 100: bm.append(v.mean()); bc.append(len(v))
    bm = np.array(bm); bc = np.array(bc); glob = bm.mean()
    scat = ((bm-glob)*np.sqrt(bc)/glob).std(ddof=1)
    m = Ks.mean(); sig = m/sqrt(sel.sum())
    P(f"  {T:>10.0e}{m:>9.4f}{(m-1)/sig:>+11.2f}{scat:>13.3f}{(m-1)/(sig*scat):>+13.2f}")
