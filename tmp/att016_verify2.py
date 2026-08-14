"""ADVERSARIAL VERIFICATION of attempt 016, part 2.

THE SUSPICION.  Their own stage-3 output line prints, for the POISSON control:
    POI   <K>_(1.05,3) = 1.0103 +- 0.0056  z = +1.85     <K>_(1.05,1.5) = 1.0214  z = +1.83
which is the SAME SIZE as the zeta "excess" they then spend two stages explaining away as
an error-bar artifact.  Poisson has K == 1 exactly.  So either (i) the pipeline has a
positive bias of ~+1% in this band, in which case the zeta excess is not an excess at all
and the "flat at 1.000" statement is right for the wrong reason, or (ii) their 4 Poisson
draws were a fluctuation.  Decide it with 60 draws.

Also: the finite-n bias of K on a FIXED-n process is computable in closed form:
    E K(tau) = 1 + (n-1) |phi(tau)|^2 ,  phi = char. fn. of one point,
plus the effect of pinning u_0 = 0 and u_{n-1} = U (which is what 'u -= u[0]' does).
DC FIRST: evaluate that, do not estimate it.
"""
import numpy as np, os, sys, time
from math import log, pi, sqrt

HERE = os.path.dirname(os.path.abspath(__file__))
def P(*a): print(*a); sys.stdout.flush()

def K_direct(u, taus, blk=512):
    u = np.asarray(u, float); taus = np.asarray(taus, float)
    out = np.empty(len(taus))
    for i in range(0, len(taus), blk):
        ph = 2.0*np.pi*np.multiply.outer(taus[i:i+blk], u)
        out[i:i+blk] = (np.cos(ph).sum(1)**2 + np.sin(ph).sum(1)**2)/len(u)
    return out

def band(u, lo=1.05, hi=3.0, sub=(1.05, 1.5)):
    U = float(u[-1] - u[0]); uu = u - u[0]
    taus = np.arange(1, int(3.0*U))/U
    K = K_direct(uu, taus)
    s1 = (taus > lo) & (taus < hi); s2 = (taus > sub[0]) & (taus < sub[1])
    return K[s1].mean(), K[s2].mean(), float(K_direct(uu, [1.0])[0]), U

STAGE = sys.argv[1] if len(sys.argv) > 1 else 'H'

# ================================================================ H: Poisson at high stats
if 'H' in STAGE:
    P("="*100)
    P("H.  POISSON CONTROL AT HIGH STATISTICS.  K == 1 is exact for Poisson; any offset is")
    P("    the PIPELINE, and the zeta 'excess' must be measured against it, not against 1.")
    P("="*100)
    rng = np.random.default_rng(20260812)
    NREP = int(os.environ.get('NPOI', 60))
    a1 = []; a2 = []; k1 = []
    t0 = time.time()
    for r in range(NREP):
        N = 4000
        x = np.sort(rng.random(N)*float(N))
        m1, m2, kk, U = band(x)
        a1.append(m1); a2.append(m2); k1.append(kk)
    a1 = np.array(a1); a2 = np.array(a2); k1 = np.array(k1)
    P(f"  Poisson(4000), {NREP} independent draws, same 'u -= u[0]', same grid j/U  "
      f"[{time.time()-t0:.0f}s]")
    P(f"    <K>_(1.05,3.0) : mean {a1.mean():.5f}  sd(draw) {a1.std(ddof=1):.5f}  "
      f"se {a1.std(ddof=1)/sqrt(NREP):.5f}   z vs 1 = {(a1.mean()-1)/(a1.std(ddof=1)/sqrt(NREP)):+.2f}")
    P(f"    <K>_(1.05,1.5) : mean {a2.mean():.5f}  sd(draw) {a2.std(ddof=1):.5f}  "
      f"se {a2.std(ddof=1)/sqrt(NREP):.5f}   z vs 1 = {(a2.mean()-1)/(a2.std(ddof=1)/sqrt(NREP)):+.2f}")
    P(f"    K(1)           : mean {k1.mean():.4f}  (Exp(1) => 1)   max {k1.max():.3f}")
    P(f"    NOTE the per-draw sd {a1.std(ddof=1):.4f} vs the NOMINAL 1/sqrt(M) = "
      f"{1/sqrt(int(1.95*4000)):.4f}  -> true/nominal = {a1.std(ddof=1)*sqrt(int(1.95*4000)):.3f}")
    P(f"    their 4 Poisson draws pooled gave 1.0103 +- 0.0056; with {NREP} draws the")
    P(f"    honest single-draw sd is {a1.std(ddof=1):.4f}, so their 4-draw se was "
      f"{a1.std(ddof=1)/2:.4f}, not 0.0056.")
    np.save(os.path.join(HERE, 'att016_verify_POI.npy'), np.vstack([a1, a2, k1]))

# ================================================================ I: uniform-on-[0,N] vs pinned
if 'I' in STAGE:
    P("\n" + "="*100)
    P("I.  DC FIRST -- where does a Poisson bias come from?  Compare three conventions.")
    P("    (a) u = x - x[0], U = x[-1]-x[0]           <- theirs (pins both ends)")
    P("    (b) u = x, U = N                            <- support known exactly")
    P("    (c) u = x - x[0] but grid on U = n-1        <- density-1 convention")
    P("="*100)
    rng = np.random.default_rng(4242)
    NREP = int(os.environ.get('NPOI2', 40))
    res = {k: [] for k in 'abc'}
    for r in range(NREP):
        N = 4000; x = np.sort(rng.random(N)*float(N))
        # (a)
        u = x - x[0]; U = float(u[-1]); tt = np.arange(1, int(3*U))/U
        K = K_direct(u, tt); res['a'].append(K[(tt > 1.05) & (tt < 3)].mean())
        # (b)
        U = float(N); tt = np.arange(1, int(3*U))/U
        K = K_direct(x, tt); res['b'].append(K[(tt > 1.05) & (tt < 3)].mean())
        # (c)
        u = x - x[0]; U = float(len(x)-1); tt = np.arange(1, int(3*U))/U
        K = K_direct(u, tt); res['c'].append(K[(tt > 1.05) & (tt < 3)].mean())
    for k in 'abc':
        v = np.array(res[k])
        P(f"    ({k}) mean {v.mean():.5f}  se {v.std(ddof=1)/sqrt(NREP):.5f}  "
          f"z vs 1 = {(v.mean()-1)/(v.std(ddof=1)/sqrt(NREP)):+.2f}")

# ================================================================ J: zeta vs Poisson, matched
if 'J' in STAGE:
    P("\n" + "="*100)
    P("J.  THE ZETA EXCESS MEASURED AGAINST THE POISSON PIPELINE BASELINE.")
    P("="*100)
    A = np.load(os.path.join(HERE, 'att016_verify_POI.npy'))
    b1, b2 = A[0], A[1]
    base1, sd1 = b1.mean(), b1.std(ddof=1)
    base2, sd2 = b2.mean(), b2.std(ddof=1)
    P(f"  Poisson pipeline baseline: <K>_(1.05,3) = {base1:.5f} +- {sd1/sqrt(len(b1)):.5f}"
      f"   (single-draw sd {sd1:.4f})")
    P(f"                             <K>_(1.05,1.5) = {base2:.5f} +- {sd2/sqrt(len(b2)):.5f}"
      f"   (single-draw sd {sd2:.4f})")
    def theta_asym(t):
        t = np.asarray(t, float)
        return (t/2*np.log(t/(2*pi)) - t/2 - pi/8 + 1/(48*t) + 7/(5760*t**3)
                + 31/(80640*t**5) + 127/(430080*t**7))
    P(f"\n  {'T':>9}{'<K>_(1.05,3)':>15}{'z vs 1 (Poi sd)':>18}{'z vs Poi base':>16}"
      f"{'<K>_(1.05,1.5)':>16}{'z vs Poi base':>16}")
    zs1 = []; zs2 = []
    for T in (1e3, 1e4, 1e5, 1e6, 1e7):
        g = np.load(os.path.join(HERE, f"att010_zeros_{T:.0e}.npy"))
        u = theta_asym(g)/pi; u -= u[0]
        m1, m2, kk, U = band(u)
        z1 = (m1-1)/sd1; z1b = (m1-base1)/sqrt(sd1**2 + (sd1/sqrt(len(b1)))**2)
        z2b = (m2-base2)/sqrt(sd2**2 + (sd2/sqrt(len(b2)))**2)
        zs1.append(z1b); zs2.append(z2b)
        P(f"  {T:>9.0e}{m1:>15.5f}{z1:>+18.2f}{z1b:>+16.2f}{m2:>16.5f}{z2b:>+16.2f}")
    P(f"\n  combined over 5 heights (sum/sqrt5):  vs Poisson baseline "
      f"{sum(zs1)/sqrt(5):+.2f} sigma on (1.05,3),  {sum(zs2)/sqrt(5):+.2f} sigma on (1.05,1.5)")

P("\ndone.")
