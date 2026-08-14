"""TAPE MODEL vs SELBERG.
Tape: cut gapval = pi/3 - 1 per section, irrational ratio -> equidistributed sawtooth
      -> S should be UNIFORM on its range.
Selberg: S is asymptotically GAUSSIAN, variance loglog(t)/(2 pi^2).
Decisive: fit both to the empirical distribution of S."""
import mpmath as mp, numpy as np, sys
from scipy import stats
mp.mp.dps=15
def P(*a): print(*a); sys.stdout.flush()
S=[];T=[]
t=20.0
while t<900.0:
    N=int(mp.nzeros(t)); th=float(mp.siegeltheta(t))
    S.append(N-1-th/np.pi); T.append(t); t+=0.37
S=np.array(S); T=np.array(T)
gap=np.pi/3-1
P(f"samples {len(S)}   gapval = pi/3 - 1 = {gap:.7f}   retained 3/pi = {3/np.pi:.7f}")
P(f"S: mean {S.mean():+.4f}  sd {S.std():.4f}  range [{S.min():.3f},{S.max():.3f}]")
sig=np.sqrt(np.log(np.log(T.mean()))/(2*np.pi**2))
P(f"Selberg sigma at mean height = {sig:.4f}   measured sd = {S.std():.4f}  ratio {S.std()/sig:.3f}")
P("")
ks_n=stats.kstest((S-S.mean())/S.std(),'norm')
lo,hi=S.min(),S.max()
ks_u=stats.kstest((S-lo)/(hi-lo),'uniform')
P(f"  KS vs GAUSSIAN : D={ks_n.statistic:.4f}  p={ks_n.pvalue:.3e}")
P(f"  KS vs UNIFORM  : D={ks_u.statistic:.4f}  p={ks_u.pvalue:.3e}")
P(f"  -> {'GAUSSIAN' if ks_n.statistic<ks_u.statistic else 'UNIFORM'} fits better "
  f"(smaller D)")
P("")
P("  decile counts of S over its range (uniform would be flat):")
h,_=np.histogram(S,bins=10)
P("   "+" ".join(f"{c:4d}" for c in h)+f"   flat would be {len(S)//10}")
P("")
P("  is the sawtooth visible?  correlate S with frac(N*gapval):")
N_=np.array([int(mp.nzeros(t)) for t in T])
saw=np.mod(N_*gap,1.0)
P(f"    corr(S, frac(N*gapval))      = {np.corrcoef(S,saw)[0,1]:+.4f}")
P(f"    corr(S, frac(N*gapval)-0.5)  = {np.corrcoef(S,saw-0.5)[0,1]:+.4f}")
P(f"    corr(S, theta/pi frac)       = {np.corrcoef(S,np.mod(np.array([float(mp.siegeltheta(t)) for t in T])/np.pi,1.0))[0,1]:+.4f}")
