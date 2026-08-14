"""NO RE-GLUE model: each pi/3 cell keeps a unit-1 segment and leaves a gap of
gapval = pi/3 - 1.  Anything landing in the gap is forced to an edge.
=> the gap is a FORBIDDEN WINDOW of width (1 - 3/pi) = 4.507% of each cell.

TEST: scan the phase of the window over the cell.  A real gap shows a DEFICIT
(count near 0).  Under uniformity every window holds ~4.507% of zeros.

PRECHECK: null -> min over phases ~ 4.5% minus a couple of sd.  A true exclusion -> ~0%.
Power is quantified below before the result is read.
"""
import mpmath as mp, numpy as np, sys
mp.mp.dps=15
def P(*a): print(*a); sys.stdout.flush()

# locate zeros as sign changes of Z
T0,T1=14.0,5000.0
step=0.08
ts=np.arange(T0,T1,step)
P(f"evaluating Z on {len(ts)} points ...")
Z=np.array([float(mp.siegelz(t)) for t in ts])
s=np.sign(Z); idx=np.nonzero(s[:-1]*s[1:]<0)[0]
g=ts[idx]+step/2
P(f"zeros located: {len(g)}   (expected ~{(T1/(2*np.pi))*np.log(T1/(2*np.pi)):.0f})")

cell=np.pi/3
frac=np.mod(g/cell,1.0)                 # position within the pi/3 cell
w=1-3/np.pi                             # forbidden width as a fraction of the cell
N=len(g)
exp=N*w; sd=np.sqrt(N*w*(1-w))
P(f"\nwindow width w = 1 - 3/pi = {w:.6f}   expected count {exp:.1f} +- {sd:.1f}")
P(f"POWER: a true exclusion gives ~0, i.e. {exp/sd:.1f} sigma below the null.  Test is decisive.\n")
phis=np.linspace(0,1,201)[:-1]
cnt=[]
for ph in phis:
    d=np.mod(frac-ph,1.0)
    cnt.append(int(np.sum(d<w)))
cnt=np.array(cnt)
P(f"  over 200 phases:  min {cnt.min()}  max {cnt.max()}  mean {cnt.mean():.1f}   null {exp:.1f}")
P(f"  min is {(exp-cnt.min())/sd:+.2f} sigma below null;  max is {(cnt.max()-exp)/sd:+.2f} above")
best=phis[np.argmin(cnt)]
P(f"  deepest deficit at phase {best:.4f}  count {cnt.min()}  ({100*cnt.min()/N:.3f}% vs {100*w:.3f}%)")
P("")
chi=np.sum((np.histogram(frac,bins=12)[0]-N/12)**2/(N/12))
P(f"  uniformity of frac(gamma/(pi/3)) over 12 bins: chi2 = {chi:.2f} (11 df, crit 19.7)")
P(f"  -> cell positions are {'NOT uniform' if chi>19.7 else 'UNIFORM'}")
