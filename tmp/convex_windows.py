"""Convex windows of log|Z| = negative transverse curvature = silent-transition candidates.
Computed from ON-LINE data only (harmonicity does the transverse part).

PRECHECK: DH's off-line pair must show as a convex window containing ZERO sign changes.
If zeta's convex windows all contain zeros / are bounded by them, the test discriminates.
"""
import mpmath as mp, numpy as np, sys
mp.mp.dps=15
def P(*a): print(*a); sys.stdout.flush()

def windows(Zf, t0, t1, step):
    ts=np.arange(t0,t1,step)
    Z=np.array([float(Zf(t)) for t in ts])
    lg=np.log(np.abs(Z)+1e-300)
    d2=(lg[2:]-2*lg[1:-1]+lg[:-2])/step**2         # d2 log|Z| / dt2
    tm=ts[1:-1]
    conv=d2>0                                       # convex => transverse curvature < 0
    segs=[]; i=0
    while i<len(conv):
        if conv[i]:
            j=i
            while j+1<len(conv) and conv[j+1]: j+=1
            segs.append((tm[i],tm[j])); i=j+1
        else: i+=1
    s=np.sign(Z); zc=ts[np.nonzero(s[:-1]*s[1:]<0)[0]]+step/2
    return segs, zc, ts, Z

P("=== ZETA, t in [10,100] ===")
segs,zc,ts,Z = windows(lambda t: mp.siegelz(t), 10.0, 100.0, 0.004)
P(f"  zeros found: {len(zc)}   convex windows: {len(segs)}")
empty=0
for a,b in segs:
    n=int(np.sum((zc>a)&(zc<b)))
    if n==0: empty+=1
P(f"  windows containing NO zero: {empty}/{len(segs)}")
wid=np.array([b-a for a,b in segs])
P(f"  window widths: min {wid.min():.4f}  median {np.median(wid):.4f}  max {wid.max():.4f}")
# for the empty ones, how deep does |Z| get?  a genuine off-line pair has a FLOOR
floors=[]
for a,b in segs:
    if int(np.sum((zc>a)&(zc<b)))==0:
        m=(ts>=a)&(ts<=b)
        floors.append(np.min(np.abs(Z[m])))
floors=np.array(floors)
P(f"  |Z| floor inside empty windows: min {floors.min():.3e}  median {np.median(floors):.3e}")
P(f"  -> a floor near 0 means the window abuts a zero; a floor bounded away means a")
P(f"     genuine silent transition.  smallest floor = {floors.min():.3e}")

P("\n=== DH positive control, t in [84,88] ===")
A=(4/mp.sqrt(5))*mp.sin(2*mp.pi/5); B=(4/mp.sqrt(5))*mp.sin(4*mp.pi/5)
XI=float((mp.sqrt(A**2+B**2)-A)/B); aa=[1,XI,-XI,-1,0]
fdh=lambda t: mp.re(mp.power(5,-mp.mpc(0.5,t))*sum(aa[r-1]*mp.zeta(mp.mpc(0.5,t),mp.mpf(r)/5) for r in range(1,6)))
segs2,zc2,ts2,Z2 = windows(fdh, 84.0, 88.0, 0.004)
P(f"  DH zeros (sign changes) in range: {len(zc2)}   convex windows: {len(segs2)}")
for a,b in segs2:
    n=int(np.sum((zc2>a)&(zc2<b)))
    m=(ts2>=a)&(ts2<=b)
    P(f"    window [{a:.4f},{b:.4f}] width {b-a:.4f}  zeros inside: {n}   |f| floor {np.min(np.abs(Z2[m])):.4f}"
      + ("   <- OFF-LINE PAIR" if abs((a+b)/2-85.6993)<0.2 else ""))
