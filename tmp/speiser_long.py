import numpy as np, sys, time
from em_zeta import zz
def P(*a): print(*a); sys.stdout.flush()
def wind(lo,hi,t0,t1,npts):
    a=np.linspace(lo,hi,npts); b=np.linspace(t0,t1,npts)
    path=np.concatenate([a+1j*t0, hi+1j*b[1:], a[::-1][1:]+1j*t1, lo+1j*b[::-1][1:]])
    _,zp=zz(path, N=int(max(30,2*t1)))
    ang=np.angle(zp); d=np.diff(np.concatenate([ang,[ang[0]]]))
    d=(d+np.pi)%(2*np.pi)-np.pi
    return d.sum()/(2*np.pi)
P("LONG SPEISER SWEEP: zeta' zeros in 0.02 < Re s < 0.49, t up to 60000")
tot=0; nb=0; t=10.0; H=50.0; t0=time.time()
while t<60000.0:
    w=wind(0.02,0.49,t,t+H,1200); n=int(round(w)); tot+=n; nb+=1
    if n!=0 or abs(w-n)>0.05:
        P(f"  ANOMALY t={t:.0f}..{t+H:.0f}  winding {w:.4f} -> {n}")
    if nb%200==0:
        P(f"  ... t={t+H:.0f}   blocks {nb}   running total {tot}   [{time.time()-t0:.0f}s]")
    t+=H
P(f"\nDONE  blocks {nb}  t in [10,60000]  wall {time.time()-t0:.0f}s")
P(f"  zeta' zeros left of the critical line: {tot}")
