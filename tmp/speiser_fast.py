"""SPEISER: RH <=> zeta' has no zeros in 0 < Re s < 1/2.
Fast Euler-Maclaurin zeta', gated to 6e-12.  Winding around boxes left of the line."""
import numpy as np, sys, time, math
from em_zeta import zz
def P(*a): print(*a); sys.stdout.flush()
def winding_box(lo,hi,t0,t1,npts):
    a=np.linspace(lo,hi,npts); b=np.linspace(t0,t1,npts)
    path=np.concatenate([a+1j*t0, hi+1j*b[1:], a[::-1][1:]+1j*t1, lo+1j*b[::-1][1:]])
    _,zp=zz(path, N=int(max(30,2*t1)))
    ang=np.angle(zp); d=np.diff(np.concatenate([ang,[ang[0]]]))
    d=(d+np.pi)%(2*np.pi)-np.pi
    return d.sum()/(2*np.pi)
P("SPEISER SWEEP with fast zeta'   (0.02 < Re s < 0.49)")
P(f"  {'t block':>16}{'winding':>11}{'zeros':>7}{'[s]':>7}")
tot=0; nb=0; t=10.0; T=3000.0; H=50.0
t_start=time.time()
while t<T:
    t0=time.time()
    w=winding_box(0.02,0.49,t,t+H,900)
    n=int(round(w)); tot+=n; nb+=1
    if nb<=6 or n!=0 or abs(w-n)>0.02 or t+H>=T:
        P(f"  {f'{t:.0f}..{t+H:.0f}':>16}{w:>11.4f}{n:>7}{time.time()-t0:>7.1f}"
          + ("   <-- VIOLATION" if n!=0 else ""))
    t+=H
P(f"\n  blocks {nb}, t in [10,{T:.0f}], total wall {time.time()-t_start:.0f}s")
P(f"  zeta' zeros with 0.02 < Re s < 0.49 : {tot}")
P(f"  {'SPEISER HOLDS -> consistent with RH' if tot==0 else 'VIOLATION'}")
