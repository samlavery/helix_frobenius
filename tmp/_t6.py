import numpy as np, time, sys
from att033A_strip_implA import solve_Z, MT
def go(A,D,K=4,solver='SCS',**kw):
    W=A/np.pi; ws=tuple(W*k/K for k in range(1,K+1)) if A>0 else ()
    t0=time.time()
    try: v,st,cc,p=solve_Z(2.0,D,ws,solver=solver,**kw)
    except Exception: v,st=float('nan'),'EXC'
    return (float('nan') if v is None else v),st,time.time()-t0
KW=dict(eps=3e-10,max_iters=400000)
print('=== Delta=0.05 (n=40) full grid, SCS eps=3e-10 ===')
for A in (0.0,0.05,0.1,0.15,0.2,0.25,0.3,0.4,0.5,1.0,2.0):
    v,st,dt=go(A,0.05,**KW); print('  A=%.2f W=%.5f Z=%.6f %s (%.0fs)'%(A,A/np.pi,v,st,dt)); sys.stdout.flush()
print('=== Delta=0.04 (n=50) crossover refinement, SCS ===')
for A in (0.15,0.175,0.2,0.225,0.25):
    v,st,dt=go(A,0.04,**KW); print('  A=%.3f Z=%.6f %s (%.0fs)'%(A,v,st,dt)); sys.stdout.flush()
print('=== w-sample density at A=0.25, Delta=0.05 (more w => higher Z) ===')
for K in (1,2,4,8,16):
    v,st,dt=go(0.25,0.05,K=K,**KW); print('  K=%2d Z=%.6f %s (%.0fs)'%(K,v,st,dt)); sys.stdout.flush()
