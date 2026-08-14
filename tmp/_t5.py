import numpy as np, time, sys
from att033A_strip_implA import solve_Z, MT
def go(A,D=0.04,K=4,solver='CLARABEL',**kw):
    W=A/np.pi; ws=tuple(W*k/K for k in range(1,K+1)) if A>0 else ()
    t0=time.time()
    try: v,st,cc,p=solve_Z(2.0,D,ws,solver=solver,**kw)
    except Exception as e: v,st=None,'EXC'
    if v is None:
        try: v,st,cc,p=solve_Z(2.0,D,ws,solver='SCS',eps=1e-9,max_iters=300000); st='SCS:'+st
        except Exception as e: v,st=float('nan'),'EXC2'
    return v,st,time.time()-t0
print('--- crossover refinement, Delta=0.04 ---'); sys.stdout.flush()
for A in (0.175,0.20,0.225,0.30,0.40):
    v,st,dt=go(A); print('  A=%.3f W=%.5f Z=%.6f %s (%.0fs)'%(A,A/np.pi,v,st,dt)); sys.stdout.flush()
print('--- w-sampling density at A=0.25 (more samples => higher Z) ---'); sys.stdout.flush()
for K in (1,2,4,8,16):
    v,st,dt=go(0.25,K=K); print('  K=%2d Z=%.6f %s (%.0fs)'%(K,v,st,dt)); sys.stdout.flush()
print('--- SCS cross-check ---'); sys.stdout.flush()
for A in (0.25,0.5):
    v,st,dt=go(A,solver='SCS',eps=1e-9,max_iters=300000)
    print('  A=%.2f SCS Z=%.6f %s (%.0fs)'%(A,v,st,dt)); sys.stdout.flush()
