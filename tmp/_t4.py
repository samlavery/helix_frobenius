import numpy as np, time, sys
from att033A_strip_implA import solve_Z, MT
print('--- crossover refinement, Delta=0.04, S=2, w-sample {W/4,W/2,3W/4,W} ---')
for A in (0.125,0.15,0.175,0.20,0.225,0.30,0.40):
    W=A/np.pi; ws=tuple(W*k/4 for k in (1,2,3,4)); t0=time.time()
    v,st,cc,p=solve_Z(2.0,0.04,ws)
    print('  A=%.3f W=%.5f  Z=%.6f  %s  (%.0fs)'%(A,W,v,st,time.time()-t0)); sys.stdout.flush()
print('--- w-sampling density check at A=0.25 (more samples => higher Z; ours is a LOWER bound) ---')
A=0.25; W=A/np.pi
for K in (1,2,4,8,16):
    ws=tuple(W*k/K for k in range(1,K+1)); t0=time.time()
    v,st,cc,p=solve_Z(2.0,0.04,ws)
    print('  K=%2d  Z=%.6f  %s (%.0fs)'%(K,v,st,time.time()-t0)); sys.stdout.flush()
print('--- solver cross-check (SCS, tight) ---')
for A in (0.25,0.5):
    W=A/np.pi; ws=tuple(W*k/4 for k in (1,2,3,4))
    v,st,_,_=solve_Z(2.0,0.04,ws,solver='SCS',eps=1e-9,max_iters=300000)
    print('  A=%.2f  SCS Z=%.6f  %s'%(A,v,st)); sys.stdout.flush()
