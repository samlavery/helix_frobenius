import numpy as np, time, sys
from att033A_strip_implA import solve_Z
print('=== w-sample density at A=0.25, Delta=0.05, CLARABEL: more w-slices must RAISE Z ===')
A=0.25; W=A/np.pi
for K in (1,2,4,8,12):
    ws=tuple(W*k/K for k in range(1,K+1)); t0=time.time()
    v,st,cc,p=solve_Z(2.0,0.05,ws)
    print('  K=%2d  Z=%.6f  %s  (%.0fs)'%(K,v,st,time.time()-t0)); sys.stdout.flush()
print('=== w=W only vs full sample (A=0.5, Delta=0.05) ===')
A=0.5; W=A/np.pi
for lab,ws in (('W only',(W,)),('W/2,W',(W/2,W)),('4-pt',tuple(W*k/4 for k in (1,2,3,4)))):
    v,st,cc,p=solve_Z(2.0,0.05,ws); print('  %-7s Z=%.6f %s'%(lab,v,st)); sys.stdout.flush()
print('=== analytic bound threshold check ===')
f=lambda W: 2*W-2*0.0928114/W
for W in (0.70,0.7824,0.85,1.0):
    print('  W=%.4f (A=%.3f)  alb=%.5f'%(W,np.pi*W,f(W)))
