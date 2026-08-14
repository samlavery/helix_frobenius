import numpy as np, cvxpy as cp, time, sys
from att033A_strip_implA import diag_sum_map
def solve2(S,Delta,ws=(),solver='CLARABEL',**kw):
    n=int(round(S/Delta)); M=n-1
    D=diag_sum_map(M); x=np.arange(n)*Delta
    lo=np.clip(x-Delta/2,0,1); hi=np.clip(x+Delta/2,0,1)
    om=(hi**2-lo**2)/(2*Delta); om[0]=Delta/4
    outside=np.where(x-Delta/2>=1-1e-12)[0]
    c=cp.Variable(n); cons=[c[0]+2*cp.sum(c[1:])==1]
    if len(outside): cons.append(c[outside]<=0)
    for w in (0.0,)+tuple(ws):
        ch=np.cosh(2*np.pi*x*w); Q=cp.Variable((n,n),PSD=True)
        cons.append(D@cp.vec(Q,order='C')==cp.multiply(ch,c))
    obj=c[0]/Delta+om[0]*c[0]+2*cp.sum(cp.multiply(om[1:],c[1:]))
    p=cp.Problem(cp.Minimize(obj),cons); p.solve(solver=solver,**kw)
    return p.value,p.status,np.array(c.value).ravel(),len(outside)
for den in (51,101):
    D=2.0/den; t0=time.time()
    v,st,cc,no=solve2(2.0,D)
    print('S=2 Delta=2/%d=%.6f n=%d out=%d Z=%.7f %s %.1fs'%(den,D,den,no,v,st,time.time()-t0)); sys.stdout.flush()
