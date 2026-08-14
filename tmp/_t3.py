import numpy as np, cvxpy as cp, time, sys
from att033A_strip_implA import diag_sum_map
def solve2(S,Delta,ws=(),edge='relax',solver='CLARABEL',**kw):
    n=int(round(S/Delta)); M=n-1
    D=diag_sum_map(M); x=np.arange(n)*Delta
    lo=np.clip(x-Delta/2,0,1); hi=np.clip(x+Delta/2,0,1)
    om=(hi**2-lo**2)/(2*Delta); om[0]=Delta/4
    if edge=='relax':  outside=np.where(x-Delta/2>=1-1e-12)[0]
    elif edge=='strict': outside=np.where(x>=1-1e-12)[0]
    elif edge=='loose': outside=np.where(x-Delta>=1-1e-12)[0]
    c=cp.Variable(n); cons=[c[0]+2*cp.sum(c[1:])==1]
    if len(outside): cons.append(c[outside]<=0)
    for w in (0.0,)+tuple(ws):
        ch=np.cosh(2*np.pi*x*w); Q=cp.Variable((n,n),PSD=True)
        cons.append(D@cp.vec(Q,order='C')==cp.multiply(ch,c))
    obj=c[0]/Delta+om[0]*c[0]+2*cp.sum(cp.multiply(om[1:],c[1:]))
    p=cp.Problem(cp.Minimize(obj),cons); p.solve(solver=solver,**kw)
    return p.value,p.status,np.array(c.value).ravel()

print('--- edge convention bracket, S=2, A=0 ---'); sys.stdout.flush()
for Delta in (0.04,0.02):
    for e in ('loose','relax','strict'):
        t0=time.time(); v,st,cc=solve2(2.0,Delta,edge=e)
        print('  Delta=%.3f edge=%-6s Z=%.7f  %s  (%.1fs)'%(Delta,e,v,st,time.time()-t0)); sys.stdout.flush()
print('--- profile of the A=0 optimum, Delta=0.02, edge=relax (rhat density c_j/Delta) ---')
v,st,cc=solve2(2.0,0.02,edge='relax')
x=np.arange(len(cc))*0.02
for j in list(range(0,6))+list(range(44,60))+[70,80,90,99]:
    print('   x=%.2f  c/D=%+.5f'%(x[j],cc[j]/0.02))
sys.stdout.flush()
print('--- solver cross-check (SCS) ---')
for e in ('relax',):
    v2,st2,_=solve2(2.0,0.04,edge=e,solver='SCS',eps=1e-9,max_iters=200000)
    print('  Delta=0.04 SCS Z=%.7f %s'%(v2,st2))
