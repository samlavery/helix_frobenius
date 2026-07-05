import math, numpy as np, mpmath as mp
mp.mp.dps=18
# Sym^5 E11 on the CARRIER: degree 6, cond 11^5.  theta(t)=sum b_n g6(n t/B), g6=MeijerG G^{6,0}_{0,6},
# B=sqrt(11^5).  Test modularity theta(1/t)=eps t^p theta(t) -- the carrier FE test (fiber failed here).
A2,A4,A6=-1,-10,-20
def sieve(n):
    s=np.ones(n+1,bool);s[:2]=False
    for i in range(2,int(n**.5)+1):
        if s[i]:s[i*i::i]=False
    return np.nonzero(s)[0]
def ap(p):
    if p==2: return 2+1-(sum(1 for x in range(2) for yy in range(2) if (yy*yy+yy-(x**3+A2*x*x+A4*x+A6))%2==0)+1)
    x=np.arange(p,dtype=np.int64);z=(4*(x**3%p)+4*A2%p*(x*x%p)+4*A4%p*x+(4*A6+1))%p
    isq=np.zeros(p,bool);isq[(x*x)%p]=True;return int(-np.where(z==0,0,np.where(isq[z],1,-1)).sum())
NN=20000; pr=sieve(NN); spf=np.zeros(NN+1,np.int64)
for p in pr[::-1]: spf[p::p]=p
def s5loc(th,k):
    pm=[2*(math.cos(5*m*th)+math.cos(3*m*th)+math.cos(m*th)) for m in range(1,k+1)];h=[1.0]
    for j in range(1,k+1):h.append(sum(pm[m-1]*h[j-m] for m in range(1,j+1))/j)
    return h
loc={}
for p in pr:
    p=int(p);k=int(math.log(NN)/math.log(p))+1
    if p==11: al=ap(11)/math.sqrt(11);loc[p]=[al**(5*j) for j in range(k+1)]
    else: loc[p]=s5loc(math.acos(max(-1,min(1,ap(p)/(2*math.sqrt(p))))),k)
b=np.zeros(NN+1);b[1]=1
for n in range(2,NN+1):
    p=int(spf[n]);m,k=n,0
    while m%p==0:m//=p;k+=1
    b[n]=b[m]*b[n//m] if m>1 else loc[p][k]
print("  Sym^5 E11 coeffs b_2,b_3 =",round(b[2],4),round(b[3],4))
B=math.sqrt(11.0**5)
xg=np.geomspace(1e-3,50,700)
def g6(mus): return np.array([float(mp.meijerg([[],[]],[list(mus),[]],x)) for x in xg])
def theta(t,g): 
    y=np.arange(1,NN+1)*t/B; v=np.interp(y,xg,g,right=0.0); return np.sum(b[1:]*v)
best=None
# degree-6 shift sets (3 Gamma_C ~ 6 Gamma_R): try Hodge-like shifts
for mus in [(0,0.5,1,1.5,2,2.5),(0,0,0,0,0,0),(0.5,0.5,1.5,1.5,2.5,2.5),(0,1,1,2,2,3),(0.25,0.75,1.25,1.75,2.25,2.75)]:
    g=g6(mus)
    ts=np.array([0.6,0.8,1.3,1.7])
    lr=np.array([theta(1/t,g)/theta(t,g) for t in ts])
    if np.any(~np.isfinite(lr)) or np.any(np.abs(lr)<1e-12): continue
    A=np.vstack([np.log(ts),np.ones_like(ts)]).T
    coef,*_=np.linalg.lstsq(A,np.log(np.abs(lr)),rcond=None)
    resid=np.std(np.log(np.abs(lr))-A@coef)
    if best is None or resid<best[0]: best=(resid,mus,coef[0],np.exp(coef[1]),lr)
if best:
    resid,mus,p,em,lr=best
    print(f"  Sym^5 carrier theta: best mus={mus} power p={p:.3f} |eps|={em:.4f} modularity residual={resid:.3e}")
    print(f"     ratios theta(1/t)/theta(t) = {[round(float(x),4) for x in lr]}")
    print("  VERDICT:", "CLEAN modularity -> Sym^5 FE lives on the carrier theta (fiber could not see it)" if resid<8e-2 and abs(em-1)<0.25 else "not clean at these shifts (resid %.2e,|eps|=%.3f)"%(resid,em))
else: print("  all shift sets degenerate")
