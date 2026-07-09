import math, numpy as np, mpmath as mp
mp.mp.dps = 18
# CARRIER test: the completed L is the Mellin of a theta over the completion kernel; the FE is the
# theta's MODULARITY.  Test theta(1/t) = eps * t^p * theta_dual(t) directly (self-dual => theta_dual=theta).
# --- SANITY 1: zeta.  theta(t)=sum_{n>=1} e^{-pi n^2 t}; modularity 2*theta+1 = t^{-1/2}(2*theta(1/t)+1)
def th_zeta(t): return float(mp.nsum(lambda n: mp.e**(-mp.pi*n*n*t),[1,mp.inf]))
t=0.7; lhs=2*th_zeta(1/t)+1; rhs=math.sqrt(t)*(2*th_zeta(t)+1)
print(f"  SANITY zeta: (2th(1/t)+1) - sqrt(t)(2th(t)+1) = {lhs-rhs:.2e}  (carrier modularity holds)")
# --- SANITY 2: Delta (wt12). theta(y)=sum tau(n) e^{-2pi n y}; modularity theta(1/y)=y^12 theta(y)
NB=300; P=np.zeros(NB+1);P[0]=1
for n in range(1,NB+1): P[n:]-=P[:NB+1-n].copy()
R=np.zeros(NB+1);R[0]=1;base=P.copy();e=24
while e:
    if e&1: R=np.convolve(R,base)[:NB+1]
    base=np.convolve(base,base)[:NB+1]; e>>=1
tau=np.zeros(NB+1); tau[1:]=R[:NB]
def th_D(y): 
    n=np.arange(1,NB+1); return np.sum(tau[1:]*np.exp(-2*np.pi*n*y))
y=0.3; print(f"  SANITY Delta: theta(1/y)-y^12 theta(y) = {th_D(1/y)-y**12*th_D(y):.3e}  (carrier modularity holds)")
# --- Sym^2 E11 (degree 3): theta(t)=sum b_n g3(n t / B), g3=MeijerG G^{3,0}_{0,3}(x|mu), B=sqrt(cond).
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
NN=3000; pr=sieve(NN); spf=np.zeros(NN+1,np.int64)
for p in pr[::-1]: spf[p::p]=p
def s2loc(th,k): 
    pm=[1+2*math.cos(2*m*th) for m in range(1,k+1)];h=[1.0]
    for j in range(1,k+1):h.append(sum(pm[m-1]*h[j-m] for m in range(1,j+1))/j)
    return h
loc={}
for p in pr:
    p=int(p);k=int(math.log(NN)/math.log(p))+1
    if p==11: al=ap(11)/math.sqrt(11);loc[p]=[al**(2*j) for j in range(k+1)]
    else: loc[p]=s2loc(math.acos(max(-1,min(1,ap(p)/(2*math.sqrt(p))))),k)
b=np.zeros(NN+1);b[1]=1
for n in range(2,NN+1):
    p=int(spf[n]);m,k=n,0
    while m%p==0:m//=p;k+=1
    b[n]=b[m]*b[n//m] if m>1 else loc[p][k]
B=math.sqrt(121.0)
# tabulate g3 for candidate shift-sets; test modularity theta(1/t)=eps t^p theta(t) by fitting p,eps
xg=np.geomspace(1e-3,40,600)
def build_g3(mus): return np.array([float(mp.meijerg([[],[]],[list(mus),[]],x)) for x in xg])
def theta_s2(t,g3): 
    y=np.arange(1,NN+1)*t/B; v=np.interp(y,xg,g3,right=0.0); return np.sum(b[1:]*v)
best=None
for mus in [(0,0.5,1),(0,0.5,1.0),(0.0,1.0,2.0),(0.5,1.0,1.5),(0,1,2)]:
    g3=build_g3(mus)
    ts=np.array([0.5,0.7,1.4,2.0])
    lr=np.array([theta_s2(1/t,g3)/theta_s2(t,g3) for t in ts])
    # fit log|ratio| = log|eps| + p log t ; clean if residual small and |eps|~1
    A=np.vstack([np.log(ts),np.ones_like(ts)]).T
    coef,res,*_=np.linalg.lstsq(A,np.log(np.abs(lr)),rcond=None)
    resid=np.std(np.log(np.abs(lr))-A@coef)
    if best is None or resid<best[0]: best=(resid,mus,coef[0],np.exp(coef[1]),lr)
resid,mus,p,epsmag,lr=best
print(f"  Sym^2 carrier theta: best mus={mus}  fitted power p={p:.3f}  |eps|={epsmag:.4f}  modularity residual={resid:.3e}")
print(f"     ratios theta(1/t)/theta(t) = {[round(float(x),4) for x in lr]}")
print("  VERDICT:", "clean modularity -> Sym^2 FE lives on the carrier theta" if resid<5e-2 and abs(epsmag-1)<0.2
      else "not clean at these shifts/scale (residual %.2e, |eps|=%.3f)"%(resid,epsmag))
