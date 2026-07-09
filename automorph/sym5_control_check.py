import math, numpy as np, mpmath as mp
mp.mp.dps=18
# NEGATIVE CONTROL: does the carrier-theta modularity test discriminate genuine Sym^5 from scrambled?
# If scrambled coeffs ALSO give clean modularity -> the test is empty (artifact). More t-points too.
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
B=math.sqrt(11.0**5)
xg=np.geomspace(1e-3,50,700)
g=np.array([float(mp.meijerg([[],[]],[[0,0,0,0,0,0],[]],x)) for x in xg])   # the all-0 kernel that "won"
def theta(t,coeff):
    y=np.arange(1,NN+1)*t/B; v=np.interp(y,xg,g,right=0.0); return np.sum(coeff[1:]*v)
ts=np.geomspace(0.4,2.5,9)
def modtest(coeff,label):
    lr=np.array([theta(1/t,coeff)/theta(t,coeff) for t in ts])
    A=np.vstack([np.log(ts),np.ones_like(ts)]).T
    coef,*_=np.linalg.lstsq(A,np.log(np.abs(lr)),rcond=None)
    resid=np.std(np.log(np.abs(lr))-A@coef)
    # also check the PHASE constancy (eps real => arg(theta(1/t)/theta(t)) constant)
    argspread=np.std(np.mod(np.angle(lr),math.pi))
    print(f"  {label:14s}: power p={coef[0]:+.3f} |eps|={math.exp(coef[1]):.4f} |log|ratio|| resid={resid:.2e} argspread={argspread:.2e}")
    return resid
rng=np.random.default_rng(0)
# controls: (1) random signs on |b_n|; (2) fully random ~N(0,1)*|b_n| magnitudes; (3) a DIFFERENT L (shift index)
bsign=b*np.concatenate([[0],rng.choice([-1,1],NN)])
brand=b*np.concatenate([[0],rng.standard_normal(NN)])
bshift=np.zeros(NN+1); bshift[1:]=b[1:][::-1]  # reversed (breaks multiplicativity)
modtest(b,"Sym^5 genuine")
modtest(bsign,"scrambled-sign")
modtest(brand,"scrambled-rand")
modtest(bshift,"reversed")
print("  -> if scrambled residuals ~ genuine, the modularity test is EMPTY (artifact); if scrambled >> genuine, genuine.")
