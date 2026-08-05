"""SURPLUS TEST.  RBRL on the tail range [a,inf) demands
      |sum_{k>=a}(Gamma_k - Delta_k)|  <=  kappa * sqrt(sum_{k>=a} mu_k^2)  -> 0
   Boundedness of E gives only O(1) there.  So tail kappa is NOT max E in disguise.
   If tail kappa stays flat as a grows, the device has content it was not given."""
import numpy as np, math, random
def sieve(N):
    s=np.ones(N+1,bool); s[:2]=False
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0].astype(np.int64)
def balmask(nv,P):
    D=(P-1)//2; ok=np.ones(len(P),bool); q=np.full(len(P),nv,dtype=np.int64)
    while True:
        liv=np.nonzero(ok&(q>0))[0]
        if liv.size==0: break
        ok[liv[(q[liv]%P[liv])>D[liv]]]=False
        q[liv]=q[liv]//P[liv]
    return ok
random.seed(9)
for N in [10**6, 10**7]:
    allp=sieve(N); lo=N//2
    ns=[random.randrange(lo,N) for _ in range(500)]
    kmax=int(math.log(N)/math.log(3))
    bands=[]
    for k in range(1,kmax+1):
        a_,b_=N**(1.0/(k+1)),N**(1.0/k)
        ii=np.nonzero((allp>a_)&(allp<=b_))[0]
        bands.append((k,ii))
    G=np.zeros((len(ns),len(bands))); D=np.zeros_like(G); M=np.zeros(len(bands))
    for bi,(k,ii) in enumerate(bands):
        if len(ii)==0: continue
        P=allp[ii]; inv=1.0/P; M[bi]=inv.sum()
        for ni,nv in enumerate(ns):
            dp=np.floor(math.log(nv)/np.log(P.astype(float))).astype(int)
            D[ni,bi]=float(np.sum(inv*((P+1)/(2.0*P))**(dp+1)))
            G[ni,bi]=float(np.sum(inv[balmask(nv,P)]))
    print(f"\nN={N}   (tail ranges [a,inf))")
    print(f"{'a':>3} {'sqrt(sum mu^2)':>15} {'max|defect|':>12} {'tail kappa':>11} "
          f"{'max tail Gamma':>15} {'sum tail Delta':>15}")
    print("-"*78)
    for a in range(1,len(bands)+1):
        den=math.sqrt((M[a-1:]**2).sum())
        if den<1e-12: break
        num=np.abs((G[:,a-1:]-D[:,a-1:]).sum(axis=1))
        print(f"{a:>3} {den:>15.6f} {num.max():>12.6f} {num.max()/den:>11.4f} "
              f"{G[:,a-1:].sum(axis=1).max():>15.6f} {D[:,a-1:].sum(axis=1).mean():>15.6f}")
