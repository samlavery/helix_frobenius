"""RAIL-BANK REGISTRATION LAW (device under calibration).
   Gamma_k(n) = sum_{p in band k} (1/p) 1[n in G_p]        cardinal reading
   DC_k(n)    = sum_{p in band k} (1/p) rho_p^{d_p+1}      continuous reading
   mass_k     = sum_{p in band k} 1/p
   DEVICE:  |sum_{k in [a,b)} (Gamma_k - DC_k)|  <=  kappa * sqrt( sum_{k in [a,b)} mass_k^2 )
   i.e. the integrated registration defect is bounded by the CARRIER SCALE of the
   range (l2 norm of band masses), not by the number of rails.
   MEASURE kappa."""
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
random.seed(5)
V=sum(math.log((k+1)/k)**2 for k in range(1,200000))
print(f"carrier scale of the full bank:  V = sum_k (log((k+1)/k))^2 = {V:.6f}   sqrt(V) = {math.sqrt(V):.6f}")
C0=sum(2.0**-k*math.log((k+1)/k) for k in range(1,200))
print(f"common mode C0 = {C0:.6f}\n")
for N in [10**5, 10**6]:
    allp=sieve(N); lo=N//2
    ns=[random.randrange(lo,N) for _ in range(700)]
    kmax=int(math.log(N)/math.log(3))
    idxs=[]
    for k in range(1,kmax+1):
        a,b=N**(1.0/(k+1)),N**(1.0/k)
        ii=np.nonzero((allp>a)&(allp<=b))[0]
        if len(ii): idxs.append((k,ii))
    best=0.0; argb=None; Emax=0.0
    for nv in ns:
        G=[];D=[];M=[]
        for k,ii in idxs:
            P=allp[ii]; inv=1.0/P
            dp=np.floor(np.log(nv)/np.log(P.astype(float))).astype(int)
            rho=((P+1)/(2.0*P))**(dp+1)
            ok=balmask(nv,P)
            G.append(float(np.sum(inv[ok]))); D.append(float(np.sum(inv*rho)))
            M.append(float(np.sum(inv)))
        G=np.array(G);D=np.array(D);M=np.array(M)
        Emax=max(Emax,G.sum())
        n_b=len(G)
        for a in range(n_b):
            for b in range(a+1,n_b+1):
                num=abs((G[a:b]-D[a:b]).sum()); den=math.sqrt((M[a:b]**2).sum())
                if den>0 and num/den>best: best,argb=num/den,(nv,a+1,b)
    print(f"N={N}:  measured kappa = {best:.4f}   at (n,band range) = {argb}")
    print(f"         max E over sample = {Emax:.4f}    C0 + kappa*sqrt(V) = "
          f"{C0+best*math.sqrt(V):.4f}")
