import numpy as np, math, random
N=10**6
sieve=np.ones(N+1,bool); sieve[:2]=False
for i in range(2,int(N**.5)+1):
    if sieve[i]: sieve[i*i::i]=False
P=np.nonzero(sieve)[0].astype(np.int64); P=P[P>=3]
half=(P-1)//2

def cfmask(n):
    m=np.ones(len(P),bool); x=np.full(len(P),n,dtype=np.int64)
    while x.any():
        m &= (x%P)<=half
        x//=P
        m &= True
    return m

def bands(n):
    """return list of (k, n_primes_in_band, n_carryfree, mass, cf_mass)"""
    m=cfmask(n); sel=P<=n
    k=np.zeros(len(P),np.int64)
    lp=np.log(P.astype(float)); k[sel]=np.floor(math.log(n)/lp[sel]).astype(np.int64)
    out=[]
    for kk in range(1,int(math.log(n)/math.log(3))+2):
        b=sel&(k==kk)
        if not b.any(): continue
        tot=b.sum(); cf=(b&m).sum()
        mass=(1.0/P[b]).sum(); cfmass=(1.0/P[b&m]).sum()
        out.append((kk,tot,cf,mass,cfmass))
    return out,(1.0/P[sel&m]).sum()

random.seed(1)
tests=[random.randrange(N//2,N) for _ in range(200)]
Es=[]
for n in tests:
    _,E=bands(n); Es.append((E,n))
Es.sort(reverse=True)
print("n ~ 10^6, 200 random samples")
print("  max E = %.4f  (n=%d)   median %.4f"%(Es[0][0],Es[0][1],Es[len(Es)//2][0]))
print("  logloglog n = %.4f ,  loglog n = %.4f"%(math.log(math.log(math.log(N))),math.log(math.log(N))))
print()
n=Es[0][1]
bb,E=bands(n)
print("band decomposition for the WORST n = %d   (E=%.4f)"%(n,E))
print("  k   #p     #cf    cf_frac    2^-k     band_mass  cf_mass   pred 2^-k*mass")
for kk,tot,cf,mass,cfm in bb[:12]:
    print("  %-3d %-7d %-6d %.5f    %.5f  %.5f    %.5f   %.5f"%(kk,tot,cf,cf/tot,2.0**-kk,mass,cfm,mass*2.0**-kk))
