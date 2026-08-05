import numpy as np, math, random
def primes(N):
    s=np.ones(N+1,bool); s[:2]=False
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=False
    p=np.nonzero(s)[0].astype(np.int64); return p[p>=3]
random.seed(7)
print(" N        samples  max E(n)   max E_small(y=100)  max E_large   logloglogN")
for e in [4,5,6]:
    N=10**e; P=primes(N); half=(P-1)//2; small=P<=100
    ns=[random.randrange(N//2,N) for _ in range(800 if e<6 else 400)]
    bE=bs=bl=0.0; arg=0
    for n in ns:
        m=np.ones(len(P),bool); x=np.full(len(P),n,dtype=np.int64)
        while x.any():
            m &= (x%P)<=half; x//=P
        sel=(P<=n)&m
        E=(1.0/P[sel]).sum(); Es=(1.0/P[sel&small]).sum(); El=E-Es
        if E>bE: bE,arg=E,n
        bs=max(bs,Es); bl=max(bl,El)
    print(" 1e%-7d %-8d %.4f     %.4f              %.4f        %.4f"%(e,len(ns),bE,bs,bl,math.log(math.log(math.log(N)))))
print()
print("  worst n at 1e6 was", arg)
