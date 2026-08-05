import numpy as np, math, random
def sieve(N):
    s=np.ones(N+1,bool); s[:2]=False
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=False
    p=np.nonzero(s)[0].astype(np.int64); return p[p>=3]
print("PRE-REGISTERED TEST: is naive/observed = pi/3 = %.6f, or does it drift to 1?"%(math.pi/3))
print()
print("   N       samples   band1 ratio   all-band ratio    pi/3=1.047198")
for e in [3,4,5,6,7]:
    N=10**e; P=sieve(N); half=(P-1)//2
    random.seed(11); ns=[random.randrange(N//2,N) for _ in range(400 if e<7 else 60)]
    o1=n1=oa=na=0.0
    for n in ns:
        m=np.ones(len(P),bool); x=np.full(len(P),n,dtype=np.int64)
        while x.any():
            m &= (x%P)<=half; x//=P
        sel=P<=n
        k=np.zeros(len(P),np.int64); k[sel]=np.floor(math.log(n)/np.log(P[sel].astype(float))).astype(np.int64)
        b1=sel&(k==1)
        o1+=(1.0/P[b1&m]).sum(); n1+=0.5*(1.0/P[b1]).sum()
        oa+=(1.0/P[sel&m]).sum()
        for kk in range(1,40):
            bb=sel&(k==kk)
            if bb.any(): na+=(2.0**-kk)*(1.0/P[bb]).sum()
    print("  1e%-6d %-9d %.6f      %.6f          %s"%(e,len(ns),n1/o1,na/oa,
          "<-- hit" if abs(n1/o1-math.pi/3)<0.003 else ""))
