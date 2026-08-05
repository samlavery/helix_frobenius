import numpy as np, math, random
N=10**6
s=np.ones(N+1,bool); s[:2]=False
for i in range(2,1001):
    if s[i]: s[i*i::i]=False
P=np.nonzero(s)[0].astype(np.int64); P=P[P>=3]; half=(P-1)//2
random.seed(3)
ns=[random.randrange(N//2,N) for _ in range(120)]
acc={}
for n in ns:
    m=np.ones(len(P),bool); x=np.full(len(P),n,dtype=np.int64)
    while x.any():
        m &= (x%P)<=half; x//=P
    sel=P<=n
    k=np.zeros(len(P),np.int64)
    k[sel]=np.floor(math.log(n)/np.log(P[sel].astype(float))).astype(np.int64)
    for kk in range(1,8):
        b=sel&(k==kk)
        if not b.any(): continue
        p=P[b].astype(float)
        obs=(1.0/P[b&m]).sum()
        naive=(2.0**-kk)*(1.0/p).sum()
        top=(n//(P[b]**kk))<=half[b]                       # exact top-digit (hyperbola) condition
        harm=((1.0/p)*((p+1)/(2*p))**kk*top).sum()          # exact per-digit density x exact top condition
        a=acc.setdefault(kk,[0.0,0.0,0.0,0])
        a[0]+=obs; a[1]+=naive; a[2]+=harm; a[3]+=1
print("aggregate over 120 random n ~ 1e6   (carry-free Mertens mass per band)")
print("  k    observed     naive 2^-k    harmonized    naive err    harm err")
to=tn=th=0
for kk in sorted(acc):
    o,na,h,c=acc[kk]; o/=c; na/=c; h/=c; to+=o; tn+=na; th+=h
    print("  %-3d  %.6f     %.6f      %.6f      %+7.2f%%    %+7.2f%%"%(kk,o,na,h,100*(na-o)/o,100*(h-o)/o))
print("  ---  --------     --------      --------")
print("  tot  %.6f     %.6f      %.6f      %+7.2f%%    %+7.2f%%"%(to,tn,th,100*(tn-to)/to,100*(th-to)/to))
