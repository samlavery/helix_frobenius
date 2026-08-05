import numpy as np, math, random
N=10**6
s=np.ones(N+1,bool); s[:2]=False
for i in range(2,1001):
    if s[i]: s[i*i::i]=False
P=np.nonzero(s)[0].astype(np.int64); P=P[P>=3]; half=(P-1)//2
random.seed(3); ns=[random.randrange(N//2,N) for _ in range(120)]
acc={}
for n in ns:
    m=np.ones(len(P),bool); x=np.full(len(P),n,dtype=np.int64)
    while x.any():
        m &= (x%P)<=half; x//=P
    sel=P<=n
    k=np.zeros(len(P),np.int64); k[sel]=np.floor(math.log(n)/np.log(P[sel].astype(float))).astype(np.int64)
    for kk in range(1,6):
        b=sel&(k==kk)
        if not b.any(): continue
        p=P[b].astype(float); w=1.0/p; rho=(p+1)/(2*p); sp=np.log((p+1)/2)/np.log(p)
        obs=(1.0/P[b&m]).sum()
        naive=(2.0**-kk)*w.sum()                       # unit-1: half per digit, k digits
        h_all=(w*rho**(kk+1)).sum()                    # harmonic density, all k+1 digits
        h_ben=(w*sp*rho**kk).sum()                     # Benford top + harmonic lower k
        a=acc.setdefault(kk,[0.,0.,0.,0.,0]); a[0]+=obs; a[1]+=naive; a[2]+=h_all; a[3]+=h_ben; a[4]+=1
print("120 random n ~ 1e6 : carry-free Mertens mass per band")
print("  k    observed     naive       all-digits   Benford-top      err_naive  err_all  err_Benford")
T=[0.,0.,0.,0.]
for kk in sorted(acc):
    o,na,ha,hb,c=acc[kk]; o/=c; na/=c; ha/=c; hb/=c
    T[0]+=o;T[1]+=na;T[2]+=ha;T[3]+=hb
    print("  %-3d  %.6f     %.6f    %.6f     %.6f      %+6.2f%%  %+6.2f%%  %+6.2f%%"
          %(kk,o,na,ha,hb,100*(na-o)/o,100*(ha-o)/o,100*(hb-o)/o))
print("  tot  %.6f     %.6f    %.6f     %.6f      %+6.2f%%  %+6.2f%%  %+6.2f%%"
      %(T[0],T[1],T[2],T[3],100*(T[1]-T[0])/T[0],100*(T[2]-T[0])/T[0],100*(T[3]-T[0])/T[0]))
print()
print("  sum_{k>=1} 2^-k log(1+1/k) = sum_{j>=2} log j / 2^j = %.6f"%sum(math.log(j)/2**j for j in range(2,200)))
