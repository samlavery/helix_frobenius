"""(a) Forcing test: at jointly balanced n, fraction of p-cascade points q_j with
rail r lower-half at levels 1,2.  Null (no forcing) = ~((r+1)/2r)^levels.
(b) Exclusion capacity: |intersection over j<=D of rho_j^{-1}(L)| in Z/r^2,
rho_j = mult. by p^{-j} mod r^2, L = two-level lower-half set."""
import numpy as np
def bal(x,p):
    while x:
        if x%p > (p-1)//2: return False
        x//=p
    return True
def primes_to(m):
    s=np.ones(m+1,bool); s[:2]=False
    for i in range(2,int(m**.5)+1):
        if s[i]: s[i*i::i]=False
    return [int(q) for q in np.nonzero(s)[0]]
P=primes_to(4000)
# harvest jointly balanced (n, p, r) from a scan window
pairs={}
for n in range(2*10**6, 2*10**6+800000):
    rails=[q for q in (3,5,7,11,13) if q*q<=n and bal(n,q)]
    for a in range(len(rails)):
        for b in range(a+1,len(rails)):
            key=(rails[a],rails[b])
            pairs.setdefault(key,[]).append(n)
print("(a) forcing test — cascade r-digit structure at jointly balanced n")
print(f"{'pair':>8} {'#n':>5} {'lvl1 frac':>9} {'null':>6} {'lvl12 frac':>10} {'null':>6}")
for (p,r),ns in sorted(pairs.items()):
    c1=c12=tot=0
    for n in ns[:400]:
        j=1
        while p**(j-1)<=n:
            q=n//p**(j-1)
            if q< r*r: break
            tot+=1
            if q%r<=(r-1)//2:
                c1+=1
                if (q//r)%r<=(r-1)//2: c12+=1
            j+=1
    if tot==0: continue
    null1=(r+1)/(2*r); null12=null1**2
    print(f"{str((p,r)):>8} {len(ns):>5} {c1/tot:>9.3f} {null1:>6.3f} {c12/tot:>10.3f} {null12:>6.3f}")
print()
print("(b) exclusion capacity — |∩_j rho_j^{-1}(L)| in Z/r^2, L = 2-level lower-half")
for (p,r) in [(3,5),(3,7),(5,7),(3,11),(5,11),(7,11),(3,13),(5,13)]:
    m=r*r
    L=np.array([1 if (x%r<=(r-1)//2 and (x//r)%r<=(r-1)//2) else 0 for x in range(m)],bool)
    cur=L.copy(); sizes=[int(cur.sum())]
    pinv=pow(p,-1,m)
    rot=1
    for j in range(1,25):
        rot=rot*pinv%m
        idx=[(x*pow(p,j,m))%m for x in range(m)]  # x in rho_j^{-1}L  <=> p^j*x ... careful
        memb=np.array([L[(x*rot)%m] for x in range(m)],bool)  # q_j = x * p^{-j}: require L at that
        cur&=memb
        sizes.append(int(cur.sum()))
        if sizes[-1]==0: break
    print(f"  (p,r)=({p},{r}): |L|={sizes[0]}/{m}, sizes={sizes}")
