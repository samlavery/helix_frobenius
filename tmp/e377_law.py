import numpy as np, math, itertools
from sympy import primerange
N=10**7
n=np.arange(1,N+1,dtype=np.int64)
def dig(p,d):
    m=np.ones(N,bool); x=n.copy()
    for _ in range(d):
        m &= (x%p)<=(p-1)//2; x=x//p
    return m
cache={}
def M(p,d):
    if (p,d) not in cache: cache[(p,d)]=dig(p,d)
    return cache[(p,d)]
PR=[3,5,7,11,13,17,31,37,101,103,251,1009]
cfg=[]
for ps in [(3,5),(3,7),(5,7),(11,13),(31,37),(101,103),(251,257),(1009,1013),
           (3,5,7),(3,5,11),(5,7,11),(11,13,17),(3,5,7,11),(3,5,7,11,13)]:
    for scale in [200,2000,20000]:
        ds=[max(1,round(math.log(scale)/math.log(p))) for p in ps]
        cfg.append((ps,tuple(ds)))
cfg=sorted(set(cfg))
rows=[]
for ps,ds in cfg:
    m=np.ones(N,bool); dens=1.0
    for p,d in zip(ps,ds):
        m &= M(p,d); dens*=(((p+1)//2)/p)**d
    obs=int(m.sum()); pred=N*dens; e=abs(obs-pred)
    S=sum(p**d for p,d in zip(ps,ds)); P=math.prod(p**d for p,d in zip(ps,ds))
    mx=max(p**d for p,d in zip(ps,ds)); L=math.prod((2*math.log(p))**d for p,d in zip(ps,ds))
    rows.append((e,S,P,mx,L,ps,ds))
print("N=1e7, %d configurations.  Which quantity predicts |err|?\n"%len(rows))
print("  ratio |err| / X      min        median      max        spread")
for nm,idx in [("sum p^d",1),("prod p^d",2),("max p^d",3),("prod (2log p)^d",4)]:
    r=sorted(e/x for e,*rest in [(a[0],)+a[1:] for a in rows] for x in [rest[idx-1]])
    print("  %-18s %10.2e %10.2e %10.2e   %8.1fx"%(nm,r[0],r[len(r)//2],r[-1],r[-1]/max(r[0],1e-300)))
print("\n  worst offenders for the ADDITIVE law (|err|/sum p^d):")
for e,S,P,mx,L,ps,ds in sorted(rows,key=lambda t:-t[0]/t[1])[:6]:
    print("    p=%-20s d=%-16s |err|=%-10.0f sum=%-10d prod/N=%.2e  ratio=%.2f"%(str(ps),str(ds),e,S,P/N,e/S))
print("\n  ALL configs with prod p^d > N  (CRT says unaffordable):")
c=0
for e,S,P,mx,L,ps,ds in rows:
    if P>N:
        c+=1
        if c<=10: print("    prod/N=%-11.2e |err|/N=%-10.2e |err|/sum=%.3f   p=%s d=%s"%(P/N,e/N,e/S,ps,ds))
print("    ... %d such configs; max |err|/N among them = %.2e"%(c,max(e/N for e,S,P,*_ in rows if P>N)))
