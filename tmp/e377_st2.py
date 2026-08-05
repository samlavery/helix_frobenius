import math, random
from mpmath import mp, siegeltheta
mp.dps=25
C=[10,756,757,3160,3186,3187,3250,7560,7561,7651,20007,59548377,59548401,45773612811,45775397187]
def base3set(lo,hi):
    out=[0]; pw=1
    while pw<=hi:
        out=[a+d*pw for a in out for d in (0,1) if a+d*pw<=hi]
        pw*=3
    return [x for x in set(out) if lo<=x<=hi]
def ks(x):
    x=sorted(x); m=len(x)
    return max(max(abs((i+1)/m-v),abs(v-i/m)) for i,v in enumerate(x))
def stat(ns,f): return ks([f(n)%1 for n in ns])
th=lambda n: float(siegeltheta(math.log(n)))/math.pi
l3=lambda n: math.log(n,3)
print("CORRECTED TEST: control = magnitude-matched draws from the SAME base-3 restricted set")
print("  (the census is a subset of {n : base-3 digits in {0,1}}, so that is the null)\n")
# magnitude bins matching the census clusters
bins=[(4,3**3),(3**5,3**7),(3**7,3**8),(3**8,3**9),(3**9,3**10),(3**16,3**17),(3**21,3**23)]
pool={b:base3set(*b) for b in bins}
assign=[]
for n in C:
    for b in bins:
        if b[0]<=n<=b[1]: assign.append(b); break
    else: assign.append(bins[-1])
random.seed(0)
for name,f in [("frac theta(log n)/pi",th),("frac log_3 n",l3)]:
    obs=stat(C,f)
    ctrl=[]
    for _ in range(3000):
        s=[random.choice(pool[b]) for b in assign]
        ctrl.append(stat(s,f))
    ctrl.sort(); p=sum(1 for c in ctrl if c>=obs)/len(ctrl)
    print("  %-22s observed KS = %.4f | control mean %.4f, 95th %.4f | p = %.3f  %s"
          %(name,obs,sum(ctrl)/len(ctrl),ctrl[int(.95*len(ctrl))],p,"NULL" if p>0.05 else "significant"))
print("\n  sanity: frac log_3 n is confined to [0, log_3(3/2)=%.4f] for EVERY base-3 restricted n"%math.log(1.5,3))
print("  census range: [%.4f, %.4f]   -> the earlier 'significance' was the digit set, not the census"
      %(min(l3(n)%1 for n in C),max(l3(n)%1 for n in C)))
