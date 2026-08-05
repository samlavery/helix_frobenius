"""MULTI-FUNCTION ON ONE RAIL BANK: where do two fibers jointly cancel?
   Fiber A: E(n)   = sum_p (1/p) 1[n in G_p]        -- rails at FLOOR (#377)
   Fiber B: g_2(n) = max defect affordable          -- rails at CEILING (#400)
   Shared carrier point n; shared rails p.  Normalised spectrum (DC = 1):
        Spec_p(n) = s_p(n) / ((p-1)/2 * d_p)
   QUESTION: do A and B load on the SAME spectral modes (joint cancellation) or
   different ones?  And is the joint maximum better than independence predicts?"""
import numpy as np, math
from sympy import primerange
NM=1600; M=2*NM+60
ALL=[int(p) for p in primerange(2,NM+1)]
S={}
for p in ALL:
    a=np.arange(M); s=np.zeros(M,dtype=np.int64); t=a.copy()
    while t.max()>0: s+=t%p; t//=p
    S[p]=s
def g2(n):
    Ps=[p for p in ALL if p<=n]; best=0
    for G in range(1,40):
        A=n+G; a1=np.arange(0,A//2+1); m=None
        for p in Ps:
            v=S[p][a1]+S[p][A-a1]-S[p][n]
            m=v if m is None else np.minimum(m,v)
        if m.max()>=G: best=G
        else: break
    return best
def bal(n,p):
    D=(p-1)//2
    while n:
        if n%p>D: return False
        n//=p
    return True
RAILS=[2,3,5,7,11,13,17,19]
ns=np.arange(300,1601)
E=np.array([sum(1.0/p for p in ALL if p<=n and bal(int(n),p)) for n in ns])
G=np.array([g2(int(n)) for n in ns],dtype=float)
Gn=G/np.log(ns)
Spec=np.zeros((len(ns),len(RAILS)))
for j,p in enumerate(RAILS):
    d=np.floor(np.log(ns)/math.log(p))+1
    Spec[:,j]=S[p][ns]/((p-1)/2*d)
print("SPECTRUM loadings (correlation of each fiber with rail p's normalised digit sum)")
print(f"{'rail':>5} {'DC mean':>8} {'corr with E':>12} {'corr with g2/logn':>18}")
for j,p in enumerate(RAILS):
    print(f"{p:>5} {Spec[:,j].mean():>8.3f} {np.corrcoef(Spec[:,j],E)[0,1]:>+12.4f}"
          f" {np.corrcoef(Spec[:,j],Gn)[0,1]:>+18.4f}")
print(f"\n  corr(E, g2/log n) = {np.corrcoef(E,Gn)[0,1]:+.4f}")
# joint cancellation: does low spectrum on MANY rails simultaneously drive both?
lowcount=(Spec<0.85).sum(axis=1)
print(f"\nJOINT LOCUS: #rails with Spec_p < 0.85 (digit-poor) vs both fibers")
print(f"{'#poor rails':>12} {'#n':>5} {'mean E':>8} {'mean g2/logn':>13}")
for k in range(0,6):
    m=lowcount==k
    if m.sum()<5: continue
    print(f"{k:>12} {m.sum():>5} {E[m].mean():>8.4f} {Gn[m].mean():>13.4f}")
r=np.corrcoef(lowcount,E)[0,1]; r2=np.corrcoef(lowcount,Gn)[0,1]
print(f"\n  corr(#poor rails, E) = {r:+.4f}    corr(#poor rails, g2/logn) = {r2:+.4f}")
# independence test on the joint maximum
zE=(E-E.mean())/E.std(); zG=(Gn-Gn.mean())/Gn.std()
J=zE+zG
top=np.argsort(-J)[:10]
print(f"\n  joint-max n (z_E + z_g2): {[int(ns[i]) for i in top[:8]]}")
print(f"  best joint z-sum = {J[top[0]]:.3f}; independence would give ~"
      f"{math.sqrt(2)*math.sqrt(2*math.log(len(ns))):.3f} for uncorrelated unit normals")
print(f"  observed corr means joint sd = {math.sqrt(2+2*np.corrcoef(zE,zG)[0,1]):.3f}")
