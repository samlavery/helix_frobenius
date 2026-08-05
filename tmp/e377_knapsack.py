import math, sys
from sympy import isprime
from itertools import combinations
def beta(p): return math.log(2*p/(p+1))/math.log(p)
def pay(S):  return sum(1.0/p for p in S)
def cost(S): return sum(beta(p) for p in S)
def ratio(p): return (1.0/p)/beta(p)
C = 1/3+1/5+1/7
base=[3,5,7]; b0 = 1.0-cost(base)
print(f"pay(3,5,7) = {pay(base):.15f}  cost = {cost(base):.9f}  leftover b0 = {b0:.9f}", flush=True)
a,b = 1e6, 1e14
for _ in range(300):
    m=(a+b)/2
    if beta(m) > b0: a=m
    else: b=m
print(f"real threshold x* = {a:.10g}   beta(x*) = {beta(a):.12f}", flush=True)
q=int(a)+1
while not isprime(q): q+=1
print(f"smallest prime q* = {q}  beta(q*) = {beta(q):.12f}  < b0 : {beta(q)<b0}", flush=True)
print(f"  => dim({{3,5,7,q*}}) = {b0-beta(q):.4g} > 0   pay = C + {1/q:.6g}", flush=True)
b1=b0-beta(q)
print(f"\nafter q*: budget b1 = {b1:.6g}; ratio(x*) = {ratio(a):.6g}; further payoff <= {ratio(a)*b1:.6g}", flush=True)
eta_hi = 1/q + ratio(a)*b1
print(f"  eta in ( {1/q:.6g} , {eta_hi:.6g} ]      SUPREMUM = C + eta,  eta < {eta_hi:.3g}", flush=True)
print(f"\ncertificate  pay(S) <= max_T [pay(T)+ratio(P)(1-cost(T))]:", flush=True)
for P,kmax in [(11,4),(41,5),(101,5)]:
    small=[p for p in range(3,P) if isprime(p)]
    best=-1; argb=None
    for k in range(0,min(kmax,len(small))+1):
        for T in combinations(small,k):
            c=cost(T)
            if c>1: continue
            v=pay(T)+ratio(P)*(1-c)
            if v>best: best,argb=v,T
    print(f"   P={P:<5} bound={best:.12f}  excess over C = {best-C:.4g}  at T={argb}", flush=True)
prev=1e9; ok=True
print("\nratio 1/p per beta_p:", flush=True)
for p in [3,5,7,11,13,17,19,23,29,31,37,41,101,1009,10007,100003]:
    r=ratio(p); ok &= (r<prev); prev=r
    print(f"   p={p:<8} beta={beta(p):.6f}  1/p={1/p:.6g}  ratio={r:.6g}", flush=True)
print(f"   strictly decreasing: {ok}", flush=True)
