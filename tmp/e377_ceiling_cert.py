"""SHARPENED CEILING CERTIFICATE.
   For admissible S (cost<=1): split T = S cap [3,P), U = S cap [P,inf).
   KEY: every p in U must INDIVIDUALLY satisfy beta_p <= b_T := 1-cost(T),
   so p >= x(b_T) where beta(x(b))=b.  Hence
        pay(U) <= r(max(P, x(b_T))) * b_T ,     r(x) = (1/x)/beta(x)  decreasing.
   Bound = max over T of [ pay(T) + that ]."""
import math
from sympy import isprime
from itertools import combinations
def beta(x): return math.log(2*x/(x+1))/math.log(x)
def ratio(x): return (1.0/x)/beta(x)
def xof(b):                      # solve beta(x)=b, b in (0, beta(3))
    lo,hi=3.0,1e300
    if b>=beta(3.0): return 3.0
    for _ in range(600):
        m=math.sqrt(lo*hi)
        if beta(m)>b: lo=m
        else: hi=m
    return lo
C=1/3+1/5+1/7
for P in [41,101]:
    small=[p for p in range(3,P) if isprime(p)]
    bmin=beta(small[-1]); kmax=int(1.0/bmin)
    best=-1; argb=None; rows=[]
    for k in range(0,min(kmax,len(small))+1):
        for T in combinations(small,k):
            c=sum(beta(p) for p in T)
            if c>1: continue
            b=1.0-c
            xr=max(float(P), xof(b))
            v=sum(1.0/p for p in T)+ratio(xr)*b
            rows.append((v,T,b,xr))
            if v>best: best,argb=v,T
    rows.sort(reverse=True)
    print(f"P={P}   |T|<= {kmax}   subsets scanned: {len(rows)}")
    print(f"   {'bound':>18} {'excess over C':>15} {'T':<22} {'budget b_T':>12} {'x(b_T)':>12}")
    for (v,T,b,xr) in rows[:6]:
        print(f"   {v:>18.15f} {v-C:>15.4g} {str(T):<22} {b:>12.6g} {xr:>12.6g}")
    print(f"   ==> CEILING  pay(S) <= {best:.15f} = C + {best-C:.4g}\n")
