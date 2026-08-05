"""Decade growth of the simultaneous-Benford sup: max M1 per decade
(random ticks + smooth-anchored candidates)."""
import numpy as np, math
def primes_to(m):
    s=np.ones(m+1,bool); s[:2]=False
    for i in range(2,int(m**.5)+1):
        if s[i]: s[i*i::i]=False
    return [int(q) for q in np.nonzero(s)[0]]
P=[p for p in primes_to(2000) if p>=3]
def M1(xv):
    m=0.0
    for p in P:
        pk=p
        while pk*p<=xv: pk*=p
        if 2*(xv//pk) < p: m+=1.0/p
    return m
rng=np.random.default_rng(380)
from itertools import product as iproduct
for E in (8,10,12,14,16,18):
    lo,hi=10**E,10**(E+1) if E<18 else 9*10**18
    best=0.0; bx=0
    for xv in rng.integers(lo,min(hi,9*10**18),40000):
        v=M1(int(xv))
        if v>best: best,bx=v,int(xv)
    # smooth-anchored: x = c * prod small primes^a near decade, c in [1,2)
    cands=[]
    base=[3,5,7,11,13,17]
    for _ in range(4000):
        S=1
        for p in rng.permutation(base):
            while S*p<lo and rng.random()<0.6: S*=p
        if S>=lo//1000:
            for mult in (1,2,3):
                x=S*mult
                while x<lo: x*=2
                if x<min(hi,9*10**18): cands.append(x)
    for xv in cands:
        v=M1(xv)
        if v>best: best,bx=v,xv
    print(f"decade 1e{E}: sup M1 ~ {best:.4f} at {bx}")
