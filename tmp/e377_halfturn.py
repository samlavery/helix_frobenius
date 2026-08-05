"""CLAIM: n in G_p  <=>  {n/p^j} < 1/2  for all j>=1.   (uniform half-turn, no sliver)
   Then the indicator per scale is the PURE square wave: odd harmonics only, 1/k decay.
   The 'even lane' (sec, no decay) of the old reading was a wrong-scale artifact."""
import math, cmath
def bal_digits(n,p):
    D=(p-1)//2
    while n:
        if n%p>D: return False
        n//=p
    return True
def bal_halfturn(n,p):
    j=1
    while p**j<=2*n:
        if (n % p**j)*2 >= p**j: return False
        j+=1
    return True
print("EQUIVALENCE CHECK  (digit criterion vs half-turn criterion)")
bad=0; tot=0
for p in [3,5,7,11,13,17,101,1009]:
    for n in range(0, 60000):
        tot+=1
        if bal_digits(n,p)!=bal_halfturn(n,p):
            bad+=1
            if bad<4: print(f"   MISMATCH p={p} n={n}")
print(f"   checked {tot} (n,p) pairs -> mismatches: {bad}\n")

print("FOURIER LANES of the per-scale indicator on Z/p  (threshold 1/2 vs (p+1)/2p)")
print(f"{'p':>6} {'alpha':>6} {'|hat| half-turn':>17} {'|hat| old (p+1)/2p':>19} "
      f"{'1/(2p)csc':>11} {'1/(2p)sec':>11}")
print("-"*80)
for p in [11,101]:
    for a in [1,2,3,4]:
        # half-turn: indicator of {r : 2r < p^1}, i.e. r <= (p-1)/2  -- same set on Z/p!
        s1=sum(cmath.exp(2j*cmath.pi*a*r/p) for r in range(p) if 2*r<p)
        s2=sum(cmath.exp(2j*cmath.pi*a*r/p) for r in range(p) if r<=(p-1)//2)
        x=math.pi*a/(2*p)
        print(f"{p:>6} {a:>6} {abs(s1)/p:>17.8f} {abs(s2)/p:>19.8f} "
              f"{1/(2*p)/math.sin(x):>11.8f} {1/(2*p)/math.cos(x):>11.8f}")
print("\nSCALE p^2: is the threshold-1/2 set on Z/p^2 the SAME as 'both digits small'?")
for p in [5,7]:
    A=set(r for r in range(p*p) if 2*r<p*p and 2*(r%p)<p)
    B=set(r for r in range(p*p) if (r%p)<=(p-1)//2 and (r//p)<=(p-1)//2)
    print(f"   p={p}: |A|={len(A)} |B|={len(B)}  identical: {A==B}   ((p+1)/2)^2={((p+1)//2)**2}")
