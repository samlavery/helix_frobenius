"""CARRY CONSERVATION.  Kummer: v_p C(2n,n) = kappa_p(n) = #carries in n+n base p.
   Exact: sum_p kappa_p log p = log C(2n,n).
   For p > sqrt(2n), kappa_p in {0,1}, and small primes contribute <= psi(sqrt 2n).
   PREDICTION (unconditional, every n, no equidistribution):
       sum_{sqrt(2n) < p <= 2n,  p nmid C(2n,n)}  log p  =  2n(1-log 2) + o(n).
   Also: does the law say anything about SMALL primes?  Measure its support."""
import numpy as np, math
def sieve(N):
    s=np.ones(N+1,bool); s[:2]=False
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]
def bal(n,p):
    D=(p-1)//2
    while n:
        if n%p>D: return False
        n//=p
    return True
print(f"{'n':>9} {'theta-bal / n':>14} {'2(1-log2)':>11} {'ratio':>8} "
      f"{'small-p share':>14} {'Mertens E(n)':>13}")
print("-"*80)
tgt=2*(1-math.log(2))
for n in [10**4, 10**5, 10**6, 3*10**6]:
    ps=sieve(2*n); r=int(math.isqrt(2*n))
    lg=np.log(ps.astype(float))
    balmask=np.array([bal(n,int(p)) for p in ps])
    big=ps>r
    thb=float(lg[big & balmask].sum())
    # what fraction of the conservation law's total mass sits on p <= sqrt(2n)?
    small=ps<=r
    ksmall=0.0
    for p in ps[small]:
        p=int(p); k=0; m=n; s2=0
        # carries = (2 s_p(n) - s_p(2n))/(p-1)
        a=n; b=2*n; sa=0; sb=0
        while a: sa+=a%p; a//=p
        while b: sb+=b%p; b//=p
        ksmall += (2*sa-sb)//(p-1)*math.log(p)
    tot=float(math.lgamma(2*n+1)-2*math.lgamma(n+1))
    E=float(np.sum(1.0/ps[balmask & (ps<=n)]))
    print(f"{n:>9} {thb/n:>14.6f} {tgt:>11.6f} {thb/(n*tgt):>8.4f} "
          f"{ksmall/tot:>14.6f} {E:>13.6f}")
print(f"\n  2(1-log2) = {tgt:.6f}   <- theta-weighted balanced density, PINNED")
