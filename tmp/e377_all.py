import math
from sympy import primerange
def carryfree(n,p):
    while n:
        if n%p > (p-1)//2: return False
        n//=p
    return True
P=list(primerange(3,2_000_001))
def SE(n):
    S=[p for p in P if p<=n and carryfree(n,p)]
    return S, sum(1.0/p for p in S), sum(1-math.log((p+1)/2)/math.log(p) for p in S)
print('kappa = min_p p(1-s_p):')
for p in [3,5,7,11,13,101]:
    print('   p=%-4d  p(1-s_p)=%.4f'%(p,p*(1-math.log((p+1)/2)/math.log(p))))
kap=3*(1-math.log(2)/math.log(3)); print('kappa=%.5f  threshold E>1/kappa=%.5f\n'%(kap,1/kap))
best=[];exc=[]
N=2_000_000
for n in range(1,N+1):
    S,E,D=SE(n) if n<200000 else (None,None,None)
    if S is None: break
    best.append((E,n,D))
    if D>1.0: exc.append((n,E,D,S[:6]))
best.sort(reverse=True)
print('top E(n) for n<200000:')
for E,n,D in best[:8]: print('   n=%-7d E=%.4f  sum(1-s_p)=%.4f  %s'%(n,E,D,'DIM-0' if D>1 else ''))
print('\n#{n<200000 : sum(1-s_p)>1  (=> n in a dimension-zero set)} = %d'%len(exc))
for n,E,D,S in exc[:15]: print('   n=%-7d E=%.4f D=%.4f  S(n) starts %s'%(n,E,D,S))
