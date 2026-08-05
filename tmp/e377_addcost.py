import numpy as np, math
from sympy import nextprime
print("TEST: is the joint interval-condition error ADDITIVE (sum p_i) or MULTIPLICATIVE (prod p_i)?")
print("count #{n<=N : n mod p_i < p_i/2 for all i}  vs  N*prod(ceil(p_i/2)/p_i)\n")
def err(N,ps):
    n=np.arange(1,N+1,dtype=np.int64)
    m=np.ones(N,bool)
    for p in ps: m &= (n%p) < (p+1)//2
    obs=m.sum(); pred=N*np.prod([((p+1)//2)/p for p in ps])
    return obs-pred, math.prod(ps), sum(ps)
for N in [10**6, 4*10**6]:
    print(" N = %d"%N)
    for kk in [2,3,4]:
        r=int(N**(1.0/(kk+0.001)))     # p_i ~ N^{1/k} so prod ~ N
        ps=[]; x=r
        for _ in range(kk): x=nextprime(x); ps.append(int(x))
        e,pr,sm=err(N,ps)
        print("   k=%d  p=%s"%(kk,ps))
        print("        error %+10.1f   sum p = %-10d  prod p = %-14d  |err|/sum = %.3f  |err|/prod = %.5f"
              %(e,sm,pr,abs(e)/sm,abs(e)/pr))
    # large primes: p ~ sqrt(N), two rails, prod ~ N  (the case CRT calls unaffordable)
    ps=[int(nextprime(int(N**0.5))), int(nextprime(int(N**0.5)+1000))]
    e,pr,sm=err(N,ps)
    print("   two rails at sqrt(N): p=%s   error %+.1f   sum %d  prod %d  |err|/sum %.3f"%(ps,e,sm,pr,abs(e)/sm))
    print()
