import numpy as np, math
from sympy import nextprime
def digits_ok(n,p,d):
    m=np.ones(len(n),bool); x=n.copy()
    for _ in range(d):
        m &= (x%p)<=(p-1)//2; x=x//p
    return m
print("TEST: additive cost at DEPTH >= 2 (Cantor-set conditions, not intervals)")
print("  error of #{n<=N : first d_i base-p_i digits in D_{p_i}}  vs  sum p_i^d_i  and  prod p_i^d_i\n")
N=2*10**7
n=np.arange(1,N+1,dtype=np.int64)
rows=[]
for ps,ds in [([3,5],[8,5]),([3,5,7],[8,5,4]),([11,13],[4,4]),([101,103],[2,2]),
              ([31,37],[3,3]),([3,5,7,11],[8,5,4,3]),([1009,1013],[2,2])]:
    m=np.ones(N,bool); pred=1.0
    for p,d in zip(ps,ds):
        m &= digits_ok(n,p,d); pred*= (((p+1)//2)/p)**d
    obs=int(m.sum()); pred*=N
    S=sum(p**d for p,d in zip(ps,ds)); P=math.prod(p**d for p,d in zip(ps,ds))
    e=obs-pred
    rows.append((ps,ds,e,S,P,P/N))
    print("  p=%-18s d=%-14s err %+10.1f   sum p^d=%-12d prod p^d=%-16d (=%.2f N)"%(str(ps),str(ds),e,S,P,P/N))
    print("        |err|/sum = %-8.3f   |err|/prod = %.2e   |err|/N = %.2e"%(abs(e)/S,abs(e)/P,abs(e)/N))
