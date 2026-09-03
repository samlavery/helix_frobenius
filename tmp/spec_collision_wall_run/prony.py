import numpy as np, itertools
rng=np.random.default_rng(11)
# Build measures from RANDOM REAL MOMENTS via Prony: guarantees real moments,
# generically all weights nonzero. Check conjugation stability of (node,weight).
bad=0; hits=0; nonreal=0
for _ in range(20000):
    n=int(rng.choice([2,3,4]))
    m=rng.normal(0,1,2*n)                      # real moments m_0..m_{2n-1}
    H=np.array([[m[i+j] for j in range(n)] for i in range(n)])
    b=-np.array([m[n+i] for i in range(n)])
    if abs(np.linalg.det(H))<1e-8: continue
    a=np.linalg.solve(H,b)                     # p(X)=X^n + a_{n-1}X^{n-1}+...
    x=np.roots(np.concatenate([[1.0],a[::-1]]))
    V=np.vander(x,n,increasing=True).T         # V[k,i]=x_i^k
    if np.linalg.cond(V)>1e10: continue
    w=np.linalg.solve(V,m[:n])
    if min(abs(w))<1e-8: continue
    hits+=1
    if max(abs(x.imag))>1e-8: nonreal+=1
    st=all(any(abs(x[j]-np.conj(x[i]))<1e-6 and abs(w[j]-np.conj(w[i]))<1e-6
               for j in range(n)) for i in range(n))
    if not st: bad+=1
print("Prony test: %d valid configs (%d containing non-real nodes)."%(hits,nonreal))
print("Configs with real moments + all weights nonzero that are NOT conjugation-stable:",bad)
