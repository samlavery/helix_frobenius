import numpy as np, itertools
rng=np.random.default_rng(7)
def disc(x): return np.real(np.prod([(x[i]-x[j])**2 for i,j in itertools.combinations(range(len(x)),2)]))

# 4a: does disc always cross zero on a path r2=0 -> r2=1 ?  (wiggly Bezier paths)
worst=-np.inf; trials=1500
for _ in range(trials):
    n=int(rng.choice([3,4]))
    r0=np.sort(rng.normal(0,2,n))
    if min(np.diff(r0))<0.3: continue
    c0=np.poly(r0)
    z=rng.normal(0,2)+1j*(0.3+abs(rng.normal(0,2)))
    r1=np.concatenate([[z,np.conj(z)],rng.normal(0,2,n-2)])
    c1=np.real(np.poly(r1))
    if sum(abs(np.roots(c1).imag)>1e-8)!=2: continue
    mid=(c0+c1)/2+np.concatenate([[0],rng.normal(0,3,n)])
    D=[]
    for t in np.linspace(0,1,801):
        c=(1-t)**2*c0+2*(1-t)*t*mid+t**2*c1; c=c/c[0]
        D.append(disc(np.roots(c)))
    worst=max(worst,min(D))
print("4a  max over %d random wiggly paths of (min disc along path) = %.3e"%(trials,worst))
print("    (>0 would be a C.1 counterexample; <=0 means a repeated root is forced)")

# 4b: with all weights nonzero, must real moments force conjugation-stability?
bad=0
for _ in range(200000):
    n=int(rng.choice([2,3,4]))
    x=rng.normal(0,2,n)+1j*rng.normal(0,2,n); w=rng.normal(0,2,n)+1j*rng.normal(0,2,n)
    m=np.array([np.sum(w*x**k) for k in range(2*n)])
    if max(abs(m.imag))<1e-9 and min(abs(w))>1e-9:
        st=all(any(abs(x[j]-np.conj(x[i]))<1e-7 and abs(w[j]-np.conj(w[i]))<1e-7
                   for j in range(n)) for i in range(n))
        if not st: bad+=1
print("4b  random configs with real moments + all weights nonzero that are NOT")
print("    conjugation-stable:",bad,"(0 = the parenthetical holds when no weight vanishes)")
