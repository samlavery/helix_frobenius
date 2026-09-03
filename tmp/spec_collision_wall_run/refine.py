import numpy as np, itertools
rng=np.random.default_rng(2026)
def cfg(m,n):
    H=np.array([[m[i+j] for j in range(n)] for i in range(n)])
    d=np.linalg.det(H)
    a=np.linalg.solve(H,-np.array([m[n+i] for i in range(n)]))
    x=np.roots(np.concatenate([[1.0],a[::-1]]))
    V=np.vander(x,n,increasing=True).T
    return x,np.linalg.solve(V,m[:n]),d
def disc(x): return np.real(np.prod([(x[i]-x[j])**2 for i,j in itertools.combinations(range(len(x)),2)]))

# regenerate the FIRST hit exactly
for trial in range(3000):
    n=int(rng.choice([3,4]))
    x0=np.sort(rng.uniform(-3,3,n))
    if min(np.diff(x0))<0.5: continue
    w0=rng.uniform(0.3,2.0,n)
    m0=np.array([np.sum(w0*x0**k) for k in range(2*n)])
    z=rng.uniform(-2,2)+1j*rng.uniform(0.4,2.0); wz=rng.normal()+1j*rng.normal()
    xr=np.sort(rng.uniform(-3,3,n-2)); wr=rng.uniform(0.3,2.0,n-2)
    x1=np.concatenate([[z,np.conj(z)],xr]); w1=np.concatenate([[wz,np.conj(wz)],wr])
    m1=np.real(np.array([np.sum(w1*x1**k) for k in range(2*n)]))
    wig=rng.normal(0,np.max(np.abs(m1))+1,2*n)
    mp=lambda t:(1-t)**2*m0+2*(1-t)*t*((m0+m1)/2+wig)+t**2*m1
    try:
        mingap=np.inf; minw=np.inf
        for t in np.linspace(0,1,1201):
            x,w,d=cfg(mp(t),n)
            mingap=min(mingap,min(abs(x[i]-x[j]) for i,j in itertools.combinations(range(n),2)))
            minw=min(minw,min(abs(w)))
        xe,_,_=cfg(m1,n)
        if mingap>1e-6 and minw>1e-6 and sum(abs(xe.imag)>1e-8)>=2:
            break
    except Exception: continue

print("Reproduced hit: n=%d, coarse-grid mingap=%.4e, min|w|=%.3e"%(n,mingap,minw))
# locate sign change of det H, then REFINE
ts=np.linspace(0,1,1201); ds=[cfg(mp(t),n)[2].real for t in ts]
idx=[i for i in range(len(ts)-1) if ds[i]*ds[i+1]<0]
print("det H sign changes on coarse grid at t in:", [(round(ts[i],5),round(ts[i+1],5)) for i in idx])
lo,hi=ts[idx[0]],ts[idx[0]+1]
print("\nREFINING around the first crossing (this is where Prony degenerates):")
print("      t          det H        min node gap    min|w_i|      max|node|    disc")
for t in np.linspace(lo-2*(hi-lo),hi+2*(hi-lo),25):
    x,w,d=cfg(mp(t),n)
    g=min(abs(x[i]-x[j]) for i,j in itertools.combinations(range(n),2))
    print("  %.8f  %+.4e  %.4e  %.4e  %.4e  %+.4e"%(t,d.real,g,min(abs(w)),max(abs(x)),disc(x)))
print("\nnode sets just before / just after the crossing:")
xa,wa,_=cfg(mp(lo-1e-9),n); xb,wb,_=cfg(mp(hi+1e-9),n)
print("  before:",np.round(np.sort_complex(xa),5)," weights",np.round(wa,5))
print("  after :",np.round(np.sort_complex(xb),5)," weights",np.round(wb,5))
print("  Hausdorff-ish jump in node set: %.4e"%max(min(abs(a-b) for b in xb) for a in xa))
