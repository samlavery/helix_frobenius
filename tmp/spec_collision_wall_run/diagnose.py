import numpy as np, itertools
rng=np.random.default_rng(2026)
def cfg(m,n):
    H=np.array([[m[i+j] for j in range(n)] for i in range(n)])
    d=np.linalg.det(H)
    if abs(d)<1e-13: return None,None,d
    a=np.linalg.solve(H,-np.array([m[n+i] for i in range(n)]))
    x=np.roots(np.concatenate([[1.0],a[::-1]]))
    V=np.vander(x,n,increasing=True).T
    return x,np.linalg.solve(V,m[:n]),d

hits=[]
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
    mingap=np.inf; minw=np.inf; maxabs=0; mind=np.inf; sgns=set(); bad=False
    for t in np.linspace(0,1,1201):
        m=(1-t)**2*m0+2*(1-t)*t*((m0+m1)/2+wig)+t**2*m1
        x,w,d=cfg(m,n)
        if x is None: bad=True; break
        mingap=min(mingap,min(abs(x[i]-x[j]) for i,j in itertools.combinations(range(n),2)))
        minw=min(minw,min(abs(w))); maxabs=max(maxabs,max(abs(x)))
        mind=min(mind,abs(d)); sgns.add(int(np.sign(d.real)))
    xe,we,_=cfg(m1,n)
    if bad or xe is None or sum(abs(xe.imag)>1e-8)<2: continue
    if mingap>1e-6 and minw>1e-6:
        hits.append((n,mingap,minw,maxabs,mind,sorted(sgns)))
print("hits:",len(hits))
print("  n  mingap     min|w|     MAX|node|   min|detH|   sign(detH) seen")
for h in hits[:15]:
    print("  %d  %.3e  %.3e  %.4e  %.3e  %s"%h)
print()
print("max node magnitude over all hits: %.4e"%max(h[3] for h in hits))
print("hits where a node exceeded 1e3 in magnitude: %d/%d"%(sum(h[3]>1e3 for h in hits),len(hits)))
print("hits where det H kept a single sign:        %d/%d"%(sum(len(h[5])==1 for h in hits),len(hits)))
