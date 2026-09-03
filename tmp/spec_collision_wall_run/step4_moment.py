import numpy as np, itertools, sys
rng=np.random.default_rng(2026)
def cfg(m,n):
    H=np.array([[m[i+j] for j in range(n)] for i in range(n)])
    d=np.linalg.det(H)
    if abs(d)<1e-13: return None,None,d
    a=np.linalg.solve(H,-np.array([m[n+i] for i in range(n)]))
    x=np.roots(np.concatenate([[1.0],a[::-1]]))
    V=np.vander(x,n,increasing=True).T
    w=np.linalg.solve(V,m[:n])
    return x,w,d

print("STEP 4 (moment space): straight + wiggly REAL-moment paths from an")
print("all-real positive-weight configuration to a conjugate-pair configuration.")
print("Tracking min node gap, min |w_i|, and det H along each path.\n")
gap_ok=0; tried=0
best=None
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
    tried+=1
    mingap=np.inf; minw=np.inf; sgn=[]; ok=True
    for t in np.linspace(0,1,1201):
        m=(1-t)**2*m0+2*(1-t)*t*((m0+m1)/2+wig)+t**2*m1
        x,w,d=cfg(m,n)
        sgn.append(np.sign(d.real) if abs(d)>1e-12 else 0.0)
        if x is None: mingap=0.0; minw=0.0; break
        mingap=min(mingap,min(abs(x[i]-x[j]) for i,j in itertools.combinations(range(n),2)))
        minw=min(minw,min(abs(w)))
    xe,we,_=cfg(m1,n)
    if xe is None or sum(abs(xe.imag)>1e-8)<2: continue
    if mingap>1e-6 and minw>1e-6:
        gap_ok+=1; best=(n,mingap,minw)
    if best is None or mingap>0: pass
print("   usable paths: %d   paths reaching a conj pair with NO node coincidence"%tried)
print("   AND no vanishing weight: %d"%gap_ok)
print("   (any such path would REFUTE C.1)")
sys.stdout.flush()
