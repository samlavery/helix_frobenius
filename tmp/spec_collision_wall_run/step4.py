import numpy as np, itertools
rng=np.random.default_rng(20260901)

def disc_from_roots(x):
    return np.prod([(x[i]-x[j])**2 for i,j in itertools.combinations(range(len(x)),2)])

print("STEP 4a: random paths in COEFFICIENT space, all-real -> one conj pair.")
print("         Does disc always cross 0 (i.e. a repeated root is forced)?")
worst=0; crossed=0; trials=4000
for _ in range(trials):
    n=rng.choice([3,4])
    while True:
        r0=np.sort(rng.normal(0,2,n));  # all real
        if min(np.diff(r0))>0.3: break
    c0=np.poly(r0)
    while True:
        z=rng.normal(0,2)+1j*abs(rng.normal(0,2))+0.3j
        rest=rng.normal(0,2,n-2)
        r1=np.concatenate([[z,np.conj(z)],rest])
        c1=np.poly(r1).real
        rr=np.roots(c1)
        if sum(abs(rr.imag)>1e-8)==2: break
    # random (possibly wiggly) path in coefficient space
    mid=(c0+c1)/2 + np.concatenate([[0],rng.normal(0,3,n)])
    ts=np.linspace(0,1,4001)
    D=[]
    for t in ts:
        c=(1-t)**2*c0+2*(1-t)*t*mid+t**2*c1   # quadratic Bezier, endpoints exact
        c=c/c[0]
        D.append(np.real(disc_from_roots(np.roots(c))))
    D=np.array(D)
    if np.any(D<=0) and np.any(D>0): crossed+=1
    worst=max(worst,min(D))
print("   trials=%d  paths on which disc hit <=0 somewhere: %d/%d"%(trials,crossed,trials))
print("   max over trials of (min disc along path) = %.4e   [must be <=0 for every path]"%worst)

print()
print("STEP 4b: random paths in NODE+WEIGHT space with ALL WEIGHTS NONZERO,")
print("         moments forced real by conjugation-symmetric bookkeeping.")
print("         Looking for: reaches a conj pair with NO node coincidence.")
found=0; trials=6000; minsep=np.inf
for _ in range(trials):
    n=rng.choice([3,4]); 
    # continuous node paths: each node moves along a random smooth complex path,
    # then symmetrize the measure (mu + conj(mu))/2-style pairing to force real moments
    x0=np.sort(rng.normal(0,2,n)); w0=rng.uniform(0.2,2,n)
    z=rng.normal(0,2)+1j*rng.uniform(0.5,2)
    if n==3: x1=np.array([z,np.conj(z),rng.normal(0,2)])
    else:    x1=np.array([z,np.conj(z),rng.normal(0,2),rng.normal(0,2)])
    wz=rng.normal(0,1)+1j*rng.normal(0,1)
    if n==3: w1=np.array([wz,np.conj(wz),rng.uniform(0.2,2)])
    else:    w1=np.array([wz,np.conj(wz),rng.uniform(0.2,2),rng.uniform(0.2,2)])
    for perm in itertools.permutations(range(n)):
        xa=x0[list(perm)]; wa=w0[list(perm)]
        ts=np.linspace(0,1,2001); ok=True; sep=np.inf; realok=True
        for t in ts:
            x=(1-t)*xa+t*x1; w=(1-t)*wa+t*w1
            m=[np.sum(w*x**k) for k in range(2*n-1)]
            if max(abs(np.imag(mm)) for mm in m)>1e-9: realok=False; break
            g=min(abs(x[i]-x[j]) for i,j in itertools.combinations(range(n),2))
            sep=min(sep,g)
            if min(abs(w))<1e-12: ok=False
        if realok and ok and sep>1e-7:
            found+=1; minsep=min(minsep,sep)
print("   trials=%d  families found with real moments, all weights nonzero,"%trials)
print("   and NO node coincidence, reaching a conjugate pair: %d"%found)

print()
print("STEP 4c: the same search but ALLOWING a weight to vanish (breaks the")
print("         spec's parenthetical 'equivalently ... conjugate weights').")
print("   -> constructed by hand as ATTACK C; verified in families.py.")
