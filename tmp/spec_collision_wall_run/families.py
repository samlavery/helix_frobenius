import numpy as np, itertools, sympy as sp

def audit(name, nodes_fn, wts_fn, n, ts=None, verbose_pts=(0.0,0.5,1.0)):
    """Check ALL spec hypotheses + report det H, prod w, disc, min node gap."""
    if ts is None:
        ts=np.unique(np.concatenate([np.linspace(0,1,2001),
                                     0.5+np.linspace(-1e-3,1e-3,401)]))
        ts=ts[(ts>=0)&(ts<=1)]
    rows=[]
    maxim=0.0; mingap=np.inf; gap_argmin=None; negdet=[]
    for t in ts:
        x=np.array(nodes_fn(t),dtype=complex); w=np.array(wts_fn(t),dtype=complex)
        assert len(x)==n and len(w)==n
        m=np.array([np.sum(w*x**k) for k in range(2*n-1)])
        maxim=max(maxim,np.max(np.abs(m.imag)))
        H=np.array([[m[i+j] for j in range(n)] for i in range(n)])
        d=np.linalg.det(H)
        disc=np.prod([(x[i]-x[j])**2 for i,j in itertools.combinations(range(n),2)])
        pw=np.prod(w)
        g=min(abs(x[i]-x[j]) for i,j in itertools.combinations(range(n),2))
        if g<mingap: mingap=g; gap_argmin=t
        if d.real < -1e-9*max(1.0,abs(d)): negdet.append((t,d.real))
        rows.append((t,d,pw,disc,g))
    print("-"*70); print("FAMILY:",name)
    x0=np.array(nodes_fn(0.0),dtype=complex); w0=np.array(wts_fn(0.0),dtype=complex)
    x1=np.array(nodes_fn(1.0),dtype=complex); w1=np.array(wts_fn(1.0),dtype=complex)
    print("  t=0 nodes  :",np.round(x0,6),"  all real:",np.max(np.abs(x0.imag))<1e-12,
          "  distinct:",min(abs(x0[i]-x0[j]) for i,j in itertools.combinations(range(n),2))>1e-9)
    print("  t=0 weights:",np.round(w0,6),"  all POSITIVE real:",
          bool(np.all(w0.real>0) and np.max(np.abs(w0.imag))<1e-12))
    print("  t=1 nodes  :",np.round(x1,6),"  t=1 weights:",np.round(w1,6))
    nr=[i for i in range(n) if abs(x1[i].imag)>1e-9]
    paired=all(any(abs(x1[j]-np.conj(x1[i]))<1e-9 and abs(w1[j]-np.conj(w1[i]))<1e-9
                   for j in range(n) if j!=i) for i in nr) and len(nr)>0
    print("  t=1 has a genuine non-real CONJUGATE PAIR (nodes & weights):",paired,
          " (#non-real nodes =",len(nr),")")
    print("  max |Im m_k| over grid, k<=%d: %.2e   (moments real)"%(2*n-2,maxim))
    err=max(abs(r[1]-r[2]*r[3]) for r in rows)
    print("  max |det H - (prod w)*disc| = %.3e   (setup check)"%err)
    print("  min pairwise node gap over grid = %.3e at t=%.6f"%(mingap,gap_argmin))
    print("  det H < 0 anywhere on grid? ", "YES at t=%.4f (%.4g)"%negdet[0] if negdet else "NO")
    for tv in verbose_pts:
        x=np.array(nodes_fn(tv),dtype=complex); w=np.array(wts_fn(tv),dtype=complex)
        m=np.array([np.sum(w*x**k) for k in range(2*n-1)])
        H=np.array([[m[i+j] for j in range(n)] for i in range(n)])
        print("    t=%.5f  detH=%+.6e  prodw=%+.4g  disc=%+.4g  mingap=%.3e"%(
            tv,np.linalg.det(H).real,np.prod(w).real,
            np.prod([(x[i]-x[j])**2 for i,j in itertools.combinations(range(n),2)]).real,
            min(abs(x[i]-x[j]) for i,j in itertools.combinations(range(n),2))))
    return rows

def sq(tau):  # continuous branch: sqrt(tau) real for tau>=0, i*sqrt(-tau) for tau<0
    return np.sqrt(tau) if tau>=0 else 1j*np.sqrt(-tau)

# ---------------- CONTROL: generic single transversal transition, n=3 ----------
# nodes 5, +-s ; tau = 1/2 - t ; weights all 1  -> det H should CHANGE SIGN
audit("CONTROL n=3 single merge, weights==1 (expect sign change)",
      lambda t:[5.0, sq(0.5-t), -sq(0.5-t)], lambda t:[1.0,1.0,1.0], 3)

# ---------------- ATTACK A on (C.2): simultaneous DOUBLE merge, r2: 0 -> 2 ----
# nodes  +-s , 3+-s  with the SAME s ; tau = 1-2t ; ALL WEIGHTS == 1 (positive!)
audit("ATTACK A  n=4 simultaneous double merge, weights==1, r2: 0 -> 2",
      lambda t:[sq(1-2*t), -sq(1-2*t), 3+sq(1-2*t), 3-sq(1-2*t)],
      lambda t:[1.0,1.0,1.0,1.0], 4)

# ---------------- ATTACK B on (C.2): weight zero AT the merge (author's flag) --
# nodes 5, +-s with tau = 1/2 - t ; w1 = tau (crosses 0 exactly at the merge)
audit("ATTACK B  n=3 merge with weight vanishing simultaneously, r2: 0 -> 1",
      lambda t:[5.0, sq(0.5-t), -sq(0.5-t)], lambda t:[0.5-t,1.0,1.0], 3)

# ---------------- ATTACK C on (C.1): zero weights break the parenthetical -----
def nodesC(t):
    if t<=0.5: return [-1.0,0.0,1.0,2.0]
    u=2*t-1
    return [-1.0,0.0,1.0+1j*u,2.0-u*(1+1j)]
def wtsC(t):
    w=max(0.0,1-2*t)
    return [1.0,1.0,w,w]
audit("ATTACK C  n=4 no node ever coincides (weights -> 0), r2 endpoint = 1",
      nodesC,wtsC,4,verbose_pts=(0.0,0.5,0.75,1.0))
