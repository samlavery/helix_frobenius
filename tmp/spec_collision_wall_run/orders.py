import sympy as sp, numpy as np, itertools
tau=sp.symbols('tau', real=True); s=sp.sqrt(tau)

def detH(nodes,wts,n):
    m=[sp.expand(sum(w*x**k for x,w in zip(nodes,wts))) for k in range(2*n-1)]
    H=sp.Matrix([[m[i+j] for j in range(n)] for i in range(n)])
    return sp.simplify(sp.expand(H.det()))

print("ATTACK A  nodes {s,-s,3+s,3-s}, weights 1,1,1,1   (tau = s^2 = 1-2t)")
dA=sp.factor(sp.simplify(detH([s,-s,3+s,3-s],[1,1,1,1],4)))
print("   det H(tau) =", dA)
print("   series at tau=0:", sp.series(sp.expand(dA),tau,0,4))
print("   order of zero at tau=0:", sp.Poly(sp.expand(dA),tau).monoms()[-1][0],
      "  value at tau=+1:",dA.subs(tau,1)," at tau=-1:",dA.subs(tau,-1))

print()
print("ATTACK B  nodes {5,s,-s}, weights {tau,1,1}   (tau = 1/2 - t)")
dB=sp.factor(sp.simplify(detH([5,s,-s],[tau,1,1],3)))
print("   det H(tau) =", dB)
print("   series at tau=0:", sp.series(sp.expand(dB),tau,0,4))
print("   value at tau=+1/2:",dB.subs(tau,sp.Rational(1,2))," at tau=-1/2:",dB.subs(tau,-sp.Rational(1,2)))

print()
print("PERTURBATION TEST (are the refuting families generic?)")
def sq(x): return np.sqrt(x) if x>=0 else 1j*np.sqrt(-x)
def dnum(nodes,wts,n):
    x=np.array(nodes,complex); w=np.array(wts,complex)
    m=[np.sum(w*x**k) for k in range(2*n-1)]
    return np.linalg.det(np.array([[m[i+j] for j in range(n)] for i in range(n)])).real
for eps in [0.0,1e-3,1e-2,5e-2]:
    # A perturbed: second pair merges at a DIFFERENT time (tau shifted by eps)
    vals=[dnum([sq(tau_),-sq(tau_),3+sq(tau_-eps),3-sq(tau_-eps)],[1,1,1,1],4)
          for tau_ in np.linspace(1,-1,20001)]
    # B perturbed: weight zero offset from the merge by eps
    valsB=[dnum([5,sq(tau_),-sq(tau_)],[tau_-eps,1,1],3)
           for tau_ in np.linspace(0.5,-0.5,20001)]
    print("   eps=%-6g  A: min det H = %+.4e   B: min det H = %+.4e"%(eps,min(vals),min(valsB)))
