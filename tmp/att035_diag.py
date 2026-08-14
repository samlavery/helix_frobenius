"""Diagnostic: is BGSTB's j_M feasible in my discretised SDP at W=1, S=1?
If yes and the SDP reports a HIGHER value, the SDP is broken.  Fail by structure."""
import numpy as np, cvxpy as cp
r2 = np.sqrt(2.0)
jF = lambda a: max(0.0, 1.0 - abs(a))
def jM(a):
    t = jF(a); return ((0.5/r2)*np.sin(r2*t) + 0.5*t*np.cos(r2*a))/(1-np.cos(r2))

def model(S, D, W, dip, edge_gauge):
    n = int(round(S/D)); x = np.arange(n)*D; sech = 1.0/np.cosh(x*W)
    Q = cp.Variable((n,n), symmetric=True)
    b = cp.hstack([cp.trace(Q)] + [sum(Q[k,k+j] for k in range(n-j)) for j in range(1,n)])
    c = cp.multiply(sech, b)
    w1 = np.where(x <= 1.0, x, 0.0)*2.0; w1[0] = D/2.0
    cons = [Q >> 0, c[0] + 2*cp.sum(c[1:]) == 1]
    if dip: cons.append(c[x >= 1.0-1e-12] <= 0)
    if edge_gauge: cons.append(b[n-1] == 0)
    return cp.Problem(cp.Minimize(c[0]/D + w1@c), cons), x, sech, D

def eval_point(bvals, x, sech, D):
    c = sech*bvals; w1 = np.where(x <= 1.0, x, 0.0)*2.0; w1[0] = D/2.0
    return (c[0]/D + w1@c)/(c[0] + 2*c[1:].sum())

def cos_poly_min(bvals, D, m=20001):
    th = np.linspace(0, np.pi, m)
    return (bvals[0] + 2*sum(bvals[j]*np.cos(j*th) for j in range(1, len(bvals)))).min()

print("W=1, S=1.  BGSTB print Z(j_M) = 1.3825236, Z(j_F) = 1.3913871")
for D in (0.04, 0.02, 0.01, 0.005):
    n = int(round(1.0/D)); x = np.arange(n)*D; sech = 1/np.cosh(x)
    bM = np.array([D*jM(xx) for xx in x]); bF = np.array([D*jF(xx) for xx in x])
    print(f"  D={D:<6} sampled j_M value = {eval_point(bM,x,sech,D):.7f}  "
          f"min cos-poly(b_M) = {cos_poly_min(bM,D):+.3e}  (feasible iff >=0)")
    print(f"          sampled j_F value = {eval_point(bF,x,sech,D):.7f}  "
          f"min cos-poly(b_F) = {cos_poly_min(bF,D):+.3e}")
    for eg in (True, False):
        p, *_ = model(1.0, D, 1.0, False, eg); p.solve(solver=cp.CLARABEL)
        print(f"          SDP edge_gauge={eg!s:5} -> {p.value:.7f} [{p.status}]")

print("\nSame diagnostic at W=0 (positive control: must reach 1.3274993):")
for D in (0.04, 0.02):
    n = int(round(1.0/D)); x = np.arange(n)*D; sech = np.ones(n)
    bM = np.array([D*jM(xx) for xx in x])
    print(f"  D={D}: sampled j_M at W=0 -> {eval_point(bM,x,sech,D):.7f}")
    for eg in (True, False):
        p, *_ = model(1.0, D, 0.0, False, eg); p.solve(solver=cp.CLARABEL)
        print(f"        SDP edge_gauge={eg!s:5} -> {p.value:.7f} [{p.status}]")
