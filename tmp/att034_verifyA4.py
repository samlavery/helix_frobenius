#!/usr/bin/env python3
"""
att034_verifyA4.py -- FAST rebuild of my independent SDP (same maths, cheap
canonicalisation).  All linear functionals are written as <M,Q>.

  min <G,Q>   s.t.  <Sm,Q> = 1,  <Theta_k,Q> <= 0 for x_k > 1,  Q >= 0
  G[i,j]  = g(|i-j|),  g(0)=1/Delta,  g(k)= x_k sech(2A x_k) for 1<=x_k<=1, else 0
  Sm[i,j] = sech(2A|i-j|Delta)
Equivalent to att034_verifyA.py by direct algebra; re-validated on the S=1 control.
"""
import sys, time
import numpy as np, cvxpy as cp
import scipy.sparse as sp

MT = 0.5 + (1/np.sqrt(2))/np.tan(1/np.sqrt(2))

def build(S, A, Delta, bmode='inside'):
    m = int(round(S/Delta))
    x = Delta*np.arange(m)
    s = 1.0/np.cosh(2*A*x)
    g = np.zeros(m); g[0] = 1.0/Delta
    tol = 1e-12
    dip = []
    for k in range(1, m):
        if x[k] < 1.0 - tol:
            g[k] = x[k]*s[k]
        elif abs(x[k]-1.0) < tol:
            if bmode == 'inside':   g[k] = x[k]*s[k]
            elif bmode == 'half':   g[k] = 0.5*x[k]*s[k]
            elif bmode == 'outside': dip.append(k)
        else:
            dip.append(k)
    I = np.arange(m)
    D = np.abs(I[:, None] - I[None, :])
    G = g[D]
    Sm = s[D]
    return m, x, s, G, Sm, dip

def solve(S, A, Delta, bmode='inside', solver='CLARABEL'):
    m, x, s, G, Sm, dip = build(S, A, Delta, bmode)
    Q = cp.Variable((m, m), symmetric=True)
    cons = [Q >> 0, cp.sum(cp.multiply(Sm, Q)) == 1]
    if dip:
        rows, cols, vals = [], [], []
        for r, k in enumerate(dip):
            for i in range(m-k):
                rows += [r, r]; cols += [i*m+(i+k), (i+k)*m+i]; vals += [0.5, 0.5]
        Aop = sp.csr_matrix((vals, (rows, cols)), shape=(len(dip), m*m))
        cons.append(Aop @ cp.reshape(Q, (m*m,), order='C') <= 0)
    prob = cp.Problem(cp.Minimize(cp.sum(cp.multiply(G, Q))), cons)
    try:
        prob.solve(solver=solver)
    except Exception as e:
        return None, None, x, "FAIL "+str(e)[:30]
    if Q.value is None:
        return None, None, x, prob.status
    b = np.array([np.trace(Q.value, offset=k) for k in range(m)])
    return prob.value, b*s, x, prob.status

if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'all'

    if what in ('all', 'ctrl'):
        print("="*80); print("RE-VALIDATE fast build on the S=1, A=0 control"); print("="*80)
        for D in [0.04, 0.02, 0.01, 0.005]:
            t = time.time(); v, cv, x, st = solve(1.0, 0.0, D)
            print("  Delta=%.4f  Z=%.8f  err=%+.3e  [%s]  %.1fs" % (D, v, v-MT, st, time.time()-t))

    if what in ('all', 'bdry'):
        print("\n"+"="*80)
        print("D1  S=2, A=0: boundary-atom convention (reported: 1.3207926 at Delta=.04)")
        print("="*80)
        for D in [0.04, 0.02, 0.01]:
            out = []
            for bm in ['inside', 'outside', 'half']:
                t = time.time(); v, cv, x, st = solve(2.0, 0.0, D, bmode=bm)
                out.append("%s=%.7f" % (bm, v))
            print("  Delta=%.3f  " % D + "  ".join(out))
        print("\n  atom profile near alpha=1, Delta=0.04, bmode=inside:")
        v, cv, x, st = solve(2.0, 0.0, 0.04, bmode='inside')
        i1 = int(round(1.0/0.04))
        for k in range(i1-3, min(i1+4, len(x))):
            print("    x=%.3f  c_k=%+.6f  density c_k/D=%+.5f" % (x[k], cv[k], cv[k]/0.04))
        print("    spike c0/D = %.6f, moment = %.6f, total = %.6f" % (cv[0]/0.04, v-cv[0]/0.04, v))
        print("\n  Delta NOT dividing 1 (no atom on the boundary):")
        for D in [0.03, 0.025, 0.015, 0.0125]:
            v, cv, x, st = solve(2.0, 0.0, D, bmode='inside')
            print("    Delta=%.4f  Z=%.7f [%s]" % (D, v, st))

    if what in ('all', 'order'):
        for bm in ['outside', 'inside']:
            print("\n"+"="*80)
            print("convergence order at S=2, A=0, bmode=%s" % bm); print("="*80)
            vals = []
            for D in [0.08, 0.04, 0.02, 0.01, 0.005]:
                v, cv, x, st = solve(2.0, 0.0, D, bmode=bm)
                vals.append((D, v)); print("  Delta=%.4f  Z=%.7f [%s]" % (D, v, st))
            for i in range(len(vals)-2):
                d1 = vals[i+1][1]-vals[i][1]; d2 = vals[i+2][1]-vals[i+1][1]
                print("    incr %.3e -> %.3e  ratio %.3f  => order %.3f"
                      % (d1, d2, d1/d2, np.log2(abs(d1/d2))))
            for o in [1.0, 1.5, 2.0]:
                r = (vals[-2][0]/vals[-1][0])**o
                print("    Richardson order %.1f : %.7f" % (o, (r*vals[-1][1]-vals[-2][1])/(r-1)))
