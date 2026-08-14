#!/usr/bin/env python3
"""
att034_verifyA2.py -- diagnosis of the S>1 (dip) discretisation.

NULL (written before running): the disagreement between my S=2 value (1.2948 at
Delta=0.04) and the reported 1.3207926 at the same Delta is caused by the ATOM THAT
LANDS EXACTLY ON alpha = 1.  In my scheme that atom (i) is exempt from the dip
constraint c_k <= 0 and (ii) enters the objective with full weight 2*x_k = 2, so the
optimiser can buy objective by driving it negative -- a pure discretisation artifact
that does not exist in the continuum (a point has measure zero).
REJECT the null if forcing c_{alpha=1} <= 0 / excluding it from the objective does
NOT move the value toward 1.3208.
"""
import numpy as np, cvxpy as cp

MT = 0.5 + (1/np.sqrt(2))/np.tan(1/np.sqrt(2))

def solve(S, A, Delta, bmode='inside', solver='CLARABEL'):
    """bmode: how the atom at exactly alpha=1 (if any) is treated.
       'inside' : counted in the objective, exempt from the dip constraint  (my v1)
       'outside': forced <= 0, NOT in the objective                          (conservative)
       'half'   : counted with weight 1/2 in the objective, unconstrained    (midpoint)
    """
    m = int(round(S/Delta))
    x = Delta*np.arange(m)
    sech = 1.0/np.cosh(2*A*x)
    Q = cp.Variable((m, m), symmetric=True)
    b = [cp.sum(cp.diag(Q, k)) for k in range(m)]
    c = [b[k]*sech[k] for k in range(m)]
    cons = [Q >> 0, c[0] + 2*cp.sum(cp.hstack(c[1:])) == 1]
    tol = 1e-12
    lin, wts = [], []
    for k in range(1, m):
        onbdry = abs(x[k]-1.0) < tol
        if onbdry:
            if bmode == 'inside':
                lin.append(c[k]); wts.append(2*x[k])
            elif bmode == 'outside':
                cons.append(c[k] <= 0)
            elif bmode == 'half':
                lin.append(c[k]); wts.append(x[k])
        elif x[k] < 1.0:
            lin.append(c[k]); wts.append(2*x[k])
        else:
            cons.append(c[k] <= 0)
    obj = c[0]/Delta + cp.sum(cp.hstack([w*t for w, t in zip(wts, lin)]))
    p = cp.Problem(cp.Minimize(obj), cons)
    try:
        p.solve(solver=solver)
    except Exception as e:
        return None, None, x, "FAIL:"+str(e)[:40]
    if Q.value is None:
        return None, None, x, p.status
    bv = np.array([np.trace(Q.value, offset=k) for k in range(m)])
    return p.value, bv*sech, x, p.status

print("="*80)
print("D1  S=2, A=0: boundary-atom convention.  Reported value at Delta=0.04 is 1.3207926")
print("="*80)
for D in [0.04, 0.02, 0.01]:
    row = []
    for bm in ['inside', 'outside', 'half']:
        v, cv, x, st = solve(2.0, 0.0, D, bmode=bm)
        row.append((bm, v, st))
    print("  Delta=%.3f  " % D + "   ".join("%s=%.7f[%s]" % (a, b, c[:9]) for a, b, c in row))

print("\n  optimal atom profile near alpha=1 (Delta=0.04, bmode=inside):")
v, cv, x, st = solve(2.0, 0.0, 0.04, bmode='inside')
i1 = int(round(1.0/0.04))
for k in range(i1-3, i1+4):
    print("     x=%.3f  c_k=%+.6f   c_k/Delta=%+.5f" % (x[k], cv[k], cv[k]/0.04))
print("     objective breakdown: spike c0/D = %.6f ; moment = %.6f ; total %.6f"
      % (cv[0]/0.04, v - cv[0]/0.04, v))

print("\n" + "="*80)
print("D2  Delta NOT dividing 1  -> no atom sits on the boundary at all")
print("="*80)
for D in [0.03, 0.025, 0.015, 0.0125]:
    v, cv, x, st = solve(2.0, 0.0, D, bmode='inside')
    print("  Delta=%.4f  (1/Delta=%.3f)  Z=%.7f  [%s]" % (D, 1/D, v, st))

print("\n" + "="*80)
print("D3  convergence order at S=2 with the CONSERVATIVE ('outside') convention")
print("="*80)
vals = []
for D in [0.08, 0.04, 0.02, 0.01]:
    v, cv, x, st = solve(2.0, 0.0, D, bmode='outside')
    vals.append((D, v))
    print("  Delta=%.4f  Z=%.7f  [%s]" % (D, v, st))
for i in range(len(vals)-2):
    d1 = vals[i+1][1]-vals[i][1]; d2 = vals[i+2][1]-vals[i+1][1]
    print("    increments %.3e -> %.3e  ratio %.3f => order %.3f"
          % (d1, d2, d1/d2, np.log2(abs(d1/d2))))
for order in [1.0, 2.0]:
    r = (vals[-2][0]/vals[-1][0])**order
    print("    Richardson order %.0f from Delta=%.3f,%.3f : %.7f"
          % (order, vals[-2][0], vals[-1][0], (r*vals[-1][1]-vals[-2][1])/(r-1)))

print("\n" + "="*80)
print("D4  same for 'inside' convention (order?)")
print("="*80)
vals = []
for D in [0.08, 0.04, 0.02, 0.01]:
    v, cv, x, st = solve(2.0, 0.0, D, bmode='inside')
    vals.append((D, v))
    print("  Delta=%.4f  Z=%.7f  [%s]" % (D, v, st))
for i in range(len(vals)-2):
    d1 = vals[i+1][1]-vals[i][1]; d2 = vals[i+2][1]-vals[i+1][1]
    print("    increments %.3e -> %.3e  ratio %.3f => order %.3f"
          % (d1, d2, d1/d2, np.log2(abs(d1/d2))))
for order in [1.0, 2.0]:
    r = (vals[-2][0]/vals[-1][0])**order
    print("    Richardson order %.0f : %.7f"
          % (order, (r*vals[-1][1]-vals[-2][1])/(r-1)))
