"""ADVERSARIAL VERIFICATION, part 2.

E.  Is Var_window(S_lines) < diagonal sum systematically, or is it window noise?
    (att012's audit only ran the direct check at T <= 1e5 where the line count is 1937.)
    If systematic, then V_line as used in the record is NOT the variance of the model it
    claims to subtract, and every "residual" is biased low by that amount.

F.  Sensitivity of the residual to the O(1) choice of cutoff X = T/(2 pi).
"""
import numpy as np, os, sys, math
from math import pi, log
HERE = os.path.dirname(os.path.abspath(__file__))
TWOPI2 = 2.0*pi*pi
def P(*a): print(*a); sys.stdout.flush()

NS = np.load(os.path.join(HERE, 'att012_verify_NS.npy'))
CUM = np.load(os.path.join(HERE, 'att012_verify_CUM.npy'))
A2 = np.diff(np.concatenate(([0.0], CUM)))

def lines_upto(X):
    j = int(np.searchsorted(NS, X, side='right'))
    return np.log(NS[:j]), np.sqrt(A2[:j]), CUM[j-1]/TWOPI2, j

def direct_var(al, am, a, b, h):
    t = np.arange(a, b, h)
    s = np.zeros(len(t))
    B = 2000
    for i in range(0, len(al), B):
        s += (am[i:i+B][:, None]*np.sin(np.outer(al[i:i+B], t))).sum(axis=0)
    s *= -1.0/pi
    return s.var(), s.mean()

P("="*96)
P("E.  Var(S_lines) over a window: diagonal (1/2pi^2)sum a_n^2  vs  DIRECT, many windows")
P("="*96)
for tc0, W, HH, NW in ((10000924.8, 1849.1, 0.05, 5),):
    al, am, vdiag, j = lines_upto(tc0/(2*pi))
    P(f"\n  cutoff X = {tc0/(2*pi):.0f}  ({j} lines)   diagonal = {vdiag:.6f}   window width {W:.0f}")
    P(f"    {'window centre':>16}{'direct Var':>13}{'ratio':>9}{'diff':>12}{'diff/(1/2pi^2)':>16}")
    rs = []
    for k in range(NW):
        tc = tc0 + k*3.0*W
        vd, mn = direct_var(al, am, tc-W/2, tc+W/2, HH)
        rs.append(vd)
        P(f"    {tc:>16.1f}{vd:>13.6f}{vd/vdiag:>9.4f}{vd-vdiag:>12.6f}{(vd-vdiag)*TWOPI2:>16.4f}")
    rs = np.array(rs)
    P(f"    sem of the mean ratio = {rs.std(ddof=1)/vdiag/np.sqrt(len(rs)):.5f}")
    P(f"    --> mean ratio {rs.mean()/vdiag:.5f}  sd {rs.std(ddof=1)/vdiag:.5f}   "
      f"mean abs bias {(rs.mean()-vdiag)*TWOPI2:+.4f} in units of 1/(2pi^2)")


P("\n" + "="*96)
P("F.  sensitivity of the residual to the O(1) cutoff convention")
P("="*96)
meas = dict(zip(['1e+03', '1e+04', '1e+05', '1e+06', '1e+07'],
                [0.165003, 0.174374, 0.186333, 0.197010, 0.205389]))
cen = dict(zip(['1e+03', '1e+04', '1e+05', '1e+06', '1e+07'],
               [3600.0009, 11799.8889, 101349.8110, 1001050.0319, 10000924.7686]))
P(f"  {'T':>8}" + "".join(f"{lab:>13}" for lab in
                          ('X=T/4pi', 'X=T/2pi', 'X=T/pi', 'X=T', 'X=2T')))
P(f"  {'':>8}" + "".join(f"{'resid*2pi^2':>13}" for _ in range(5)))
for tag in meas:
    tc = cen[tag]; row = f"  {float(tag):>8.0e}"
    for f in (0.5, 1.0, 2.0, 2*pi, 4*pi):
        _, _, vl, _ = lines_upto(f*tc/(2*pi))
        row += f"{(meas[tag]-vl)*TWOPI2:>13.4f}"
    P(row)
P("  (the record's claim 'residual = 1/(2pi^2) exactly' is the X = T/2pi column = 1.000)")
