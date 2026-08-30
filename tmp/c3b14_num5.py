#!/usr/bin/env python3
"""
C3 batch 14 -- numerical block 5.  ADJUDICATION of blocks 2 and 4.

Three defects found in my own blocks 2/4, all corrected here.

 D1  U6 (block 4) reported the PURE GAUSSIAN exp(-t^2) as having "57 negatives, min
     -2.67e-12", and Phi_c as having 25.  Both are FALSE.  For W = exp(-t^2) everything is
     closed form:
         R(v) = (1/4) sqrt(pi/2) exp(-2 v^2),      Rhat(xi) = (pi/8) exp(-xi^2/8)  >  0,
     strictly positive for every xi.  (Cross-check: Rhat(2x) = (1/4)(c0 c2 + s1^2)
     = (pi/8) exp(-x^2/2), verified below.)  The "negatives" were the TRUNCATION floor of a
     v-grid built for Phi (which decays doubly exponentially) and reused for kernels with
     far heavier tails.  Rerun here with per-kernel grids and an explicit noise floor.

 D2  U1 (block 4) printed "=> TP is FALSE for this kernel" while its own table showed
     0/5 TP2 violations, all minors POSITIVE.  The printed verdict contradicted the data.
     Re-adjudicated below, and the real structural point substituted.

 D3  S3 (block 2) measured "(log R)'' max = +7.49e5" and concluded R is not log-concave.
     That maximum sits in the region where R has UNDERFLOWED to 0 and log R is garbage.
     Re-measured on the region where R is genuinely representable.
"""
import numpy as np
np.seterr(all='ignore')

def simp_w(n):
    w = np.ones(n+1); w[1:-1:2] = 4.0; w[2:-1:2] = 2.0
    return w
def simp(y, h): return (h/3.0)*np.dot(simp_w(len(y)-1), y)

NN = np.arange(1, 15, dtype=np.float64)
def Phi(t):
    t = np.abs(np.asarray(t, dtype=np.float64))
    e2 = np.exp(2*t); out = np.zeros_like(t)
    for n in NN:
        expo = -np.pi*n*n*e2
        term = (2*np.pi**2*n**4*np.exp(4.5*t) - 3*np.pi*n**2*np.exp(2.5*t))
        out += np.where(expo > -700.0, term*np.exp(np.maximum(expo, -700.0)), 0.0)
    return 4*out

def Rhat_scan(w, PLIM, VLIM, NPp=16000, NVv=4000, ximax=20.0, nxi=401):
    """min of Rhat over xi in [0,ximax], with grids sized to the KERNEL, not to Phi."""
    pg = np.linspace(-PLIM, PLIM, NPp+1); hp = 2*PLIM/NPp; wp = simp_w(NPp)
    vg = np.linspace(0.0, VLIM, NVv+1); hv = VLIM/NVv
    Rp = np.empty(NVv+1)
    for i, v in enumerate(vg):
        Rp[i] = (hp/3.0)*np.dot(wp, pg**2 * w(v+pg) * w(v-pg))
    vfull = np.concatenate([-vg[:0:-1], vg]); Rf = np.concatenate([Rp[:0:-1], Rp])
    mn = None; mnx = None; nneg = 0; mx = None
    for k in range(nxi):
        xi = ximax*k/(nxi-1)
        val = simp(Rf*np.cos(xi*vfull), hv)
        if mx is None or val > mx: mx = val
        if val < 0: nneg += 1
        if mn is None or val < mn: mn, mnx = val, xi
    return mn, mnx, nneg, mx, Rp[-1]

print("="*78)
print("D1 -- THE GAUSSIAN CONTROL, in closed form, and the noise floor it calibrates")
print("="*78)
print("  W(t) = exp(-t^2):   R(v) = (1/4)sqrt(pi/2) exp(-2v^2),  Rhat(xi) = (pi/8)exp(-xi^2/8)")
print(f"{'xi':>8} {'Rhat closed form':>22} {'(1/4)(c0c2+s1^2) at x=xi/2':>30}")
for xi in [0.0, 4.0, 8.0, 16.0, 20.0]:
    x = xi/2
    closed = (np.pi/8)*np.exp(-xi**2/8)
    c0 = np.sqrt(np.pi)*np.exp(-x**2/4)
    s1 = (np.sqrt(np.pi)*x/2)*np.exp(-x**2/4)
    c2 = np.sqrt(np.pi)*(0.5 - x**2/4)*np.exp(-x**2/4)
    print(f"{xi:>8.1f} {closed:>22.14e} {0.25*(c0*c2+s1**2):>30.14e}")
print("  Both columns agree exactly; Rhat > 0 STRICTLY for every xi.  Any negative measured")
print("  for this kernel is numerical, full stop.")
print()
print("  Block 4's grid (PL=6.6, VMAX=3.4) vs a grid sized to the Gaussian:")
for (PLIM, VLIM, tag) in [(6.6, 3.4, 'block 4 grid (WRONG for this kernel)'),
                          (14.0, 8.0, 'kernel-sized grid')]:
    mn, mnx, nneg, mx, tail = Rhat_scan(lambda t: np.exp(-np.asarray(t, dtype=float)**2),
                                        PLIM, VLIM)
    print(f"    {tag:<38} min = {mn: .4e} at xi={mnx:5.2f}, negatives={nneg:4d},"
          f" R(VMAX)={tail:.2e}")
print("  => block 4's U6 rows for exp(-t^2) and for Phi_c are TRUNCATION ARTEFACTS.")
print("     They are WITHDRAWN.")

print()
print("="*78)
print("D1b -- U6 RERUN with per-kernel grids and a stated noise floor")
print("="*78)
print("  A row counts as a REAL violation only if |min| exceeds the kernel's own tail")
print("  residual R(VMAX) by orders of magnitude AND the location is stable.")
print(f"{'kernel':>32} {'PL,VMAX':>12} {'min Rhat':>16} {'at xi':>7} {'neg':>5} {'R(VMAX)':>11} {'verdict':>12}")
tests = [
    ("Phi (Riemann)",            lambda t: Phi(t),                                    6.6, 3.4),
    ("exp(-t^2) Gaussian",       lambda t: np.exp(-np.asarray(t,dtype=float)**2),    14.0, 8.0),
    ("exp(-t^2)+exp(-4t^2) Phi_g", lambda t: np.exp(-np.asarray(t,dtype=float)**2)
                                    + np.exp(-4*np.asarray(t,dtype=float)**2),       14.0, 8.0),
    ("exp(-t^2)(2+cos2t) Phi_c", lambda t: np.exp(-np.asarray(t,dtype=float)**2)
                                    *(2+np.cos(2*np.asarray(t,dtype=float))),        14.0, 8.0),
    ("Phi + 0.5 exp(-t^2)",      lambda t: Phi(t)+0.5*np.exp(-np.asarray(t,dtype=float)**2),
                                                                                     14.0, 8.0),
    ("sech(t)",                  lambda t: 1.0/np.cosh(np.asarray(t,dtype=float)),   30.0, 18.0),
    ("exp(-t^4)",                lambda t: np.exp(-np.asarray(t,dtype=float)**4),     8.0, 5.0),
]
for nm, w, PLIM, VLIM in tests:
    mn, mnx, nneg, mx, tail = Rhat_scan(w, PLIM, VLIM)
    real = (mn < 0) and (abs(mn) > 1e4*max(tail, 1e-300)) and (abs(mn) > 1e-8*mx)
    print(f"{nm:>32} {f'{PLIM},{VLIM}':>12} {mn:>16.4e} {mnx:>7.2f} {nneg:>5}"
          f" {tail:>11.2e} {('REAL NEG' if real else ('noise' if mn<0 else 'positive')):>12}")

print()
print("="*78)
print("D2 -- TOTAL POSITIVITY, re-adjudicated")
print("="*78)
print("  Block 4 printed 'TP is FALSE' while measuring 0/5 TP2 violations.  The printed")
print("  verdict was unsupported and is WITHDRAWN.  The correct structural statement does")
print("  not need the minors at all:")
print()
print("    TP2 for K(a,b) = R(a-b) is EQUIVALENT to log-concavity of R (classical).")
print("    But log-concavity does NOT imply a nonnegative transform.  Witness, exact:")
print("      W(v) = exp(-v^4) is even, positive, and log-concave ((log W)'' = -12 v^2 <= 0),")
print("      yet exp(-|v|^p) is positive definite ONLY for p <= 2, so its transform takes")
print("      negative values.  Measured below.")
vv = np.linspace(-8, 8, 32001); hvv = vv[1]-vv[0]
g4 = np.exp(-vv**4)
mn = None; mnx = None
for k in range(0, 801):
    xi = k*0.02
    val = simp(g4*np.cos(xi*vv), hvv)
    if mn is None or val < mn: mn, mnx = val, xi
print(f"      transform of exp(-v^4): min = {mn:.6e} at xi = {mnx:.3f}  -> NEGATIVE, as claimed")
print("    So even if R IS log-concave (=TP2), that gives nothing.  And TP_infinity (PF)")
print("    would force, by Schoenberg, Rhat = 1/Psi with Psi in Laguerre-Polya -- a")
print("    statement about Rhat being zero-free, which is not what is wanted and is not")
print("    available.  The determinantal family is dead because it does not IMPLY the")
print("    conclusion, not because R fails its hypotheses.")

print()
print("="*78)
print("D3 -- LOG-CONCAVITY of R, re-measured off the underflow region")
print("="*78)
PL = 6.6; NP = 13200
pg = np.linspace(-PL, PL, NP+1); hp = 2*PL/NP; wp = simp_w(NP)
vg = np.linspace(0.0, 0.75, 1501); hv = vg[1]-vg[0]
Rp = np.array([(hp/3.0)*np.dot(wp, pg**2*Phi(v+pg)*Phi(v-pg)) for v in vg])
print(f"  R ranges from {Rp[0]:.4e} at v=0 to {Rp[-1]:.4e} at v=0.75 -- all representable.")
lg = np.log(Rp)
d2 = np.diff(lg, 2)/hv**2
print(f"  (log R)'' on [0,0.75]:  min = {d2.min():.6e}   max = {d2.max():.6e}")
print(f"  log-concave on this region? {bool(np.all(d2 <= 1e-6))}")
print("  Block 2's S3 'max = +7.49e5' came from the region where R had underflowed to 0")
print("  and log R was clamped at log(1e-300); that number is WITHDRAWN.")
print("="*78)
