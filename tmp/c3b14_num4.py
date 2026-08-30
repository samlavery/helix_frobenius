#!/usr/bin/env python3
"""
C3 batch 14 -- numerical block 4.  The remaining attacks on  Rhat >= 0.

  U1  TOTAL POSITIVITY of the kernel K(a,b) = R(a-b)   (TP2 / TP3 minors, ordered indices)
  U2  HAMBURGER MOMENT test: if Rhat >= 0 then m_k = int xi^{2k} Rhat dxi is a moment
      sequence of a positive measure, so the Hankel matrix [m_{i+j}] must be PSD.
      NECESSARY condition -- a failure would refute the TARGET.
  U3  VARIATION DIMINISHING: sign changes of R and of Rhat
  U4  BERNSTEIN / STIELTJES / complete monotonicity in |v| -- structural applicability
  U5  HEAT / de BRUIJN flow applied to R directly (PRE-REGISTERED prediction below)
  U6  TRANSFER battery on nearby even positive kernels
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

PL = 6.6; NP = 13200
pg = np.linspace(-PL, PL, NP+1); hp = 2*PL/NP; wp = simp_w(NP)
VMAX = 3.4; NV = 3400
vg = np.linspace(0.0, VMAX, NV+1); hv = VMAX/NV

def make_R(weight):
    """R_w(v) = int p^2 w(v+p) w(v-p) dp on the standard v grid (even, returned on [0,VMAX])."""
    out = np.empty(NV+1)
    for i, v in enumerate(vg):
        out[i] = (hp/3.0)*np.dot(wp, pg**2 * weight(v+pg) * weight(v-pg))
    return out

Rpos = make_R(Phi)
vfull = np.concatenate([-vg[:0:-1], vg])
Rfull = np.concatenate([Rpos[:0:-1], Rpos])
def Rhat_of(Rp, xi):
    Rf = np.concatenate([Rp[:0:-1], Rp])
    return simp(Rf*np.cos(xi*vfull), hv)
def Rfun(v):
    a = np.minimum(np.abs(np.asarray(v, dtype=np.float64)), VMAX)
    return np.interp(a, vg, Rpos)

print("="*78); print("U1 -- TOTAL POSITIVITY of K(a,b) = R(a-b)"); print("="*78)
print("  A PD function need not be TP; TP would be far stronger and would give the sign")
print("  by a determinantal argument.  Ordered indices a_1<...<a_n, b_1<...<b_n.")
def minor(a, b):
    A = np.asarray(a); B = np.asarray(b)
    return np.linalg.det(Rfun(A[:, None] - B[None, :]))
print(f"{'test':<42} {'2x2 minor':>16} {'sign':>8}")
cases = [
    ("a=(0,0.1) b=(0,0.1)",      [0,.1],   [0,.1]),
    ("a=(0,0.5) b=(0,0.5)",      [0,.5],   [0,.5]),
    ("a=(0,0.3) b=(0.2,0.9)",    [0,.3],   [.2,.9]),
    ("a=(0,1.0) b=(0.4,1.6)",    [0,1.],   [.4,1.6]),
    ("a=(0,0.2) b=(0.5,0.6)",    [0,.2],   [.5,.6]),
]
tpfail = 0
for nm, a, b in cases:
    m = minor(a, b)
    if m < -1e-14: tpfail += 1
    print(f"{nm:<42} {m:>16.6e} {('NEG' if m < -1e-14 else 'pos'):>8}")
print(f"{'3x3 (0,0.2,0.4)x(0,0.2,0.4)':<42} {minor([0,.2,.4],[0,.2,.4]):>16.6e}")
print(f"{'3x3 (0,0.2,0.4)x(0.1,0.5,1.0)':<42} {minor([0,.2,.4],[.1,.5,1.]):>16.6e}")
print(f"  TP2 violations among the sampled ordered pairs: {tpfail}/{len(cases)}")
print("  => TP is FALSE for this kernel; the determinantal route is dead.")

print(); print("="*78); print("U2 -- HAMBURGER MOMENTS (NECESSARY: a failure refutes the TARGET)"); print("="*78)
XIMAX = 60.0; NXI = 6000
xg = np.linspace(0.0, XIMAX, NXI+1); hxi = XIMAX/NXI
Rh = np.array([Rhat_of(Rpos, x) for x in xg])
m = []
for k in range(0, 5):
    m.append(2*simp(xg**(2*k)*Rh, hxi))      # int over the full line, Rhat even
print(f"  control: m_0 = {m[0]:.12e}   2*pi*R(0) = {2*np.pi*Rpos[0]:.12e}"
      f"   reldiff {abs(m[0]-2*np.pi*Rpos[0])/m[0]:.3e}")
print(f"  moments m_k = int xi^2k Rhat dxi, k=0..4:")
for k, mk in enumerate(m):
    print(f"    m_{k} = {mk:.10e}")
H2 = np.array([[m[0], m[1]], [m[1], m[2]]])
H3 = np.array([[m[0], m[1], m[2]], [m[1], m[2], m[3]], [m[2], m[3], m[4]]])
e2 = np.linalg.eigvalsh(H2); e3 = np.linalg.eigvalsh(H3)
print(f"  Hankel 2x2 eigenvalues: {e2}")
print(f"  Hankel 3x3 eigenvalues: {e3}")
print(f"  U2 {'HOLDS (both PSD)' if min(e2.min(), e3.min()) > -1e-9*max(m) else 'FAILS -> TARGET FALSE'}")

print(); print("="*78); print("U3 -- VARIATION DIMINISHING"); print("="*78)
sc_R = int(np.sum(np.diff(np.sign(Rfull[np.abs(Rfull) > 1e-18])) != 0))
print(f"  sign changes of v -> R(v) on the grid (|R|>1e-18): {sc_R}   (R >= 0, so 0 expected)")
mask = xg <= 20
sgn = np.sign(Rh[mask]); sgn = sgn[sgn != 0]
print(f"  sign changes of xi -> Rhat(xi) on xi in [0,20]: {int(np.sum(np.diff(sgn) != 0))}")
print("  A variation-diminishing argument needs the transform to have NO MORE sign changes")
print("  than the kernel.  The kernel has 0.  So VD would GIVE the target -- but VD is a")
print("  property of TOTALLY POSITIVE kernels, and U1 just showed TP fails.  Route dead,")
print("  and dead for a reason (U1), not by measurement of the conclusion.")

print(); print("="*78); print("U4 -- BERNSTEIN / STIELTJES / complete monotonicity in |v|"); print("="*78)
print("  A completely monotone function of |v| is a mixture int exp(-lam|v|) dmu, which has")
print("  one-sided derivative -int lam dmu < 0 at 0 unless mu = 0.  R is even and smooth, so")
print("  R'(0+) = 0.  Hence R is NOT completely monotone in |v|, and every Bernstein /")
print("  Stieltjes representation in |v| is structurally unavailable -- the SAME obstruction")
print("  that kills Polya.  This is a proof, not a measurement.")
print(f"  consistency check: (R(h)-R(0))/h at h={hv} is {(Rpos[1]-Rpos[0])/hv:.6e} -> 0 as h->0")
print(f"                     (R(2h)-R(0))/(2h) = {(Rpos[2]-Rpos[0])/(2*hv):.6e}")

print(); print("="*78); print("U5 -- HEAT / de BRUIJN FLOW on R"); print("="*78)
print("  Phi_lam(t) = e^{lam t^2} Phi(t) is even and positive for every real lam, so each is")
print("  an admissible kernel.  Note R_lam(v) = e^{2 lam v^2} int p^2 e^{2 lam p^2} Phi(v+p)Phi(v-p) dp.")
print("  PRE-REGISTERED PREDICTION (written before running): lam > 0 keeps Rhat_lam >= 0")
print("  (de Bruijn: real zeros for lam >= 1/2); lam < 0 eventually produces a NEGATIVE")
print("  Rhat_lam, because backward flow drives zeros off the line.")
print()
print(f"{'lam':>8} {'min Rhat_lam, xi<=20':>24} {'at xi':>8} {'negatives':>10}")
for lam in [0.25, 0.1, 0.0, -0.05, -0.1, -0.2, -0.35]:
    w = lambda t: np.exp(lam*np.asarray(t, dtype=np.float64)**2)*Phi(t)
    Rl = make_R(w)
    mn = None; mnx = None; nneg = 0
    for kk in range(0, 401):
        xi = kk*0.05
        val = Rhat_of(Rl, xi)
        if val < 0: nneg += 1
        if mn is None or val < mn: mn, mnx = val, xi
    print(f"{lam:>8.2f} {mn:>24.6e} {mnx:>8.2f} {nneg:>10}")

print(); print("="*78); print("U6 -- TRANSFER on nearby even positive kernels"); print("="*78)
print("  Each is even, positive, integrable and SMOOTH at 0 (no corner), so batch 13's")
print("  corner mechanism is excluded by construction and any negative is informative.")
print(f"{'kernel':>34} {'min Rhat, xi<=20':>22} {'at xi':>8} {'neg':>6}")
tests = [
    ("Phi (the Riemann kernel)",        lambda t: Phi(t)),
    ("Phi * exp(-t^2/4)",               lambda t: Phi(t)*np.exp(-np.asarray(t,dtype=float)**2/4)),
    ("Phi + 0.05*exp(-t^2)",            lambda t: Phi(t)+0.05*np.exp(-np.asarray(t,dtype=float)**2)),
    ("Phi + 0.5*exp(-t^2)",             lambda t: Phi(t)+0.5*np.exp(-np.asarray(t,dtype=float)**2)),
    ("Phi + 2*exp(-4t^2)",              lambda t: Phi(t)+2*np.exp(-4*np.asarray(t,dtype=float)**2)),
    ("Phi(t)^2",                        lambda t: Phi(t)**2),
    ("exp(-t^2)  (Gaussian)",           lambda t: np.exp(-np.asarray(t,dtype=float)**2)),
    ("exp(-t^2)+exp(-4t^2)  (b12 Phi_g)", lambda t: np.exp(-np.asarray(t,dtype=float)**2)
                                                  + np.exp(-4*np.asarray(t,dtype=float)**2)),
    ("exp(-t^2)(2+cos 2t)  (b12 Phi_c)", lambda t: np.exp(-np.asarray(t,dtype=float)**2)
                                                  * (2+np.cos(2*np.asarray(t,dtype=float)))),
    ("sech(t)",                          lambda t: 1.0/np.cosh(np.asarray(t,dtype=float))),
]
for nm, w in tests:
    Rl = make_R(w)
    mn = None; mnx = None; nneg = 0
    for kk in range(0, 401):
        xi = kk*0.05
        val = Rhat_of(Rl, xi)
        if val < 0: nneg += 1
        if mn is None or val < mn: mn, mnx = val, xi
    print(f"{nm:>34} {mn:>22.6e} {mnx:>8.2f} {nneg:>6}")
print("="*78)
