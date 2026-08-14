#!/usr/bin/env python3
"""
Attempt 035 — the majorant-count lemma, derived and evaluated.

LEMMA M: R(s) <= B(s) := min over band-limited majorants m >= 1_{[-s,s]}, supp mhat in [-1,1]:
    [ int m dv  +  int_{-1}^{1} mhat(alpha)|alpha| d alpha  -  m(0) ]
(unconditional; spike reads int m with mass 1, ramp reads mhat|alpha|, diagonal drop uses
N*/N >= 1 and m(0) >= 1). Computed as a Fourier LP on mhat-atoms with circle-positivity.
Units: v in mean spacings (gap = |gamma-gamma'| * l/(2pi)); mhat(alpha) at alpha in [-1,1].
Conventions: m(v) = c0 + 2 sum_j c_j cos(pi... we use m(v) = sum_atoms c_j e^{i 2pi? ...}
CHOOSE: pairing e^{i pi alpha v}?? — in mean-spacing units the band [-1,1] in alpha pairs
with v by e^{i 2pi alpha v}... The Montgomery convention: F(alpha) pairs with test g(v)
(v in mean spacings) via ghat(alpha) = int g(v) e^{-2pi i alpha v} dv. Selberg majorant of
[-s,s] with supp ghat in [-1,1]: int m = 2s + 1 achievable. We verify our LP reproduces
int-m ~ 2s+1 (control!) and then read the full objective.

LP discretization: mhat atoms at alpha_j = j*Delta, j=-n..n (even); m(v) = sum_j a_j
e^{2pi i alpha_j v} periodic with period P = 1/Delta. Constraints m >= 1 on [-s,s]-grid,
m >= 0 on the rest of the period (relaxation on a fine grid + post-verify).
Objective: a-atoms: int m = ahat... with atoms: int_period-normalized: the spike reads the
TOTAL integral int m dv over R for a decaying m — but our periodized m doesn't decay!
RESOLUTION: for the periodized model the spike (width 1/l -> 0) reads (1/P)int_period m
per unit-... NO: the honest object: the pair-form sum over the window; with a periodized
majorant the count-bound reads R(s) <= (window-density-sum) — the periodization P must
exceed the window... AVOID: use the compactly-band-limited NON-periodic class directly:
m(v) = sum_j a_j sinc-basis... SIMPLEST HONEST ROUTE: parametrize mhat as a continuous
piecewise-linear function on [-1,1] (hat basis at alpha_j), giving m(v) = sum_j a_j
tri_j(v)-transforms (explicit smooth decaying functions); constraints on a fine v-grid
out to V ~ 60 with tail-domination via |m(v)| <= C/v^2-of-the-basis (hat-transform decay).
"""
import numpy as np
from scipy.optimize import linprog
import time

def B_of_s(s, n=60, V=80.0, dv=0.02, verbose=False):
    # mhat piecewise-linear on [-1,1], even: nodes alpha_j = j/n, j=0..n, values y_j >= ...
    # m(v) = y_0 * T0(v) + sum_{j>=1} y_j * Tj(v),
    # where Tj = transform of the even pair of hat functions at +-alpha_j:
    # hat at alpha_j width 1/n: transform: (1/n) sinc^2(pi v/n)-shaped * 2cos(2pi alpha_j v)
    # with our convention m(v) = int mhat(alpha) e^{2pi i alpha v} d alpha:
    # hat_j(alpha) transform = (1/n)*sinc^2(pi v / n)*e^{2pi i alpha_j v}; even pair -> 2cos.
    alphas = np.arange(n+1)/n
    vg = np.arange(0.0, V, dv)   # even functions: v >= 0 suffices
    def sinc2(x):
        out = np.ones_like(x)
        nz = np.abs(x) > 1e-12
        out[nz] = (np.sin(x[nz])/x[nz])**2
        return out
    base = (1.0/n)*sinc2(np.pi*vg/n)
    T = np.empty((n+1, len(vg)))
    T[0] = base
    for j in range(1, n+1):
        T[j] = 2*base*np.cos(2*np.pi*alphas[j]*vg)
    # objective: int m dv = mhat(0)?? NO: int_R m dv = mhat-value at alpha=0?? With
    # m(v)=int mhat e^{2pi i a v} da: int_R m dv = mhat(0-as-density)?? int_R e^{2pi i a v} dv
    # = delta(a): int m dv = mhat(0)-DENSITY = y_0. GOOD: spike-term = y_0.
    # ramp-term: int_{-1}^1 mhat|alpha| = 2 * int_0^1 mhat(a) a da: piecewise-linear exact:
    wts = np.zeros(n+1)
    for j in range(n+1):
        # integral of hat_j(a)*a over [0,1], hat width 1/n, both-sides even counted via 2x:
        a0 = alphas[j]
        wts[j] = 2 * (a0/n if 0 < j < n else (a0/n/1 if j == n else 0.0))
        if j == 0:
            wts[j] = 2*(1.0/(6*n**2))  # int_0^{1/n} (1 - n a) a da = 1/(6 n^2)
        elif j == n:
            wts[j] = 2*(a0/(2*n) - 1.0/(6*n**2))
    # m(0) = sum_j y_j * T[j][0]
    m0coef = T[:, 0]
    # LP: minimize y_0 + wts.y - m0coef.y  s.t.  m(v) >= 1 on [0,s], m(v) >= 0 on (s, V]
    c = np.zeros(n+1); c[0] += 1.0; c += wts; c -= m0coef
    mask1 = vg <= s + 1e-12
    A_ub = -T.T                       # -m(v) <= -1 or 0
    b_ub = np.where(mask1, -1.0, 0.0)
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=[(None, None)]*(n+1), method="highs")
    if not res.success:
        return None, None
    y = res.x
    # post-verify on finer grid
    vf = np.arange(0.0, V, 0.005)
    basef = (1.0/n)*sinc2(np.pi*vf/n)
    mf = y[0]*basef + sum(y[j]*2*basef*np.cos(2*np.pi*alphas[j]*vf) for j in range(1, n+1))
    viol = min(np.min(mf[vf <= s] - 1.0), np.min(mf[vf > s]))
    B = res.fun
    intm = y[0]
    return B, (intm, viol)

print("LEMMA M constants: B(s) vs 2s (true GUE R(s) ~ 2s - 1 for s >~ 1):", flush=True)
Btab = {}
for s in [0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 8.0]:
    t0 = time.time()
    B, info = B_of_s(s)
    if B is None:
        print(f"  s={s}: LP failed", flush=True)
    else:
        Btab[s] = B
        print(f"  s={s:4.1f}: B(s) = {B:7.3f}   (int m = {info[0]:.3f}, expect ~{2*s+1:.1f}; "
              f"min-slack {info[1]:+.1e})   excess over 2s: {B-2*s:+.3f}  [{time.time()-t0:.0f}s]", flush=True)

# ---------------- envelope constants from the trapezoid spectrum ----------------
# |phihat(omega)|^2 with Ihat(-Om) = 2pi min(Om-L, L)_+/Om, |phihat|^2 = |Ihat|^2/4 both sides.
# Z-normalization: kernel G_Z(v) = (1/(pi L))^2 * (1/2pi) int |Ihat|^2/4 e^{i om v} dom (both sides).
# Tail part: |om| > l. Explicit: G_t0 := G_tail(0) = (1/(piL))^2 (1/4pi) int_{l}^inf |Ihat(-Om)|^2 dOm
# = (1/(piL))^2 (1/4pi) (2pi)^2 int_l^inf [min(Om-L,L)+/Om]^2 dOm ; for l >= 2L (theta<=1/2):
# = (pi/(piL)^2) * L^2 int_l^inf dOm/Om^2 = (pi/(piL)^2) L^2 / l = 1/(pi... compute numerically:
import scipy.integrate as si
def tail_consts(theta, l):
    L = theta*l
    f = lambda Om: (min(Om-L, L) if Om > L else 0.0)**2/Om**2
    I_tail, _ = si.quad(f, l, np.inf, limit=200)
    G_t0 = (1.0/(np.pi*L))**2 * np.pi * I_tail          # = (1/(piL))^2*(1/4pi)*(2pi)^2*I_tail
    # A2: |G_tail(v)| <= A2/v^2 via two integrations by parts: A2 = (1/(piL))^2*(1/4pi)*TV(d/dOm |Ihat|^2-tail)
    # |Ihat|^2-tail = (2pi)^2 L^2/Om^2 on [l,inf): derivative -2(2pi)^2L^2/Om^3: TV = (2pi)^2 L^2 * [2/l^2]
    # plus the jump at Om = l: |Ihat(l)|^2 = (2pi)^2 L^2/l^2 (delta in derivative):
    A2 = (1.0/(np.pi*L))**2*(1/(4*np.pi))*2*((2*np.pi)**2*L**2/l**2 + (2*np.pi)**2*L**2/l**2)
    return G_t0, A2

l = 9.0   # representative log(T/2pi)
theta = 0.5
G_t0, A2 = tail_consts(theta, l)
print(f"\nENVELOPE (theta={theta}, l={l}): G_t0 = {G_t0:.5f}, A2 = {A2:.5f}  (units: t; mean spacing = 2pi/l = {2*np.pi/l:.3f})", flush=True)

# ---------------- assembly: the charge and the contraction ----------------
# off-diag tail-charge per unit t: dbar * [ sum over graded windows count*envelope ]
# in mean-spacing units s: pairs per zero within [s, s+ds]: dR <= dB(s): charge:
# Q := sum_pairs |G_tail| / (N) <= sum_k [B(s_k) - B(s_{k-1})]*Genv(s_{k-1})
# with Genv(s) = min(G_t0, A2/((s*2pi/l))^2). Grade to s_max then integrate the far part
# with the mean+BW density (counts <= 2s*1 + c-BW-fluct: use dB ~ 2 ds + ... beyond LP table).
sp = 2*np.pi/l
svals = sorted(Btab.keys())
Q = 0.0
prevB = 0.0; prevs = 0.0
for s in svals:
    env = min(G_t0, A2/((max(prevs, 0.25)*sp)**2))
    Q += (Btab[s] - prevB)*env
    prevB, prevs = Btab[s], s
# far tail beyond s_max: dR <= 2 ds (+BW-fluct absorbed into a 1.3 factor), env = A2/(s sp)^2:
smax = svals[-1]
far, _ = si.quad(lambda s: 2*1.3*A2/((s*sp)**2), smax, np.inf)
Q += far
print(f"tail-charge Q = sum |G_tail|-bound per zero = {Q:.5f}  vs  G_t0 = {G_t0:.5f}", flush=True)

# contraction: the tail-energy G_t0 and the charge Q are both ~(row-mass)-proportional...
# Assemble the row-bound: 2pi^2 int Z^2/T <= 2pi^2[ diag + band-offdiag-exact + dbar*Q ]
# diag: exact = (1-ln2)/(pi^2 theta) * ... use the measured-exact diag value scaling:
dbar = l/(2*np.pi)
diag = dbar*(1.0/(np.pi*theta*l))**2*2*np.pi*(theta*l)*(1-np.log(2))   # dbar*||z||^2
band_off_exact_plus_diag_identity = np.log(1/theta) - 0.5              # from the identity's band part
rowbound_naive = 2*np.pi**2*(diag + dbar*Q) - np.log(1/theta) + 0.5
print(f"diag = {diag:.5f} (cf. measured 0.0565)", flush=True)
print(f"charge term 2pi^2*dbar*Q = {2*np.pi**2*dbar*Q:.4f}", flush=True)
print(f"PRE-CONTRACTION explicit row-bound (theta=1/2, l=9): {rowbound_naive:.3f}", flush=True)
print("(contraction refinement: G_t0 and A2 scale with the actual tail mass ~ row/2pi^2-ish;", flush=True)
print(" solving row <= [2pi^2 diag - ln(1/theta)+1/2] + a*row with a = charge/tail-mass-ratio)", flush=True)
