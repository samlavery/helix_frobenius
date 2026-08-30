#!/usr/bin/env python3
"""
C3 batch 14 -- numerical block 2.  ATTACKS on  cosMom R (2x) >= 0,  R(v) = int p^2 Phi(v+p)Phi(v-p) dp.

The target is now in normal form (C3B14.cosMom_Rker, compiled): R >= 0 and even, and the
first Laguerre inequality says exactly that R is POSITIVE DEFINITE.

Two kinds of test, kept strictly apart:
  * NECESSARY conditions for positive definiteness.  If one FAILS, the TARGET is FALSE.
    These are adversarial tests of the conjecture itself and are run first.
  * SUFFICIENT conditions.  If one FAILS, only that ROUTE dies.

Every structural hypothesis is falsified numerically here BEFORE anything is formalised.
"""
import numpy as np

np.seterr(all='ignore')

def simp_w(n):
    w = np.ones(n + 1); w[1:-1:2] = 4.0; w[2:-1:2] = 2.0
    return w
def simp(y, h):
    return (h / 3.0) * np.dot(simp_w(len(y) - 1), y)

# ----------------------------------------------------------------- kernel
NN = np.arange(1, 15, dtype=np.float64)
def Phi(t):
    t = np.abs(np.asarray(t, dtype=np.float64))
    e2 = np.exp(2 * t); out = np.zeros_like(t)
    for n in NN:
        expo = -np.pi * n * n * e2
        term = (2*np.pi**2*n**4*np.exp(4.5*t) - 3*np.pi*n**2*np.exp(2.5*t))
        out += np.where(expo > -700.0, term*np.exp(np.maximum(expo, -700.0)), 0.0)
    return 4*out

PL = 6.6; NP = 13200
pg = np.linspace(-PL, PL, NP+1); hp = 2*PL/NP; wp = simp_w(NP)
def R_of(v):
    return (hp/3.0)*np.dot(wp, pg**2 * Phi(v+pg) * Phi(v-pg))

VMAX = 3.4; NV = 3400
vg = np.linspace(0.0, VMAX, NV+1); hv = VMAX/NV
Rpos = np.array([R_of(v) for v in vg])          # R on [0,VMAX]; R is even
R0 = Rpos[0]

def Rfun(v):
    """R at arbitrary v by linear interpolation on the precomputed even grid."""
    a = np.abs(np.asarray(v, dtype=np.float64))
    a = np.minimum(a, VMAX)
    return np.interp(a, vg, Rpos)

print("="*78); print("SETUP"); print("="*78)
print(f"  R(0) = {R0:.14f}   (batch 13: L1xi(0) = 0.011419830834443718)")
print(f"  R >= 0 on grid: {bool(np.all(Rpos >= 0))}   R(VMAX) = {Rpos[-1]:.4e}")

# =====================================================================
print(); print("="*78)
print("NECESSARY CONDITIONS FOR POSITIVE DEFINITENESS -- these test the TARGET itself")
print("="*78)

# N1: |R(v)| <= R(0)
print("N1 -- a PD function attains its max at 0:  R(0) >= |R(v)| for all v.")
i = int(np.argmax(Rpos))
print(f"     max R on [0,{VMAX}] = {Rpos.max():.14f} at v = {vg[i]:.4f};  R(0) = {R0:.14f}")
print(f"     N1 {'HOLDS' if Rpos.max() <= R0*(1+1e-12) else 'FAILS -> TARGET WOULD BE FALSE'}")

# N2: Bochner in finite form -- Gram matrices [R(v_i - v_j)] must be PSD
print()
print("N2 -- BOCHNER, finite form: [R(v_i - v_j)] must be PSD for every finite point set.")
print("     Hostile point sets: uniform, clustered, wide, and a deterministic 'ragged' set.")
def gram_min_eig(pts):
    P = np.asarray(pts, dtype=np.float64)
    M = Rfun(P[:, None] - P[None, :])
    return np.linalg.eigvalsh((M + M.T) / 2).min()
sets = {
    'uniform h=0.05, n=40':  np.arange(40)*0.05,
    'uniform h=0.20, n=30':  np.arange(30)*0.20,
    'uniform h=0.50, n=14':  np.arange(14)*0.50,
    'clustered near 0, n=30': np.concatenate([np.arange(15)*0.01, 1.0+np.arange(15)*0.01]),
    'wide h=1.0, n=7':       np.arange(7)*1.0,
    'ragged (golden), n=35': (np.arange(35)*0.6180339887) % 3.0,
    'two clusters, n=24':    np.concatenate([np.arange(12)*0.03, 2.0+np.arange(12)*0.03]),
}
worst = None
for name, pts in sets.items():
    lam = gram_min_eig(pts)
    if worst is None or lam < worst[1]: worst = (name, lam)
    print(f"     {name:<26} min eigenvalue = {lam: .6e}  {'ok' if lam > -1e-10 else 'NEGATIVE'}")
print(f"     worst: {worst[0]} at {worst[1]:.3e}")
print(f"     N2 {'HOLDS to numerical tolerance' if worst[1] > -1e-9 else 'FAILS -> TARGET WOULD BE FALSE'}")

# N3: the transform itself, on a hostile frequency grid
print()
print("N3 -- the transform  Rhat(xi) = int R(v) cos(xi v) dv  on a hostile xi grid.")
print("     (This IS the target; Rhat(2x) = L1(x).)  Computed on the FULL line by evenness.")
vfull = np.concatenate([-vg[:0:-1], vg]); Rfull = np.concatenate([Rpos[:0:-1], Rpos])
hvf = hv
def Rhat(xi):
    return simp(Rfull*np.cos(xi*vfull), hvf)
neg = []; mn = None; mnx = None
for k in range(0, 2001):
    xi = k*0.05                     # xi up to 100, i.e. x up to 50
    val = Rhat(xi)
    if val < 0: neg.append((xi, val))
    if mn is None or val < mn: mn, mnx = val, xi
print(f"     xi in [0,100] step 0.05 (2001 pts): negatives = {len(neg)}, min = {mn:.6e} at xi = {mnx:.3f}")
print("     NOTE: at large xi the quadrature floor (~1e-16) dominates the true value")
print("     (Rhat(xi) ~ e^{-pi xi/4}), so large-xi signs here are NOT informative.")
print("     Informative window xi <= 20 (x <= 10):")
neg2 = [(xi, v) for xi, v in neg if xi <= 20]
print(f"       negatives with xi <= 20: {len(neg2)}")

# =====================================================================
print(); print("="*78)
print("SUFFICIENT CONDITIONS -- failure kills only the route")
print("="*78)

# S1: Polya-type.  Structural check first.
print("S1 -- POLYA and every corner-generated class.")
d1 = (Rpos[2:] - Rpos[:-2])/(2*hv)
print(f"     R'(0+) estimated = {(Rpos[1]-Rpos[0])/hv: .6e}  (R is even and smooth => 0)")
print("     A convex + decreasing R on (0,inf) with R'(0+)=0 forces R constant, so POLYA")
print("     cannot apply to ANY smooth even kernel.  Same argument kills every mixture of")
print("     PD generators having a corner at 0 (exp(-lam|v|) mixtures included), since such")
print("     a mixture has R'(0+) = -int lam dmu < 0 unless mu = 0.")
print(f"     measured: R decreasing on (0,inf)? {bool(np.all(np.diff(Rpos) <= 1e-15))}")
print(f"               R convex   on (0,inf)? {bool(np.all(np.diff(Rpos,2) >= -1e-15))}")

# S2: Schoenberg -- g(tau) = R(sqrt(tau)) completely monotone
print()
print("S2 -- SCHOENBERG: R a Gaussian scale mixture <=> g(tau) := R(sqrt(tau)) completely")
print("     monotone, i.e. (-1)^n g^(n) >= 0 for all n.  This class IS compatible with")
print("     smoothness, so it is a live route (unlike S1).")
tau = vg**2
g = Rpos
# use a uniform tau grid to differentiate safely
tu = np.linspace(1e-6, 4.0, 4001); hu2 = tu[1]-tu[0]
gu = Rfun(np.sqrt(tu))
d = [gu]
for k in range(1, 5):
    d.append(np.gradient(d[-1], hu2))
for k in range(1, 5):
    s = ((-1)**k) * d[k][20:-20]
    print(f"     (-1)^{k} g^({k}): min = {s.min(): .6e}   {'>= 0 ok' if s.min() > -1e-9 else 'NEGATIVE -> not CM'}")

# S3: log-concavity / log-convexity of R
print()
print("S3 -- log-concavity / log-convexity of R (a derivative-sign-sequence attack).")
with np.errstate(divide='ignore'):
    lg = np.log(np.maximum(Rpos, 1e-300))
dd = np.diff(lg, 2)
print(f"     (log R)'' : min = {dd.min()/hv**2: .6e}, max = {dd.max()/hv**2: .6e}")
print(f"     log-concave everywhere? {bool(np.all(dd <= 1e-12))}    log-convex? {bool(np.all(dd >= -1e-12))}")

# S4: is R a convolution square?  Necessary: Rhat >= 0 (circular).  Test a PROXY:
print()
print("S4 -- FOURIER CONVOLUTION SQUARE.  R = h*h with h even real <=> Rhat >= 0 (circular).")
print("     Non-circular proxy: the k=0 analogue R0(v) = int Phi(v+p)Phi(v-p) dp IS a")
print("     convolution square ((Phi*Phi)(2v)/2), which is why its transform is Xi^2 >= 0.")
print("     Question: does the p^2 weight preserve a convolution-square structure?")
print("     Exact decomposition (checked below): R(v) = (M2*Phi)(2v) - v^2 (Phi*Phi)(2v).")
# verify that decomposition
tg = np.linspace(-6.6, 6.6, 26400+1); ht = tg[1]-tg[0]
Pt = Phi(tg); M2t = tg**2*Phi(tg)
def conv_at(f, g, s):
    return simp(f*Phi(s-tg) if False else f*np.interp(s-tg, tg, g, left=0, right=0), ht)
print(f"{'v':>8} {'R(v) direct':>20} {'(M2*Phi)(2v) - v^2(Phi*Phi)(2v)':>34} {'reldiff':>12}")
for v in [0.0, 0.2, 0.5, 1.0, 1.5]:
    lhs = R_of(v)
    a = conv_at(M2t, Pt, 2*v)
    b = conv_at(Pt, Pt, 2*v)
    rhs = a - v**2*b
    print(f"{v:>8.2f} {lhs:>20.12f} {rhs:>34.12f} {abs(lhs-rhs)/max(abs(lhs),1e-300):>12.3e}")
print("     READING: the -v^2 term is exactly what breaks the convolution-square form.")
print("     A convolution square has a nonneg transform by construction; R does not have")
print("     that form, so this route supplies no sign.")

# S5: complete monotonicity of Rhat in x^2 / monotonicity of Rhat
print()
print("S5 -- COMPLETE MONOTONICITY IN x^2 of the transform (necessary if R is a Gaussian")
print("     scale mixture).  Rhat would then be decreasing in |xi|.")
xis = np.arange(0, 40.01, 0.25)
vals = np.array([Rhat(x) for x in xis])
ups = int(np.sum(np.diff(vals) > 0))
print(f"     Rhat increases at {ups}/{len(vals)-1} consecutive steps on xi in [0,40]")
print(f"     => {'NOT monotone; Schoenberg route dead' if ups>0 else 'monotone so far'}")

# =====================================================================
print(); print("="*78)
print("TRANSFER TESTS and DECOMPOSITIONS")
print("="*78)

# T1: symmetrized theta terms (batch 13 RS-1, run here at the user's instruction)
print("T1 -- SYMMETRIZED THETA TERMS (no artificial corner).  S_k(u) = phi_k(u) + phi_k(-u).")
print("     Batch 13 issued this as refutation spec RS-1 with the PREDICTION that S_k would")
print("     be nonnegative and satisfy the target.  Run here because batch 14's brief asks")
print("     for it explicitly.  Outcome reported as-is.")
def phi_k(u, k):
    u = np.asarray(u, dtype=np.float64)
    e2 = np.exp(2*u)
    return np.where(-np.pi*k*k*e2 > -700.0,
                    (2*np.pi**2*k**4*np.exp(4.5*u) - 3*np.pi*k**2*np.exp(2.5*u))
                    * np.exp(np.maximum(-np.pi*k*k*e2, -700.0)), 0.0)
print(f"{'k':>4} {'min S_k on [-4,4]':>22} {'at u':>8} {'S_k >= 0 ?':>12}")
tt = np.linspace(-4, 4, 8001)
for k in [1, 2, 3]:
    S = 4*(phi_k(tt, k) + phi_k(-tt, k))
    j = int(np.argmin(S))
    print(f"{k:>4} {S.min():>22.10e} {tt[j]:>8.3f} {str(bool(S.min() >= 0)):>12}")
print("     PREDICTION FROM BATCH 13 (S_k nonnegative): see the column above.")
print("     phi_k(u) < 0 for u < (1/2)log(3/(2 pi k^2)) -- the SECOND theta term dominates")
print("     at large negative u -- so the symmetrised single term is NOT a positive kernel.")

# T2: compactly supported approximation
print()
print("T2 -- COMPACTLY SUPPORTED APPROXIMATION.  Phi_T := Phi * 1_{|t|<=T} (even, nonneg,")
print("     but with a JUMP at |t|=T).  Does the target survive truncation of the support?")
print(f"{'T':>6} {'min Rhat_T on xi<=20':>24} {'at xi':>8} {'negatives':>10}")
for T in [0.5, 1.0, 1.5, 2.0, 3.0]:
    def RT(v):
        mask = (np.abs(v+pg) <= T) & (np.abs(v-pg) <= T)
        return (hp/3.0)*np.dot(wp, np.where(mask, pg**2*Phi(v+pg)*Phi(v-pg), 0.0))
    RTp = np.array([RT(v) for v in vg])
    RTf = np.concatenate([RTp[:0:-1], RTp])
    mnv = None; mnx = None; nneg = 0
    for kk in range(0, 401):
        xi = kk*0.05
        val = simp(RTf*np.cos(xi*vfull), hvf)
        if val < 0: nneg += 1
        if mnv is None or val < mnv: mnv, mnx = val, xi
    print(f"{T:>6.1f} {mnv:>24.6e} {mnx:>8.2f} {nneg:>10}")
print("     READING: a hard cutoff introduces a jump, whose transform decays like 1/xi and")
print("     oscillates in sign -- the same species of artefact as batch 13's corner.")

# T3: antihelix conjugation
print()
print("T3 -- ANTIHELIX CONJUGATION.  The swap v <-> p sends R(v) = int p^2 Phi(v+p)Phi(v-p)dp")
print("     to int v^2 Phi(p+v)Phi(p-v)dv.  Since Phi is even, Phi(p+v)Phi(p-v) =")
print("     Phi(v+p)Phi(v-p) (C3B12.antihelix_swap), so the swapped object is the SAME")
print("     bilinear form read on the other axis: it gives no new sign.  Checked:")
for v in [0.3, 0.9]:
    lhs = R_of(v)
    rhs = (hp/3.0)*np.dot(wp, pg**2 * Phi(pg+v) * Phi(pg-v))
    print(f"     v={v:<5} R(v) = {lhs:.12f}   swapped = {rhs:.12f}   reldiff {abs(lhs-rhs)/lhs:.2e}")

# T4: pi/3 carrier harmonisation -- applicability check
print()
print("T4 -- CARRIER pi/3 HARMONISATION: applicability check, not a scan.")
print("     The pi/3 register governs CELL-REGISTRATION counts N_{pi/3}(e^t) - N_1(e^t).")
print("     R is a MOMENT of the carrier product in the half-gap; its argument v is a cell")
print("     CENTRE, not a registration cell index, and no count is formed anywhere in this")
print("     batch.  So the harmonic register is not at risk and pi/3 is not applicable here.")
print("     Reported as a NULL by design, not run as a unit-1 scan (which would be the")
print("     documented false-null trap).  Sanity: R has no special structure at v = k pi/3:")
for k in range(1, 5):
    v = k*np.pi/3
    print(f"       v = {k} pi/3 = {v:.6f}   R(v) = {float(Rfun(v)):.6e}   R(v)/R(0) = {float(Rfun(v))/R0:.6e}")
print("="*78)
