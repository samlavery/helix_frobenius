#!/usr/bin/env python3
"""
Attempt 028 (CGdL x Sylvester transplant) — matrix-level verification harness.

Pipeline:
 1. Load the S=2 SDP atoms (Delta=0.01). Kernel on the circle theta = Delta*l*v:
        p(theta) = c0 + 2 sum_j c_j cos(j theta)  >= 0.
 2. Spectral factorization (Fejér–Riesz on the circle): a(z), |a(e^{i th})|^2 = p(theta).
    GATE A: reconstruction error.
 3. Family: Psi(v) = sum_k a_k e^{i k Delta l v} (one period, truncated), Gabor grid
    tau_j = T + j*h2, h2 = pi/l (doubled density) over a window [T, 2T'].
    GATE B: Psi decay within the period; unit constancy Sum_j |Psi(gamma - tau_j)|^2.
 4. Configurations from true zeros (att019 cache) + adversarial edits (their §8(5)):
    doubles, off-line pairs at several depths, mixed, near-extremal (2/3 s + 1/6 d).
 5. For each: A_{jj'} = Sum_rho m_rho Psi(gamma_rho - tau_j) conj(Psi(bar-gamma_rho - tau_j')),
    normalized units; test  3 s1 + 4 s2 + 4 p  >=  4 tr Ahat - ||Ahat||_F^2 - edge slop.
 6. Fejér baseline (their flat-window kernel at lambda=1) same pipeline, same configs:
    the certificate improvement on TRUE zeros ~ (Z_Fejer - Z_geff) modulo finite-T.
"""
import numpy as np
import time

REPO = "/Users/samuellavery/work/helix_frobenius"

# ---------- 1. kernel atoms ----------
dat = np.load(f"{REPO}/tmp/att027_c_S2.npy")
xs, cv = dat[0], dat[1]
Delta = xs[1] - xs[0]
n = len(xs) - 1
# repair mild SCS infeasibility: lift c0 until min_theta p >= margin
th = np.linspace(0, 2*np.pi, 200001)
pth = cv[0] + 2*(np.cos(np.outer(th, np.arange(1, n+1))) * cv[1:]).sum(axis=1)
lift = max(0.0, -(pth.min())) + 1e-8
cv0 = cv.copy(); cv0[0] += lift
Znum = cv[0]/Delta + 2*(xs[1:][xs[1:] <= 1.0]*cv[1:][xs[1:] <= 1.0]).sum()
print(f"kernel: n={n} Delta={Delta:.4f}  min p = {pth.min():+.2e} -> lift {lift:.2e}"
      f"   Z(atoms) = {Znum:.7f}", flush=True)

# ---------- 2. spectral factorization ----------
# roots of P(z) = sum_{j=-n..n} c_|j| z^{j+n}; take roots inside unit circle
coeffs = np.concatenate([cv0[::-1], cv0[1:]])          # z^0 .. z^{2n}, c_{-n}..c_n
P = np.polynomial.polynomial.Polynomial(coeffs)
roots = P.roots()
inside = roots[np.abs(roots) < 1.0 - 1e-12]
onc = roots[np.abs(np.abs(roots) - 1.0) <= 1e-12]
# pair up on-circle roots (should be even multiplicity); take half
onc_sorted = onc[np.argsort(np.angle(onc))]
take_onc = onc_sorted[::2] if len(onc) else np.array([])
sel = np.concatenate([inside, take_onc])
assert len(sel) == n, f"factorization root count {len(sel)} != {n} (|roots|={len(roots)}, onc={len(onc)})"
a = np.polynomial.polynomial.polyfromroots(sel)         # monic, degree n
# scale: |a|^2 integrates to c0 -> sum |a_k|^2 = c0
a = a * np.sqrt(cv0[0] / np.sum(np.abs(a)**2))
# GATE A
prec = np.abs(np.polynomial.polynomial.polyval(np.exp(1j*th[:20000]), a))**2
pref = cv0[0] + 2*(np.cos(np.outer(th[:20000], np.arange(1, n+1))) * cv0[1:]).sum(axis=1)
gateA = np.max(np.abs(prec - pref)) / np.max(pref)
print(f"GATE A (factorization reconstr.): rel err = {gateA:.2e}", flush=True)

# ---------- 3. family ----------
T0 = 1000.0
l = np.log(T0/(2*np.pi))
period = 2*np.pi/(Delta*l)
h2 = np.pi/l
W = 800.0                      # tau-window [T0, T0+W]
taus = T0 + h2*np.arange(int(W/h2))
d2 = len(taus)

def Psi(v):
    """Psi(v) = sum_k a_k e^{i k Delta l v}, v complex array."""
    z = np.exp(1j*Delta*l*np.asarray(v, dtype=complex))
    return np.polynomial.polynomial.polyval(z, a)

# GATE B: decay + unit constancy
vg = np.linspace(-period/2, period/2, 4001)
Pv = np.abs(Psi(vg))
print(f"GATE B: |Psi| center/edge = {Pv.max():.3f}/{np.max(Pv[np.abs(vg)>period/4]):.4f} "
      f"(period {period:.1f}, window {W})", flush=True)
gmid = T0 + W/2
units = [np.sum(np.abs(Psi(g - taus))**2) for g in [gmid, gmid+0.31, gmid+1.73, gmid-5.11]]
print(f"GATE B2: unit Sum|Psi(g-tau_j)|^2 at 4 interior heights: "
      + " ".join(f"{u:.5f}" for u in units), flush=True)
UNIT = np.mean(units)

# ---------- 4. configurations ----------
zeros = np.load(f"{REPO}/tmp/att019_zeros_to20k.npy")
gam = zeros[(zeros > T0 + 5) & (zeros < T0 + W - 5)]
print(f"config base: {len(gam)} true zeros in ({T0+5:.0f}, {T0+W-5:.0f})", flush=True)

def config_true():
    return [(g, 0.0, 1) for g in gam]                       # (gamma, y=beta-1/2, mult)
def config_doubles():
    return [(g, 0.0, 2) for g in gam[::2]]
def config_pairs(depth):
    out = []
    for g in gam[::2]:
        out += [(g, depth, 1), (g, -depth, 1)]
    return out
def config_mixed():
    out = []
    for i, g in enumerate(gam):
        if i % 4 == 0:
            out.append((g, 0.05, 1)); out.append((g, -0.05, 1))
        elif i % 4 == 1:
            continue
        else:
            out.append((g, 0.0, 1))
    return out
def config_extremal():
    # per 4 consecutive true zeros: 2 simple + 1 double (count 4), 4th ordinate dropped
    out = []
    for i in range(0, len(gam)-3, 4):
        out += [(gam[i], 0.0, 1), (gam[i+1], 0.0, 1), (gam[i+2], 0.0, 2)]
    return out

def counts(cfg):
    s1 = sum(1 for (_, y, m) in cfg if y == 0.0 and m == 1)
    s2 = sum(1 for (_, y, m) in cfg if y == 0.0 and m >= 2)
    pp = sum(1 for (_, y, m) in cfg if y > 0.0)             # one per pair (y>0 member)
    N = sum(m for (_, y, m) in cfg)
    return s1, s2, pp, N

# ---------- 5. matrix test ----------
def run(cfg, name, kernel="geff"):
    t0 = time.time()
    s1, s2, pp, N = counts(cfg)
    A = np.zeros((d2, d2), dtype=complex)
    for (g, y, m) in cfg:
        grho = g - 1j*y                                     # gamma_rho = gamma - i y
        u = Psi(grho - taus)                                # row vector over tau_j
        v = np.conj(Psi(np.conj(grho) - taus))              # bar-gamma_rho leg
        A += m * np.outer(u, v)
    Ah = A / UNIT
    trA = np.real(np.trace(Ah))
    frob = np.real(np.sum(Ah * np.conj(Ah.T)))              # ||A||_F^2 = tr(A A^dag); A Hermitian up to edge
    herm = np.max(np.abs(A - A.conj().T)) / np.max(np.abs(A))
    LHS = 3*s1 + 4*s2 + 4*pp
    RHS = 4*trA - frob
    print(f"  {name:22s} N={N:4d} s1={s1:4d} s2={s2:3d} p={pp:3d} | "
          f"herm {herm:.1e} | trA {trA:8.1f} | ||A||F^2 {frob:9.1f} | "
          f"LHS {LHS:5d}  RHS {RHS:8.1f}  slack {LHS-RHS:+8.1f}  cert/N {(RHS-2*N)/N:+.4f}"
          f"  [{time.time()-t0:.0f}s]", flush=True)
    return trA, frob, N

print("=== counting inequality, kernel g_eff (S=2 optimal) ===", flush=True)
run(config_true(),      "TRUE (all simple)")
run(config_doubles(),   "all doubles")
run(config_pairs(1e-4), "pairs depth 1e-4")
run(config_pairs(0.2),  "pairs depth 0.2")
run(config_pairs(0.45), "pairs depth 0.45")
run(config_mixed(),     "mixed 50/25")
run(config_extremal(),  "extremal 2/3+1/6")
