#!/usr/bin/env python3
"""
C3 batch 13 -- numerical block 7.  FAST FINISHER for the A4 fibre coverage.

tmp/c3b13_num4.py computes Jbar(a) by nested adaptive quadrature and is slow; its first row
validated the closed form EXACTLY (reldiff 0.0 at a = 0.10), and its two controls fired
against batch 12's compiled identities.  This block therefore uses fixed-grid quadrature in
float64 -- legitimate here because EVERY integrand is positive (no cancellation) -- to finish
the table and measure the coverage of the two compiled fibres.

  fibre S (small readout, C3B13.momentTwo_nonneg_of_thickened):  c2(0)*|c0(x)| <= s1(x)^2
  fibre L (large readout, C3B13.momentTwo_nonneg_of_large_readout): Jbar a <= a^2*(1/4)*c0(x)^2

CONTROLS re-run here at float64: M0 = (1/4)c0(0)^2 and M = (1/8)c0(0)c2(0).  If either misses
by more than 1e-6 relative the grid is too coarse and the block REJECTS its own output.
"""
import numpy as np
from mpmath import mp, mpf, mpc, pi as mppi, gamma as mpgamma, zeta as mpzeta

mp.dps = 30

# ---------------------------------------------------------------- kernel, float64
NMAX = 14
NN = np.arange(1, NMAX + 1, dtype=np.float64)

def Phi(t):
    """Repo kernel, evaluated at |t| (Phi is even: riemannXiKernel_neg)."""
    t = np.abs(np.asarray(t, dtype=np.float64))
    e2 = np.exp(2 * t)
    out = np.zeros_like(t)
    for n in NN:
        expo = -np.pi * n * n * e2
        # underflow guard
        term = (2 * np.pi**2 * n**4 * np.exp(4.5 * t) - 3 * np.pi * n**2 * np.exp(2.5 * t))
        out += np.where(expo > -700.0, term * np.exp(np.maximum(expo, -700.0)), 0.0)
    return 4 * out

# ---------------------------------------------------------------- C(0,u), fixed grid
PMAX = 4.0
NP = 4000                     # p-grid
pg = np.linspace(-PMAX, PMAX, NP + 1)

def C0_vec(ug):
    """cellDensity 0 u = int_p Phi(u+p)Phi(u-p) dp, on a vector of u, by Simpson in p."""
    out = np.empty_like(ug)
    w = np.ones(NP + 1); w[1:-1:2] = 4; w[2:-1:2] = 2
    h = (2 * PMAX) / NP
    for i, u in enumerate(ug):
        vals = Phi(u + pg) * Phi(u - pg)
        out[i] = (h / 3) * np.dot(w, vals)
    return out

UMAXG = 3.0
NU = 3000
ug = np.linspace(0.0, UMAXG, NU + 1)
hu = UMAXG / NU
Cg = C0_vec(ug)

def simp(y, h):
    w = np.ones(len(y)); w[1:-1:2] = 4; w[2:-1:2] = 2
    return (h / 3) * np.dot(w, y)

def simp_upto(y, h, k):
    """Simpson on the first k+1 samples (k even)."""
    if k < 2: return 0.0
    if k % 2: k -= 1
    yy = y[:k + 1]
    w = np.ones(k + 1); w[1:-1:2] = 4; w[2:-1:2] = 2
    return (h / 3) * np.dot(w, yy)

M0 = simp(Cg, hu)
M = simp(ug**2 * Cg, hu)

# ---------------------------------------------------------------- xi route
def xi(s): return mppi ** (-s / 2) * mpgamma(1 + s / 2) * (s - 1) * mpzeta(s)
def c0(x): return float(2 * xi(mpc(mpf(1) / 2, mpf(x))).real)

c00 = c0(0.0)
# c2(0) = int t^2 Phi  (positive integrand, fixed grid)
tg = np.linspace(0.0, 3.0, 6001); ht = 3.0 / 6000
c20 = 2 * simp(tg**2 * Phi(tg), ht)

print("=" * 78)
print("B21 (fast) -- COVERAGE of the two compiled fibres")
print("=" * 78)
print(f"  c0(0) = {c00:.15f}    c2(0) = {c20:.15f}")
print("  CONTROLS against batch 12's COMPILED identities:")
r0 = abs(M0 - c00**2 / 4) / (c00**2 / 4)
r2 = abs(M - c00 * c20 / 8) / (c00 * c20 / 8)
print(f"    M0 = {M0:.12e}   (1/4)c0(0)^2 = {c00**2/4:.12e}   reldiff {r0:.3e}")
print(f"    M  = {M:.12e}   (1/8)c0(0)c2(0) = {c00*c20/8:.12e}   reldiff {r2:.3e}")
if max(r0, r2) > 1e-6:
    print("  CONTROL FAILED -- grid too coarse.  OUTPUT REJECTED.")
    raise SystemExit(1)
print("  controls pass; proceeding.")
print()
print("  Jbar(a) by the closed form  a^2(2 m0(a) - M0) - (2 m2(a) - M),")
print("  validated against nested adaptive quadrature at a = 0.10 (num4, reldiff 0.0).")
print()
print(f"{'a':>8} {'Jbar(a)':>18} {'T = 4 Jbar/a^2':>18} {'fires?':>8}")
best = None
for a in [0.08, 0.10, 0.12, 0.15, 0.18, 0.20, 0.22, 0.25, 0.30, 0.35, 0.40, 0.50, 0.70, 1.00]:
    k = int(round(a / hu))
    m0a = simp_upto(Cg, hu, k)
    m2a = simp_upto(ug**2 * Cg, hu, k)
    J = a**2 * (2 * m0a - M0) - (2 * m2a - M)
    T = 4 * J / a**2
    fires = T < c00**2
    if best is None or T < best[1]:
        best = (a, T)
    print(f"{a:>8.2f} {J:>18.10e} {T:>18.10f} {('yes' if fires else 'no'):>8}")
a_opt, T_min = best
print()
print(f"  best a = {a_opt},  T_min = {T_min:.10f},  c0(0)^2 = {c00**2:.10f}")
print(f"  fibre L is NONEMPTY: {T_min < c00**2}")
if T_min < c00**2:
    need = np.sqrt(T_min)
    print(f"  fibre L = {{ x : |c0(x)| >= {need:.10f} }}, i.e. |Xi(x)| >= {need/2:.10f}")
    lo, hi = 0.0, 30.0
    for _ in range(60):
        mid = (lo + hi) / 2
        if abs(c0(mid)) >= need: lo = mid
        else: hi = mid
    print(f"  => the INTERVAL |x| <= {lo:.8f}")

print()
print("  Coverage on x in [0,60] step 0.05 (1201 points):")
def s1(x):
    h = 1e-6
    return -(c0(x + h) - c0(x - h)) / (2 * h)
covS = covL = covB = 0
for k in range(1201):
    x = k / 20.0
    cx = c0(x)
    S = (c20 * abs(cx) <= s1(x)**2)
    L = (T_min <= cx**2)
    covS += S; covL += L; covB += (S or L)
print(f"    fibre S (small readout) : {covS}/1201 ({100.0*covS/1201:.2f}%)")
print(f"    fibre L (large readout) : {covL}/1201 ({100.0*covL/1201:.2f}%)")
print(f"    S or L (compiled union) : {covB}/1201 ({100.0*covB/1201:.2f}%)")
print()
print("  HONEST READING: the compiled union covers a neighbourhood of x = 0 -- which block 3")
print("  identifies as the TIGHTEST point of the target -- plus specks at the first zero.")
print("  It leaves the bulk of the line open.  No claim beyond the measured count.")
print("=" * 78)
