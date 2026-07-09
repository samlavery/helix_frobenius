"""Residues after a cancellation event: existence, re-absorption, dissipation rate.

QUESTION (Sam): after a focal cancellation (a vanishing), does a residue exist?
If so it is re-absorbed into the fiber and dissipates between vanishings at some
fixed rate; earlier research matched GUE for Lehmer pairs with repulsion playing
no role.

DEFINITIONS (fiber-intrinsic; no L anywhere, the fiber is our own tapered bank):
    F(y)  = sum_n (-1)^(n+1) n^(-1/2) w(n/N) e^(-iy ln n)     (eta channel fiber)
    R_k   = |F'(gamma_k)|            the REOPENING RATE at vanishing k
            (= the reciprocal of the residue of 1/F at the vanishing:
             Res_{y=gamma_k} 1/F = 1/F'(gamma_k); exists iff the vanishing is simple)
    tent test: between consecutive vanishings, is |F| a fixed-slope tent
            (dissipation at fixed rate -> mid-gap max ~ R * gap/2, exponent 1 in gap)
            or a local double-zero profile (max ~ C * gap^2 / 4, exponent 2)?
    unfolding: mean spacing delta(t) = 2pi / log(t/2pi); unfolded rate
            Rhat_k = R_k * delta(gamma_k)^(1/2)?  -- we test several normalizations
            empirically and report which (if any) is constant across zeros.

MEASUREMENTS:
  [1] R_k for zeros 1..60 (existence: R_k > 0 <=> simple vanishing, residue exists)
  [2] correlation of R_k with the min neighbor gap (repulsion-linked?) vs
      constancy after unfolding (fixed rate?)
  [3] mid-gap profile: for each consecutive pair, max |F| between them; log-log
      slope of max-vs-gap  (1 = fixed-rate tent, 2 = analytic double-zero)
  [4] the classic LEHMER PAIR (zeros 6709/6710, gamma ~ 7005.06 / 7005.10):
      R at both, mid-pair bump height, compared against BOTH predictions using
      the typical unfolded rate from [1].
  [5] re-absorption exhibit: lane resultants P, M through a vanishing -- the
      common (absorbed) component vs the regrowing imbalance.

Reference ordinates via mpmath.zetazero (verification/targeting only).
"""
import math
import sys

import mpmath as mp
import numpy as np

mp.mp.dps = 20


def fiber(y, N):
    """The eta-channel fiber readout at height y: tapered finite bank, no L."""
    n = np.arange(1, N + 1, dtype=np.float64)
    sgn = np.where(n % 2 == 1, 1.0, -1.0)
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    return complex(np.sum(sgn * w * n ** (-0.5) * np.exp(-1j * y * np.log(n))))


def fiber_lanes(y, N):
    n = np.arange(1, N + 1, dtype=np.float64)
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    term = w * n ** (-0.5) * np.exp(-1j * y * np.log(n))
    P = complex(np.sum(np.where(n % 2 == 1, term, 0)))
    M = complex(np.sum(np.where(n % 2 == 0, term, 0)))
    return P, M


def slope(y, N, h=2e-4):
    return abs(fiber(y + h, N) - fiber(y - h, N)) / (2 * h)


def mean_spacing(t):
    return 2 * math.pi / math.log(t / (2 * math.pi))


def bank_size(t):
    return max(4000, int(60 * t / (2 * math.pi)))


print("[0] internal convergence check (fiber value stable in N)")
for t in (100.0, 7005.0):
    N1, N2 = bank_size(t), 2 * bank_size(t)
    d = abs(fiber(t, N1) - fiber(t, N2))
    print(f"    t={t:>7}: |F_N - F_2N| = {d:.2e}  (N={N1})")

print()
print("[1,2] reopening rates R_k at zeros 1..60 (residue existence + normalization)")
K = 60
gammas = [float(mp.im(mp.zetazero(k))) for k in range(1, K + 1)]
N0 = bank_size(gammas[-1])
R = np.array([slope(g, N0) for g in gammas])
gaps = np.diff(gammas)
min_gap = np.array([gaps[0]] + [min(gaps[i - 1], gaps[i]) for i in range(1, K - 1)] + [gaps[-1]])
delta = np.array([mean_spacing(g) for g in gammas])

print(f"    all R_k > 0 (simple vanishings, residue exists): {bool(np.all(R > 1e-6))}")
print(f"    R_k range: [{R.min():.4f}, {R.max():.4f}]   mean {R.mean():.4f}  cv {R.std()/R.mean():.3f}")
for label, Rn in (("R (raw)", R), ("R*delta", R * delta), ("R*delta^1/2", R * np.sqrt(delta))):
    cv = Rn.std() / Rn.mean()
    print(f"    normalization {label:12s}: coeff of variation = {cv:.3f}")
rho = np.corrcoef(R * delta, min_gap / delta)[0, 1]
rho_raw = np.corrcoef(R, min_gap)[0, 1]
print(f"    corr(unfolded R, unfolded min neighbor gap) = {rho:.3f}   (raw: {rho_raw:.3f})")
print("    -> strong positive corr = gap-linked (analytic/repulsion-like); ~0 = fixed rate")

print()
print("[3] mid-gap bump height vs gap: exponent test (1 = fixed-rate tent, 2 = double-zero)")
mids = []
for i in range(K - 1):
    a, b = gammas[i], gammas[i + 1]
    ys = np.linspace(a, b, 41)[1:-1]
    m = max(abs(fiber(float(y), N0)) for y in ys)
    mids.append(m)
mids = np.array(mids)
gap_unf = gaps / np.array([mean_spacing(0.5 * (gammas[i] + gammas[i + 1])) for i in range(K - 1)])
mid_unf = mids * np.sqrt(delta[:-1])  # bring heights to common scale (same normalization family)
lg, lm = np.log(gap_unf), np.log(mids)
A = np.vstack([lg, np.ones_like(lg)]).T
expo, off = np.linalg.lstsq(A, lm, rcond=None)[0]
print(f"    log-log fit  max|F| ~ gap^p  over 59 consecutive pairs:  p = {expo:.2f}")
r_pred_tent = np.corrcoef(mids, R[:-1] * gaps / 2)[0, 1]
print(f"    corr(mid max, R_left*gap/2) = {r_pred_tent:.3f}  (tent prediction quality)")

print()
print("[4] the classic Lehmer pair (zeros 6709, 6710)")
gl1 = float(mp.im(mp.zetazero(6709)))
gl2 = float(mp.im(mp.zetazero(6710)))
gl0 = float(mp.im(mp.zetazero(6708)))
gl3 = float(mp.im(mp.zetazero(6711)))
NL = bank_size(gl2)
print(f"    gamma = {gl1:.6f}, {gl2:.6f}   gap = {gl2-gl1:.6f}  (mean spacing {mean_spacing(gl1):.4f},"
      f" unfolded gap {(gl2-gl1)/mean_spacing(gl1):.4f})")
Rl1, Rl2 = slope(gl1, NL), slope(gl2, NL)
Rn0, Rn3 = slope(gl0, NL), slope(gl3, NL)
ys = np.linspace(gl1, gl2, 41)[1:-1]
bump = max(abs(fiber(float(y), NL)) for y in ys)
print(f"    R at pair zeros: {Rl1:.5f}, {Rl2:.5f}   R at neighbors (6708, 6711): {Rn0:.4f}, {Rn3:.4f}")
typ_unf = float(np.mean(R * np.sqrt(delta)))
tent_pred = 0.5 * (gl2 - gl1) * typ_unf / math.sqrt(mean_spacing(gl1))
print(f"    mid-pair bump max|F| = {bump:.6f}")
print(f"    fixed-rate tent prediction (typical unfolded rate): {tent_pred:.6f}"
      f"   ratio obs/pred = {bump / tent_pred:.3f}")
quad_scale = float(np.median(mids / (gap_unf ** 2)))
quad_pred = quad_scale * ((gl2 - gl1) / mean_spacing(gl1)) ** 2
print(f"    double-zero quadratic prediction (median low-zero scale): {quad_pred:.6f}"
      f"   ratio obs/pred = {bump / quad_pred:.3f}")

print()
print("[5] re-absorption exhibit: lanes through the Lehmer pair (P, M common vs imbalance)")
for y in (gl1 - 0.05, gl1, 0.5 * (gl1 + gl2), gl2, gl2 + 0.05):
    P, M = fiber_lanes(float(y), NL)
    common = 0.5 * abs(P + M)
    imb = abs(P - M)
    print(f"    y = {y:>12.6f}:  |P|={abs(P):8.4f}  |M|={abs(M):8.4f}  common={common:8.4f}  imbalance={imb:.6f}")
