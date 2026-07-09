"""Reverb at scale: crossover gap, cluster product law (pairs/triples/quads), CUE test.

Pipeline (fiber-intrinsic: zeros and rates extracted from OUR tapered bank grid;
mpmath zetazero only spot-verifies 10 sampled ordinates at the end):

  [1] grid |F(y)| on y in [14, 2000] via the phase-recurrence sweep;
      extract every vanishing gamma_k (complex Newton step) and its
      reopening rate R_k = |F'(gamma_k)| from the same grid.
  [2] sanity: zero count vs Riemann-von-Mangoldt; spot-check vs zetazero.
  [3] crossover: normalized mid-gap bump vs unfolded gap; exponent in the
      small-gap and large-gap strata; two-branch fit -> crossover gap g*.
  [4] cluster product law: Rhat_k = R_k / local-median(R);
      S_k(W) = prod of unfolded distances to neighbors within window W.
      Fit window W* by variance explained; report suppression by cluster
      class (isolated / pair / triple / quad members) raw and corrected.
  [5] CUE Monte Carlo: |P'(lambda_k)| = prod_{j!=k} |lambda_k - lambda_j|
      for Haar-unitary eigenangles, normalized by median; KS/quantile
      comparison against Rhat (should match if GUE-ness = gap configuration)
      and against Rhat/S (should be NARROWER: product law absorbs the GUE shape).
"""
import math

import mpmath as mp
import numpy as np

mp.mp.dps = 20
rng = np.random.default_rng(7)

Y0, Y1, DY = 14.0, 2000.0, 0.02
NBANK = 26000


def mean_spacing(t):
    return 2 * math.pi / math.log(t / (2 * math.pi))


print("[1] fiber grid sweep and zero/rate extraction")
n = np.arange(1, NBANK + 1, dtype=np.float64)
sgn = np.where(n % 2 == 1, 1.0, -1.0)
u = n / NBANK
w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
amp = sgn * w * n ** (-0.5)
ln = np.log(n)

ny = int((Y1 - Y0) / DY) + 1
ys = Y0 + DY * np.arange(ny)
z = amp * np.exp(-1j * Y0 * ln)
step = np.exp(-1j * DY * ln)
F = np.empty(ny, dtype=np.complex128)
for j in range(ny):
    F[j] = z.sum()
    z *= step
absF = np.abs(F)

# convergence spot check at the top of the range with a doubled bank
def fiber_ref(y, N):
    m = np.arange(1, N + 1, dtype=np.float64)
    s = np.where(m % 2 == 1, 1.0, -1.0)
    v = m / N
    ww = np.where(v < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - v * v, 1e-300, None)), 0.0)
    return complex(np.sum(s * ww * m ** (-0.5) * np.exp(-1j * y * np.log(m))))

drift = abs(F[-1] - fiber_ref(float(ys[-1]), NBANK))
conv = abs(fiber_ref(1999.0, NBANK) - fiber_ref(1999.0, 2 * NBANK))
print(f"    recurrence drift at y=2000: {drift:.2e}   taper floor |F_N-F_2N|: {conv:.2e}")

gammas, rates = [], []
for j in range(1, ny - 1):
    if absF[j] < absF[j - 1] and absF[j] < absF[j + 1] and absF[j] < 0.25:
        Fp = (F[j + 1] - F[j - 1]) / (2 * DY)
        if abs(Fp) < 1e-12:
            continue
        gamma = float(ys[j] - (F[j] / Fp).real)
        gammas.append(gamma)
        rates.append(abs(Fp))
gammas = np.array(gammas)
rates = np.array(rates)
print(f"    vanishings found: {len(gammas)}   (first {gammas[0]:.6f}, last {gammas[-1]:.3f})")

print()
print("[2] sanity")
T = float(gammas[-1])
NvM = T / (2 * math.pi) * math.log(T / (2 * math.pi)) - T / (2 * math.pi) + 7.0 / 8.0
print(f"    Riemann-von-Mangoldt N(T) = {NvM:.1f}  vs found {len(gammas)}")
idx = rng.choice(len(gammas), 10, replace=False)
worst = 0.0
for i in sorted(idx):
    ref = float(mp.im(mp.zetazero(int(i) + 1)))
    worst = max(worst, abs(ref - gammas[i]))
print(f"    spot-check 10 ordinates vs zetazero: worst |diff| = {worst:.2e}")

spacing = np.array([mean_spacing(g) for g in gammas])
gaps = np.diff(gammas)
gap_unf = gaps / spacing[:-1]

print()
print("[3] crossover: normalized mid-gap bump vs unfolded gap")
bump = np.empty(len(gaps))
gidx = ((gammas - Y0) / DY).astype(int)
for i in range(len(gaps)):
    a, b = gidx[i] + 2, gidx[i + 1] - 1
    bump[i] = absF[a:b].max() if b > a else np.nan
ok = ~np.isnan(bump)
# local normalization of bump scale (running median over 101 neighbors)
med_b = np.array([np.median(bump[max(0, i - 50):i + 51]) for i in range(len(bump))])
bn = bump / med_b
strata = [("g < 0.5 ", gap_unf < 0.5), ("0.5-1.0 ", (gap_unf >= 0.5) & (gap_unf < 1.0)),
          ("1.0-1.6 ", (gap_unf >= 1.0) & (gap_unf < 1.6)), ("g >= 1.6", gap_unf >= 1.6)]
print(f"    {'stratum':>9} {'count':>6} {'fit exponent p':>15}")
for name, sel in strata:
    s = sel & ok & (bn > 0)
    if s.sum() > 8:
        p = np.polyfit(np.log(gap_unf[s]), np.log(bn[s]), 1)[0]
        print(f"    {name:>9} {int(s.sum()):>6} {p:>15.2f}")
small = (gap_unf < 0.45) & ok
large = (gap_unf > 1.1) & ok
c2 = float(np.median(bn[small] / gap_unf[small] ** 2)) if small.sum() else float("nan")
c1 = float(np.median(bn[large] / gap_unf[large]))
gstar = c1 / c2 if c2 > 0 else float("nan")
print(f"    branch scales: linear c1 = {c1:.3f}, quadratic c2 = {c2:.3f}  ->  crossover g* = {gstar:.2f} spacings")

print()
print("[4] cluster product law (pairs, triples, quads)")
# two-pass baseline: local median over ISOLATED zeros only (no neighbor within 0.6 sp),
# so cluster suppression does not contaminate its own baseline
iso0 = np.ones(len(gammas), dtype=bool)
iso0[1:] &= (gaps / spacing[:-1]) > 0.6
iso0[:-1] &= (gaps / spacing[:-1]) > 0.6
med_R = np.empty(len(rates))
for i in range(len(rates)):
    lo, hi = max(0, i - 60), i + 61
    pool = rates[lo:hi][iso0[lo:hi]]
    med_R[i] = np.median(pool if len(pool) > 10 else rates[lo:hi])
Rhat = rates / med_R

def S_of(W):
    S = np.ones(len(gammas))
    for k in range(len(gammas)):
        j = k - 1
        while j >= 0 and (gammas[k] - gammas[j]) / spacing[k] < W:
            S[k] *= (gammas[k] - gammas[j]) / spacing[k]
            j -= 1
        j = k + 1
        while j < len(gammas) and (gammas[j] - gammas[k]) / spacing[k] < W:
            S[k] *= (gammas[j] - gammas[k]) / spacing[k]
            j += 1
    return S

print(f"    {'window W':>9} {'var explained':>14} {'beta (slope)':>13}")
best = None
for W in (0.5, 0.75, 1.0, 1.25, 1.5, 2.0):
    S = S_of(W)
    sel = S < 0.999999  # zeros with at least one neighbor inside the window
    if sel.sum() < 20:
        continue
    lS, lR = np.log(S[sel]), np.log(Rhat[sel])
    beta, b0 = np.polyfit(lS, lR, 1)
    resid = lR - (beta * lS + b0)
    ve = 1 - resid.var() / lR.var()
    print(f"    {W:>9.2f} {ve:>14.3f} {beta:>13.2f}")
    if best is None or ve > best[1]:
        best = (W, ve, beta)
Wstar = best[0]
S = S_of(Wstar)
print(f"    best window W* = {Wstar} spacings (measured reverb window; compare g* = {gstar:.2f})")

nbr = np.array([int(round(-math.log(max(s, 1e-300)) > 0)) for s in S])  # placeholder replaced below
count_nbr = np.zeros(len(gammas), dtype=int)
for k in range(len(gammas)):
    c = 0
    j = k - 1
    while j >= 0 and (gammas[k] - gammas[j]) / spacing[k] < Wstar:
        c += 1
        j -= 1
    j = k + 1
    while j < len(gammas) and (gammas[j] - gammas[k]) / spacing[k] < Wstar:
        c += 1
        j += 1
    count_nbr[k] = c
print(f"    {'class':>16} {'count':>6} {'median Rhat':>12} {'median Rhat/S':>14}")
for cls, name in ((0, "isolated"), (1, "pair member"), (2, "triple member"), (3, "quad+ member")):
    sel = count_nbr == cls if cls < 3 else count_nbr >= 3
    if sel.sum():
        print(f"    {name:>16} {int(sel.sum()):>6} {np.median(Rhat[sel]):>12.3f} {np.median(Rhat[sel]/S[sel]):>14.3f}")
cv_raw = Rhat.std() / Rhat.mean()
corrected = Rhat / S
cv_cor = corrected.std() / corrected.mean()
print(f"    cv(Rhat) = {cv_raw:.3f}   cv(Rhat/S) = {cv_cor:.3f}")

tight3 = None
for k in range(1, len(gammas) - 1):
    span = (gammas[k + 1] - gammas[k - 1]) / spacing[k]
    if tight3 is None or span < tight3[0]:
        tight3 = (span, k)
span3, k3 = tight3
print(f"    tightest triple: span {span3:.3f} spacings at gamma = "
      f"{gammas[k3-1]:.4f}/{gammas[k3]:.4f}/{gammas[k3+1]:.4f}; "
      f"Rhat = {Rhat[k3-1]:.3f}/{Rhat[k3]:.3f}/{Rhat[k3+1]:.3f}, "
      f"Rhat/S = {Rhat[k3-1]/S[k3-1]:.3f}/{Rhat[k3]/S[k3]:.3f}/{Rhat[k3+1]/S[k3+1]:.3f}")

np.savez("tmp/reverb_data.npz", gammas=gammas, rates=rates, Rhat=Rhat, S=S,
         bump=bump, gap_unf=gap_unf, count_nbr=count_nbr)

print()
print("[5] CUE comparison, Keating-Snaith dictionary: matrix size N = log(t/2pi) ~ 6")
M, NC = 3000, 6
cue_n_list, cue_cor_list = [], []
sp_c = 2 * math.pi / NC
for _ in range(M):
    G = (rng.standard_normal((NC, NC)) + 1j * rng.standard_normal((NC, NC))) / math.sqrt(2)
    Q, R = np.linalg.qr(G)
    Q = Q * (np.diagonal(R) / np.abs(np.diagonal(R)))
    ang = np.sort(np.angle(np.linalg.eigvals(Q)))
    lam = np.exp(1j * ang)
    vals, Ts = [], []
    for k in range(NC):
        d = np.abs(lam[k] - np.delete(lam, k))
        vals.append(np.exp(np.sum(np.log(d))))
        arc = np.abs(np.angle(lam[k] * np.conj(np.delete(lam, k)))) / sp_c
        close = arc < 0.5
        Ts.append(np.prod(arc[close]) if np.any(close) else 1.0)
    vals = np.array(vals); Ts = np.array(Ts)
    cue_n_list.append(vals)      # N=6 blocks ~ the fiber's local window; normalize pooled
    cue_cor_list.append(vals / Ts)
cue_n = np.concatenate(cue_n_list)
cue_n = cue_n / np.median(cue_n)
cue_cor = np.concatenate(cue_cor_list)
cue_cor = cue_cor / np.median(cue_cor)
data_n = Rhat / np.median(Rhat)
cor_n = corrected / np.median(corrected)

def ks(a, b):
    allv = np.sort(np.concatenate([a, b]))
    ca = np.searchsorted(np.sort(a), allv, side="right") / len(a)
    cb = np.searchsorted(np.sort(b), allv, side="right") / len(b)
    return float(np.max(np.abs(ca - cb)))

qs = (5, 25, 50, 75, 95)
print(f"    {'quantile %':>11} {'CUE |P′|':>10} {'fiber Rhat':>11} {'Rhat/S':>8}")
for q in qs:
    print(f"    {q:>11} {np.percentile(cue_n, q):>10.3f} {np.percentile(data_n, q):>11.3f} "
          f"{np.percentile(cor_n, q):>8.3f}")
print(f"    KS(CUE, Rhat)   = {ks(cue_n, data_n):.3f}")
print(f"    KS(CUE/T, Rhat/S) = {ks(cue_cor / np.median(cue_cor), cor_n):.3f}   (both cluster-corrected)")
print(f"    spread: sd(log CUE) = {np.log(cue_n).std():.3f}  sd(log Rhat) = {np.log(data_n).std():.3f}")
print(f"            sd(log CUE/T) = {np.log(cue_cor).std():.3f}  sd(log Rhat/S) = {np.log(cor_n).std():.3f}")
