#!/usr/bin/env python3
"""
Attempt 040 — the edge-split executed exactly (theta = 1/2, so 2L = l: clean).

Objects (per-pair kernels, Z-normalized by (pi L)^{-2} throughout):
  G_tail(v) = (1/(piL))^2 * pi L^2 [cos(lv)/l - v*(pi/2 - Si(lv))]        (exact)
  E(v)      = -(1/(piL))^2 * (pi L^2/l^2) * sin(lv)/v                     (band-limited edge)
  G_sm      = G_tail - E                                                   (smooth remainder)
Checks:
  A. G_tail(0) = (1/(piL))^2 * pi L^2/l  (= 1/(pi l) at theta=1/2: 035's G_t0)  [conventions]
  B. envelope |G_sm(v)| <= (1/(piL))^2 * 2 pi L^2/(l^3 v^2) for lv >~ 3         [Si remainder]
  C. spectral identity on the zeros: sum_pairs G_tail = sum_pairs E + sum_pairs G_sm
     (trivial pointwise; computed to verify normalizations end-to-end)
  D. the readings: sum_pairs E (signed, = a band reading), sum_pairs G_sm (signed),
     and the CHARGES: sum |G_sm| actual, and Lemma-M-graded bound.
Everything reported in int Z^2/T units (divide pair-sums by window length; add diagonal
separately for reference).
"""
import numpy as np
from scipy.special import sici
import time

REPO = "/Users/samuellavery/work/helix_frobenius"
zeros = np.sort(np.load(f"{REPO}/tmp/att019_zeros_to20k.npy"))
T0, T1 = 3000.0, 19000.0
z = zeros[(zeros > T0) & (zeros < T1)]
N = len(z)
Tlen = T1 - T0
Tmid = np.exp(np.mean(np.log(z)))
l = np.log(Tmid/(2*np.pi))
theta = 0.5
L = theta*l
norm = 1.0/(np.pi*L)**2

def G_tail(v):
    v = np.asarray(v, dtype=float)
    out = np.empty_like(v)
    av = np.abs(v)
    si, _ = sici(l*av)
    out = norm*np.pi*L**2*(np.cos(l*av)/l - av*(np.pi/2 - si))
    return out

def E_edge(v):
    v = np.asarray(v, dtype=float)
    av = np.where(np.abs(v) < 1e-12, 1e-12, np.abs(v))
    return -norm*(np.pi*L**2/l**2)*np.sin(l*av)/av

# A: value at 0
print(f"l={l:.3f} L={L:.3f}  G_tail(0) = {G_tail(1e-14):.6f}  vs  1/(pi l) = {1/(np.pi*l):.6f}", flush=True)

# B: envelope check
vv = np.linspace(0.05, 30, 4000)
Gs = G_tail(vv) - E_edge(vv)
env = norm*2*np.pi*L**2/(l**3*vv**2)
bad = np.sum(np.abs(Gs[vv > 3/l]) > env[vv > 3/l]*1.05)
print(f"envelope violations (lv>3): {bad}/{np.sum(vv>3/l)}   max|Gs|/env = {np.max(np.abs(Gs[vv>3/l])/env[vv>3/l]):.3f}", flush=True)
print(f"G_sm(0) = {G_tail(1e-14) - E_edge(1e-14):.6f}  (expect ~ 2/(pi l) = {2/(np.pi*l):.6f})", flush=True)

# C+D: pair sums over the zeros (signed) and absolute charges
t0 = time.time()
win = 250.0
sums = {"tail": 0.0, "edge": 0.0, "smooth": 0.0, "abs_smooth": 0.0, "abs_edge": 0.0}
for i, g in enumerate(z):
    lo, hi = np.searchsorted(z, g - win), np.searchsorted(z, g + win)
    d = z[lo:hi] - g
    d = d[d != 0.0]
    gt = G_tail(d); ee = E_edge(d)
    sums["tail"] += np.sum(gt)
    sums["edge"] += np.sum(ee)
    sums["smooth"] += np.sum(gt - ee)
    sums["abs_smooth"] += np.sum(np.abs(gt - ee))
    sums["abs_edge"] += np.sum(np.abs(ee))
# to int Z^2/T units: pair-sum / Tlen
for k in sums:
    sums[k] /= Tlen
diag_tail = N/Tlen*G_tail(1e-14)   # diagonal of the tail part
print(f"[{time.time()-t0:.0f}s] in int Z^2/T units:", flush=True)
print(f"  diag_tail = {diag_tail:.5f}", flush=True)
print(f"  sum_pairs G_tail (signed offdiag) = {sums['tail']:+.5f}", flush=True)
print(f"  sum_pairs E      (signed offdiag) = {sums['edge']:+.5f}", flush=True)
print(f"  sum_pairs G_sm   (signed offdiag) = {sums['smooth']:+.5f}", flush=True)
print(f"  charge sum|G_sm| (offdiag)        = {sums['abs_smooth']:.5f}", flush=True)
print(f"  charge sum|E|    (offdiag)        = {sums['abs_edge']:.5f}", flush=True)
print(f"  TAIL total (diag+signed) = {diag_tail + sums['tail']:+.5f}   [= the row-content: Row/(2pi^2) ~ {1.09/ (2*np.pi**2):.5f} at Row~1.09... note Row/(2pi^2) with Row~0.9: {0.9/(2*np.pi**2):.5f}]", flush=True)
