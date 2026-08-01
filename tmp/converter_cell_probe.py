"""Converter probe: the two local cell statements of HarmonizedCellTelescoping.lean.

Native ledger  Smult(t) = N_mult(t) - 1 - theta(t)/pi  measured on harmonized cells.
Targets (the file's two named inputs, numerics before Lean):
  (L1) boundary accumulation  B_n = int_{g_0}^{g_n} Smult dt   -- need o(g_n); measure rate
  (L2) single-cell abs mass   M_n = int_{cell n} |Smult| dt    -- need o(g_n); measure rate
Plus the mu6/pi-3 sub-cell decomposition of each residue (harmonic-scale law: unit-1-only
scans give false nulls; measure whether pi-cell balance is assembled from cancelling
pi/3 sub-residues).

Event heights = locator-validated zero ordinates (focal-closure cross-validated 1e-12);
the cached zeta ordinates serve as the certified event list -- readout-verification role,
not a locator.  theta = Riemann-Siegel theta via scipy loggamma (exact formula).
"""

import bisect
import numpy as np
from scipy.special import loggamma

ZCACHE = "/Users/samuellavery/work/helix_frobenius/tmp/zeta_zeros_cache.txt"
GCACHE = "/Users/samuellavery/work/helix_frobenius/tmp/gram_cache.txt"

zeros = [float(x) for x in open(ZCACHE).read().split()]
gz = [float(x) for x in open(GCACHE).read().split()]
gram = gz[0::2]  # theta(g_n) = n*pi
print("zeros: %d (top %.3f)   gram pts: %d (top %.3f)" % (len(zeros), zeros[-1], len(gram), gram[-1]))

def theta(t):
    t = np.asarray(t, dtype=float)
    return np.imag(loggamma(0.25 + 0.5j * t)) - 0.5 * t * np.log(np.pi)

def theta_prime(t):
    # d/dt Im lngamma(1/4+it/2) = Re psi(1/4+it/2)/2; asymptotic suffices for Newton seeds
    return 0.5 * np.log(np.asarray(t) / (2 * np.pi))

# ---- validation anchors (frozen instrument) ----
gs = np.array(gram)
dev = np.abs(theta(gs) - np.pi * np.arange(len(gs)))
print("anchor 1: max |theta(g_n) - n pi| = %.2e" % dev.max())
n_chk = [0, 100, 2500, 4999]
for n in n_chk:
    N = bisect.bisect_right(zeros, gram[n])
    s = N - 1 - theta(gram[n]) / np.pi
    if abs(s - round(s)) > 1e-8:
        raise SystemExit("anchor 2 FAILED at n=%d: S(g_n)=%.6f not integer" % (n, s))
print("anchor 2: S(g_n) integer at sampled ticks (S values: %s)" %
      [int(round(bisect.bisect_right(zeros, gram[n]) - 1 - n)) for n in n_chk])

# usable range: complete zero counts only
T_top = zeros[-1] - 5.0
M = max(n for n in range(len(gram)) if gram[n] <= T_top)
print("cells: g_0=%.3f .. g_%d=%.3f" % (gram[0], M, gram[M]))

# ---- exact integrals ----
XGL, WGL = np.polynomial.legendre.leggauss(8)

def int_theta(a, b):
    m, h = 0.5 * (a + b), 0.5 * (b - a)
    return h * np.dot(WGL, theta(m + h * XGL))

def int_smult(a, b):
    """exact int_a^b Smult:  N piecewise-constant + exact event overlaps - (b-a) - int theta/pi"""
    Na = bisect.bisect_right(zeros, a)
    lo, hi = bisect.bisect_right(zeros, a), bisect.bisect_right(zeros, b)
    s = Na * (b - a) + sum(b - zeros[i] for i in range(lo, hi))
    return s - (b - a) - int_theta(a, b) / np.pi

def smult(t):
    return bisect.bisect_right(zeros, t) - 1 - float(theta(t)) / np.pi

def int_abs_smult(a, b):
    """split at events; on each piece Smult = c - theta/pi strictly decreasing -> <=1 root"""
    pts = [a] + [z for z in zeros[bisect.bisect_right(zeros, a):bisect.bisect_right(zeros, b)]] + [b]
    total = 0.0
    for u, v in zip(pts[:-1], pts[1:]):
        if v - u < 1e-12:
            continue
        su, sv = smult(u + 1e-9), smult(v - 1e-9)
        if su * sv >= 0:
            total += abs(int_smult(u, v))
        else:
            c = bisect.bisect_right(zeros, u + 1e-9) - 1  # Smult = c - theta/pi on (u,v)
            # Newton for theta(r) = c*pi
            r = 0.5 * (u + v)
            for _ in range(50):
                step = (float(theta(r)) - c * np.pi) / float(theta_prime(r))
                r -= step
                r = min(max(r, u), v)
                if abs(step) < 1e-11:
                    break
            total += abs(int_smult(u, r)) + abs(int_smult(r, v))
    return total

# ---- pi-cells (Gram) ----
A = np.array([int_smult(gram[n], gram[n + 1]) for n in range(M)])
Mass = np.array([int_abs_smult(gram[n], gram[n + 1]) for n in range(M)])
B = np.concatenate([[0.0], np.cumsum(A)])  # B[n] = int_{g_0}^{g_n}

print("\n== (L1) boundary accumulation B_n = int Smult ==")
print("range: [%.4f, %.4f]   final B_M = %.4f" % (B.min(), B.max(), B[-1]))
for frac in (0.25, 0.5, 1.0):
    n = int(M * frac)
    print("  n=%4d  g_n=%8.2f  B_n=%+.4f   B_n/log(g_n)=%+.4f   B_n/g_n=%+.2e"
          % (n, gram[n], B[n], B[n] / np.log(gram[n]), B[n] / gram[n]))
# growth of running max |B| vs log g
runmax = np.maximum.accumulate(np.abs(B[1:]))
print("  running max|B| at M/4, M/2, M: %.4f  %.4f  %.4f" % (runmax[M // 4], runmax[M // 2], runmax[-1]))

print("\n== (L2) per-cell residues A_n and abs mass M_n ==")
W = 500
for lab, arr in (("A", np.abs(A)), ("mass", Mass)):
    wmax = [arr[i:i + W].max() for i in range(0, M - W + 1, W)]
    wrms = [np.sqrt((arr[i:i + W] ** 2).mean()) for i in range(0, M - W + 1, W)]
    ns = np.array([gram[i + W // 2] for i in range(0, M - W + 1, W)])
    # loglog slope of window RMS vs height
    sl = np.polyfit(np.log(ns), np.log(wrms), 1)[0]
    print("  %s: global max %.4f  window RMS %.4f -> %.4f  (loglog slope vs height: %+.3f)"
          % (lab, arr.max(), wrms[0], wrms[-1], sl))

# ---- mu6 refinement: theta-step pi/3, 3 sub-cells per pi-cell ----
sub = np.empty((M, 3))
for n in range(M):
    a, b = gram[n], gram[n + 1]
    cuts = [a]
    for j in (1, 2):
        target = (n + j / 3.0) * np.pi
        r = a + (b - a) * j / 3.0
        for _ in range(50):
            step = (float(theta(r)) - target) / float(theta_prime(r))
            r -= step
            if abs(step) < 1e-11:
                break
        cuts.append(r)
    cuts.append(b)
    sub[n] = [int_smult(cuts[k], cuts[k + 1]) for k in range(3)]

recon = np.abs(sub.sum(axis=1) - A).max()
print("\n== mu6 (pi/3) sub-cell decomposition ==   reconstruction check: %.2e" % recon)
rms_cell = np.sqrt((A ** 2).mean())
rms_sub = np.sqrt((sub ** 2).mean())
print("RMS per pi-cell residue: %.4f   RMS per pi/3 sub-residue: %.4f   ratio sub/cell: %.3f"
      % (rms_cell, rms_sub, rms_sub / rms_cell))
# cancellation index: how much of sub-residue magnitude cancels inside the pi-cell
canc = np.abs(sub).sum(axis=1) / np.maximum(np.abs(A), 1e-15)
print("within-cell cancellation |sub|_1/|A|: median %.2f   90%% %.2f" %
      (np.median(canc), np.percentile(canc, 90)))
# mod-6 class means over two-gram-cell period (k = 3n+j mod 6)
k_idx = (3 * np.arange(M)[:, None] + np.arange(3)[None, :]) % 6
print("mod-6 class means of sub-residues:")
for k in range(6):
    v = sub[k_idx == k]
    print("  k=%d: mean %+.5f  rms %.4f  (n=%d)" % (k, v.mean(), np.sqrt((v**2).mean()), v.size))
print("\ndone.")
