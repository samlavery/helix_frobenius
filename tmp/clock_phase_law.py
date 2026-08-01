"""Clock-phase law probe: the per-cell residue in the harmonized clock chart.

On Gram cell n (theta/pi in [n, n+1]) with boundary defect s_n = S(g_n) and events at
clock phases tau_i = theta(gamma_i)/pi - n in [0,1], the clock-chart residue is EXACT:

    A~_n := int_0^1 Smult dtau = s_n + sum_i (1 - tau_i) - 1/2

so the entire residue story is the joint law of (s_n, {tau_i}).  Measured here:
  1. relation of the t-residue A_n to L_n * A~_n  (is |A_n|<1 the clock law x length?)
  2. max/distribution of A~_n vs the boundary defect s_n
  3. event clock-phase distribution: mean (centering law), thirds occupancy (mu6
     middle-cell law per-event), parity classes
  4. Rosser-block balance of (tau_i - 1/2)
  5. exploratory: zeta6-weighted mu6 sub-residue closure on 2pi super-cells vs
     phase-shuffled null

Event heights = the certified cached ordinates (readout-verification role).
"""

import bisect
import numpy as np
from scipy.special import loggamma

rng = np.random.default_rng(20260731)

ZC = "/Users/samuellavery/work/helix_frobenius/tmp/zeta_zeros_cache.txt"
GC = "/Users/samuellavery/work/helix_frobenius/tmp/gram_cache.txt"
zeros = [float(x) for x in open(ZC).read().split()]
gram = [float(x) for x in open(GC).read().split()][0::2]

def theta(t):
    t = np.asarray(t, dtype=float)
    return np.imag(loggamma(0.25 + 0.5j * t)) - 0.5 * t * np.log(np.pi)

M = max(n for n in range(len(gram) - 1) if gram[n + 1] <= zeros[-1] - 5.0)
print("cells 0..%d (heights %.2f .. %.2f)" % (M - 1, gram[0], gram[M]))

# event clock phases
zarr = np.array(zeros)
zin = zarr[(zarr > gram[0]) & (zarr <= gram[M])]
ph = theta(zin) / np.pi          # in [n, n+1] for cell n
cell = np.floor(ph).astype(int)
tau = ph - cell
# guard: all cells in range
assert cell.min() >= 0 and cell.max() < M

# boundary defects and per-cell event lists
s = np.array([bisect.bisect_right(zeros, gram[n]) - 1 - n for n in range(M + 1)])
k = np.bincount(cell, minlength=M)
# anchor: telescoping s_{n+1} = s_n + k_n - 1 exactly
assert np.all(s[1:] == s[:-1] + k - 1), "telescoping anchor FAILED"
print("anchor: s_(n+1) = s_n + k_n - 1 exact for all %d cells; max|s|=%d, max k=%d"
      % (M, np.abs(s).max(), k.max()))

# exact clock residues
sum1mtau = np.zeros(M)
np.add.at(sum1mtau, cell, 1.0 - tau)
At = s[:-1] + sum1mtau - 0.5     # A~_n

# ---- 1. chart transfer: A_n vs L_n * A~_n ----
XGL, WGL = np.polynomial.legendre.leggauss(8)
def int_theta(a, b):
    m, h = 0.5 * (a + b), 0.5 * (b - a)
    return h * np.dot(WGL, theta(m + h * XGL))
def int_smult(a, b):
    Na = bisect.bisect_right(zeros, a)
    lo, hi = bisect.bisect_right(zeros, a), bisect.bisect_right(zeros, b)
    v = Na * (b - a) + sum(b - zeros[i] for i in range(lo, hi))
    return v - (b - a) - int_theta(a, b) / np.pi
A = np.array([int_smult(gram[n], gram[n + 1]) for n in range(M)])
L = np.diff(np.array(gram[:M + 1]))
corr = A - L * At
print("\n== 1. chart transfer ==")
print("max|A_n - L_n*A~_n| = %.4f   median = %.5f   rel to RMS(A): %.3f"
      % (np.abs(corr).max(), np.median(np.abs(corr)), np.abs(corr).max() / np.sqrt((A**2).mean())))
iamax = int(np.argmax(np.abs(A)))
print("argmax|A|: cell %d (height %.1f, L=%.2f, A=%.4f, A~=%.4f)"
      % (iamax, gram[iamax], L[iamax], A[iamax], At[iamax]))
W = 500
wmaxA = [np.abs(A[i:i + W]).max() for i in range(0, M - W + 1, W)]
wmaxAt = [np.abs(At[i:i + W]).max() for i in range(0, M - W + 1, W)]
print("windowed max|A|:  %s" % " ".join("%.3f" % v for v in wmaxA))
print("windowed max|A~|: %s" % " ".join("%.3f" % v for v in wmaxAt))

# ---- 2. clock residue vs boundary defect ----
print("\n== 2. clock residue vs defect ==")
print("max|A~| = %.4f   RMS = %.4f" % (np.abs(At).max(), np.sqrt((At**2).mean())))
for sv in sorted(set(s[:-1].tolist())):
    m_ = s[:-1] == sv
    print("  s=%+d: n=%4d  max|A~|=%.4f  mean A~=%+.4f" %
          (sv, m_.sum(), np.abs(At[m_]).max(), At[m_].mean()))
resid = At - (s[:-1] + (k - 1) / 2.0)   # remove the deterministic (s,k) part:
# for k events at symmetric positions, sum(1-tau) ~ k/2, so A~ ~ s + k/2 - 1/2
print("centered residue A~ - (s + (k-1)/2): max|.| = %.4f  RMS = %.4f"
      % (np.abs(resid).max(), np.sqrt((resid**2).mean())))

# ---- 3. event clock-phase law ----
print("\n== 3. event clock phases ==")
print("events: %d   mean tau = %.5f  (SE %.5f)   median = %.5f"
      % (tau.size, tau.mean(), tau.std() / np.sqrt(tau.size), np.median(tau)))
thirds = np.array([(tau < 1/3).mean(), ((tau >= 1/3) & (tau < 2/3)).mean(), (tau >= 2/3).mean()])
print("thirds occupancy [0,1/3),[1/3,2/3),[2/3,1]: %.4f  %.4f  %.4f" % tuple(thirds))
par = cell % 2
for p in (0, 1):
    tp = tau[par == p]
    print("  parity %d: mean tau %.5f  middle-third %.4f" %
          (p, tp.mean(), ((tp >= 1/3) & (tp < 2/3)).mean()))
# phases conditioned on cell occupancy
for kk in (0, 1, 2, 3):
    m_ = k == kk
    if kk == 0 or not m_.any():
        print("  k=%d cells: %d" % (kk, m_.sum()))
        continue
    tt = tau[np.isin(cell, np.nonzero(m_)[0])]
    print("  k=%d cells: %d   mean tau %.4f   middle-third %.4f"
          % (kk, m_.sum(), tt.mean(), ((tt >= 1/3) & (tt < 2/3)).mean()))

# ---- 4. Rosser-block balance ----
print("\n== 4. Rosser-block balance of (tau - 1/2) ==")
zb = np.nonzero(s[:M + 1] == 0)[0]
blocks = [(zb[i], zb[i + 1]) for i in range(len(zb) - 1) if zb[i + 1] > zb[i]]
bsum, blen = [], []
for a_, b_ in blocks:
    m_ = (cell >= a_) & (cell < b_)
    bsum.append((tau[m_] - 0.5).sum())
    blen.append(b_ - a_)
bsum = np.array(bsum); blen = np.array(blen)
print("blocks: %d  (len 1: %d, len>1: %d, max len %d)"
      % (len(blocks), (blen == 1).sum(), (blen > 1).sum(), blen.max()))
print("block sum(tau-1/2): mean %+.5f  RMS %.4f;  per-event RMS %.4f vs raw tau-1/2 RMS %.4f"
      % (bsum.mean(), np.sqrt((bsum**2).mean()),
         np.sqrt((bsum**2).mean() / max(blen.mean(), 1)), np.sqrt(((tau - 0.5)**2).mean())))

# ---- 5. zeta6-weighted mu6 closure on 2pi super-cells ----
print("\n== 5. zeta6-weighted mu6 sub-residue closure ==")
def subres(n):
    """exact clock-chart residues of the 3 mu6 sub-cells of cell n"""
    m_ = cell == n
    ts = np.sort(tau[m_])
    out = []
    for j in range(3):
        lo, hi = j / 3.0, (j + 1) / 3.0
        ev = np.clip(hi - np.maximum(ts, lo), 0.0, None).sum()
        out.append(s[n] * (hi - lo) + ev - 0.5 * (hi**2 - lo**2))
    return out
sub = np.array([subres(n) for n in range(M)])
z6 = np.exp(2j * np.pi * np.arange(6) / 6.0)
P = (M // 2)
six = sub[:2 * P].reshape(P, 6)
w = six @ z6
obs = np.sqrt((np.abs(w)**2).mean())
null = []
for _ in range(200):
    perm = np.array([rng.permutation(6) for _ in range(P)])
    null.append(np.sqrt((np.abs(np.take_along_axis(six, perm, 1) @ z6)**2).mean()))
null = np.array(null)
print("RMS|sum zeta6^j a_j| = %.4f   shuffled null: %.4f +/- %.4f   p(obs<=null) = %.3f"
      % (obs, null.mean(), null.std(), (null <= obs).mean()))
print("\ndone.")
