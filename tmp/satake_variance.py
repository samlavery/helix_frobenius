"""What is the +-4% Satake variability?  Split-span decomposition on zeta.

The weight law's FORM is exact (algebraic silences at 1e-6), but the measured/predicted
scale scatters by ~3-5% per line.  Candidates:
  (A) estimator noise (finite span): residuals DECORRELATE between disjoint spans,
      std shrinks ~ 1/sqrt(T);
  (B) deterministic structure (skirt leakage between lines + second-order
      intermodulation ln p +- ln q stealing primary power): residuals REPRODUCE
      between spans (corr ~ 1), std span-independent;
  (C) additive broadband arch floor: uniform upward bias, shrinking with span.

Method: zeta (eta de-modulated), t in [1000,3000]; line amplitudes by the direct
windowed projection A = |2 <w s e^{i om t}> / <w>| at the parabolic-refined peak;
prediction A = p^{-k/2}/k from log|zeta| = sum (p^{-k/2}/k) cos(t k ln p).
Report per-line residuals on half1/half2/full + cross-span correlation + covariates.
"""
import math

import numpy as np

N, dy = 40000, 0.01
T0, T1 = 1000.0, 3000.0
n = np.arange(1, N + 1, dtype=np.float64)
sgn = np.where(n.astype(np.int64) % 2 == 1, 1.0, -1.0)
u = n / N
w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
amp = sgn * w * n ** (-0.5)
ln = np.log(n)

ny = int((T1 - T0) / dy) + 1
ts = T0 + dy * np.arange(ny)
z = amp * np.exp(-1j * T0 * ln)
step = np.exp(-1j * dy * ln)
F = np.empty(ny, dtype=np.complex128)
for j in range(ny):
    F[j] = z.sum()
    z *= step
F /= (1.0 - math.sqrt(2.0) * np.exp(-1j * ts * math.log(2.0)))
s = np.log(np.abs(F))
med = np.median(s)
s = np.clip(s, med - 4.0, None) - np.mean(s)

LINES = [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1),
         (29, 1), (31, 1), (37, 1), (2, 2), (3, 2), (5, 2), (2, 3)]


def measure(seg_t, seg_s):
    """Per-line amplitude by windowed projection at the refined frequency."""
    Wn = np.hanning(len(seg_s))
    ws = seg_s * Wn
    out = {}
    for p, k in LINES:
        om0 = k * math.log(p)
        # parabolic refinement on a fine local frequency grid
        oms = om0 + np.linspace(-0.004, 0.004, 9)
        amps = [abs(np.sum(ws * np.exp(1j * o * seg_t))) for o in oms]
        j = int(np.argmax(amps))
        j = min(max(j, 1), 7)
        d = 0.5 * (amps[j-1] - amps[j+1]) / (amps[j-1] - 2*amps[j] + amps[j+1] + 1e-300)
        omh = oms[j] + d * (oms[1] - oms[0])
        A = 2.0 * abs(np.sum(ws * np.exp(1j * omh * seg_t))) / np.sum(Wn)
        out[(p, k)] = A / (p ** (-k / 2.0) / k)      # measured/predicted
    return out


half = ny // 2
r1 = measure(ts[:half], s[:half])
r2 = measure(ts[half:], s[half:])
rf = measure(ts, s)

print(f"{'line':>6} {'half1':>7} {'half2':>7} {'full':>7} | resid1 resid2 (reproduce?)")
res1, res2, resf = [], [], []
for pk in LINES:
    p, k = pk
    a, b, c = r1[pk], r2[pk], rf[pk]
    res1.append(a - 1); res2.append(b - 1); resf.append(c - 1)
    print(f"ln{p}^{k:<2} {a:>7.4f} {b:>7.4f} {c:>7.4f} | {a-1:+.4f} {b-1:+.4f}")
res1, res2, resf = map(np.array, (res1, res2, resf))
corr = float(np.corrcoef(res1, res2)[0, 1])
print()
print(f"per-line std:  half1 {res1.std():.4f}  half2 {res2.std():.4f}  full {resf.std():.4f}")
print(f"cross-span correlation of residuals: {corr:+.3f}")
print(f"noise prediction: corr ~ 0, std_full ~ std_half/1.41 = {res1.std()/1.414:.4f}")
print(f"structure prediction: corr ~ 1, std_full ~ std_half")
print(f"mean residual (additive-floor bias): half {res1.mean():+.4f}/{res2.mean():+.4f}, full {resf.mean():+.4f}")
