"""Is the ~1% Satake deficit the REVERB TAX?  (Sam: medium self-interaction resistance.)

Three signals, same grid t in [1000,3000], same estimator, 16 lines:
  (A) exact truncated explicit series  sum_{p^k<=1000} (p^{-k/2}/k) cos(t k ln p)
      -> calibrates the estimator: any deviation from 1.0000 here is METHOD, not medium;
  (B) the fiber log|zeta(1/2+it)| (eta de-modulated, clip median-4)
      -> reproduces the measured deficit;
  (C) the fiber with dip neighborhoods EXCISED (zeros located, +-0.06 linearly bridged)
      -> attribution: if the deficit vanishes with the dips, it is the arches' tax —
         the reverb events pay their spectral cost out of the prime clocks' lines.
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
absF = np.abs(F)

# (A) exact truncated explicit series
def sieve(m):
    s = np.ones(m + 1, dtype=bool); s[:2] = False
    for i in range(2, int(m ** 0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

sA = np.zeros(ny)
for p in sieve(1000):
    pk, k = int(p), 1
    while pk <= 1000:
        sA += (pk ** -0.5 / k) * np.cos(ts * math.log(p) * k)
        pk *= int(p); k += 1

# (B) fiber, clipped
sB = np.log(absF)
mB = np.median(sB)
sB = np.clip(sB, mB - 12.0, None)

# (C) fiber with dips excised
zi = [j for j in range(1, ny - 1)
      if absF[j] < absF[j-1] and absF[j] < absF[j+1] and absF[j] < 0.25]
sC = sB.copy()
half = int(0.06 / dy)
for j in zi:
    a, b = max(j - half, 0), min(j + half, ny - 1)
    sC[a:b+1] = np.linspace(sC[a], sC[b], b - a + 1)
print(f"zeros located: {len(zi)}; excised fraction: {len(zi)*2*half*dy/(T1-T0):.3f}")

LINES = [(2,1),(3,1),(5,1),(7,1),(11,1),(13,1),(17,1),(19,1),(23,1),(29,1),(31,1),(37,1),
         (2,2),(3,2),(5,2),(2,3)]
Wn = np.hanning(ny)
sw = np.sum(Wn)

def measure(sig):
    x = (sig - np.mean(sig)) * Wn
    out = {}
    for p, k in LINES:
        om0 = k * math.log(p)
        oms = om0 + np.linspace(-0.004, 0.004, 9)
        amps = [abs(np.sum(x * np.exp(1j * o * ts))) for o in oms]
        j = min(max(int(np.argmax(amps)), 1), 7)
        d = 0.5*(amps[j-1]-amps[j+1])/(amps[j-1]-2*amps[j]+amps[j+1]+1e-300)
        omh = oms[j] + d * (oms[1]-oms[0])
        A = 2.0 * abs(np.sum(x * np.exp(1j * omh * ts))) / sw
        out[(p, k)] = A / (p ** (-k/2.0) / k)
    return out

rA, rB, rC = measure(sA), measure(sB), measure(sC)
print(f"{'line':>6} {'A series':>9} {'B fiber':>8} {'C excised':>9} | deficit B, C (method-corrected by A)")
dB, dC = [], []
for pk in LINES:
    p, k = pk
    b_corr, c_corr = rB[pk]/rA[pk] - 1, rC[pk]/rA[pk] - 1
    dB.append(b_corr); dC.append(c_corr)
    print(f"ln{p}^{k:<2} {rA[pk]:>9.5f} {rB[pk]:>8.4f} {rC[pk]:>9.4f} | {b_corr:+.4f}  {c_corr:+.4f}")
print()
print(f"A (estimator calibration): mean {np.mean([rA[x] for x in LINES]):.5f}  "
      f"(1.00000 = clean estimator)")
print(f"method-corrected deficit:  fiber {np.mean(dB):+.4f}   dips-excised {np.mean(dC):+.4f}")
print(f"VERDICT: if C ~ 0 while B ~ -1%, the deficit IS the reverb tax — the arches pay")
print(f"for themselves out of the prime clocks' coherent power.")
