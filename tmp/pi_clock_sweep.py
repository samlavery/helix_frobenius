"""Full-span sweep [50,450], dy=0.01, on compressed 27.a amp vector.
Then log-clip-Hann-rfft spectroscopy with parabolic peak interpolation.
Verdict: (A) ln8=2.07944  vs (B) 2pi/3=2.09440  vs (C) other/sideband."""
import math
import time
import numpy as np

amp = np.load("pi_clock_amp.npy")
ln = np.load("pi_clock_ln.npy")
nz = amp != 0
amp = amp[nz].copy()
ln = ln[nz].copy()

t_lo, t_hi, dy = 50.0, 450.0, 0.01
ny = int((t_hi - t_lo) / dy) + 1
t0 = time.time()
z = (amp * np.exp(-1j * t_lo * ln)).astype(np.complex128)
step = np.exp(-1j * dy * ln)
F = np.empty(ny, dtype=np.complex128)
for j in range(ny):
    F[j] = z.sum()
    z *= step
print("swept %d steps in %.1fs" % (ny, time.time() - t0))
absF = np.abs(F).astype(np.float32)
np.save("pi_clock_absF.npy", absF)

# ---- spectroscopy ----
absF = absF.astype(np.float64)
x = np.log(np.maximum(absF, np.percentile(absF, 1.0)))
x -= x.mean()
win = np.hanning(len(x))
X = np.fft.rfft(x * win)
P = np.abs(X)**2
omega = 2 * math.pi * np.fft.rfftfreq(len(x), d=dy)
res = 2 * math.pi / (t_hi - t_lo)
domega = omega[1] - omega[0]
print("span %.0f, resolution (bin) %.5f, targets ln8 vs 2pi/3 are %.5f apart (=%.1f bins)"
      % (t_hi - t_lo, res, abs(math.log(8) - 2*math.pi/3), abs(math.log(8) - 2*math.pi/3)/domega))

def parabolic_peak(P, i):
    """Parabolic interpolation around index i -> (omega_interp, height_interp)."""
    if i <= 0 or i >= len(P) - 1:
        return omega[i], P[i]
    y0, y1, y2 = P[i-1], P[i], P[i+1]
    denom = (y0 - 2*y1 + y2)
    if denom == 0:
        return omega[i], y1
    delta = 0.5 * (y0 - y2) / denom
    om = omega[i] + delta * domega
    ht = y1 - 0.25 * (y0 - y2) * delta
    return om, ht

# background estimate: local median in a window excluding a small core
def peakbg(om_target, core=0.012, bglo=0.09, bghi=0.28, exclude=None):
    sel = np.abs(omega - om_target) < max(core, 2.0 * res)
    bg = (np.abs(omega - om_target) > bglo) & (np.abs(omega - om_target) < bghi)
    if exclude:
        for e in exclude:
            bg &= np.abs(omega - e) > 0.05
    i = np.where(sel)[0]
    imax = i[np.argmax(P[i])]
    om_i, ht_i = parabolic_peak(P, imax)
    ratio = P[imax] / np.median(P[bg])
    return ratio, om_i, ht_i, omega[imax]

print("\n=== (b) pi-based candidates + log-line calibration ===")
LOGLINES = [math.log(k) for k in (2,3,4,5,7,8,9,11,13,16)]
cands = [
    ("pi/3   ", math.pi/3),
    ("pi/2   ", math.pi/2),
    ("2pi/3  ", 2*math.pi/3),
    ("pi     ", math.pi),
    ("4pi/3  ", 4*math.pi/3),
    ("ln4    ", math.log(4)),
    ("ln7    ", math.log(7)),
    ("ln9    ", math.log(9)),
    ("ln13   ", math.log(13)),
    ("ln3    ", math.log(3)),
    ("ln8    ", math.log(8)),
]
print("  %-8s %-9s %-12s %-11s %-11s" % ("name", "target", "peak/bg", "om_interp", "om_bin"))
for name, om in cands:
    ratio, om_i, ht_i, om_bin = peakbg(om)
    print("  %-8s %-9.5f %-12.1f %-11.5f %-11.5f" % (name, om, ratio, om_i, om_bin))

print("\n=== (a) ZOOM omega in [1.90, 2.30]: all local maxima > 10x local median ===")
lo, hi = 1.90, 2.30
mask = (omega >= lo) & (omega <= hi)
idx = np.where(mask)[0]
# local median across the whole zoom band as reference:
band_med = np.median(P[idx])
print("  zoom band median P = %.4g" % band_med)
maxima = []
for i in idx:
    if i <= 0 or i >= len(P) - 1:
        continue
    if P[i] > P[i-1] and P[i] >= P[i+1]:
        # local median in +-0.09 window excluding +-0.02 core
        w = (np.abs(omega - omega[i]) < 0.09) & (np.abs(omega - omega[i]) > 0.02)
        lm = np.median(P[w]) if w.any() else band_med
        if P[i] > 10 * lm:
            om_i, ht_i = parabolic_peak(P, i)
            maxima.append((om_i, P[i], P[i]/lm, omega[i]))
maxima.sort(key=lambda r: -r[1])
print("  %-11s %-12s %-10s %-11s" % ("om_interp", "height", "x_localmed", "om_bin"))
for om_i, h, r, om_bin in maxima:
    tag = ""
    if abs(om_i - math.log(8)) < 0.006: tag = " <-- ln8 (2.07944)"
    if abs(om_i - 2*math.pi/3) < 0.006: tag += " <-- 2pi/3 (2.09440)"
    if abs(om_i - math.log(7)) < 0.008: tag += " (near ln7=1.9459)"
    print("  %-11.5f %-12.4g %-10.1f %-11.5f%s" % (om_i, h, r, om_bin, tag))

print("\n  reference targets: ln7=%.5f ln8=%.5f 2pi/3=%.5f ln9=%.5f"
      % (math.log(7), math.log(8), 2*math.pi/3, math.log(9)))
print("  sideband check: 2*ln7 - (ln7 line spacing)... intermod of ln7=1.9459 with low-freq")

print("\n=== (c) comb re-verify at long span ===")
for name, om, pred in [("ln3", math.log(3), "DEAD(bad)"), ("ln9", math.log(9), "DEAD(bad)"),
                       ("ln4", math.log(4), "BRIGHT"), ("ln7", math.log(7), "bright(split)"),
                       ("ln13", math.log(13), "alive(split)")]:
    ratio, om_i, ht_i, om_bin = peakbg(om)
    print("  %-6s %-9.5f peak/bg=%-9.1f  %s" % (name, om, ratio, pred))
