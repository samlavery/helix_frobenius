"""Timing probe: measure per-t-step cost of the phase-recurrence sweep on the
compressed (nonzero-only) amp vector. Choose W to stay under ~7 min/call."""
import time
import numpy as np

amp = np.load("pi_clock_amp.npy")
ln = np.load("pi_clock_ln.npy")
nz = amp != 0
amp = amp[nz].copy()
ln = ln[nz].copy()
print("compressed length:", amp.size)

dy = 0.01
t_lo = 50.0
# probe: 200 steps
nprobe = 200
z = (amp * np.exp(-1j * t_lo * ln)).astype(np.complex128)
step = np.exp(-1j * dy * ln)
F = np.empty(nprobe, dtype=np.complex128)
t0 = time.time()
for j in range(nprobe):
    F[j] = z.sum()
    z *= step
el = time.time() - t0
per = el / nprobe
print("%.4fs for %d steps -> %.6f ms/step" % (el, nprobe, per*1000))
# full span steps:
total_steps = int((450 - 50) / dy) + 1
print("total steps for full span:", total_steps, "-> est %.1f min" % (per*total_steps/60))
# W (t-units) per ~6min segment:
budget_s = 6 * 60
steps_per_call = budget_s / per
W = steps_per_call * dy
print("steps/6min-call:", int(steps_per_call), "-> W (t-units) ~ %.1f" % W)
