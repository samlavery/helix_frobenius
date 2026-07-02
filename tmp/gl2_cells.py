"""Phase-cell law at GL(2): does the pi-quantization survive the doubled winding?

The weld-pinning argument is degree-blind: self-dual completed L on the line is real up to
the eps-ray, so the exact-Gamma-gauged fiber phase must be CONSTANT between vanishings and
jump exactly pi at each — the cells are pi for GL(2) exactly as for GL(1), with the doubled
winding absorbed by the doubled Gamma factor (the gauge runs twice as fast, the cells don't
change).  Measured here for Delta (weight 12, level 1) and E11 (weight 2, conductor 11).

Gauges (exact, scipy loggamma):
  Delta: theta(t) = -t ln(2pi) + Im logGamma(6 + it)          [s_ar = s_an + 11/2]
  E11:   theta(t) = t ln(sqrt(11)/2pi) + Im logGamma(1 + it)  [s_ar = s_an + 1/2]
"""
import math
import sys

import numpy as np
from scipy.special import loggamma

sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius")
from focal_closure import delta_lambda, e11_lambda

CASES = [
    ("Delta", delta_lambda(20000)[1:], 9.0, 60.0,
     lambda t: -t * math.log(2 * math.pi) + np.imag(loggamma(6.0 + 1j * t))),
    ("E11", e11_lambda(12000)[1:], 3.0, 40.0,
     lambda t: t * math.log(math.sqrt(11.0) / (2 * math.pi)) + np.imag(loggamma(1.0 + 1j * t))),
]

print(f"{'form':>6} {'zeros':>6} {'cell mean/pi':>13} {'cell sd/pi':>11} {'pin ray':>8} {'pin sd':>9}")
for tag, lam, t0, t1, theta_fn in CASES:
    N = len(lam)
    n = np.arange(1, N + 1, dtype=np.float64)
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    amp = lam * w * n ** (-0.5)
    ln = np.log(n)
    dy = 0.005
    ys = t0 + dy * np.arange(int((t1 - t0) / dy) + 1)
    z = amp * np.exp(-1j * t0 * ln)
    step = np.exp(-1j * dy * ln)
    F = np.empty(len(ys), dtype=np.complex128)
    for j in range(len(ys)):
        F[j] = z.sum()
        z *= step
    G = F * np.exp(1j * theta_fn(ys))
    absF = np.abs(F)
    med = float(np.median(absF))
    zi = [j for j in range(1, len(ys) - 1)
          if absF[j] < absF[j - 1] and absF[j] < absF[j + 1] and absF[j] < 0.25 * med]
    Phi = np.unwrap(np.angle(G))
    before = np.array([Phi[j - 4] for j in zi])
    cells = np.abs(np.diff(before)) / math.pi
    mask = absF > 0.5 * med
    psi = np.mod(np.angle(G[mask]), math.pi)
    zbar = np.mean(np.exp(2j * psi))
    ray = (np.angle(zbar) / 2) % math.pi
    sd = math.sqrt(max(0.0, -0.5 * math.log(max(abs(zbar), 1e-300))))
    print(f"{tag:>6} {len(zi):>6} {float(np.mean(cells)):>13.4f} {float(np.std(cells)):>11.4f} "
          f"{ray/math.pi:>7.4f}p {sd/math.pi:>8.5f}p")

print()
print("Prediction: cell mean 1.0000 pi, pinned ray = arg(eps)/2 = 0 (both eps = +1).")
print("The doubled winding lives entirely in the doubled gauge; the quanta are unchanged.")
