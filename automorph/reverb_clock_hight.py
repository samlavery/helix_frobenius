"""Decisive clock test at high t: crossover in the four target windows (t ~ 52k-72k,
spacing ~ 0.67-0.70, where the two clocks separate by > 2x):

  GROWTH CLOCK  (window = one e-fold of the bank, dy ~ 1):    g* ~ 1/0.68 ~ 1.5
  SPACING CLOCK (window = newest-effective-phasor turn):       g* ~ 1.0
"""
import math

import numpy as np


def mean_spacing(t):
    return 2 * math.pi / math.log(t / (2 * math.pi))


def window_events(T0, half=16.0, dy=0.0025, mult=40):
    N = int(mult * T0 / (2 * math.pi))
    n = np.arange(1, N + 1, dtype=np.float64)
    sgn = np.where(n % 2 == 1, 1.0, -1.0)
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    amp = sgn * w * n ** (-0.5)
    ln = np.log(n)
    y0 = T0 - half
    ny = int(2 * half / dy) + 1
    ys = y0 + dy * np.arange(ny)
    z = amp * np.exp(-1j * y0 * ln)
    step = np.exp(-1j * dy * ln)
    F = np.empty(ny, dtype=np.complex128)
    for j in range(ny):
        F[j] = z.sum()
        z *= step
    absF = np.abs(F)
    med = float(np.median(absF))
    zs = []
    for j in range(1, ny - 1):
        if absF[j] < absF[j - 1] and absF[j] < absF[j + 1] and absF[j] < 0.3 * med:
            Fp = (F[j + 1] - F[j - 1]) / (2 * dy)
            if abs(Fp) > 1e-12:
                zs.append(float(ys[j] - (F[j] / Fp).real))
    zs = np.array(zs)
    zi = ((zs - y0) / dy).astype(int)
    out = []
    for i in range(len(zs) - 1):
        a, b = zi[i] + 2, zi[i + 1] - 1
        if b <= a:
            continue
        out.append(((zs[i + 1] - zs[i]) / mean_spacing(T0), float(absF[a:b].max())))
    return out, med


if __name__ == "__main__":
    events = []
    for T0 in (66678.0, 71733.0, 52206.0, 55712.0):
        ev, med = window_events(T0)
        events += [(g, b / med) for g, b in ev]   # normalize bumps by window ambient
        print(f"  t~{T0:.0f}: {len(ev)} gaps, ambient {med:.2f}")
    g = np.array([e[0] for e in events])
    bn = np.array([e[1] for e in events])
    for cut_lo, cut_hi in ((0.45, 1.1), (0.5, 1.2)):
        small = g < cut_lo
        large = g > cut_hi
        c2 = float(np.median(bn[small] / g[small] ** 2))
        c1 = float(np.median(bn[large] / g[large]))
        print(f"  cuts ({cut_lo},{cut_hi}): n_small={int(small.sum())} n_large={int(large.sum())}"
              f"   c1={c1:.3f} c2={c2:.3f}   g* = {c1/c2:.2f} unfolded"
              f"   -> raw y* = {c1/c2*mean_spacing(60000):.2f}")
    print()
    print("  growth clock predicts g* ~ 1.5 here; spacing clock predicts g* ~ 1.0")
