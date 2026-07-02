"""The ambient field's texture: prime-clock spectroscopy with conductor holes.

Hypothesis (the 'fiber/harmonic-resistance' side, relocated): the ambient field
log|L(1/2+it)| carries the Euler-side oscillations sum_p p^(-1/2) cos(t ln p),
so its power spectrum has peaks at RAW frequencies ln(p^k) (weight ~ n^(-1)/k^2),
and a character's ambient is missing exactly its own ramified prime.

Predictions:
  zeta   : peaks at ln 2,3,4,5,7,8,9,11,13,29,31; nulls at ln 18, ln 21
  chi5c  : same EXCEPT a hole at ln 5 (5 | conductor)   [also ln25 gone]
  chi29  : same EXCEPT a hole at ln 29
Power ratio = peak power / local background median.  Presence >> 1, hole ~ 1.

Run: python3 ambient_spectrum.py zeta|chi5c|chi29
"""
import math
import sys

import numpy as np

sys.path.insert(0, "tmp")
from amp_cross import chi_sweep, eta_sweep  # noqa: E402

TARGETS = [
    ("ln2", math.log(2)), ("ln3", math.log(3)), ("ln4", math.log(4)),
    ("ln5", math.log(5)), ("ln7", math.log(7)), ("ln8", math.log(8)),
    ("ln9", math.log(9)), ("ln11", math.log(11)), ("ln13", math.log(13)),
    ("ln18*", math.log(18)), ("ln21*", math.log(21)),
    ("ln29", math.log(29)), ("ln31", math.log(31)),
]


def spectrum_report(taus, absv, label):
    dt = taus[1] - taus[0]
    x = np.log(np.maximum(absv, np.percentile(absv, 1.0)))
    x = x - x.mean()
    w = np.hanning(len(x))
    P = np.abs(np.fft.rfft(x * w)) ** 2
    freq = 2 * np.pi * np.fft.rfftfreq(len(x), d=dt)
    res = 2 * math.pi / (taus[-1] - taus[0])
    print(f"[{label}]  span {taus[-1]-taus[0]:.0f}, resolution {res:.4f} rad")
    print(f"   {'target':>7} {'omega':>7} {'peak/background':>16}")
    for name, om in TARGETS:
        pk_sel = np.abs(freq - om) < max(0.012, 2.0 * res)
        bg_sel = (np.abs(freq - om) > 0.06) & (np.abs(freq - om) < 0.22)
        # exclude other targets from the background annulus
        for _, om2 in TARGETS:
            if om2 != om:
                bg_sel &= np.abs(freq - om2) > 0.03
        ratio = float(P[pk_sel].max() / np.median(P[bg_sel]))
        mark = " <-- hole?" if ratio < 3.0 else ""
        print(f"   {name:>7} {om:>7.3f} {ratio:>16.1f}{mark}")


if __name__ == "__main__":
    which = sys.argv[1]
    if which == "zeta":
        taus, F = eta_sweep(1000.0, 2000.0, 0.01, 2000.0)   # de-modulated -> pure |zeta|
        spectrum_report(taus, np.abs(F), "zeta (de-modulated eta), t in [1000, 2000]")
    elif which == "chi5c":
        v5 = np.zeros(5, dtype=np.complex128)
        v5[1], v5[2], v5[4], v5[3] = 1.0, 1j, -1.0, -1j
        taus, F = chi_sweep(v5, 5, 1600.0, 2000.0, 0.01, 2000.0)
        spectrum_report(taus, np.abs(F), "chi mod 5 order 4, t in [1600, 2000]")
    elif which == "chi29":
        v29 = np.zeros(29, dtype=np.complex128)
        for a in range(1, 29):
            v29[a] = 1.0 if pow(a, 14, 29) == 1 else -1.0
        taus, F = chi_sweep(v29, 29, 1750.0, 2000.0, 0.0125, 2000.0)
        spectrum_report(taus, np.abs(F), "chi mod 29 quadratic, t in [1750, 2000]")
