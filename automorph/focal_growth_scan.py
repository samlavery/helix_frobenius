"""Focal-closure growth scan: the 3-D finite fiber locates its own vanishings.

The fiber GROWS along the carrier.  At head height Z the bank holds every phasor
n <= Z.  Phasor n's angle is its carrier angle theta_n = ln n (the linear-spiral
placement, helix_geometry_3d sec 1b: geometry fixed at construction).  The only
readout is the head's own projection y = log Z (GeometricReadout: the one log,
applied to the head height, never to a search parameter).  Each phasor enters as
a point and grows to full magnitude x_n^(-1/2) over the newest fraction of the
fiber (self-similar C-inf growth window w(n/Z), w(0)=1 -- model.py's 'grow',
scaled to the head).

Focal state of the WHOLE finite bank at head Z (three channels, Phasor3D):
    P(Z) = sum_{chi(n)=+1} a_n(Z) e^{-i log(Z) theta_n}     (spin plane, + lane)
    M(Z) = sum_{chi(n)=-1} a_n(Z) e^{-i log(Z) theta_n}     (spin plane, - lane)
    U(Z) = sum_{chi(n)=0}  a_n(Z)                           (mass axis)
A VANISHING is the focal closure P(Z) = M(Z): the two lane resultants coincide
as complex vectors.  Closure measure  c(Z) = |P-M| / max(|P|,|M|)  (projective,
scale-free).  NO L-function, NO reference zeros, NO external frequency sweep:
one parameter, the head height Z, detected as local minima of c(Z).

Published reference zeros enter ONLY the final |diff| column.
"""
import math
import sys

import numpy as np

sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius/carrier_fiber")
from carrier_fiber import REFERENCE_GAMMAS  # final |diff| column ONLY

PI3 = math.pi / 3.0

CHARS = {
    "eta_trivial": (2, lambda n: np.where(n % 2 == 1, 1.0, -1.0)),
    "chi3": (3, lambda n: np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0))),
    "chi4": (4, lambda n: np.where(n % 4 == 1, 1.0, np.where(n % 4 == 3, -1.0, 0.0))),
    "chi5": (5, lambda n: np.where(np.isin(n % 5, (1, 4)), 1.0, np.where(np.isin(n % 5, (2, 3)), -1.0, 0.0))),
    "chi8": (8, lambda n: np.where(np.isin(n % 8, (1, 7)), 1.0, np.where(np.isin(n % 8, (3, 5)), -1.0, 0.0))),
}

# scan windows in the readout coordinate y = log Z (head height Z = e^y).
# chosen by budget (cost per sample ~ Z), not by zero locations.
WINDOWS = {
    "eta_trivial": (13.60, 14.60),   # Z up to ~2.2e6 (budget); deeper zeros cost e^gamma
    "chi3": (1.50, 11.60),           # Z up to ~1.1e5
    "chi4": (1.50, 11.00),
    "chi5": (1.50, 12.20),
    "chi8": (1.50, 11.00),
}


def lanes(name, y):
    """Whole-bank lane resultants at head Z = e^y.  Everything finite; one log (of the head)."""
    q, chi_fn = CHARS[name]
    Z = math.exp(y)
    N = int(Z)
    if N < 2:
        return 0j, 0j, 0.0
    n = np.arange(1, N + 1, dtype=np.float64)
    c = chi_fn(n.astype(np.int64))
    u = n / Z
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    x = PI3 * n                                   # the pi/3-scaled carrier coordinate
    amp = w * x ** (-0.5)                         # grown magnitude on the carrier scale
    spin_plane = np.exp(-1j * y * np.log(x))      # rotation rate = the head readout y = log Z
    P = complex(np.sum(np.where(c > 0, amp, 0.0) * spin_plane))
    M = complex(np.sum(np.where(c < 0, amp, 0.0) * spin_plane))
    U = float(np.sum(np.where(c == 0, amp, 0.0)))
    return P, M, U


def closure(name, y):
    P, M, _ = lanes(name, y)
    d = max(abs(P), abs(M))
    return abs(P - M) / d if d > 0 else 1.0


def golden(f, a, b, iters=60):
    gr = (5.0 ** 0.5 - 1.0) / 2.0
    c, d = b - gr * (b - a), a + gr * (b - a)
    fc, fd = f(c), f(d)
    for _ in range(iters):
        if fc < fd:
            b, d, fd = d, c, fc
            c = b - gr * (b - a)
            fc = f(c)
        else:
            a, c, fc = c, d, fd
            d = a + gr * (b - a)
            fd = f(d)
    return 0.5 * (a + b)


def scan(name, per_unit=240):
    y0, y1 = WINDOWS[name]
    ys = np.linspace(y0, y1, max(9, int((y1 - y0) * per_unit)))
    cs = np.array([closure(name, float(y)) for y in ys])
    med = float(np.median(cs))
    hits = [
        float(ys[i])
        for i in range(1, len(ys) - 1)
        if cs[i] < cs[i - 1] and cs[i] < cs[i + 1] and cs[i] < 0.25 * med
    ]
    return [golden(lambda t: closure(name, t), h - 1.5 * (ys[1] - ys[0]), h + 1.5 * (ys[1] - ys[0])) for h in hits]


if __name__ == "__main__":
    print("FOCAL-CLOSURE GROWTH SCAN: one parameter (head height Z), whole finite bank,")
    print("closure = lane-resultant coincidence P(Z)=M(Z).  No L, no seeds, no freq sweep.")
    print("Reference gammas appear ONLY in the |diff| column.\n")
    for name in ("chi3", "chi4", "chi5", "chi8", "eta_trivial"):
        found = scan(name)
        ref = REFERENCE_GAMMAS[name]
        print(f"{name}  (scan window y in {WINDOWS[name]}):")
        print(f"   {'closure y':>12} {'height Z=e^y':>14} {'c(Z) at min':>12} {'c off (+0.4)':>12} {'nearest ref':>12} {'|diff|':>9}")
        for y in found:
            P, M, U = lanes(name, y)
            c_on = closure(name, y)
            c_off = closure(name, y + 0.4)
            near = min(ref, key=lambda g: abs(g - y))
            print(f"   {y:>12.6f} {math.exp(y):>14.1f} {c_on:>12.2e} {c_off:>12.3f} {near:>12.6f} {abs(y - near):>9.1e}")
        if not found:
            print("   (no closure events in window)")
        print()
