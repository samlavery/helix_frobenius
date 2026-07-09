"""Phase-cell law at vanishings (Sam's claim): the fiber's winding amplitude
advances pi between consecutive vanishings (with a sign flip at each), EXCEPT
the first vanishing, which sits only pi/2 from the hinge (y = 0, the midpoint
of the double helix).  Hence helix and anti-helix first vanishings are pi
apart, with Frobenius det 1 (conjugate pair) enforcing the two-strand ledger.

Measurement (fiber-only): unwrapped argument Phi(y) of the fiber along the
line from the hinge; record Phi just before each vanishing.  Robust prediction
independent of jump conventions: the FIRST interval is HALF the typical one.
"""
import math

import numpy as np

CHARS = {
    "zeta(eta-demod)": (2, lambda n: np.where(n % 2 == 1, 1.0, -1.0), True),
    "chi3": (3, lambda n: np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0)), False),
    "chi4": (4, lambda n: np.where(n % 4 == 1, 1.0, np.where(n % 4 == 3, -1.0, 0.0)), False),
    "chi5": (5, lambda n: np.where(np.isin(n % 5, (1, 4)), 1.0, np.where(np.isin(n % 5, (2, 3)), -1.0, 0.0)), False),
    "chi8": (8, lambda n: np.where(np.isin(n % 8, (1, 7)), 1.0, np.where(np.isin(n % 8, (3, 5)), -1.0, 0.0)), False),
}

N = 12000
dy = 0.005
Y1 = 60.0

print("phase accumulated to each vanishing (units of pi); prediction: first = 0.5, steps = 1.0")
print(f"{'character':>16} {'first/pi':>9} {'jump/pi':>9} {'drift/pi':>10} {'std':>6} {'n zeros':>8}")
for name, (q, chi_fn, demod) in CHARS.items():
    n = np.arange(1, N + 1, dtype=np.float64)
    c = chi_fn(n.astype(np.int64))
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    amp = c * w * n ** (-0.5)
    ln = np.log(n)
    ny = int(Y1 / dy) + 1
    ys = dy * np.arange(ny)
    z = amp.astype(np.complex128)
    step = np.exp(-1j * dy * ln)
    F = np.empty(ny, dtype=np.complex128)
    for j in range(ny):
        F[j] = z.sum()
        z *= step
    if demod:
        F = F / (1.0 - math.sqrt(2.0) * np.exp(-1j * ys * math.log(2.0)))
    absF = np.abs(F)
    med = float(np.median(absF))
    zi = []
    for j in range(1, ny - 1):
        if absF[j] < absF[j - 1] and absF[j] < absF[j + 1] and absF[j] < 0.25 * med:
            zi.append(j)
    Phi = np.unwrap(np.angle(F))
    # separate the two components: jump AT each vanishing vs smooth drift BETWEEN
    b = np.array([Phi[j - 3] for j in zi])   # just before
    a = np.array([Phi[j + 3] for j in zi])   # just after
    first = (b[0] - Phi[0]) / math.pi
    jumps = (a - b) / math.pi                 # the sign flip
    drifts = (b[1:] - a[:-1]) / math.pi       # the winding between vanishings
    print(f"{name:>16} {first:>9.3f} {float(np.median(jumps)):>9.3f} "
          f"{float(np.median(drifts)):>10.3f} {float(np.std(drifts)):>6.3f} {len(zi):>8}")
    if name == "chi3":
        print(f"     chi3 drifts/pi: " + " ".join(f"{s:+.2f}" for s in drifts[:12]))
