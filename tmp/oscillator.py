import math
import numpy as np
from scipy.signal import hilbert

CHARS = {
    "zeta": (1, lambda n: np.where(n % 2 == 1, 1.0, -1.0), True, 45.0),
    "chi3": (3, lambda n: np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0)), False, 40.0),
    "chi4": (4, lambda n: np.where(n % 4 == 1, 1.0, np.where(n % 4 == 3, -1.0, 0.0)), False, 40.0),
    "chi5": (5, lambda n: np.where(np.isin(n % 5, (1, 4)), 1.0, np.where(np.isin(n % 5, (2, 3)), -1.0, 0.0)), False, 40.0),
    "chi8": (8, lambda n: np.where(np.isin(n % 8, (1, 7)), 1.0, np.where(np.isin(n % 8, (3, 5)), -1.0, 0.0)), False, 40.0),
}
N, dy = 12000, 0.005

print("THE FIBER AS ITS OWN OSCILLATOR: envelope+phase via analytic signal of the")
print("de-chirped real fiber, extended EVENLY across the hinge (conjugacy => turning point).")
print("prediction: first crossing at 0.500 pi (quarter cycle), cells 1.000 pi (half cycles)")
print(f"{'char':>6} {'first/pi':>9} {'median cell/pi':>15} {'sd':>7}")
for name, (q, chi_fn, demod, Y1) in CHARS.items():
    n = np.arange(1, N + 1, dtype=np.float64)
    c = chi_fn(n.astype(np.int64))
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0/np.clip(1.0 - u*u, 1e-300, None)), 0.0)
    amp = c * w * n**-0.5
    ln = np.log(n)
    ny = int(Y1/dy) + 1
    ys = dy*np.arange(ny)
    z = amp.astype(np.complex128)
    step = np.exp(-1j*dy*ln)
    F = np.empty(ny, dtype=np.complex128)
    for j in range(ny):
        F[j] = z.sum(); z *= step
    if demod:
        F = F / (1.0 - math.sqrt(2.0)*np.exp(-1j*ys*math.log(2.0)))
    absF = np.abs(F)
    med = float(np.median(absF))
    zi = [j for j in range(1, ny-1)
          if absF[j] < absF[j-1] and absF[j] < absF[j+1] and absF[j] < 0.25*med]
    # de-chirped real oscillator: |F| with sign flips at crossings
    sgn = np.ones(ny)
    for j in zi:
        sgn[j:] *= -1.0
    s = absF * sgn
    # even extension across the hinge (the conjugate-midpoint symmetry)
    s_ext = np.concatenate([s[::-1][:-1], s])
    phi = np.unwrap(np.angle(hilbert(s_ext)))[ny-1:]
    b = np.array([phi[j-1] for j in zi])
    first = abs(b[0] - phi[0]) / math.pi
    cells = np.abs(np.diff(b)) / math.pi
    print(f"{name:>6} {first:>9.3f} {float(np.median(cells)):>15.3f} {float(np.std(cells)):>7.3f}")
