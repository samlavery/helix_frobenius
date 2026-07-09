import math
import numpy as np

CHARS = {
    "eta":  (1, lambda n: np.where(n % 2 == 1, 1.0, -1.0), 15.0),
    "chi3": (3, lambda n: np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0)), 9.0),
    "chi4": (4, lambda n: np.where(n % 4 == 1, 1.0, np.where(n % 4 == 3, -1.0, 0.0)), 7.0),
    "chi5": (5, lambda n: np.where(np.isin(n % 5, (1, 4)), 1.0, np.where(np.isin(n % 5, (2, 3)), -1.0, 0.0)), 7.5),
    "chi8": (8, lambda n: np.where(np.isin(n % 8, (1, 7)), 1.0, np.where(np.isin(n % 8, (3, 5)), -1.0, 0.0)), 6.0),
}
U = math.pi/3.0

print("GROWTH-PATH phase odometer: head-coupled fiber born at 0 (newest phasor always ramping).")
print("first-cell phase to the first vanishing, running carrier gauge.  Prediction: 0.500 pi")
print(f"{'char':>6} {'gamma_1':>9} {'raw first/pi':>13} {'gauged first/pi':>16}")
for name, (q, chi_fn, ymax) in CHARS.items():
    dy = 0.01 if name == "eta" else 0.005
    ys = np.arange(0.2, ymax, dy)
    Nmax = int(math.exp(ymax)) + 2
    n = np.arange(1, Nmax + 1, dtype=np.float64)
    c = chi_fn(n.astype(np.int64))
    x = U * n
    base = c * x**-0.5
    lnx = np.log(x)
    F = np.empty(len(ys), dtype=np.complex128)
    for j, y in enumerate(ys):
        Z = math.exp(y)
        N = min(int(Z), Nmax)
        u = n[:N] / Z
        w = np.exp(1.0 - 1.0/np.clip(1.0 - u*u, 1e-300, None))
        F[j] = np.sum(base[:N] * w * np.exp(-1j*y*lnx[:N]))
    absF = np.abs(F)
    win = int(2.0/dy)
    locmed = np.interp(np.arange(len(ys)), np.arange(0, len(ys), 100),
                       [np.median(absF[max(0,k-win):k+win]) for k in range(0, len(ys), 100)])
    zi = None
    for j in range(3, len(ys)-1):
        if absF[j] < absF[j-1] and absF[j] < absF[j+1] and absF[j] < 0.2*locmed[j]:
            zi = j; break
    Phi = np.unwrap(np.angle(F))
    g1 = ys[zi]
    raw = (Phi[zi-3] - Phi[0]) / math.pi
    thp = 0.5*np.log(np.maximum(q*ys[:zi]/(2*math.pi), 1e-12))
    thp = np.maximum(thp, 0.0)
    gauged = (Phi[zi-3] - Phi[0] + np.trapezoid(thp, dx=dy)) / math.pi
    print(f"{name:>6} {g1:>9.3f} {raw:>13.3f} {gauged:>16.3f}")
