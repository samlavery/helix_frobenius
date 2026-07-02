import math
import numpy as np

CHARS = {
    "zeta": (2, lambda n: np.where(n % 2 == 1, 1.0, -1.0), True),
    "chi3": (3, lambda n: np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0)), False),
    "chi4": (4, lambda n: np.where(n % 4 == 1, 1.0, np.where(n % 4 == 3, -1.0, 0.0)), False),
    "chi5": (5, lambda n: np.where(np.isin(n % 5, (1, 4)), 1.0, np.where(np.isin(n % 5, (2, 3)), -1.0, 0.0)), False),
    "chi8": (8, lambda n: np.where(np.isin(n % 8, (1, 7)), 1.0, np.where(np.isin(n % 8, (3, 5)), -1.0, 0.0)), False),
}
SCALES = [("bare 1", 1.0), ("pi/3", math.pi/3), ("pi/6", math.pi/6), ("pi/2", math.pi/2), ("2pi/3", 2*math.pi/3)]
N, dy, Y1 = 12000, 0.005, 60.0

results = {}
for name, (q, chi_fn, demod) in CHARS.items():
    n = np.arange(1, N + 1, dtype=np.float64)
    c = chi_fn(n.astype(np.int64))
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0/np.clip(1.0 - u*u, 1e-300, None)), 0.0)
    amp = c * w * n**-0.5
    ln = np.log(n)
    ny = int(Y1/dy) + 1
    ys = dy * np.arange(ny)
    z = amp.astype(np.complex128)
    step = np.exp(-1j*dy*ln)
    F = np.empty(ny, dtype=np.complex128)
    for j in range(ny):
        F[j] = z.sum(); z *= step
    if demod:
        F = F / (1.0 - math.sqrt(2.0)*np.exp(-1j*ys*math.log(2.0)))
    absF = np.abs(F); med = float(np.median(absF))
    zi = [j for j in range(1, ny-1)
          if absF[j] < absF[j-1] and absF[j] < absF[j+1] and absF[j] < 0.25*med]
    Phi1 = np.unwrap(np.angle(F))
    row = {}
    for lbl, s in SCALES:
        Phi = Phi1 - ys*math.log(s)   # carrier-normalized phase
        b = np.array([Phi[j-3] for j in zi])
        a = np.array([Phi[j+3] for j in zi])
        first = (b[0]-Phi[0])/math.pi
        drift = float(np.median((b[1:]-a[:-1])/math.pi))
        sd = float(np.std((b[1:]-a[:-1])/math.pi))
        row[lbl] = (first, drift, sd)
    results[name] = row

print(f"{'':>6}", end="")
for lbl, _ in SCALES:
    print(f" | {lbl:>19}", end="")
print()
print(f"{'char':>6}", end="")
for _ in SCALES:
    print(f" | {'first':>6} {'drift':>6} {'sd':>5}", end="")
print()
for name, row in results.items():
    print(f"{name:>6}", end="")
    for lbl, _ in SCALES:
        f_, d_, s_ = row[lbl]
        print(f" | {f_:>6.3f} {d_:>6.3f} {s_:>5.3f}", end="")
    print()
# aggregate: distance of (|first|, |drift|) from (0.5, 1.0) pooled over chars
print()
print("aggregate |first|-0.5 and |drift|-1.0 (rms over characters):")
for lbl, _ in SCALES:
    ef = np.sqrt(np.mean([(abs(results[nm][lbl][0]) - 0.5)**2 for nm in results]))
    ed = np.sqrt(np.mean([(abs(results[nm][lbl][1]) - 1.0)**2 for nm in results]))
    print(f"   {lbl:>7}: first-err {ef:.3f}   drift-err {ed:.3f}")
