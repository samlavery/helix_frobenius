import math
import numpy as np

CHARS = {
    "zeta": (2, lambda n: np.where(n % 2 == 1, 1.0, -1.0), True),
    "chi3": (3, lambda n: np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0)), False),
    "chi4": (4, lambda n: np.where(n % 4 == 1, 1.0, np.where(n % 4 == 3, -1.0, 0.0)), False),
    "chi5": (5, lambda n: np.where(np.isin(n % 5, (1, 4)), 1.0, np.where(np.isin(n % 5, (2, 3)), -1.0, 0.0)), False),
    "chi8": (8, lambda n: np.where(np.isin(n % 8, (1, 7)), 1.0, np.where(np.isin(n % 8, (3, 5)), -1.0, 0.0)), False),
}
N, dy, Y1 = 12000, 0.005, 60.0

print("Is the phase-cell fluctuation (S(T)) removable by carrier normalization?")
print(f"{'char':>6} {'corr(D,gap)':>12} {'ln s*':>8} {'s*':>7} {'sd bare':>8} {'sd at s*':>9} {'removed':>8}")
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
    Phi = np.unwrap(np.angle(F))
    b = np.array([Phi[j-3] for j in zi])
    a = np.array([Phi[j+3] for j in zi])
    gam = np.array([ys[j] for j in zi])
    D = (b[1:] - a[:-1])          # bare drift per cell (radians)
    gap = np.diff(gam)            # cell widths
    rho = float(np.corrcoef(D, gap)[0, 1])
    # D(s) = D - gap*ln(s); var minimized at ln s* = cov(D,gap)/var(gap)
    lns = float(np.cov(D, gap)[0, 1] / np.var(gap))
    Ds = D - gap * lns
    sd0, sd1 = float(np.std(D))/math.pi, float(np.std(Ds))/math.pi
    print(f"{name:>6} {rho:>12.3f} {lns:>8.3f} {math.exp(lns):>7.3f} {sd0:>8.3f} {sd1:>9.3f} "
          f"{100*(1-sd1/sd0):>7.1f}%")
    if name == "chi3":
        print(f"       median drift at s*: {np.median(Ds)/math.pi:+.3f} pi   "
              f"(theta'-scale check: 0.5*ln(q*30/2pi) = {0.5*math.log(q*30/(2*math.pi)):.3f})")
