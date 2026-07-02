import math
import numpy as np

CHARS = {
    "chi3": (3, lambda n: np.where(n % 3 == 1, 1.0, np.where(n % 3 == 2, -1.0, 0.0)), False),
    "chi4": (4, lambda n: np.where(n % 4 == 1, 1.0, np.where(n % 4 == 3, -1.0, 0.0)), False),
    "chi5": (5, lambda n: np.where(np.isin(n % 5, (1, 4)), 1.0, np.where(np.isin(n % 5, (2, 3)), -1.0, 0.0)), False),
    "chi8": (8, lambda n: np.where(np.isin(n % 8, (1, 7)), 1.0, np.where(np.isin(n % 8, (3, 5)), -1.0, 0.0)), False),
}
N, dy, Y1 = 12000, 0.005, 60.0
U = math.pi / 3.0

print("CONTINUOUS-GROWTH fiber: phasor n = integral over its own cell [x_(n-1), x_n],")
print("first phasor grows from EXACTLY 0.  Cells in the running carrier gauge.")
print(f"{'char':>6} {'first/pi':>9} {'cell drift/pi':>14} {'sd':>7} {'zeros vs discrete':>18}")
for name, (q, chi_fn, demod) in CHARS.items():
    n = np.arange(1, N + 1, dtype=np.float64)
    c = chi_fn(n.astype(np.int64))
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0/np.clip(1.0 - u*u, 1e-300, None)), 0.0)
    xn = U * n
    xm = U * (n - 1.0)
    sq_n = np.sqrt(xn)
    sq_m = np.sqrt(np.maximum(xm, 0.0))
    ln_n = np.log(xn)
    ln_m = np.where(n > 1, np.log(np.maximum(xm, 1e-300)), 0.0)
    ny = int(Y1/dy) + 1
    ys = dy*np.arange(ny)
    # recurrences for x^{-iy} on both cell edges
    zn = (c * w * sq_n).astype(np.complex128)     # will carry x_n^{1/2 - iy}
    zm = (c * w * sq_m).astype(np.complex128)     # x_{n-1}^{1/2 - iy}; n=1 edge is 0
    zm[0] = 0.0
    stn = np.exp(-1j*dy*ln_n)
    stm = np.exp(-1j*dy*ln_m)
    F = np.empty(ny, dtype=np.complex128)
    for j in range(ny):
        F[j] = (zn.sum() - zm.sum()) / (0.5 - 1j*ys[j])
        zn *= stn
        zm *= stm
    if demod:
        F = F / (1.0 - math.sqrt(2.0)*np.exp(-1j*ys*math.log(2.0)))
    absF = np.abs(F)
    win = int(8.0/dy)
    locmed = np.array([np.median(absF[max(0,j-win):j+win]) for j in range(0, ny, 200)])
    locmed = np.interp(np.arange(ny), np.arange(0, ny, 200), locmed)
    zi = [j for j in range(1, ny-1)
          if absF[j] < absF[j-1] and absF[j] < absF[j+1] and absF[j] < 0.25*locmed[j]]
    gam = np.array([ys[j] for j in zi])
    Phi = np.unwrap(np.angle(F))
    b = np.array([Phi[j-3] for j in zi])
    a = np.array([Phi[j+3] for j in zi])
    thp_first = 0.5*np.log(np.maximum(q*np.maximum(gam[0],1.0)/(2*math.pi), 1.01))
    # corrected first phase: raw winding + integral of local density from 0.. (use trapz of theta')
    tgrid = ys[:zi[0]]
    thp_grid = 0.5*np.log(np.maximum(q*np.maximum(tgrid, 1e-9)/(2*math.pi), 1e-9))
    thp_grid = np.maximum(thp_grid, 0.0)          # density clock nonnegative
    corr_first = (b[0] - Phi[0] + np.trapezoid(thp_grid, dx=dy)) / math.pi
    tm = 0.5*(gam[1:] + gam[:-1])
    thp = 0.5*np.log(np.maximum(q*tm/(2*math.pi), 1.01))
    D = (b[1:] - a[:-1]) + thp*np.diff(gam)
    # zero agreement vs the plain discrete fiber's zeros (quick reference from earlier run)
    print(f"{name:>6} {corr_first:>9.3f} {float(np.median(D))/math.pi:>14.3f} "
          f"{float(np.std(D))/math.pi:>7.3f} {len(zi):>10} zeros")
    if name == "chi3":
        print(f"       first zeros located: " + " ".join(f"{g:.3f}" for g in gam[:5])
              + "   (discrete-fiber refs: 8.040, 11.249, 15.705, 18.262, 20.456)")
