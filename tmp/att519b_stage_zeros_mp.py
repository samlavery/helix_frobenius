"""att519b -- the escort law at U = 1.5 in 40-digit arithmetic.

att519 found the stage Xi_1 non-real-rooted with a conjugate pair at +-31.28 +- 1.11 i, and the
tracking-window edge (tail ~ Xi) at t* ~ 4 e^{2U} = 29.6.  PREDICTION (recorded before running):
Xi_{1.5} has a non-real pair near t* ~ 4 e^{3} = 80, inside |Im z| <= 2; double precision cannot
see it (|Xi(80)| ~ 1e-27), so this uses mpmath at 40 digits.  Decision rule as in att519: argument
principle on the rectangle Re in [60, 100], Im in [-2, 2] vs sign changes on [60, 100].
"""

import mpmath as mp

mp.mp.dps = 40
PI = mp.pi
U = mp.mpf("1.5")


def phi(u):
    s = mp.mpf(0)
    e2 = mp.exp(2 * u)
    e9 = mp.exp(mp.mpf(9) / 2 * u)
    e5 = mp.exp(mp.mpf(5) / 2 * u)
    for n in range(1, 14):
        s += (2 * PI**2 * n**4 * e9 - 3 * PI * n**2 * e5) * mp.exp(-PI * n * n * e2)
    return 4 * s


# Gauss-Legendre nodes at working precision (mpmath computes them exactly to dps)
_nodes = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(mp.mpf(0), U, 7, mp.mp.prec)
_PW = [(x, phi(x) * w) for (x, w) in _nodes]


def xi_stage(z):
    return 2 * mp.fsum(pw * mp.cos(z * x) for (x, pw) in _PW)


def winding(a, b, n):
    tot = mp.mpf(0)
    prev = None
    for k in range(n + 1):
        z = a + (b - a) * mp.mpf(k) / n
        ph = mp.arg(xi_stage(z))
        if prev is not None:
            d = ph - prev
            while d > PI:
                d -= 2 * PI
            while d < -PI:
                d += 2 * PI
            if abs(d) > PI / 2:
                raise RuntimeError(f"phase step {float(d):.2f} too large on side {a}->{b}; refine")
            tot += d
        prev = ph
    return tot


def main():
    print("nodes:", len(_PW), "  Phi(1.5) =", mp.nstr(phi(U), 5))
    T0, T1, H = mp.mpf(60), mp.mpf(100), mp.mpf(2)
    corners = [mp.mpc(T0, -H), mp.mpc(T1, -H), mp.mpc(T1, H), mp.mpc(T0, H), mp.mpc(T0, -H)]
    sides_n = [500, 120, 500, 120]
    tot = mp.mpf(0)
    for (a, b), n in zip(zip(corners[:-1], corners[1:]), sides_n):
        tot += winding(a, b, n)
    nrect = int(mp.nint(tot / (2 * PI)))
    # real zeros on [60, 100]
    npts = 1601
    vals = [xi_stage(mp.mpc(T0 + (T1 - T0) * mp.mpf(k) / (npts - 1), 0)).real for k in range(npts)]
    nreal = sum(1 for k in range(npts - 1) if vals[k] * vals[k + 1] < 0)
    print(f"U = 1.5, rectangle Re in [60,100], Im in [-2,2]: zeros = {nrect}, real zeros = {nreal}, "
          f"excess = {nrect - nreal}")
    print("|Xi_1.5(t)| at t = 60, 80, 100:", [mp.nstr(abs(xi_stage(mp.mpc(t, 0))), 3) for t in (60, 80, 100)])
    if nrect > nreal:
        # locate: coarse grid on Im in (0.05, 2], Newton
        best = []
        for i in range(1, 21):
            y = H * mp.mpf(i) / 20
            for j in range(0, 161):
                x = T0 + (T1 - T0) * mp.mpf(j) / 160
                best.append((abs(xi_stage(mp.mpc(x, y))), mp.mpc(x, y)))
        best.sort(key=lambda p: p[0])
        found = []
        for _, z0 in best[:12]:
            z = z0
            for _ in range(80):
                f = xi_stage(z)
                h = mp.mpf("1e-12")
                df = (xi_stage(z + h) - xi_stage(z - h)) / (2 * h)
                if df == 0:
                    break
                step = f / df
                z -= step
                if abs(step) < mp.mpf("1e-30"):
                    break
            if abs(xi_stage(z)) < mp.mpf("1e-35") and abs(z.imag) > mp.mpf("1e-6") and z.imag > 0:
                if all(abs(z - w) > mp.mpf("1e-6") for w in found):
                    found.append(z)
        for z in sorted(found, key=lambda w: w.real):
            print(f"   off-axis zero: z = {mp.nstr(z.real, 8)} + {mp.nstr(z.imag, 6)} i   "
                  f"|Xi| = {mp.nstr(abs(xi_stage(z)), 3)}   (predicted edge t* = 4e^3 = {mp.nstr(4*mp.e**3, 5)})")


if __name__ == "__main__":
    main()
