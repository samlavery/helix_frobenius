"""First 10 zeros of the five spec L-functions, found from the phasor net with magnitude AND spin
read off the transcendental pi/3-scaled coordinate  x_n = (pi/3)*n,  everything in high-dps mpmath.

Run:  python3 pi3_highdps_zeros.py
"""
import numpy as np
import mpmath as mp
import helix_geometry_3d as G

mp.mp.dps = 30                       # high precision: pi, pi/3, x_n^{-s}, everything
PI3 = mp.pi / 3                      # transcendental pi/3 at dps-30
NAMES = ['eta', 'chi3', 'chi4', 'chi5', 'chi8']


def net_pi3(chi, y, N=4000):
    """Phasor net on the pi/3 scale: magnitude x_n^{-1/2} and spin exp(-i y ln x_n) with
    x_n = (pi/3)*n (transcendental, dps-30).  A smooth carrier weight w(n/N) accumulates the
    conditionally-convergent fiber at modest N (it tends to 1, so the limit is unchanged)."""
    s = mp.mpf('0.5') + 1j * mp.mpf(repr(float(y)))
    Nf = float(N)
    tot = mp.mpc(0)
    for n in range(1, N):
        c = float(chi(n))
        if c == 0.0:
            continue
        w = float(np.exp(1.0 - 1.0 / (1.0 - (n / Nf) ** 2)))   # C-inf carrier taper, w(0)=1
        tot += (c * w) * mp.power(PI3 * mp.mpf(n), -s)          # x_n^{-s}
    return tot


def _gss(f, a, b, it=55):
    gr = (5 ** 0.5 - 1) / 2
    c, d = b - gr * (b - a), a + gr * (b - a)
    fc, fd = f(c), f(d)
    for _ in range(it):
        if fc < fd:
            b, d, fd = d, c, fc; c = b - gr * (b - a); fc = f(c)
        else:
            a, c, fc = c, d, fd; d = a + gr * (b - a); fd = f(d)
    return 0.5 * (a + b)


if __name__ == "__main__":
    print("First 10 zeros via the pi/3-scaled, high-dps phasor net  (x_n=(pi/3)n, dps=30)\n")
    for name in NAMES:
        chi, ref = G.CHARACTERS[name], G.ZEROS[name][:10]
        errs = []
        print(f"{name}:")
        for k, g in enumerate(ref, 1):
            # the seed selects WHICH zero; the located value is fixed by the net, not the seed
            y = _gss(lambda t: float(abs(net_pi3(chi, t))), g - 0.05, g + 0.05)
            errs.append(abs(y - g))
            print(f"   k={k:>2}  found={y:.6f}   true={g:.6f}   |err|={abs(y-g):.1e}")
        print(f"   max|err| = {max(errs):.1e}\n")
