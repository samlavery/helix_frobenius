"""C3 booking probe — Davenport–Heilbronn positive control (2026-08-28).

Design law: the control must fail by PRESENT structure.  DH satisfies the FE
and has genuine off-line zeros (first pair near 0.8085 + 85.6993i), so the
cell-ledger tally functional (flips of the despun readout vs argument-principle
census per box) must BOOK those pairs as integer defects, or the probe is
wrong.  ζ is the null control (202/202 exact, prior run).

Registered prediction: defect = 2 per off-line pair in its box, 0 elsewhere,
depth-independent (integer booking — no small-δ evasion).
"""
import mpmath as mp

mp.mp.dps = 25

# chi mod 5 with chi(2) = i (odd primitive character)
CHI = {1: mp.mpf(1), 2: mp.mpc(0, 1), 3: mp.mpc(0, -1), 4: mp.mpf(-1), 0: 0}
KAPPA = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)

def Lchi(s, conj=False):
    tot = mp.mpf(0)
    for a in (1, 2, 3, 4):
        c = CHI[a]
        if conj:
            c = mp.conj(c)
        tot += c * mp.zeta(s, mp.mpf(a) / 5)
    return 5 ** (-s) * tot

def dh(s):
    return ((1 - mp.mpc(0, 1) * KAPPA) / 2) * Lchi(s) \
         + ((1 + mp.mpc(0, 1) * KAPPA) / 2) * Lchi(s, conj=True)

def dh_theta(t):
    """Clock of the DH gamma factor (5/pi)^{s/2} Gamma((s+1)/2) at s = 1/2+it."""
    s = mp.mpc(0.5, t)
    return mp.im((s / 2) * mp.log(5 / mp.pi) + mp.loggamma((s + 1) / 2))

def Zdh(t):
    z = mp.exp(mp.mpc(0, 1) * dh_theta(t)) * dh(mp.mpc(0.5, t))
    return mp.re(z)   # imaginary part should vanish (FE self-dual); monitored

def winding_count(t1, t2, sig_lo=-0.5, sig_hi=1.5, n_edge=800):
    """Zeros of dh in the rectangle [sig_lo,sig_hi] x [t1,t2] by arg winding."""
    pts = []
    for i in range(n_edge + 1):   # bottom: lo->hi at t1
        pts.append(mp.mpc(sig_lo + (sig_hi - sig_lo) * i / n_edge, t1))
    for i in range(1, n_edge + 1):  # right: t1->t2
        pts.append(mp.mpc(sig_hi, t1 + (t2 - t1) * i / n_edge))
    for i in range(1, n_edge + 1):  # top: hi->lo
        pts.append(mp.mpc(sig_hi - (sig_hi - sig_lo) * i / n_edge, t2))
    for i in range(1, n_edge + 1):  # left: t2->t1
        pts.append(mp.mpc(sig_lo, t2 - (t2 - t1) * i / n_edge))
    tot = mp.mpf(0)
    prev = mp.arg(dh(pts[0]))
    for p in pts[1:]:
        a = mp.arg(dh(p))
        d = a - prev
        while d > mp.pi:
            d -= 2 * mp.pi
        while d < -mp.pi:
            d += 2 * mp.pi
        tot += d
        prev = a
    return int(mp.nint(tot / (2 * mp.pi)))

def flips(t1, t2, step=0.02):
    n = int(mp.ceil((t2 - t1) / step))
    xs = [t1 + (t2 - t1) * i / n for i in range(n + 1)]
    vs = [Zdh(x) for x in xs]
    imax = max(abs(mp.im(mp.exp(mp.mpc(0, 1) * dh_theta(x)) * dh(mp.mpc(0.5, x))))
               for x in xs[:: max(1, n // 20)])
    f = 0
    for i in range(n):
        if vs[i] * vs[i + 1] < 0:
            f += 1
    return f, float(imax)

def main():
    print("DH control — boxes of height 2, t in [80, 92] (brackets first off-line pair)")
    print("plus background [10, 22]")
    for t1 in [10, 12, 14, 16, 18, 20] + [80, 82, 84, 86, 88, 90]:
        t2 = t1 + 2
        F, imax = flips(t1, t2)
        N = winding_count(t1, t2)
        tag = "PASS" if F == N else f"DEFECT {N - F}"
        print(f"  box [{t1:3d},{t2:3d}]: flips {F}  census {N}  {tag}"
              f"   (Z-imag sanity {imax:.1e})")

if __name__ == '__main__':
    main()
