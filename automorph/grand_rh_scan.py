"""Focal-closure growth scan across the GRH/grand-RH families.

Same mechanism as focal_growth_scan.py -- whole finite bank, head-height readout
y = log Z, self-similar growth window, closure of the lane system -- generalized
to one representative per new structural family:

  1. COMPLEX Dirichlet characters (degree 1, non-real):
       chi5c = order-4 character mod 5   (chi(2) = i)
       chi7c = order-6 character mod 7   (chi(3) = e^{i pi/3})
     Lanes: one resultant R_a per active residue class a; the vanishing is the
     closure of the chi-weighted lane POLYGON  sum_a chi(a) R_a = 0.
     Certification: my own mpmath Hurwitz-zeta zero list (independent of model).

  2. GL(2) holomorphic cusp form, level 1: Ramanujan Delta (weight 12).
     lambda(n) = tau(n)/n^{11/2}, tau built from scratch via eta^24
     (Jacobi eta^3 sparse series, three FFT squarings).
     Lanes: sign lanes with arrow length |lambda(n)| x_n^{-1/2}.
     Certification: LMFDB published zeros (final column) + second-window check.

  3. GL(2) weight 2, conductor 11: elliptic curve 11.a,  eta(q)^2 eta(q^11)^2.
     lambda(n) = a_n/sqrt(n).  Same lanes.  Same certification.

No L-function is evaluated anywhere in the locator; references appear only in
the final columns.
"""
import math
import sys

import numpy as np

PI3 = math.pi / 3.0

# ---------------------------------------------------------------- coefficients


def eta_pentagonal(N):
    """prod (1-q^n) as a dense length-N array (pentagonal number theorem)."""
    c = np.zeros(N, dtype=np.float64)
    k = 0
    while True:
        done = True
        for kk in (k, -k) if k else (0,):
            m = kk * (3 * kk - 1) // 2
            if m < N:
                c[m] += (-1) ** kk
                done = False
        if k and done:
            break
        k += 1
    return c


def eta3(N):
    """prod (1-q^n)^3 = sum_k (-1)^k (2k+1) q^{k(k+1)/2} (Jacobi)."""
    c = np.zeros(N, dtype=np.float64)
    k = 0
    while True:
        m = k * (k + 1) // 2
        if m >= N:
            break
        c[m] += (-1) ** k * (2 * k + 1)
        k += 1
    return c


def fft_square_trunc(a, N):
    L = 1
    while L < 2 * N:
        L *= 2
    fa = np.fft.rfft(a, L)
    out = np.fft.irfft(fa * fa, L)[:N]
    return out


def exact_square_trunc(a, N, B=8192.0):
    """Exact truncated square of an integer-valued float64 array via balanced
    limb splitting: each cross-convolution has values <= N*(B/2)^2 ~ 2e13, so
    float64 FFT roundoff (<0.5) is killed by rounding; magnitudes are local in
    the output index, so small coefficients stay exact even when the array's
    dynamic range exceeds 2^53."""
    limbs = []
    r = a.copy()
    for _ in range(10):
        if not np.any(r):
            break
        d = np.round(r / B)
        limbs.append(r - B * d)
        r = d
    L = 1
    while L < 2 * N:
        L *= 2
    Fs = [np.fft.rfft(l, L) for l in limbs]
    out = np.zeros(N, dtype=np.float64)
    for i in range(len(limbs)):
        for j in range(i, len(limbs)):
            conv = np.round(np.fft.irfft(Fs[i] * Fs[j], L)[:N])
            out += ((1.0 if i == j else 2.0) * B ** (i + j)) * conv
    return out


def fft_mul_trunc(a, b, N):
    L = 1
    while L < 2 * N:
        L *= 2
    out = np.fft.irfft(np.fft.rfft(a, L) * np.fft.rfft(b, L), L)[:N]
    return out


def tau_lambda(N):
    """lambda(n) = tau(n)/n^{5.5} for n=1..N (analytic normalization)."""
    P = eta3(N)                       # eta^3   (values <= ~3300: exact)
    P = exact_square_trunc(P, N)      # eta^6
    P = exact_square_trunc(P, N)      # eta^12
    P = exact_square_trunc(P, N)      # eta^24
    tau = np.zeros(N + 1)
    tau[1:] = P[: N]                  # Delta = q * eta(q)^24
    for n, want in ((1, 1), (2, -24), (3, 252), (4, -1472), (5, 4830), (6, -6048)):
        assert abs(tau[n] - want) / max(1, abs(want)) < 1e-9, (n, tau[n], want)
    assert tau[2] * tau[3] == tau[6] and tau[2] * tau[5] == tau[10]   # Hecke multiplicativity
    for p in (101, 1009, 10007, 100003):                              # Deligne |lambda(p)| <= 2
        if p <= N:
            assert abs(tau[p] / p ** 5.5) <= 2.0, p
    n = np.arange(0, N + 1, dtype=np.float64)
    lam = np.zeros(N + 1)
    lam[1:] = tau[1:] / n[1:] ** 5.5
    return lam


def e11_lambda(N):
    """lambda(n) = a_n/sqrt(n) for 11.a: q prod (1-q^n)^2 (1-q^{11n})^2."""
    P1 = eta_pentagonal(N)
    A = fft_square_trunc(P1, N)
    N11 = N // 11 + 2
    P11 = np.zeros(N, dtype=np.float64)
    small = eta_pentagonal(N11)
    idx = np.arange(N11) * 11
    keep = idx < N
    P11[idx[keep]] = small[keep]
    B = fft_square_trunc(P11, N)
    prod = fft_mul_trunc(A, B, N)
    a = np.zeros(N + 1)
    a[1:] = np.rint(prod[:N])         # exact small integers
    for n, want in ((1, 1), (2, -2), (3, -1), (4, 2), (5, 1), (7, -2), (11, 1)):
        assert a[n] == want, (n, a[n], want)
    n = np.arange(0, N + 1, dtype=np.float64)
    lam = np.zeros(N + 1)
    lam[1:] = a[1:] / np.sqrt(n[1:])
    return lam


def dirichlet_values(q, gen, order):
    """Complex character mod q: chi(gen) = primitive `order`-th root of unity."""
    vals = np.zeros(q, dtype=np.complex128)
    zeta = np.exp(2j * np.pi / order)
    a, k = 1, 0
    while True:
        a = (a * gen) % q if k else 1
        if k and a == 1:
            break
        vals[a] = zeta ** k
        k += 1
    return vals


# ------------------------------------------------------------------- closure


def closure_dirichlet(vals, q, y):
    Z = math.exp(y)
    N = int(Z)
    if N < q + 1:
        return 1.0
    n = np.arange(1, N + 1, dtype=np.float64)
    chi = vals[(n.astype(np.int64)) % q]
    u = n / Z
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    x = PI3 * n
    term = w * x ** (-0.5) * np.exp(-1j * y * np.log(x))
    F = 0j
    max_lane = 0.0
    for a in range(1, q):
        if vals[a] == 0:
            continue
        lane = complex(np.sum(np.where(n.astype(np.int64) % q == a, term, 0)))
        F += vals[a] * lane
        max_lane = max(max_lane, abs(lane))
    return abs(F) / max_lane if max_lane > 0 else 1.0


def closure_cusp(lam, y, window="bump", stretch=1.0):
    Z = math.exp(y) * stretch
    N = min(int(Z), len(lam) - 1)
    if N < 4:
        return 1.0
    n = np.arange(1, N + 1, dtype=np.float64)
    lv = lam[1 : N + 1]
    u = n / Z
    if window == "bump":
        w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    else:  # alternative shape for the independent second-window check
        w = np.where(u < 1.0, np.exp(-(u * u) / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    x = PI3 * n
    term = np.abs(lv) * w * x ** (-0.5) * np.exp(-1j * y * np.log(x))
    P = complex(np.sum(np.where(lv > 0, term, 0)))
    M = complex(np.sum(np.where(lv < 0, term, 0)))
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


def scan(f, y0, y1, per_unit=240, depth_cut=2e-2):
    ys = np.linspace(y0, y1, max(9, int((y1 - y0) * per_unit)))
    cs = np.array([f(float(y)) for y in ys])
    med = float(np.median(cs))
    step = float(ys[1] - ys[0])
    out = []
    for i in range(1, len(ys) - 1):
        if cs[i] < cs[i - 1] and cs[i] < cs[i + 1] and cs[i] < 0.25 * med:
            y = golden(f, float(ys[i]) - 1.5 * step, float(ys[i]) + 1.5 * step)
            if f(y) < depth_cut:
                out.append(y)
    return out


# ---------------------------------------------------------------- ground truth


def mpmath_dirichlet_zeros(vals, q, t_max):
    """Independent zero list for a complex character via Hurwitz zeta."""
    import mpmath as mp

    mp.mp.dps = 20

    def L(t):
        s = mp.mpf("0.5") + 1j * mp.mpf(t)
        return abs(q ** (-s) * mp.fsum(complex(vals[a]) * mp.zeta(s, mp.mpf(a) / q) for a in range(1, q) if vals[a] != 0))

    ts = np.arange(0.2, t_max, 0.02)
    Ls = np.array([L(float(t)) for t in ts])
    zeros = []
    for i in range(1, len(ts) - 1):
        if Ls[i] < Ls[i - 1] and Ls[i] < Ls[i + 1] and Ls[i] < 0.15:
            t = golden(lambda u: L(float(u)), float(ts[i]) - 0.03, float(ts[i]) + 0.03)
            if L(float(t)) < 1e-9:
                zeros.append(float(t))
    return zeros


LMFDB = {
    "Delta": [9.222379399921103, 13.907549861392134, 17.442776978234473],
    "E11": [6.362613894713089, 8.603539619290756, 10.035509097181079, 11.451258610345211, 13.568639057129995],
}

if __name__ == "__main__":
    print("GRAND-RH FOCAL-CLOSURE SCAN -- one representative per structural family")
    print("locator: whole-bank lane closure, head readout y=log Z; no L in the loop\n")

    for name, q, gen, order, ymax in (("chi5c (order 4)", 5, 2, 4, 11.0), ("chi7c (order 6)", 7, 3, 6, 10.0)):
        vals = dirichlet_values(q, gen, order)
        found = scan(lambda y: closure_dirichlet(vals, q, y), 1.6, ymax)
        truth = mpmath_dirichlet_zeros(vals, q, ymax + 0.3)
        print(f"{name}: complex character, lane-polygon closure")
        print(f"   independent mpmath zeros in window: {['%.6f' % t for t in truth]}")
        print(f"   {'closure y':>12} {'Z=e^y':>10} {'depth':>10} {'nearest truth':>13} {'|diff|':>9}")
        for y in found:
            near = min(truth, key=lambda g: abs(g - y)) if truth else float("nan")
            print(f"   {y:>12.6f} {math.exp(y):>10.1f} {closure_dirichlet(vals, q, y):>10.2e} {near:>13.6f} {abs(y - near):>9.1e}")
        missed = [t for t in truth if t < ymax and min((abs(t - y) for y in found), default=9) > 1e-2]
        print(f"   missed truth zeros in window: {['%.4f' % t for t in missed] if missed else 'none'}\n")

    print("Delta (GL(2), weight 12, level 1): building tau(n) via eta^24 ...")
    lamD = tau_lambda(1_300_000)
    fD = lambda y: closure_cusp(lamD, y)
    foundD = scan(fD, 8.5, 9.8, per_unit=240) + scan(fD, 13.55, 14.15, per_unit=120)
    print(f"   {'closure y':>12} {'Z=e^y':>12} {'depth':>10} {'2nd-window':>11} {'off(+0.3)':>10} {'LMFDB':>13} {'|diff|':>9}")
    for y in foundD:
        alt = closure_cusp(lamD, y, window="alt", stretch=1.7)
        off = closure_cusp(lamD, y + 0.3)
        near = min(LMFDB["Delta"], key=lambda g: abs(g - y))
        print(f"   {y:>12.6f} {math.exp(y):>12.1f} {fD(y):>10.2e} {alt:>11.2e} {off:>10.3f} {near:>13.6f} {abs(y - near):>9.1e}")
    print()

    print("E11 (GL(2), weight 2, conductor 11): building a_n via eta(q)^2 eta(q^11)^2 ...")
    lamE = e11_lambda(1_000_000)
    fE = lambda y: closure_cusp(lamE, y)
    foundE = scan(fE, 5.6, 11.7, per_unit=240) + scan(fE, 13.35, 13.78, per_unit=120)
    print(f"   {'closure y':>12} {'Z=e^y':>12} {'depth':>10} {'2nd-window':>11} {'off(+0.3)':>10} {'LMFDB':>13} {'|diff|':>9}")
    for y in foundE:
        alt = closure_cusp(lamE, y, window="alt", stretch=1.7)
        off = closure_cusp(lamE, y + 0.3)
        near = min(LMFDB["E11"], key=lambda g: abs(g - y))
        print(f"   {y:>12.6f} {math.exp(y):>12.1f} {fE(y):>10.2e} {alt:>11.2e} {off:>10.3f} {near:>13.6f} {abs(y - near):>9.1e}")
    missedE = [t for t in LMFDB["E11"] if (5.6 < t < 11.7 or 13.35 < t < 13.78) and min((abs(t - y) for y in foundE), default=9) > 1e-2]
    print(f"   missed LMFDB zeros in windows: {['%.4f' % t for t in missedE] if missedE else 'none'}")
