"""Multi-height phi-horizon sweep: does the skew-influence horizon collapse in
raw ordinate units (reverb/growth clock, non-GUE scale) or in mean spacings
(GUE-compatible)?

Five height samples, one analysis: for each inter-zero gap of moderate size
(0.35-0.95 spacings), measure the arch peak position phi; fit the product model
truncated at horizon h (zeros within h of the gap midpoint); find h* minimizing
mean |phi_meas - phi_model| over the sample.  Verdict = which column of h* is
constant across heights: raw or unfolded.

  H1  t ~ 1500-2000      eta-fiber bank          spacing ~ 1.12
  H2  t ~ 52k-72k        eta-fiber (4 windows)   spacing ~ 0.68   + R-S bridge
  H3  t ~ 1e6            Riemann-Siegel + C0     spacing ~ 0.524
  H4  t ~ 1e7            Riemann-Siegel + C0     spacing ~ 0.441
  H5  t ~ 1.085e10       R-S base-split + C0     spacing ~ 0.295

Run:  python3 horizon_sweep.py A|B|C
"""
import math
import sys

import numpy as np

H_GRID = [0.15, 0.2, 0.28, 0.4, 0.55, 0.75, 1.0, 1.4, 1.9, 2.6, 3.5]
EDGE = 3.6


def mean_spacing(t):
    return 2 * math.pi / math.log(t / (2 * math.pi))


def phi_analysis(segments, sp, label):
    """segments: list of (taus, vals_abs, zeros). Pool moderate gaps, scan horizons."""
    recs = []
    for taus, vals, zeros in segments:
        dt = taus[1] - taus[0]
        lo, hi = taus[0] + EDGE, taus[-1] - EDGE
        zi = ((zeros - taus[0]) / dt).astype(int)
        for i in range(len(zeros) - 1):
            g = zeros[i + 1] - zeros[i]
            if not (0.35 < g / sp < 0.95):
                continue
            if zeros[i] < lo or zeros[i + 1] > hi:
                continue
            a, b = zi[i] + 2, zi[i + 1] - 1
            if b <= a + 4:
                continue
            yseg = taus[a:b]
            phi_m = (float(yseg[int(np.argmax(vals[a:b]))]) - zeros[i]) / g
            recs.append((yseg, zeros, zeros[i], zeros[i + 1], phi_m))
    print(f"  {label}: spacing {sp:.3f}, moderate gaps used: {len(recs)}")
    if len(recs) < 6:
        print("   (too few gaps)")
        return
    errs = []
    for h in H_GRID:
        tot = 0.0
        for yseg, zeros, zl, zr, phi_m in recs:
            mid = 0.5 * (zl + zr)
            M = np.ones(len(yseg))
            for zz in zeros:
                if abs(zz - mid) < h:
                    M *= np.abs(yseg - zz)
            phi_mod = (float(yseg[int(np.argmax(M))]) - zl) / (zr - zl)
            tot += abs(phi_m - phi_mod)
        errs.append(tot / len(recs))
    best = int(np.argmin(errs))
    flat = [H_GRID[i] for i, e in enumerate(errs) if e < 1.05 * errs[best]]
    print("   h_raw: " + " ".join(f"{h:6.2f}" for h in H_GRID))
    print("   err  : " + " ".join(f"{e:6.4f}" for e in errs))
    print(f"   h* = {H_GRID[best]:.2f} raw = {H_GRID[best]/sp:.2f} spacings"
          f"   (err {errs[best]:.4f}; 5%-flat range raw [{flat[0]:.2f}, {flat[-1]:.2f}])")


def extract_zeros_complex(taus, F):
    absF = np.abs(F)
    med = float(np.median(absF))
    dt = taus[1] - taus[0]
    zs = []
    for j in range(1, len(taus) - 1):
        if absF[j] < absF[j - 1] and absF[j] < absF[j + 1] and absF[j] < 0.3 * med:
            Fp = (F[j + 1] - F[j - 1]) / (2 * dt)
            if abs(Fp) > 1e-12:
                zs.append(float(taus[j] - (F[j] / Fp).real))
    return np.array(zs)


def extract_zeros_real(taus, Z):
    zs = []
    for j in range(1, len(taus)):
        if Z[j - 1] * Z[j] < 0:
            zs.append(float(taus[j - 1] + Z[j - 1] / (Z[j - 1] - Z[j]) * (taus[j] - taus[j - 1])))
    return np.array(zs)


def eta_sweep(t_lo, t_hi, dy, t_ref):
    N = int(40 * t_ref / (2 * math.pi))
    n = np.arange(1, N + 1, dtype=np.float64)
    sgn = np.where(n % 2 == 1, 1.0, -1.0)
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    amp = sgn * w * n ** (-0.5)
    ln = np.log(n)
    ny = int((t_hi - t_lo) / dy) + 1
    taus = t_lo + dy * np.arange(ny)
    z = amp * np.exp(-1j * t_lo * ln)
    step = np.exp(-1j * dy * ln)
    F = np.empty(ny, dtype=np.complex128)
    for j in range(ny):
        F[j] = z.sum()
        z *= step
    return taus, F


def rs_sweep(t_lo, t_hi, dy):
    """Riemann-Siegel Z with first correction; requires no integer-a crossing."""
    K_lo = int(math.sqrt(t_lo / (2 * math.pi)))
    K_hi = int(math.sqrt(t_hi / (2 * math.pi)))
    assert K_lo == K_hi, "window crosses an integer-a boundary"
    K = K_lo
    n = np.arange(1, K + 1, dtype=np.float64)
    ln = np.log(n)
    inv = 1.0 / np.sqrt(n)
    ts = np.arange(t_lo, t_hi + dy, dy)
    Z = np.empty(len(ts))
    for s in range(0, len(ts), 2000):
        tt = ts[s:s + 2000]
        theta = tt / 2 * np.log(tt / (2 * math.pi)) - tt / 2 - math.pi / 8 + 1.0 / (48 * tt)
        ph = theta[:, None] - tt[:, None] * ln[None, :]
        main = 2.0 * (np.cos(ph) @ inv)
        aa = np.sqrt(tt / (2 * math.pi))
        p = aa - np.floor(aa)
        cosden = np.cos(2 * math.pi * p)
        psi = np.where(np.abs(cosden) > 0.05,
                       np.cos(2 * math.pi * (p * p - p - 1.0 / 16)) / np.where(np.abs(cosden) > 0.05, cosden, 1.0),
                       0.0)
        Z[s:s + 2000] = main + (-1) ** (K + 1) * (tt / (2 * math.pi)) ** (-0.25) * psi
    return ts, Z


if __name__ == "__main__":
    part = sys.argv[1] if len(sys.argv) > 1 else "A"

    if part == "A":
        print("[H1] eta-fiber, t in [1500, 2000]")
        taus, F = eta_sweep(1500.0, 2000.0, 0.01, 2000.0)
        zs = extract_zeros_complex(taus, F)
        print(f"  zeros found: {len(zs)}")
        phi_analysis([(taus, np.abs(F), zs)], mean_spacing(1750.0), "H1 eta t~1750")

        print("[H3] Riemann-Siegel + C0, t ~ 1e6")
        ts, Z = rs_sweep(999850.0, 1000150.0, 0.005)
        zs = extract_zeros_real(ts, Z)
        print(f"  zeros found: {len(zs)}")
        phi_analysis([(ts, np.abs(Z), zs)], mean_spacing(1e6), "H3 RS t~1e6")

        print("[H4] Riemann-Siegel + C0, t ~ 1e7")
        ts, Z = rs_sweep(9999920.0, 10000080.0, 0.004)
        zs = extract_zeros_real(ts, Z)
        print(f"  zeros found: {len(zs)}")
        phi_analysis([(ts, np.abs(Z), zs)], mean_spacing(1e7), "H4 RS t~1e7")

    elif part == "B":
        targets = (52206.0, 55712.0, 66678.0, 71733.0)
        segs_eta, segs_rs = [], []
        for T0 in targets:
            taus, F = eta_sweep(T0 - 11.0, T0 + 11.0, 0.005, T0 + 11.0)
            segs_eta.append((taus, np.abs(F), extract_zeros_complex(taus, F)))
            ts, Z = rs_sweep(T0 - 11.0, T0 + 11.0, 0.002)
            segs_rs.append((ts, np.abs(Z), extract_zeros_real(ts, Z)))
        sp = mean_spacing(60000.0)
        print("[H2-eta] eta-fiber, four windows t ~ 52k-72k")
        phi_analysis(segs_eta, sp, "H2 eta t~52k-72k")
        print("[H2-RS] Riemann-Siegel + C0, same windows (method bridge)")
        phi_analysis(segs_rs, sp, "H2 RS t~52k-72k")

    elif part == "D":
        def chi_sweep(vals, q, t_lo, t_hi, dy, t_ref):
            N = int(40 * q * t_ref / (2 * math.pi))
            n = np.arange(1, N + 1, dtype=np.int64)
            chi = vals[n % q]
            nf = n.astype(np.float64)
            u = nf / N
            w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
            amp = chi * w * nf ** (-0.5)
            ln = np.log(nf)
            ny = int((t_hi - t_lo) / dy) + 1
            taus = t_lo + dy * np.arange(ny)
            z = amp * np.exp(-1j * t_lo * ln)
            step = np.exp(-1j * dy * ln)
            F = np.empty(ny, dtype=np.complex128)
            for j in range(ny):
                F[j] = z.sum()
                z *= step
            return taus, F

        v29 = np.zeros(29, dtype=np.complex128)
        for aa in range(1, 29):
            v29[aa] = 1.0 if pow(aa, 14, 29) == 1 else -1.0
        print("[D1] chi mod 29 (real quadratic), t in [1750, 2000]")
        taus, F = chi_sweep(v29, 29, 1750.0, 2000.0, 0.0125, 2000.0)
        zs = extract_zeros_complex(taus, F)
        sp29 = 2 * math.pi / math.log(29 * 1875.0 / (2 * math.pi))
        print(f"  zeros found: {len(zs)}   spacing {sp29:.3f} (zeta-equivalent t ~ 6e4 at t=1875!)")
        phi_analysis([(taus, np.abs(F), zs)], sp29, "D1 chi29 t~1875")

        v5 = np.zeros(5, dtype=np.complex128)
        v5[1], v5[2], v5[4], v5[3] = 1.0, 1j, -1.0, -1j
        print("[D2] chi mod 5 order 4 (complex), t in [1600, 2000]")
        taus, F = chi_sweep(v5, 5, 1600.0, 2000.0, 0.01, 2000.0)
        zs = extract_zeros_complex(taus, F)
        sp5 = 2 * math.pi / math.log(5 * 1800.0 / (2 * math.pi))
        print(f"  zeros found: {len(zs)}   spacing {sp5:.3f}")
        phi_analysis([(taus, np.abs(F), zs)], sp5, "D2 chi5c t~1800")

    elif part == "C":
        import mpmath as mp
        mp.mp.dps = 40
        t0 = mp.mpf("10854395965.14210")
        sp = float(2 * mp.pi / mp.log(t0 / (2 * mp.pi)))
        a = mp.sqrt(t0 / (2 * mp.pi))
        K = int(a)
        print(f"[H5] R-S base-split + C0, t ~ 1.085e10, K = {K}")
        two_pi = 2 * mp.pi
        ln = np.array([float(mp.log(n)) for n in range(1, K + 1)])
        basep = np.array([float((t0 * mp.log(n)) % two_pi) for n in range(1, K + 1)])
        th0 = float(mp.siegeltheta(t0) % two_pi)
        thp = float(mp.log(t0 / (2 * mp.pi)) / 2)
        inv = 1.0 / np.sqrt(np.arange(1, K + 1, dtype=np.float64))
        p = float(a - mp.floor(a))
        cosden = math.cos(2 * math.pi * p)
        psi = (math.cos(2 * math.pi * (p * p - p - 1.0 / 16)) / cosden) if abs(cosden) > 0.05 else 0.0
        corr = (-1) ** (K + 1) * float((t0 / two_pi) ** mp.mpf("-0.25")) * psi
        half = 16.0 * sp
        dy = 2.5e-4
        taus = np.arange(-half, half + dy, dy)
        z0 = th0 - basep
        Z = np.empty(len(taus))
        ez = np.exp(1j * z0)
        step = np.exp(1j * (thp * dy - dy * ln))
        for j in range(len(taus)):
            Z[j] = 2.0 * float(np.dot(inv, ez.real)) + corr
            ez *= step
        # note: phase(tau) = th0 + thp*tau - basep - tau*ln  -> handled by recurrence
        zs = extract_zeros_real(taus, Z)
        print(f"  zeros found: {len(zs)} in +-16 spacings")
        phi_analysis([(taus, np.abs(Z), zs)], sp, "H5 RS t~1.085e10")
