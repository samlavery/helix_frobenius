"""Amplitude crossover: repulsion (unfolds) vs fiber/harmonic resistance (raw).

Observable: bump/ambient = (max |L| between consecutive zeros) / (running-median
ambient), on CLEAN observables only:
  - zeta via de-modulated eta fiber  |F_eta| / |1 - 2^{1-s}|  (exact prefactor)
  - zeta via Riemann-Siegel + C0 at 1e6 / 1e7
  - Dirichlet chi fibers (converge to |L| directly, no prefactor)

Samples (spacing):            S1 zeta t~1750 (1.116)   S2 zeta t~52-72k (0.686)
  S3 zeta 1e6 (0.525)         S4 zeta 1e7 (0.440)      S5 chi29 t~1875 (0.693)
  S6 chi5c t~1800 (0.865)     S7 chi101 t~1940 (0.607)

Each sample dumps per-gap records (g_unfolded, dy_raw, bump/ambient) to
tmp/amp_<tag>.npz.  The collate step bins the curves in BOTH unit systems and
scores cross-sample collapse: the system with lower variance wins.

Run: python3 amp_cross.py A|B|C|D|collate
"""
import math
import sys

import numpy as np

LN2 = math.log(2.0)


def mean_spacing_zeta(t):
    return 2 * math.pi / math.log(t / (2 * math.pi))


def mean_spacing_chi(q, t):
    return 2 * math.pi / math.log(q * t / (2 * math.pi))


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
    # de-modulate the eta prefactor: F_eta = (1 - 2^{1-s}) zeta(s), s = 1/2 + i t
    pref = 1.0 - math.sqrt(2.0) * np.exp(-1j * taus * LN2)
    return taus, F / pref


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


def rs_sweep(t_lo, t_hi, dy):
    K_lo = int(math.sqrt(t_lo / (2 * math.pi)))
    K_hi = int(math.sqrt(t_hi / (2 * math.pi)))
    assert K_lo == K_hi
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
        cd = np.cos(2 * math.pi * p)
        psi = np.where(np.abs(cd) > 0.05,
                       np.cos(2 * math.pi * (p * p - p - 1.0 / 16)) / np.where(np.abs(cd) > 0.05, cd, 1.0), 0.0)
        Z[s:s + 2000] = main + (-1) ** (K + 1) * (tt / (2 * math.pi)) ** (-0.25) * psi
    return ts, Z


def zeros_complex(taus, F):
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


def zeros_real(taus, Z):
    zs = []
    for j in range(1, len(taus)):
        if Z[j - 1] * Z[j] < 0:
            zs.append(float(taus[j - 1] + Z[j - 1] / (Z[j - 1] - Z[j]) * (taus[j] - taus[j - 1])))
    return np.array(zs)


def ambient_curve(taus, absv, block=8.0):
    centers, meds = [], []
    e = taus[0]
    while e < taus[-1]:
        m = (taus >= e) & (taus < e + block)
        if m.sum() > 50:
            centers.append(e + block / 2)
            meds.append(float(np.median(absv[m])))
        e += block
    return np.interp(taus, centers, meds)


def dump(taus, obs_abs, zeros, sp, tag):
    A = ambient_curve(taus, obs_abs)
    dt = taus[1] - taus[0]
    zi = ((zeros - taus[0]) / dt).astype(int)
    g_u, dy_r, bn = [], [], []
    for i in range(len(zeros) - 1):
        a, b = zi[i] + 2, zi[i + 1] - 1
        if b <= a + 3:
            continue
        pk = a + int(np.argmax(obs_abs[a:b]))
        graw = zeros[i + 1] - zeros[i]
        g_u.append(graw / sp)
        dy_r.append(graw)
        bn.append(obs_abs[pk] / A[pk])
    np.savez(f"tmp/amp_{tag}.npz", g=np.array(g_u), dy=np.array(dy_r), b=np.array(bn), sp=sp)
    print(f"  [{tag}] spacing {sp:.3f}, gaps {len(g_u)} -> tmp/amp_{tag}.npz")


if __name__ == "__main__":
    part = sys.argv[1]

    if part == "A":
        taus, F = eta_sweep(1500.0, 2000.0, 0.01, 2000.0)
        dump(taus, np.abs(F), zeros_complex(taus, F), mean_spacing_zeta(1750.0), "S1_zeta1750")
        ts, Z = rs_sweep(999850.0, 1000150.0, 0.005)
        dump(ts, np.abs(Z), zeros_real(ts, Z), mean_spacing_zeta(1e6), "S3_zeta1e6")
        ts, Z = rs_sweep(9999920.0, 10000080.0, 0.004)
        dump(ts, np.abs(Z), zeros_real(ts, Z), mean_spacing_zeta(1e7), "S4_zeta1e7")

    elif part == "B":
        segs = []
        for T0 in (52206.0, 55712.0, 66678.0, 71733.0):
            taus, F = eta_sweep(T0 - 11.0, T0 + 11.0, 0.005, T0 + 11.0)
            segs.append((taus, F))
        g_u, dy_r, bn = [], [], []
        sp = mean_spacing_zeta(60000.0)
        for taus, F in segs:
            A = ambient_curve(taus, np.abs(F), block=4.0)
            zs = zeros_complex(taus, F)
            dt = taus[1] - taus[0]
            zi = ((zs - taus[0]) / dt).astype(int)
            absF = np.abs(F)
            for i in range(len(zs) - 1):
                a, b = zi[i] + 2, zi[i + 1] - 1
                if b <= a + 3:
                    continue
                pk = a + int(np.argmax(absF[a:b]))
                graw = zs[i + 1] - zs[i]
                g_u.append(graw / sp)
                dy_r.append(graw)
                bn.append(absF[pk] / A[pk])
        np.savez("tmp/amp_S2_zeta60k.npz", g=np.array(g_u), dy=np.array(dy_r), b=np.array(bn), sp=sp)
        print(f"  [S2_zeta60k] spacing {sp:.3f}, gaps {len(g_u)} -> tmp/amp_S2_zeta60k.npz")

    elif part == "C":
        v29 = np.zeros(29, dtype=np.complex128)
        for a in range(1, 29):
            v29[a] = 1.0 if pow(a, 14, 29) == 1 else -1.0
        taus, F = chi_sweep(v29, 29, 1750.0, 2000.0, 0.0125, 2000.0)
        dump(taus, np.abs(F), zeros_complex(taus, F), mean_spacing_chi(29, 1875.0), "S5_chi29")
        v5 = np.zeros(5, dtype=np.complex128)
        v5[1], v5[2], v5[4], v5[3] = 1.0, 1j, -1.0, -1j
        taus, F = chi_sweep(v5, 5, 1600.0, 2000.0, 0.01, 2000.0)
        dump(taus, np.abs(F), zeros_complex(taus, F), mean_spacing_chi(5, 1800.0), "S6_chi5c")

    elif part == "D":
        v101 = np.zeros(101, dtype=np.complex128)
        for a in range(1, 101):
            v101[a] = 1.0 if pow(a, 50, 101) == 1 else -1.0
        taus, F = chi_sweep(v101, 101, 1875.0, 2000.0, 0.0125, 2000.0)
        dump(taus, np.abs(F), zeros_complex(taus, F), mean_spacing_chi(101, 1937.0), "S7_chi101")

    elif part == "collate":
        import glob
        BINS = [0.3, 0.5, 0.7, 0.9, 1.1, 1.4, 1.8, 2.3, 3.0]
        samples = []
        for f in sorted(glob.glob("tmp/amp_S*.npz")):
            d = np.load(f)
            samples.append((f.split("amp_")[1][:-4], d["g"], d["dy"], d["b"], float(d["sp"])))
        for units, xi in (("UNFOLDED (spacings)", 1), ("RAW (ordinate dy)", 2)):
            print(f"binned median bump/ambient vs gap in {units}:")
            hdr = "   sample        sp  " + " ".join(f"[{BINS[k]:.1f},{BINS[k+1]:.1f})" for k in range(len(BINS) - 1))
            print(hdr)
            table = {}
            for name, g, dy, b, sp in samples:
                x = g if xi == 1 else dy
                row = []
                for k in range(len(BINS) - 1):
                    m = (x >= BINS[k]) & (x < BINS[k + 1])
                    row.append(float(np.median(b[m])) if m.sum() >= 4 else np.nan)
                table[name] = row
                print(f"   {name:12s} {sp:5.3f} " + " ".join(f"{v:9.3f}" if not np.isnan(v) else "        -" for v in row))
            score, nb = 0.0, 0
            for k in range(len(BINS) - 1):
                col = [np.log(t[k]) for t in table.values() if not np.isnan(t[k]) and t[k] > 0]
                if len(col) >= 4:
                    score += float(np.var(col))
                    nb += 1
            print(f"   COLLAPSE SCORE ({units}): {score:.4f} over {nb} bins  (lower = better collapse)")
            print()
