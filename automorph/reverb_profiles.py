"""Reverb profile geometry at pairs and triples.

Sam's picture: after the first crossing the reverb energy rises then dissipates;
the next crossing should appear ~halfway down the slope; at a triple the middle
crossing's reverb creates a NEW HIGHER PEAK, with the third crossing again around
the halfway point of that dissipation.

Parameter-free test: the local product model (Lean `cluster_product_law`) says
|F(y)| ~ |C| * prod_zeros |y - gamma_i| near a cluster, so peak HEIGHT RATIOS and
peak POSITIONS in each inter-crossing gap are predicted from the zero positions
alone (C cancels in ratios; positions need no scale at all).

Per cluster we report, for each internal gap:
    g        unfolded gap
    P_meas   measured peak height of |F| in the gap
    P_model  product-model peak, scaled once (to the first gap's peak)
    phi      measured peak position fraction (gamma_left -> peak)/(gap)
             phi = 0.5 : peak at midpoint -> dissipation occupies exactly half
             the interval ("crossing appears one half-slope down")
    phi_mod  product-model prediction for phi (skews at triples)

Clusters: the 4 tightest triples below t=2000 (from cached reverb_data.npz),
the classic Lehmer pair (t~7005), and Sam's tightest pair (t~55713).
All profiles fiber-only (tapered bank, recurrence sweep); zeros re-extracted
from each fine window itself.
"""
import math

import numpy as np


def mean_spacing(t):
    return 2 * math.pi / math.log(t / (2 * math.pi))


def profile(t_lo, t_hi, npts, t_ref):
    N = int(60 * t_ref / (2 * math.pi))
    n = np.arange(1, N + 1, dtype=np.float64)
    sgn = np.where(n % 2 == 1, 1.0, -1.0)
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    amp = sgn * w * n ** (-0.5)
    ln = np.log(n)
    dy = (t_hi - t_lo) / (npts - 1)
    z = amp * np.exp(-1j * t_lo * ln)
    step = np.exp(-1j * dy * ln)
    F = np.empty(npts, dtype=np.complex128)
    for j in range(npts):
        F[j] = z.sum()
        z *= step
    return t_lo + dy * np.arange(npts), F


def analyze(label, t_center, t_half, npts=2400):
    sp = mean_spacing(t_center)
    ys, F = profile(t_center - t_half, t_center + t_half, npts, t_center)
    absF = np.abs(F)
    dy = ys[1] - ys[0]
    med = float(np.median(absF))
    zs, rs = [], []
    for j in range(1, npts - 1):
        if absF[j] < absF[j - 1] and absF[j] < absF[j + 1] and absF[j] < 0.3 * med:
            Fp = (F[j + 1] - F[j - 1]) / (2 * dy)
            if abs(Fp) > 1e-12:
                zs.append(float(ys[j] - (F[j] / Fp).real))
                rs.append(abs(Fp))
    zs = np.array(zs)
    print(f"[{label}]  ambient |F| ~ {med:.2f}   zeros in window: "
          + "/".join(f"{g:.4f}" for g in zs))

    zi = ((zs - ys[0]) / dy).astype(int)
    print(f"    {'gap':>10} {'g (unf)':>8} {'P_meas':>8} {'P_model':>8} {'phi':>6} {'phi_mod':>8}")
    scale = None
    for i in range(len(zs) - 1):
        a, b = zi[i] + 2, zi[i + 1] - 1
        if b <= a:
            continue
        seg = absF[a:b]
        pk = int(np.argmax(seg))
        P = float(seg[pk])
        ypk = float(ys[a + pk])
        phi = (ypk - zs[i]) / (zs[i + 1] - zs[i])
        # product model on the same grid segment, using ALL window zeros
        yseg = ys[a:b]
        Mseg = np.ones_like(yseg)
        for g in zs:
            Mseg *= np.abs(yseg - g)
        mk = int(np.argmax(Mseg))
        phi_m = (float(yseg[mk]) - zs[i]) / (zs[i + 1] - zs[i])
        if scale is None:
            scale = P / float(Mseg[mk])
        Pm = scale * float(Mseg[mk])
        gunf = (zs[i + 1] - zs[i]) / sp
        print(f"    {zs[i+1]-zs[i]:>10.4f} {gunf:>8.3f} {P:>8.4f} {Pm:>8.4f} {phi:>6.3f} {phi_m:>8.3f}")
    print()


if __name__ == "__main__":
    d = np.load("tmp/reverb_data.npz")
    gam = d["gammas"]
    sp_all = np.array([mean_spacing(g) for g in gam])
    spans = [((gam[k + 1] - gam[k - 1]) / sp_all[k], k) for k in range(1, len(gam) - 1)]
    spans.sort()
    print("Tightest triples below t=2000 (span in mean spacings):",
          ", ".join(f"{s:.3f}@{gam[k]:.1f}" for s, k in spans[:4]))
    print()
    for s, k in spans[:4]:
        c = float(gam[k])
        analyze(f"triple span {s:.3f} at t~{c:.1f}", c, 2.2 * mean_spacing(c))
    analyze("Lehmer pair t~7005.08", 7005.0817, 2.2 * mean_spacing(7005.0))
    analyze("Sam pair t~55713.42", 55713.4234, 2.0 * mean_spacing(55713.0), npts=1600)
