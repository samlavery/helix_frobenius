"""Reverb check at Sam's candidate close pairs: 66678 / 71733.

Both readings tested: as ordinate heights (t ~ 66678, 71733) and as zero indices
(index 66678 -> t ~ 52206, index 71733 -> t ~ 55712 via Riemann-von Mangoldt).

Per window (fiber-only, recurrence sweep, no L):
  - extract all vanishings + reopening rates; count vs Riemann-von Mangoldt;
  - report the three tightest pairs: unfolded gap g, member rates Rhat
    (baseline = median rate of isolated zeros in the window), mid-pair bump;
  - reverb tests: PRODUCT LAW  Rhat(member) / g  ~ O(1)   (rate = distance to partner)
                  TENT FAILURE bump / (Rbar * gap/2)  << 1  inside the reverb window.
"""
import math

import numpy as np


def mean_spacing(t):
    return 2 * math.pi / math.log(t / (2 * math.pi))


def analyze_window(T0, half=12.0, dy=0.0025, mult=40):
    N = int(mult * T0 / (2 * math.pi))
    n = np.arange(1, N + 1, dtype=np.float64)
    sgn = np.where(n % 2 == 1, 1.0, -1.0)
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    amp = sgn * w * n ** (-0.5)
    ln = np.log(n)

    y0 = T0 - half
    ny = int(2 * half / dy) + 1
    ys = y0 + dy * np.arange(ny)
    z = amp * np.exp(-1j * y0 * ln)
    step = np.exp(-1j * dy * ln)
    F = np.empty(ny, dtype=np.complex128)
    for j in range(ny):
        F[j] = z.sum()
        z *= step
    absF = np.abs(F)

    # convergence at window center with a 1.5x bank
    N2 = int(1.5 * N)
    m = np.arange(1, N2 + 1, dtype=np.float64)
    s2 = np.where(m % 2 == 1, 1.0, -1.0)
    v = m / N2
    w2 = np.where(v < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - v * v, 1e-300, None)), 0.0)
    Fc = complex(np.sum(s2 * w2 * m ** (-0.5) * np.exp(-1j * T0 * np.log(m))))
    jc = int((T0 - y0) / dy)
    conv = abs(F[jc] - Fc)

    med = float(np.median(absF))
    gammas, rates = [], []
    for j in range(1, ny - 1):
        if absF[j] < absF[j - 1] and absF[j] < absF[j + 1] and absF[j] < 0.3 * med:
            Fp = (F[j + 1] - F[j - 1]) / (2 * dy)
            if abs(Fp) < 1e-12:
                continue
            gammas.append(float(ys[j] - (F[j] / Fp).real))
            rates.append(abs(Fp))
    gammas = np.array(gammas)
    rates = np.array(rates)

    def NvM(T):
        return T / (2 * math.pi) * math.log(T / (2 * math.pi)) - T / (2 * math.pi) + 7.0 / 8.0

    expected = NvM(T0 + half) - NvM(T0 - half)
    sp = mean_spacing(T0)
    gaps = np.diff(gammas)
    g_unf = gaps / sp

    iso = np.ones(len(gammas), dtype=bool)
    iso[1:] &= g_unf > 0.6
    iso[:-1] &= g_unf > 0.6
    Rbar = float(np.median(rates[iso])) if iso.sum() > 4 else float(np.median(rates))

    print(f"  window t in [{T0-half:.0f}, {T0+half:.0f}]  bank N={N}  taper floor={conv:.1e}  ambient |F|~{med:.2f}")
    print(f"  vanishings: {len(gammas)}  (Riemann-von Mangoldt expects {expected:.1f})"
          f"   mean spacing {sp:.4f}   isolated baseline rate Rbar={Rbar:.2f}")
    order = np.argsort(g_unf)
    print(f"  {'pair at gamma':>26} {'gap':>9} {'g (unf)':>8} {'Rhat_1':>7} {'Rhat_2':>7} "
          f"{'Rhat/g':>7} {'bump':>9} {'tent ratio':>10}")
    for i in order[:3]:
        a, b = gammas[i], gammas[i + 1]
        ja, jb = int((a - y0) / dy) + 2, int((b - y0) / dy) - 1
        bump = float(absF[ja:jb].max()) if jb > ja else float("nan")
        r1, r2 = rates[i] / Rbar, rates[i + 1] / Rbar
        g = g_unf[i]
        tent = bump / (Rbar * gaps[i] / 2)
        print(f"  {a:>12.4f}/{b:<12.4f} {gaps[i]:>9.4f} {g:>8.4f} {r1:>7.3f} {r2:>7.3f} "
              f"{0.5*(r1+r2)/g:>7.2f} {bump:>9.4f} {tent:>10.3f}")
    return gammas, rates


if __name__ == "__main__":
    for label, T0 in (("HEIGHT reading 66678", 66678.0), ("HEIGHT reading 71733", 71733.0),
                      ("INDEX reading 66678 -> t~52206", 52206.0),
                      ("INDEX reading 71733 -> t~55712", 55712.0)):
        print(f"[{label}]")
        analyze_window(T0)
        print()
