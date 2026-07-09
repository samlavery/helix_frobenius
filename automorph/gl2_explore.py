"""GL(2) exploration: ambient spectroscopy reads the Hecke eigenvalues, and the
universal reverb curve extends to degree 2.

Predictions (computed below from the coefficients themselves):
  - ambient power at ln(p^k) has weight |c_{p^k}|^2 / 1, c_{p^k} = (alpha^k+beta^k)/(k p^{k/2})
    (Newton recursion s_k = lam*s_{k-1} - s_{k-2} for good p; c = a_p^k/k p^{k/2} at bad p)
  - Delta: ln4 peak EXCEEDS ln2 (|lam(2)^2-2| > |lam(2)|) -- impossible in GL(1)
  - E11: ln11 present at unit strength (|a_11| = 1) -- neither zeta-like nor a hole
  - bump/ambient vs locally-unfolded gap should land on the SAME universal curve

Run: python3 gl2_explore.py delta|e11
"""
import math
import sys

import numpy as np

sys.path.insert(0, ".")
from focal_closure import delta_lambda, e11_lambda  # noqa: E402

TARGETS = [("ln2", 2), ("ln3", 3), ("ln4", 4), ("ln5", 5), ("ln7", 7), ("ln8", 8),
           ("ln9", 9), ("ln11", 11), ("ln13", 13), ("ln18*", 18), ("ln21*", 21)]


def predicted_weights(lam, bad=None):
    """|c_n|^2 for n = p^k targets, from the coefficients (Newton's identities)."""
    out = {}
    for name, n in TARGETS:
        p = None
        for q in (2, 3, 5, 7, 11, 13):
            k = 0
            m = n
            while m % q == 0:
                m //= q
                k += 1
            if m == 1 and k >= 1:
                p, kk = q, k
                break
        if p is None:
            out[name] = 0.0
            continue
        if bad and p == bad[0]:
            c = (bad[1] ** kk) / kk / p ** (kk / 2)
        else:
            lp = lam[p]
            s = {0: 2.0, 1: lp}
            for j in range(2, kk + 1):
                s[j] = lp * s[j - 1] - s[j - 2]
            c = s[kk] / kk / 1.0
            c = c / p ** (0)  # amplitude normalization folded below
            c = s[kk] / kk * p ** (-kk / 2) * p ** (kk / 2)  # keep s_k/k; p-power via lam normalization
            c = s[kk] / kk
        # in analytic normalization lam(p) = a_p/p^{(w-1)/2}, the log-series coefficient at
        # n = p^k is (alpha^k + beta^k)/k with |alpha|=|beta|=1, times n^{-1/2} in the fiber;
        # relative peak weight ~ |s_k/k|^2 / n
        out[name] = (c / 1.0) ** 2 / n if not (bad and p == bad[0]) else ((bad[1] ** kk) / kk) ** 2 / n
    return out


def sweep(lam, t_lo, t_hi, dy, N):
    lamv = lam[1:N + 1].astype(np.float64)
    n = np.arange(1, N + 1, dtype=np.float64)
    u = n / N
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    amp = lamv * w * n ** (-0.5)
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


def analyze(taus, F, label, weights):
    absF = np.abs(F)
    dt = taus[1] - taus[0]
    # spectroscopy
    x = np.log(np.maximum(absF, np.percentile(absF, 1.0)))
    x -= x.mean()
    P = np.abs(np.fft.rfft(x * np.hanning(len(x)))) ** 2
    freq = 2 * math.pi * np.fft.rfftfreq(len(x), d=dt)
    res = 2 * math.pi / (taus[-1] - taus[0])
    print(f"[{label}] span {taus[-1]-taus[0]:.0f}, resolution {res:.3f}")
    print(f"   {'target':>6} {'peak/bg':>12} {'predicted rel. weight (ln2=1)':>30}")
    ratios = {}
    for name, nn in TARGETS:
        om = math.log(nn)
        pk = np.abs(freq - om) < max(0.012, 2.0 * res)
        bg = (np.abs(freq - om) > 0.08) & (np.abs(freq - om) < 0.25)
        for name2, n2 in TARGETS:
            if n2 != nn:
                bg &= np.abs(freq - math.log(n2)) > 0.04
        ratios[name] = float(P[pk].max() / np.median(P[bg]))
    w2 = weights.get("ln2", 1.0) or 1.0
    for name, nn in TARGETS:
        pred = weights.get(name, 0.0) / w2
        print(f"   {name:>6} {ratios[name]:>12.1f} {pred:>30.3f}")
    # universal reverb curve, locally unfolded
    med = float(np.median(absF))
    zs, dts = [], taus[1] - taus[0]
    for j in range(1, len(taus) - 1):
        if absF[j] < absF[j - 1] and absF[j] < absF[j + 1] and absF[j] < 0.3 * med:
            Fp = (F[j + 1] - F[j - 1]) / (2 * dt)
            if abs(Fp) > 1e-12:
                zs.append(float(taus[j] - (F[j] / Fp).real))
    zs = np.array(zs)
    print(f"   zeros: {len(zs)}")
    gaps = np.diff(zs)
    loc = np.array([np.mean(gaps[max(0, i - 20):i + 21]) for i in range(len(gaps))])
    # ambient curve
    centers, meds = [], []
    e = taus[0]
    while e < taus[-1]:
        m = (taus >= e) & (taus < e + 8.0)
        if m.sum() > 50:
            centers.append(e + 4.0)
            meds.append(float(np.median(absF[m])))
        e += 8.0
    A = np.interp(taus, centers, meds)
    zi = ((zs - taus[0]) / dt).astype(int)
    g_u, bn = [], []
    for i in range(len(zs) - 1):
        a, b = zi[i] + 2, zi[i + 1] - 1
        if b <= a + 3:
            continue
        pk = a + int(np.argmax(absF[a:b]))
        g_u.append(gaps[i] / loc[i])
        bn.append(absF[pk] / A[pk])
    g_u, bn = np.array(g_u), np.array(bn)
    BINS = [0.3, 0.5, 0.7, 0.9, 1.1, 1.4, 1.8, 2.3]
    ref = [0.22, 0.45, 0.95, 1.35, 2.3, 4.3, 9.0]
    print(f"   universal curve check (GL(1) reference in parens):")
    row = []
    for k in range(len(BINS) - 1):
        m = (g_u >= BINS[k]) & (g_u < BINS[k + 1])
        v = float(np.median(bn[m])) if m.sum() >= 4 else float("nan")
        row.append(f"{v:.2f}({ref[k]})")
    print("   " + "  ".join(row))


if __name__ == "__main__":
    which = sys.argv[1]
    if which == "delta":
        N = 260000
        lam = delta_lambda(N)
        lam_p = {p: float(lam[p]) for p in (2, 3, 5, 7, 11, 13)}
        wts = predicted_weights(lam_p)
        taus, F = sweep(lam, 200.0, 500.0, 0.01, N)
        analyze(taus, F, "Ramanujan Delta, t in [200, 500]", wts)
    elif which == "e11":
        N = 530000
        lam = e11_lambda(N)
        lam_p = {p: float(lam[p]) for p in (2, 3, 5, 7, 13)}
        lam_p[11] = 0.0
        wts = predicted_weights(lam_p, bad=(11, 1.0))
        taus, F = sweep(lam, 80.0, 250.0, 0.01, N)
        analyze(taus, F, "elliptic curve 11.a, t in [80, 250]", wts)
