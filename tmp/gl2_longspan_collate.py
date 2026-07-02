"""Collate long-span GL(2) segments, run prime-clock spectroscopy and the
quantitative Satake two-clock weight-law test.

For each form:
  1. concatenate the aligned absF segments into one uniform-grid array;
  2. power spectrum of log|F| (clip bottom 1 pct, subtract mean, Hann, rfft);
  3. peak/background ratio at ln(p^k), p in primes<=31, k in 1..3 (n=p^k<=~50),
     plus composite nulls ln18, ln21, ln30;
  4. Satake amplitude prediction A(p,k) = |s_k|/k * p^(-k/2),
     s_0=2, s_1=lambda(p), s_k=lambda(p)*s_{k-1}-s_{k-2}  (good p);
     for E11 bad prime 11: a_11=1 so amplitude = 11^(-k/2)/k;
  5. per-prime theta_p = arccos(lambda(p)/2) and the k=2 conjugate-clock check
     |2 cos(2 theta_p)|/2 = |s_2|/2 scaling.

Usage: python3 gl2_longspan_collate.py <delta|e11>   (writes to the shared results file)
"""
import math
import sys
import numpy as np

FORMS = {
    "delta": ("tmp/gl2long_delta_lambda.npy", 1_500_000, 200.0, 1200.0, 0.02, 5, "Ramanujan Delta (wt 12, level 1)"),
    "e11":   ("tmp/gl2long_e11_lambda.npy",   1_400_000,  80.0,  400.0, 0.01, 4, "Elliptic curve 11.a (wt 2, cond 11)"),
}

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
KMAX = 3
NULLS = [18, 21, 30]  # composites, not prime powers


def prime_powers():
    """List of (label, n, p, k) for n=p^k <= ~50."""
    out = []
    for p in PRIMES:
        for k in range(1, KMAX + 1):
            n = p ** k
            if n <= 50:
                out.append((f"ln{n}", n, p, k))
    return out


def satake_s(lam_p, kmax):
    """s_k = alpha^k+beta^k via s_0=2, s_1=lam, s_k=lam*s_{k-1}-s_{k-2}."""
    s = [2.0, lam_p]
    for k in range(2, kmax + 1):
        s.append(lam_p * s[-1] - s[-2])
    return s


def collate(form):
    lam_file, N, t0, t_end, dy, nseg, title = FORMS[form]
    segs = []
    expect_j = 0
    for k in range(nseg):
        a = np.load(f"tmp/gl2long_{form}_{k}.npy")
        j_lo, j_hi = np.load(f"tmp/gl2long_{form}_{k}_idx.npy")
        assert j_lo == expect_j, f"seg {k} gap: expected j_lo={expect_j}, got {j_lo}"
        assert j_hi - j_lo == len(a), f"seg {k} length mismatch"
        segs.append(a)
        expect_j = j_hi
    absF = np.concatenate(segs)
    taus = t0 + dy * np.arange(len(absF))
    return absF, taus, dy, title, N


def power_spectrum(absF, dy):
    x = np.log(np.maximum(absF, np.percentile(absF, 1.0)))
    x = x - x.mean()
    P = np.abs(np.fft.rfft(x * np.hanning(len(x)))) ** 2
    freq = 2 * math.pi * np.fft.rfftfreq(len(x), d=dy)
    return freq, P


def peak_bg(freq, P, om, res, all_oms):
    """Peak power in a narrow window at omega; background median in an annulus
    excluding all target frequencies."""
    pk_sel = np.abs(freq - om) < max(0.010, 2.0 * res)
    bg_sel = (np.abs(freq - om) > 0.06) & (np.abs(freq - om) < 0.30)
    for om2 in all_oms:
        if abs(om2 - om) > 1e-9:
            bg_sel &= np.abs(freq - om2) > 0.035
    peak = float(P[pk_sel].max())
    bg = float(np.median(P[bg_sel]))
    return peak, bg


def analyze(form, out_lines):
    lam_file, N, t0, t_end, dy, nseg, title = FORMS[form]
    absF, taus, dy, title, N = collate(form)
    lam = np.load(lam_file)
    lam_p = {p: float(lam[p]) for p in PRIMES}

    freq, P = power_spectrum(absF, dy)
    span = taus[-1] - taus[0]
    res = 2 * math.pi / span

    pp = prime_powers()
    all_oms = [math.log(n) for _, n, _, _ in pp] + [math.log(n) for n in NULLS]

    out_lines.append("=" * 78)
    out_lines.append(f"{title}   [form={form}]")
    out_lines.append(f"  span t in [{taus[0]:.0f}, {taus[-1]:.0f}]  ({span:.0f} units), "
                     f"dy={dy}, {len(absF)} samples, bank N={N}")
    out_lines.append(f"  FFT resolution = {res:.4f} rad  (window >= {max(0.010, 2*res):.4f})")
    out_lines.append("")

    # --- composite null floor: their peak/bg ratios estimate the no-line floor ---
    # composites ln18=2*3^2, ln21=3*7, ln30=2*3*5 are NOT prime powers, so they carry
    # no Euler-product line: their peak/bg ratio ~ O(1) is the detection floor.
    null_ratios = []
    for n in NULLS:
        om = math.log(n)
        peak, bg = peak_bg(freq, P, om, res, all_oms)
        null_ratios.append(peak / bg)
    # Some composites (e.g. ln30 for E11) sit within a resolution element of a strong
    # neighbouring prime line and pick up its sidelobe, so they are NOT clean nulls. The
    # robust floor is the MINIMUM composite-null ratio (the cleanest, least-contaminated
    # null). Detection then uses an absolute peak/bg threshold, well above any null.
    null_floor = float(min(null_ratios))
    DET_THRESH = 100.0   # real Euler lines run 1e2-1e6; clean nulls are O(1-30)
    out_lines.append(f"  composite-null ratios (ln18,ln21,ln30): "
                     f"{[round(r,2) for r in null_ratios]}")
    out_lines.append(f"  cleanest null (min) ~ {null_floor:.2f}; "
                     f"detection threshold peak/bg > {DET_THRESH:.0f}")
    out_lines.append("  (nulls near a strong line, e.g. E11 ln30 next to ln31, are sidelobe-"
                     "contaminated and not representative)")
    out_lines.append("")

    # --- peak/bg table + Satake predictions ---
    out_lines.append("  PRIME-CLOCK SPECTROSCOPY  (peak/background ratio)")
    out_lines.append(f"  {'line':>6} {'n':>4} {'p':>3} {'k':>2} {'omega':>7} "
                     f"{'peak/bg':>9} {'detected':>9} {'sqrt(pow)':>11}")
    rows = []
    for label, n, p, k in pp:
        om = math.log(n)
        peak, bg = peak_bg(freq, P, om, res, all_oms)
        ratio = peak / bg
        det = ratio > DET_THRESH
        sqrtpow = math.sqrt(peak)
        rows.append(dict(label=label, n=n, p=p, k=k, om=om, ratio=ratio,
                         det=det, sqrtpow=sqrtpow, peak=peak))
        out_lines.append(f"  {label:>6} {n:>4} {p:>3} {k:>2} {om:>7.3f} "
                         f"{ratio:>9.2f} {('YES' if det else '.'):>9} {sqrtpow:>11.4e}")
    out_lines.append("")

    # --- Satake amplitude table: measured (rel ln2) vs predicted (rel ln2) ---
    # reference = ln2 line
    ln2 = next(r for r in rows if r["n"] == 2)
    ref_meas = ln2["sqrtpow"]
    # predicted FIBER amplitude A(p,k) = |s_k|/k * p^(-k/2), s_1 = analytic lam(p).
    # For the bad prime 11 (curve 11.a, multiplicative reduction, a_11 = +1) the fiber
    # already carries the analytic normalization: lam(11) = a_11/sqrt(11), so s_1 = lam(11)
    # and the SAME formula applies -- no separate unit-strength case. (The naive "unit
    # strength |a_11|=1" over-predicts by sqrt(11); the fiber measures lam(11)*11^-1/2.)
    def amp_pred(p, k):
        s = satake_s(lam_p[p], k)
        return abs(s[k]) / k * p ** (-k / 2)
    ref_pred = amp_pred(2, 1)

    out_lines.append("  SATAKE TWO-CLOCK WEIGHT LAW  "
                     "(amplitude A = |s_k|/k * p^-k/2 ; s_k=alpha^k+beta^k)")
    out_lines.append(f"  {'line':>6} {'lam(p)':>8} {'s_k':>9} "
                     f"{'meas/ln2':>10} {'pred/ln2':>10} {'meas/pred':>11} {'det':>4}")
    for r in rows:
        p, k = r["p"], r["k"]
        s = satake_s(lam_p[p], k)
        sk = s[k]
        lpv = lam_p[p]
        pred = amp_pred(p, k)
        meas_rel = r["sqrtpow"] / ref_meas
        pred_rel = pred / ref_pred
        mp = meas_rel / pred_rel if pred_rel != 0 else float("nan")
        det = "YES" if r["det"] else "."
        out_lines.append(f"  {r['label']:>6} {lpv:>8.4f} {sk:>9.4f} "
                         f"{meas_rel:>10.4f} {pred_rel:>10.4f} {mp:>11.3f} {det:>4}")
    out_lines.append("")

    # --- conjugate-clock (theta_p) check on detected k=1 & k=2 lines ---
    out_lines.append("  CONJUGATE-CLOCK CHECK  theta_p = arccos(lam(p)/2), "
                     "k=2 predicted scaling |s_2|/2 = |2cos(2 theta_p)|/2")
    out_lines.append(f"  {'p':>3} {'lam(p)':>8} {'theta_p':>8} "
                     f"{'|s2|/2 pred':>12} {'k1 det':>7} {'k2 det':>7} "
                     f"{'meas k2/k1':>11} {'pred k2/k1':>11}")
    for p in PRIMES:
        r1 = next((r for r in rows if r["p"] == p and r["k"] == 1), None)
        r2 = next((r for r in rows if r["p"] == p and r["k"] == 2), None)
        if r1 is None:
            continue
        lp = lam_p[p]
        # arccos domain guard (bad prime 11 for e11 has |lam|>2 not applicable)
        arg = lp / 2.0
        theta = math.acos(arg) if abs(arg) <= 1.0 else float("nan")
        s2 = satake_s(lp, 2)[2]
        pred_s2_half = abs(s2) / 2.0
        k1det = "YES" if r1["det"] else "."
        if r2 is not None:
            k2det = "YES" if r2["det"] else "."
            meas_ratio = r2["sqrtpow"] / r1["sqrtpow"]
            # predicted k2/k1 amplitude ratio = A(p,2)/A(p,1)
            pred_ratio = amp_pred(p, 2) / amp_pred(p, 1) if amp_pred(p, 1) != 0 else float("nan")
        else:
            k2det = "-"
            meas_ratio = float("nan")
            pred_ratio = float("nan")
        out_lines.append(f"  {p:>3} {lp:>8.4f} {theta:>8.4f} "
                         f"{pred_s2_half:>12.4f} {k1det:>7} {k2det:>7} "
                         f"{meas_ratio:>11.4f} {pred_ratio:>11.4f}")
    out_lines.append("")
    return rows, null_floor


if __name__ == "__main__":
    form = sys.argv[1]
    out = []
    analyze(form, out)
    print("\n".join(out))
