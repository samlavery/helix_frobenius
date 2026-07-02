"""32.a (CM form eta(4t)^2 eta(8t)^2, level 32) long-span spectroscopy.

Collate the aligned segments (t in [50,450], dy=0.01, bank N=5M), re-report the CM
comb at the long span, and FINE-ZOOM the power spectrum on omega in [1.20, 1.60] to
locate the anomalous ln4-window feature to +-0.01.

The Euler product forbids ANY 2-power line: prime 2 is additive, a_{2^k} = 0 exactly
(verified in the bank build). So a feature at ln4 = 1.38629 would be non-Euler; the
short-span run could not distinguish ln4 from e.g. ln(4.2)=1.435 (window +-0.126).
"""
import math
import numpy as np

LAM_FILE = "tmp/gl2long_cm32_lambda.npy"
N = 5_000_000
T0, T_END, DY, NSEG = 50.0, 450.0, 0.01, 4


def collate():
    segs, expect = [], 0
    for k in range(NSEG):
        a = np.load(f"tmp/gl2long_cm32_{k}.npy")
        j_lo, j_hi = np.load(f"tmp/gl2long_cm32_{k}_idx.npy")
        assert j_lo == expect, (k, j_lo, expect)
        assert j_hi - j_lo == len(a)
        segs.append(a); expect = j_hi
    absF = np.concatenate(segs)
    taus = T0 + DY * np.arange(len(absF))
    return absF, taus


def power_spectrum(absF, dy):
    x = np.log(np.maximum(absF, np.percentile(absF, 1.0)))
    x = x - x.mean()
    P = np.abs(np.fft.rfft(x * np.hanning(len(x)))) ** 2
    freq = 2 * math.pi * np.fft.rfftfreq(len(x), d=dy)
    return freq, P


def parabolic_peak(freq, P, i):
    """Sub-bin parabolic interpolation of a peak at bin index i. Returns (omega, height)."""
    if i <= 0 or i >= len(P) - 1:
        return freq[i], P[i]
    y0, y1, y2 = P[i - 1], P[i], P[i + 1]
    denom = (y0 - 2 * y1 + y2)
    delta = 0.5 * (y0 - y2) / denom if denom != 0 else 0.0
    df = freq[1] - freq[0]
    om = freq[i] + delta * df
    h = y1 - 0.25 * (y0 - y2) * delta
    return om, h


def run(out_lines):
    absF, taus = collate()
    span = taus[-1] - taus[0]
    res = 2 * math.pi / span
    freq, P = power_spectrum(absF, DY)

    out_lines.append("=" * 78)
    out_lines.append("CM form 32.a  (eta(4t)^2 eta(8t)^2, level 32, curve y^2=x^3-x)   [form=cm32]")
    out_lines.append(f"  span t in [{taus[0]:.0f}, {taus[-1]:.0f}]  ({span:.0f} units), "
                     f"dy={DY}, {len(absF)} samples, bank N={N}")
    out_lines.append(f"  FFT resolution = {res:.4f} rad   (bank verified: a_(2^k)=0 exactly, "
                     "so NO 2-power line is possible from the Euler product)")
    out_lines.append("")

    # --- comb re-report at long span ---
    comb = [("ln2", 2, "dead (bad prime 2)"), ("ln3", 3, "DEAD k=1 (a3=0)"),
            ("ln4", 4, "FORBIDDEN (a4=0)"), ("ln5", 5, "ALIVE (5=1 mod 4)"),
            ("ln7", 7, "DEAD k=1 (a7=0)"), ("ln8", 8, "FORBIDDEN (a8=0)"),
            ("ln9", 9, "ALIVE k=2 (from silent p=3!)"), ("ln11", 11, "DEAD k=1 (a11=0)"),
            ("ln13", 13, "ALIVE (13=1 mod 4)"), ("ln25", 25, "ALIVE k=2 of p=5"),
            ("ln49", 49, "ALIVE k=2 of p=7"), ("ln18*", 18, "null (composite)"),
            ("ln21*", 21, "null (composite)")]
    all_oms = [math.log(n) for _, n, _ in comb]
    out_lines.append("  CM COMB (peak/background ratio at long span)")
    out_lines.append(f"  {'line':>6} {'omega':>7} {'peak/bg':>10}   prediction")
    for name, nn, pred in comb:
        om = math.log(nn)
        pk = np.abs(freq - om) < max(0.010, 2.0 * res)
        bg = (np.abs(freq - om) > 0.08) & (np.abs(freq - om) < 0.30)
        for om2 in all_oms:
            if abs(om2 - om) > 1e-9:
                bg &= np.abs(freq - om2) > 0.04
        ratio = float(P[pk].max() / np.median(P[bg]))
        out_lines.append(f"  {name:>6} {om:>7.3f} {ratio:>10.1f}   {pred}")
    out_lines.append("")

    # --- FINE ZOOM on the ln4 window: omega in [1.20, 1.60] ---
    lo, hi = 1.20, 1.60
    sel = (freq >= lo) & (freq <= hi)
    fz, Pz = freq[sel], P[sel]
    idx0 = np.where(sel)[0][0]
    # find local maxima in the zoom, sorted by height
    peaks = []
    for j in range(1, len(Pz) - 1):
        if Pz[j] > Pz[j - 1] and Pz[j] >= Pz[j + 1]:
            om, h = parabolic_peak(freq, P, idx0 + j)
            peaks.append((h, om, fz[j]))
    peaks.sort(reverse=True)
    # local background in the zoom band (median away from the top peaks)
    top_oms = [p[1] for p in peaks[:6]]
    bg_mask = np.ones(len(fz), dtype=bool)
    for om in top_oms:
        bg_mask &= np.abs(fz - om) > 0.05
    bg_med = float(np.median(Pz[bg_mask])) if bg_mask.sum() > 3 else float(np.median(Pz))

    out_lines.append(f"  FINE ZOOM omega in [{lo}, {hi}]  (resolution {res:.4f}, "
                     f"reference marks: ln4={math.log(4):.5f}, ln(4.2)={math.log(4.2):.5f}, "
                     f"2*ln2={2*math.log(2):.5f})")
    out_lines.append(f"  local zoom background median power = {bg_med:.3e}")
    out_lines.append(f"  {'rank':>4} {'omega_peak':>11} {'height':>12} {'h/bg':>10} "
                     f"{'dist to ln4':>12} {'implied n=e^om':>14}")
    for r, (h, om, fbin) in enumerate(peaks[:8], 1):
        out_lines.append(f"  {r:>4} {om:>11.5f} {h:>12.4e} {h/bg_med:>10.1f} "
                         f"{om - math.log(4):>+12.5f} {math.exp(om):>14.5f}")
    out_lines.append("")

    # verdict inputs: the dominant peak, and whether a second comparable peak exists
    if peaks:
        h1, om1, _ = peaks[0]
        d_ln4 = abs(om1 - math.log(4))
        d_ln42 = abs(om1 - math.log(4.2))
        out_lines.append(f"  DOMINANT peak: omega = {om1:.5f} (h/bg = {h1/bg_med:.0f})")
        out_lines.append(f"    |omega - ln4|   = {d_ln4:.5f}  ({d_ln4/res:.2f} resolution elements)")
        out_lines.append(f"    |omega - ln4.2| = {d_ln42:.5f}")
        if len(peaks) > 1:
            h2, om2, _ = peaks[1]
            out_lines.append(f"  2nd peak: omega = {om2:.5f}, h/bg = {h2/bg_med:.0f}, "
                             f"height ratio 2nd/1st = {h2/h1:.3f}")
        # A real line must rise ABOVE the local background; if the top peak is below
        # background it is noise ripple, not a spectral line.
        if h1 / bg_med < 3.0:
            structure = "NO LINE (top 'peak' is below background -> empty band, pure noise)"
        elif len(peaks) > 1 and peaks[1][0] / h1 > 0.25:
            structure = "MULTIPLET/STRUCTURE"
        else:
            structure = "SINGLE dominant line"
        out_lines.append(f"  structure: {structure}")
    out_lines.append("")
    return peaks, bg_med, res


if __name__ == "__main__":
    out = []
    run(out)
    print("\n".join(out))
