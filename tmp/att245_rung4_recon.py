#!/usr/bin/env python3
"""
att245 — RUNG-4 RECON (log 3, log 4): the two-clock symbol
  sigma2(r) = d(r) - sqrt2*log2*cos(r log2) - (2 log3/sqrt3)*cos(r log3)
(valid for supports in [log3, log4): prime powers 2 and 3 only).

Measurement pass (scipy digamma is fine here — this is recon, not certificate):
 1. negative-set census on (0, 400) + alignment diagnostics per dip
    (2-clock index j ~ r/(2pi/log2), 3-clock phase offset; the log3/log2
    continued-fraction convergent 19/12 predicts a deep near-alignment ~108.8)
 2. floor table: inf sigma2 on [R2, 400] vs the crude Lemma-C bound d(R2)-2.2489
 3. true margins past log3 (att240 machinery, primes auto-included)
 4. feasibility: P1 (beta ~ a h^4 I4/16) vs cubic-spline (beta ~ 2a (h^4/384)^2 I8)
    against alpha_chol = 1.3 n^2 u  — where does each architecture close?
"""
import numpy as np, math
from scipy.special import digamma
import att239_weil_support_bench as B
import att240_margin_law as C

LOG2, LOG3, LOG4 = math.log(2.0), math.log(3.0), math.log(4.0)
C2 = math.sqrt(2.0) * LOG2                 # 0.980258
C3 = 2.0 * LOG3 / math.sqrt(3.0)           # 1.268558
CSUM = C2 + C3                             # 2.248817
U = 1.1102230246251565e-16
RES2 = 2 * math.pi / LOG2                  # 9.0647
RES3 = 2 * math.pi / LOG3                  # 5.7192

def dfun(r):
    return np.real(digamma(0.25 + 0.5j * np.asarray(r, dtype=float))) - math.log(math.pi)

def sig2(r):
    r = np.asarray(r, dtype=float)
    return dfun(r) - C2 * np.cos(r * LOG2) - C3 * np.cos(r * LOG3)

def census(rmax=400.0, step=2e-4):
    print("== SIGMA2 NEGATIVE-SET CENSUS (0, %.0f) ==" % rmax, flush=True)
    r = np.arange(step, rmax, step)
    s = sig2(r)
    sgn = np.diff(np.sign(s))
    idx = np.where(sgn != 0)[0]
    pts = [0.0] + [r[i] for i in idx] + [rmax]
    print(f"  sigma2(0) = {float(sig2(0.0)):+.4f}   sign changes: {len(idx)}")
    segs = []
    for j in range(len(pts) - 1):
        mid = 0.5 * (pts[j] + pts[j + 1])
        if sig2(mid) < 0:
            lo, hi = pts[j], pts[j + 1]
            m = (r >= lo) & (r <= hi)
            area = float(np.sum(np.abs(s[m])) * step)
            i0 = np.argmin(s[m])
            rmin, smin = r[m][i0], s[m][i0]
            segs.append((lo, hi, area, rmin, smin))
    for lo, hi, area, rmin, smin in segs:
        j2 = rmin / RES2; j3 = rmin / RES3
        ph2 = abs(j2 - round(j2)); ph3 = abs(j3 - round(j3))
        print(f"  NEG ({lo:8.4f},{hi:8.4f}) w {hi-lo:6.3f} mass {area:7.4f} "
              f"min {smin:+7.4f} @ {rmin:8.4f}  [2-clk j={j2:6.2f} off {ph2:.3f}; "
              f"3-clk k={j3:6.2f} off {ph3:.3f}]")
    last_neg = segs[-1][1] if segs else 0.0
    print(f"  LAST negative point below {rmax}: r = {last_neg:.4f}")
    # the 19/12 convergent site
    r1912 = 12 * RES2
    print(f"  19/12 convergent site r = {r1912:.4f}: sigma2 = {float(sig2(r1912)):+.4f} "
          f"(d = {float(dfun(r1912)):+.4f}, crude floor d-{CSUM:.4f} = "
          f"{float(dfun(r1912))-CSUM:+.4f})")
    return r, s, last_neg

def floor_table(r, s, last_neg):
    print("== FLOOR TABLE: inf sigma2 on [R2, 400] vs crude d(R2) - 2.2488 ==")
    for R2 in [50, 55, 60, 65, 80, 100, 120, 150]:
        m = r >= R2
        i0 = np.argmin(s[m])
        print(f"  R2 = {R2:5.1f}: grid inf = {s[m][i0]:+.4f} at r = {r[m][i0]:8.3f}"
              f"   crude bound = {float(dfun(R2)) - CSUM:+.4f}"
              f"   {'(R2 below last negative!)' if R2 < last_neg else ''}")

def margins():
    print("== TRUE MARGINS past log3 (att240 machinery, primes-in, even sector) ==")
    out = {}
    for L in [1.11, 1.13, 1.15, 1.17, 1.20, 1.24, 1.28]:
        lam, _ = C.lam_min_sector(L, "even", K=40, Nq=1400)
        out[L] = lam
        pp = [n for n, _ in B.prime_powers(L)]
        print(f"  L = {L:.3f} (e^L = {math.exp(L):.4f}, primes {pp}): lam = {lam:+.4e}")
    return out

def feasibility(margins_d, r, s):
    print("== FEASIBILITY MAP: P1 vs CUBIC complement, R2* = 65 band ==")
    R2s = 65.0
    m = (r <= R2s)
    I4 = float(np.sum(np.abs(s[m] - 0.05) * r[m] ** 4) * (r[1] - r[0])) / math.pi
    I8 = float(np.sum(np.abs(s[m] - 0.05) * r[m] ** 8) * (r[1] - r[0])) / math.pi
    mm = r >= R2s
    s0 = float(np.min(s[mm]))
    maxW = float(np.max(np.abs(s[m] - s0)))
    print(f"  band [0,{R2s:.0f}]: I4 ~ {I4:.3e}, I8 ~ {I8:.3e}; s0(grid inf beyond) = {s0:+.4f}; maxW = {maxW:.2f}")
    print(f"  {'L':>6} {'margin':>10} {'mu~0.7m':>10} | {'P1: h':>9} {'n':>8} {'alpha':>9} {'ok?':>4}"
          f" | {'P3: h':>9} {'n':>7} {'alpha':>9} {'ok?':>4}")
    for L, lam in margins_d.items():
        a = L / 2.0
        mu = 0.7 * lam
        bt = 0.3 * mu * s0 / maxW if s0 > 0 else float('nan')
        # P1: beta = (a h^4/16) I4  (x2 for two quadratures folded into I4 pad)
        h1 = (bt * 16.0 / (2 * a * I4)) ** 0.25 if bt > 0 else float('nan')
        n1 = int(2 * a / h1) if h1 == h1 else 0
        a1 = 1.3 * n1 * n1 * U
        ok1 = "YES" if (n1 and a1 < 0.3 * mu) else "no"
        # cubic spline: |Ghat_perp| <= ||G|| sqrt(2a) (5/384) h^4 r^4 -> beta = 2a (5h^4/384)^2 I8
        h3 = (bt / (2 * a * (5.0 / 384.0) ** 2 * I8)) ** 0.125 if bt > 0 else float('nan')
        n3 = int(2 * a / h3) if h3 == h3 else 0
        a3 = 1.3 * n3 * n3 * U
        ok3 = "YES" if (n3 and a3 < 0.3 * mu) else "no"
        print(f"  {L:6.2f} {lam:10.2e} {mu:10.2e} | {h1:9.2e} {n1:8d} {a1:9.2e} {ok1:>4}"
              f" | {h3:9.2e} {n3:7d} {a3:9.2e} {ok3:>4}")

def main():
    r, s, last_neg = census()
    floor_table(r, s, last_neg)
    md = margins()
    feasibility(md, r, s)

if __name__ == "__main__":
    main()
