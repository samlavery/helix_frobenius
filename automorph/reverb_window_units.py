"""Which clock sets the reverb window?

Hypotheses for the crossover:
  A. NEWEST-PHASOR TURN: window = one full 2pi revolution of the AFE-edge phasor
     (n = t/2pi, spin rate ln(t/2pi)) = one mean spacing -> crossover CONSTANT in
     UNFOLDED units across heights, and in raw units it tracks 2pi/log(t/2pi).
  B. GROWTH CLOCK: window = the O(1) ordinate time to grow a phasor to completion
     (~ ln 2 for bank doubling) -> crossover CONSTANT in RAW ordinate units.

Discriminator: fit the crossover per t-band (cached t<=2000 zeros; spacings
2.27 -> 1.09 across bands) in BOTH unit systems.  Whichever system gives a
band-independent crossover wins.
"""
import math

import numpy as np

d = np.load("tmp/reverb_data.npz")
gam, rates, bump, gap_unf = d["gammas"], d["rates"], d["bump"], d["gap_unf"]


def mean_spacing(t):
    return 2 * math.pi / math.log(t / (2 * math.pi))


sp = np.array([mean_spacing(g) for g in gam])
gaps_raw = np.diff(gam)
ok = ~np.isnan(bump)
med_b = np.array([np.median(bump[max(0, i - 50):i + 51]) for i in range(len(bump))])
bn = bump / med_b

bands = [("t in [14, 400)", (gam[:-1] >= 14) & (gam[:-1] < 400)),
         ("t in [400, 1000)", (gam[:-1] >= 400) & (gam[:-1] < 1000)),
         ("t in [1000, 2000)", (gam[:-1] >= 1000) & (gam[:-1] < 2000))]

print(f"{'band':>18} {'<spacing>':>10} {'n_small/n_large':>16} "
      f"{'g* (unfolded)':>14} {'y* (raw dy)':>12} {'y*/spacing':>11}")
for name, sel in bands:
    s = sel & ok & (bn > 0)
    spc = float(np.mean(sp[:-1][sel]))
    # unfolded fit
    small_u = s & (gap_unf < 0.45)
    large_u = s & (gap_unf > 1.1)
    c2u = float(np.median(bn[small_u] / gap_unf[small_u] ** 2)) if small_u.sum() > 3 else np.nan
    c1u = float(np.median(bn[large_u] / gap_unf[large_u])) if large_u.sum() > 3 else np.nan
    gstar = c1u / c2u if c2u and not np.isnan(c2u) else np.nan
    # raw fit (same events, raw gap units; thresholds scaled by band spacing)
    small_r = s & (gaps_raw < 0.45 * spc)
    large_r = s & (gaps_raw > 1.1 * spc)
    c2r = float(np.median(bn[small_r] / gaps_raw[small_r] ** 2)) if small_r.sum() > 3 else np.nan
    c1r = float(np.median(bn[large_r] / gaps_raw[large_r])) if large_r.sum() > 3 else np.nan
    ystar = c1r / c2r if c2r and not np.isnan(c2r) else np.nan
    print(f"{name:>18} {spc:>10.3f} {int(small_u.sum()):>7}/{int(large_u.sum()):<8} "
          f"{gstar:>14.2f} {ystar:>12.2f} {ystar/spc:>11.2f}")

print()
print("A (newest-phasor turn) predicts: g* constant across bands, y* proportional to spacing.")
print("B (growth clock ~ln2=0.69)      predicts: y* constant ~0.7, g* rising as spacing falls.")
print()
print(f"reference: ln 2 = {math.log(2):.3f}; spacings at t = 2000 / 7005 / 70000: "
      f"{mean_spacing(2000):.3f} / {mean_spacing(7005):.3f} / {mean_spacing(70000):.3f}")
