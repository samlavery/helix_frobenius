"""Reverb product law at a Gourdon ultra-close pair: t ~ 1.085e10, gap 2.42e-5
(normalized spacing 8.19e-5 -- four decades tighter than the classic Lehmer pair).

Method (big ordinates handled as STRINGS -> mpmath; never floats):
  COARSE window (+-2 spacings): Riemann-Siegel MAIN SUM in numpy, with base
    phases (t0*ln n mod 2pi) precomputed once in mpmath at dps 40; theta
    linearized (theta'' ~ 1/2t ~ 5e-11 negligible).  Gives ambient scale,
    neighbor zeros, and the isolated baseline rate Rbar.  (No R-S correction:
    ~(t/2pi)^-1/4 ~ 5e-3 absolute, irrelevant at ambient scale.)
  FINE window (the pair +- 3 gaps): mp.siegelz at dps 40 (full corrections,
    arbitrary precision) -- refine both ordinates by bisection (Z real, sign
    changes), measure member slopes |Z'|, the arch position phi, and the
    mid-pair bump.
Tests:  product law  Rhat_member / g  ~ O(1);  arch phi ~ 0.5;
        tent ratio  bump/(Rbar*gap/2)  <<  1.
"""
import math

import mpmath as mp
import numpy as np

mp.mp.dps = 40

T0_STR = "10854395965.14210"      # Gourdon table row (gamma_n), n ~ 3,501,697,795
GAP_STR = "0.00002420"
t0 = mp.mpf(T0_STR)
gap_ref = float(mp.mpf(GAP_STR))

sp = float(2 * mp.pi / mp.log(t0 / (2 * mp.pi)))
print(f"pair height t0 = {T0_STR}   table gap = {gap_ref}   mean spacing = {sp:.4f}")
print(f"table normalized gap delta = {gap_ref/sp:.3e}")

# ---------------- coarse window: numpy R-S main sum with exact base phases
a = mp.sqrt(t0 / (2 * mp.pi))
K = int(a)
print(f"R-S main sum length K = {K}")
two_pi = 2 * mp.pi
ln_n = np.array([float(mp.log(n)) for n in range(1, K + 1)])
base = np.array([float((t0 * mp.log(n)) % two_pi) for n in range(1, K + 1)])
th0 = float(mp.siegeltheta(t0) % two_pi)
thp = float(mp.log(t0 / (2 * mp.pi)) / 2)
inv_sqrt = 1.0 / np.sqrt(np.arange(1, K + 1, dtype=np.float64))


def Zmain(tau):
    ph = th0 + thp * tau - base - tau * ln_n
    return 2.0 * float(np.dot(inv_sqrt, np.cos(ph)))


half = 5.0 * sp
dt = 2e-4
taus = np.arange(-half, half + dt, dt)
Zc = np.array([Zmain(float(t)) for t in taus])
zeros_c, rates_c = [], []
for j in range(1, len(taus)):
    if Zc[j - 1] * Zc[j] < 0:
        frac = Zc[j - 1] / (Zc[j - 1] - Zc[j])
        zeros_c.append(float(taus[j - 1] + frac * dt))
        rates_c.append(abs(Zc[j] - Zc[j - 1]) / dt)
zeros_c = np.array(zeros_c)
rates_c = np.array(rates_c)
ambient = float(np.median(np.abs(Zc)))
iso = np.ones(len(zeros_c), dtype=bool)
if len(zeros_c) > 2:
    dgap = np.diff(zeros_c)
    iso[1:] &= dgap > 0.6 * sp
    iso[:-1] &= dgap > 0.6 * sp
Rbar = float(np.median(rates_c[iso])) if iso.sum() > 2 else float(np.median(rates_c))
print(f"coarse window: {len(zeros_c)} zeros in +-2 spacings, ambient |Z| ~ {ambient:.3f}, "
      f"isolated baseline rate Rbar = {Rbar:.2f}")
print("coarse zero offsets (tau):", ", ".join(f"{z:+.4f}" for z in zeros_c))

# ---------------- fine window: mp.siegelz around the pair
def Zf(tau):
    return mp.siegelz(t0 + mp.mpf(tau))


def bisect(a_, b_, iters=80):
    fa = Zf(a_)
    for _ in range(iters):
        m = (a_ + b_) / 2
        fm = Zf(m)
        if fa * fm <= 0:
            b_ = m
        else:
            a_, fa = m, fm
    return (a_ + b_) / 2


# bracket the two sign changes near tau = 0 .. gap
g = mp.mpf(GAP_STR)
scan = [mp.mpf(-2) * g + mp.mpf(k) * g / 8 for k in range(41)]
vals = [Zf(s) for s in scan]
brackets = [(scan[i - 1], scan[i]) for i in range(1, len(scan)) if vals[i - 1] * vals[i] < 0]
print(f"fine scan: {len(brackets)} sign changes near the pair")
z1 = bisect(*brackets[0])
z2 = bisect(*brackets[1])
gap_meas = float(z2 - z1)
print(f"refined pair: tau = {float(z1):+.8f}, {float(z2):+.8f}   gap = {gap_meas:.4e}"
      f"   (table {gap_ref:.4e})")

h = mp.mpf(gap_meas) / 50
R1 = abs(float((Zf(z1 + h) - Zf(z1 - h)) / (2 * h)))
R2 = abs(float((Zf(z2 + h) - Zf(z2 - h)) / (2 * h)))

npts = 33
arch_t = [z1 + (z2 - z1) * mp.mpf(k) / (npts - 1) for k in range(npts)]
arch = [abs(float(Zf(s))) for s in arch_t]
pk = int(np.argmax(arch))
bump = arch[pk]
phi = pk / (npts - 1)

g_unf = gap_meas / sp
r1n, r2n = R1 / Rbar, R2 / Rbar
print()
print(f"member rates      : R = {R1:.6f}, {R2:.6f}   (baseline Rbar = {Rbar:.2f})")
print(f"suppression Rhat  : {r1n:.3e}, {r2n:.3e}")
print(f"PRODUCT LAW Rhat/g: {r1n/g_unf:.2f}, {r2n/g_unf:.2f}   (O(1) predicted)")
print(f"arch position phi : {phi:.3f}   (0.5 = symmetric arch)")
print(f"mid-pair bump     : {bump:.3e}")
print(f"tent ratio        : {bump/(Rbar*gap_meas/2):.3e}   (fixed-rate tent fails by this factor)")
print(f"quadratic scale   : bump/(ambient*g^2) = {bump/(ambient*g_unf**2):.2f}"
      f"   (product-model O(1) check)")

# ---------------- horizon test: arch skew of MODERATE gaps vs product model,
# with the model truncated at different horizons (raw dy). Reverb (growth clock)
# says the best horizon ~ 1.1 raw ~ 3.7 spacings HERE; GUE says ~1 spacing.
print()
print("HORIZON TEST at t~1e10 (spacing %.3f; raw window 1.1 = %.1f spacings)" % (sp, 1.1/sp))
gidx = ((zeros_c + half) / dt).astype(int)
print(f"   {'gap(sp)':>8} {'phi_meas':>9} {'phi_full':>9} {'phi_1.1raw':>10} {'phi_1sp':>8}")
rows = []
for i in range(len(zeros_c) - 1):
    gsp = (zeros_c[i+1] - zeros_c[i]) / sp
    if not (0.35 < gsp < 0.95):
        continue
    a_, b_ = gidx[i] + 2, gidx[i + 1] - 1
    if b_ <= a_ + 4:
        continue
    seg = np.abs(Zc[a_:b_]); yseg = taus[a_:b_]
    phi_m = (float(yseg[int(np.argmax(seg))]) - zeros_c[i]) / (zeros_c[i+1] - zeros_c[i])
    def phi_model(horizon):
        M = np.ones_like(yseg)
        mid = 0.5 * (zeros_c[i] + zeros_c[i+1])
        for zz in zeros_c:
            if abs(zz - mid) < horizon:
                M *= np.abs(yseg - zz)
        return (float(yseg[int(np.argmax(M))]) - zeros_c[i]) / (zeros_c[i+1] - zeros_c[i])
    rows.append((gsp, phi_m, phi_model(99.0), phi_model(1.1), phi_model(1.0 * sp)))
    print(f"   {gsp:>8.3f} {phi_m:>9.3f} {rows[-1][2]:>9.3f} {rows[-1][3]:>10.3f} {rows[-1][4]:>8.3f}")
if rows:
    import numpy as _np
    arr = _np.array(rows)
    for lbl, col in (("full window", 2), ("1.1 raw (reverb)", 3), ("1 spacing (GUE)", 4)):
        print(f"   mean |phi_meas - phi_model| for {lbl:>17}: {float(_np.mean(_np.abs(arr[:,1]-arr[:,col]))):.4f}")
