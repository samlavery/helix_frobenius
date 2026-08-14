"""PM5(b) redone.  The first pass used pad=200 at T=500, but the taper reach there is
|phihat(r)| < 1e-3*L only for r > ~224, so the k-sum was still truncated inside the reach
and the noise floor was 2e-3 relative -- too high to exclude a small narrow feature.
Establish pad convergence first, then redo the fine sweeps at an adequate pad.
"""
import numpy as np
from zeta23_bench import phihat, a_const, load_zeros
from zeta23_controls import traces_ext

GAM = load_zeros()
T = 500.0
l = np.log(T / (2 * np.pi))
L, w = l, 0.05 * l / 2
print(f"T={T}  L={L:.5f}  w={w:.5f}")
r = np.arange(1, 3000, 0.5)
env = np.abs(phihat(r, L, w))
reach = r[np.where(env > 1e-6 * L)[0][-1]]
print(f"  taper reach: |phihat(r)| < 1e-6*L only beyond r = {reach:.0f}")

print("\n  PAD CONVERGENCE at c=1/2 and c=1 (zero set covers the whole padded reach):")
for pad in [200., 400., 800., 1600., 2400.]:
    g = GAM[(GAM >= max(0., T - pad - reach)) & (GAM <= 2 * T + pad + reach)]
    row = []
    for c in [0.5, 1.0]:
        _, t1, t2 = traces_ext(g, T, L, w, c, pad=pad)
        row.append(t1**2 / t2)
    print(f"    pad={pad:6.0f}  nzeros={g.size:5d}   C(c=1/2)={row[0]:14.8f}   "
          f"C(c=1)={row[1]:14.8f}   ratio-1={row[0]/row[1]-1:+.2e}")

PAD = 1600.
g = GAM[(GAM >= 0.) & (GAM <= 2 * T + PAD + reach)]
print(f"\n  fine sweeps at pad={PAD:.0f}, {g.size} zeros, step 2e-4:")
print(f"  {'c*':>6} {'C(c*)':>14} {'window range':>13} {'ctr resid':>11} "
      f"{'resid sd':>10} {'ctr/sd':>7}")
for cent, nm in [(1/3, "1/3"), (0.5, "1/2"), (2/3, "2/3"), (5/6, "5/6"),
                 (3/np.pi, "3/pi"), (1.0, "1"), (np.pi/3, "pi/3")]:
    cs = cent + np.arange(-15, 16) * 2e-4
    Cs = np.array([traces_ext(g, T, L, w, c, pad=PAD)[1]**2
                   / traces_ext(g, T, L, w, c, pad=PAD)[2] for c in cs])
    resid = Cs - np.poly1d(np.polyfit(cs, Cs, 1))(cs)
    sd = resid.std(ddof=2)
    print(f"  {nm:>6} {Cs[15]:14.8f} {np.ptp(Cs):13.2e} {resid[15]:+11.2e} "
          f"{sd:10.2e} {resid[15]/sd:7.2f}")
print("  (ctr/sd is how many sigma the exact harmonic value sits off the smooth trend)")
