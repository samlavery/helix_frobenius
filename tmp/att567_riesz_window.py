#!/usr/bin/env python3
"""
att567 — THE RIESZ WINDOW: the finite-stage marriage measure that is HILBERT at every stage (ledger 568).
Route-around of ledger 567's theorem (a plateau at the front forces a Krein defect): remove the plateau.
Riesz weights w(n) = (1 − log n/L)₊, kernel K_R(w) = (x^w − 1)/(L w²) = expRatio(L,w)/w; on the line
Re K_R(iu) = (1 − cos Lu)/(L u²) ≥ 0 — the FEJÉR kernel, mass 1.  Under RH the density
   D_R(t) = ϑ′(t)/π + END_R(t) − (1/π) Σ_{n≤x} Λ(n)(1 − log n/L) n^{−½} cos(t log n) = (1/π)Σ_γ Fejér_L(γ − t) + O(x^{−1})
is POSITIVE at every x.  An off-line pair at ½ ± δ + iγ₀ contributes Re[K_R(δ+iu) + K_R(−δ+iu)], of amplitude
x^δ/(L(δ²+u²)) with the phase e^{iLu}: negative for some (x, t).  Hence RH ⟺ D_{R,x}(t) ≥ 0 for all x > 1, t.
PRE-REGISTERED on [10, 60], x ∈ {10², 10³, 10⁴}:  P1 min_t D_R(t) ≥ −0.005 (grid/END noise);  P2 negative mass
per window ≤ 0.005 (vs Selberg 0.19–0.20, sharp 0.36–0.45 in att566);  P3 window counts within 0.05 of 1.
"""
import math, time, sys, numpy as np
sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius/tmp")
from att566_krein_constant import ZEROS, prime_powers, theta_prime_over_pi, bank, windows

def run(L, z, thp, dz):
    x = math.exp(L); ns, lams = prime_powers(int(x) + 1); ln = np.log(ns)
    w = np.maximum(1 - ln/L, 0.0)
    wv = 0.5 - 1j*z; END = np.real((x**wv - 1)/(L*wv**2))/math.pi
    D = thp + END - bank(z, ns, lams, w)
    rows = []
    for a, b, g in windows():
        sel = (z >= a) & (z < b)
        rows.append((a, b, g, np.sum(D[sel])*dz, z[sel][np.argmax(D[sel])] - g, np.sum(np.maximum(-D[sel], 0))*dz))
    return D, rows

dz = 0.01; z = np.arange(5.0, 65.0 + dz/2, dz)
t0 = time.time(); thp = theta_prime_over_pi(z); print("theta'/pi: %.0fs" % (time.time() - t0))
for L in (math.log(1e2), math.log(1e3), math.log(1e4)):
    t0 = time.time(); D, rows = run(L, z, thp, dz); sel = (z >= 10) & (z <= 60)
    print("=" * 90)
    print("RIESZ window, x = %.0f (L = %.3f), Fejér main lobe 4π/L = %.2f   [%.0fs]" % (math.exp(L), L, 4*math.pi/L, time.time() - t0))
    print("   min_t D_R on [10,60] = %+.5f at t = %.2f ;  negative mass on [10,60] = %.5f ;  N(60)−N(10) = %.4f (true 13)"
          % (D[sel].min(), z[sel][np.argmin(D[sel])], np.sum(np.maximum(-D[sel], 0))*dz, np.sum(D[sel])*dz))
    print("   window            zero      count    peak−zero   neg.mass")
    for a, b, g, cnt, d, neg in rows:
        print("   [%6.2f,%6.2f]  %8.4f  %+8.4f  %+9.4f  %8.5f" % (a, b, g, cnt, d, neg))
    errs = [abs(r[3]-1) for r in rows]; negs = [r[5] for r in rows]
    print("   mean|count−1| = %.4f  max = %.4f ;  MEAN NEGATIVE MASS = %.5f" % (np.mean(errs), np.max(errs), np.mean(negs)))
