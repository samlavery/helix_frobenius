#!/usr/bin/env python3
"""att658b — structure of the weighted autocorrelations κ_n(d) = ∫(2v+d)^{2n}Φ(v)Φ(v+d)dv (att658 P3/P4),
with Φ evaluated by evenness, Φ(u) = Φ_series(|u|) (the series converges slowly for u < 0; att658's κ used the
truncated series there and went negative — a bug, not a finding).
P3 κ_n log-concave on [0,6] for n = 0..3 (prediction yes); P4 κ_n not convex near d = 0 (prediction: bell-shaped)."""
import mpmath as mp
mp.mp.dps = 22
out = open("tmp/att658b_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def Phi_series(u):
    u = mp.mpf(u); tot = mp.mpf(0); e2 = mp.exp(2*u)
    for n in range(1, 9):
        tot += (2*mp.pi**2*n**4*mp.exp(mp.mpf(9)/2*u) - 3*mp.pi*n**2*mp.exp(mp.mpf(5)/2*u))*mp.exp(-mp.pi*n**2*e2)
    return tot
def Phi(u): return Phi_series(abs(mp.mpf(u)))
say("evenness check: Φ_series(0.3) = %s ; Φ_series(−0.3) with 60 terms = %s" % (mp.nstr(Phi_series(0.3), 12),
    mp.nstr(sum((2*mp.pi**2*n**4*mp.exp(mp.mpf(9)/2*mp.mpf(-0.3)) - 3*mp.pi*n**2*mp.exp(mp.mpf(5)/2*mp.mpf(-0.3)))*mp.exp(-mp.pi*n**2*mp.exp(mp.mpf(-0.6))) for n in range(1, 61)), 12)))
def kappa(n, d):
    d = mp.mpf(d)
    return mp.quad(lambda v: (2*v + d)**(2*n)*Phi(v)*Phi(v + d), [-4 - d, -d/2 - 1, -d/2, -d/2 + 1, 0, 1, 2, 4])
ds = [mp.mpf(i)/10 for i in range(0, 61)]
for n in range(0, 4):
    ks = [kappa(n, d) for d in ds]
    lk = [mp.log(k) for k in ks]
    dec = all(ks[i+1] <= ks[i] for i in range(len(ks)-1))
    conv2 = [ks[i+1] - 2*ks[i] + ks[i-1] for i in range(1, len(ks)-1)]
    logc2 = [lk[i+1] - 2*lk[i] + lk[i-1] for i in range(1, len(lk)-1)]
    first_convex = next((float(ds[i+1]) for i, c in enumerate(conv2) if c > 0), None)
    say("n=%d  κ_n(0)=%s  decreasing: %s ; log-concave at all grid points: %s (max 2nd diff of log %.2e at d=%.1f) ; convex from d≈%s ; concave near 0: %s"
        % (n, mp.nstr(ks[0], 6), dec, all(c <= 0 for c in logc2), max(logc2), float(ds[1 + logc2.index(max(logc2))]), first_convex, conv2[0] < 0))
    # width: where κ falls to half
    half = next((float(ds[i]) for i in range(len(ks)) if ks[i] < ks[0]/2), None)
    say("      half-width d½ ≈ %s ; ratio κ_n(d)/κ_n(0) at d=1,2,3: %s" % (half, ", ".join(mp.nstr(ks[10*j]/ks[0], 4) for j in (1, 2, 3))))
