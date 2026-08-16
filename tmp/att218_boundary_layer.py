"""att218: empirical boundary-layer width of the band-local criterion.
With the 150-zero list as the 'verified band' (H = gamma_150 = 318.85), compute
S(s) = sum (s-rho)^{-1}(sbar-1+rho)^{-1} truncated at H, at sigma = 0.75, and
measure the positivity margin as tau -> H: prediction (prop:bandlocal) — margin
~ order-1 (nearest-zero protection) until the last ~C log H units, degrading as
the protection above tau vanishes at the truncation edge."""
from mpmath import mp, mpf, mpc, log, nstr

mp.dps = 30
Z = [mpf(l.strip()) for l in open("tmp/zeros150_dps45.txt")]
H = Z[-1]
SIG = mpf("0.75")

def S(tau):
    s = mpc(SIG, tau)
    tot = mpf(0)
    for g in Z:
        for sgn in (1, -1):
            rho = mpc(mpf(1) / 2, sgn * g)
            tot += ((s - rho) ** -1 * (s.conjugate() - 1 + rho) ** -1).real
    return tot

print("H = %s,  log H = %s,  sigma = %s" % (nstr(H, 6), nstr(log(H), 4), SIG))
print(" tau      H-tau    S(tau)      nearest-zero dist")
for tau in [250, 280, 300, 310, 314, 316, 317, 318, 318.5, 318.8, 319, 320, 322, 325, 330]:
    t = mpf(tau)
    d = min(abs(t - g) for g in Z)
    print(" %7.1f  %6.2f   %-10s  %.3f" % (tau, float(H - t), nstr(S(t), 4), float(d)),
          flush=True)
