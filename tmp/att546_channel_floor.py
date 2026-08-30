# Seat door, high left channel: Re[xi'/xi(sigma+it)] for sigma < 1/2, t > 634.5.
# DC prediction from the chi clock: Re[xi'/xi] ~ -(1/2)log(t/2pi) + Re-part of mirror AC.
# Pre-registered: floor <= 0 at every grid point supports the seat door; any
# positive value in the channel is a falsification hit (publish it).
from mpmath import mp, mpc, zeta, digamma, log, pi, re
mp.dps = 30
def xilog(s):
    return 1/s + 1/(s-1) - log(pi)/2 + digamma(s/2)/2 + zeta(s, derivative=1)/zeta(s)
print(f"{'t':>8} {'sigma':>6} {'Re[xi_l/xi]':>14} {'-0.5*log(t/2pi)':>16} {'AC (resid)':>12}")
worst = -1e9
for t in [700, 1000, 2000, 5000, 10000]:
    for sig in [0.05, 0.20, 0.35, 0.45, 0.49, 0.499]:
        v = re(xilog(mpc(sig, t)))
        dc = -0.5*log(t/(2*pi))
        print(f"{t:>8} {sig:>6.3f} {float(v):>14.6f} {float(dc):>16.6f} {float(v-dc):>12.6f}")
        worst = max(worst, float(v))
print("max Re over grid:", worst, "-> SIGN CONDITION", "HOLDS on grid" if worst <= 0 else "VIOLATED")
