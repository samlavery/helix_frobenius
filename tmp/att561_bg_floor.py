# Does the COMPILED background-immune floor predict the measured cell floor?
# Theory: over a mu6 cycle the n=1 clock rotates fully while higher clocks lag
# (step (pi/3)(1 - log n/theta')), so Z ~ B + A cos(theta), A = 2 (n=1 RS amplitude).
# Compiled bound: max over cycle |Z| >= A*sqrt(2)/2 = 1.414 (sharp form: A*sqrt(3)/2 = 1.732).
# PRE-REGISTERED: if measured max >= 1.414 the compiled bound is TIGHT/valid as stated;
# if measured max < 1.414 the lag of higher clocks matters and the bound applies only to
# the ROTATING PART -- report the effective amplitude A_eff = measured_max/(sqrt(2)/2).
from mpmath import mp, mpf, siegelz, siegeltheta, findroot, pi, sqrt, log
mp.dps = 15
def t_of(target, t0): return findroot(lambda t: siegeltheta(t) - target, t0)
print(f"{'height':>9} {'measured min-cycle max|Z|':>26} {'A_eff':>8} {'theta_prime':>12} {'lag n=2':>9}")
for T0 in [1000, 10000, 100000, 1000000]:
    th0 = siegeltheta(mpf(T0)); k0 = int(th0/(pi/3)) + 1
    ts = [(k, t_of(k*pi/3, mpf(T0) + (k-k0)*mpf(T0)/2000 + 1)) for k in range(k0, k0+72)]
    zs = [abs(siegelz(t)) for _, t in ts]
    cyc = [max(zs[6*c+j] for j in range(6)) for c in range(12)]
    m = min(cyc)
    thp = log(mpf(T0)/(2*pi))/2
    lag = float((1 - log(2)/thp))     # fraction of full pi/3 step the n=2 clock makes
    print(f"{T0:>9} {float(m):>26.4f} {float(m/(sqrt(2)/2)):>8.3f} {float(thp):>12.4f} {lag:>9.3f}")
