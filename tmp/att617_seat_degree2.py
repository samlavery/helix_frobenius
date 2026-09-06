# Degree-2 rung of the seat door in the chart sigma0 in (1, 3/2):
#   I(s) := 2 Re(xi'/xi)(s)/(2 sigma0 - 1) - |(xi'/xi)'(s)|  >= 0 ?
# Zero side (under RH): I = sum |x|^2 - |sum x^2|, x = 1/(s - rho).
import mpmath as mp
mp.mp.dps = 30
def logderiv_xi(s):
    z = mp.zeta(s); z1 = mp.zeta(s, derivative=1)
    return 1/s + 1/(s-1) - mp.log(mp.pi)/2 + mp.psi(0, s/2)/2 + z1/z
def dlogderiv_xi(s):
    z = mp.zeta(s); z1 = mp.zeta(s, derivative=1); z2 = mp.zeta(s, derivative=2)
    return -1/s**2 - 1/(s-1)**2 + mp.psi(1, s/2)/4 + z2/z - (z1/z)**2
def I_prime(s):
    d = 2*s.real - 1
    return 2*mp.re(logderiv_xi(s))/d - abs(dlogderiv_xi(s))
# zero side with the first K zeros (both signs of ordinate)
K = 400
zeros = [mp.zetazero(k).imag for k in range(1, K+1)]
def I_zero(s):
    S2 = mp.mpc(0); A = mp.mpf(0)
    for g in zeros:
        for sg in (1, -1):
            x = 1/(s - mp.mpc(0.5, sg*g))
            A += abs(x)**2; S2 += x*x
    return A - abs(S2), A, abs(S2)
print("consistency check (zero side truncated at K=%d zeros vs prime/Gamma side):" % K)
for s in [mp.mpc(1.2, 20.0), mp.mpc(1.05, 14.0), mp.mpc(1.4, 50.3)]:
    Ip = I_prime(s); Iz, A, B = I_zero(s)
    print("  s=%s  I_prime=%.6f  I_zero=%.6f  (A=%.5f |S2|=%.5f)" % (s, Ip, Iz, A, B))
print()
print("scan: min of I(s) and of the ratio |(xi'/xi)'| / (2Re(xi'/xi)/d) over gamma in [0,120]")
mp.mp.dps = 15
for sig in [1.02, 1.05, 1.1, 1.2, 1.3, 1.45]:
    d = 2*sig - 1
    best = None; worst_ratio = None
    g = mp.mpf(0)
    while g <= 120:
        s = mp.mpc(sig, g)
        L = logderiv_xi(s); D = dlogderiv_xi(s)
        val = 2*mp.re(L)/d - abs(D)
        ratio = abs(D)/(2*mp.re(L)/d)
        if best is None or val < best[0]: best = (val, g)
        if worst_ratio is None or ratio > worst_ratio[0]: worst_ratio = (ratio, g)
        g += mp.mpf('0.05')
    print("  sigma0=%.2f  min I = %+.5f at gamma=%.2f   max ratio = %.5f at gamma=%.2f" %
          (sig, best[0], best[1], worst_ratio[0], worst_ratio[1]))
# the off-line pair's deficit alone, for reference
print()
print("isolated off-line pair at anchor height (u=0): pair violates by 4 delta^2/(a a')^2")
for sig, beta in [(1.2, 0.6), (1.2, 0.75), (1.05, 0.9)]:
    a = sig - beta; ap = sig - 1 + beta
    lhs = 1/a**2 + 1/ap**2; rhs = 2/(a*ap)
    print("  sigma0=%.2f beta=%.2f: |S2_pair|=%.4f  2ReS1_pair/d=%.4f  deficit=%.4f" % (sig, beta, lhs, rhs, lhs-rhs))
