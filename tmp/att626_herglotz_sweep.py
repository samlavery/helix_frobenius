# att626 — the Herglotz function of the nontrivial zeros' transported measure is the seat's log-derivative
# at the moved anchor s_z = (s + z c)/(1+z):  Φ_s(z) = μ̂_0 + 2Σ_{k≥1} μ̂_k z^k = (2/d)[L(s_z) − i Im L(s)],  L = ξ'/ξ.
from mpmath import mp, mpf, mpc, zeta, gamma, log, pi, diff, conj, re, im, fabs, zetazero, quad, inf, sqrt
mp.dps = 25
def xi(s): return s*(s-1)/2 * pi**(-s/2) * gamma(s/2) * zeta(s)
def L(s):  return diff(xi, s) / xi(s)
def s_of_z(s, z): c = 1 - conj(s); return (s + z*c)/(1 + z)
# (1) per-atom identity, random data
import random
random.seed(1)
for _ in range(3):
    s = mpc(random.uniform(-1, 0.5), random.uniform(5, 50)); rho = mpc(random.uniform(0, 1), random.uniform(-40, 40)); z = mpc(random.uniform(-0.7, 0.7), random.uniform(-0.7, 0.7))
    c = 1 - conj(s); d = s - c
    w = (rho - c)/(s - rho); om = 1/((s - rho)*(rho - c))
    lhs = om*(1 + w*z)/(1 - w*z); rhs = (1/d)*(-1/(s - rho) + 1/(rho - c) + 2/(s_of_z(s, z) - rho))
    print("per-atom identity |lhs−rhs| = %.2e" % fabs(lhs - rhs))
# (2) summed identity from the first K zeros (+ conjugates), with a smooth tail correction beyond γ_K
K = 3000
gam = [zetazero(n).imag for n in range(1, K+1)]
print("K = %d zeros, γ_K = %.3f" % (K, gam[-1]))
def Phi_from_zeros(s, z, tail=True):
    c = 1 - conj(s); tot = mpc(0)
    for g in gam:
        for rho in (mpc(0.5, g), mpc(0.5, -g)):
            w = (rho - c)/(s - rho); om = 1/((s - rho)*(rho - c))
            tot += om*(1 + w*z)/(1 - w*z)
    if tail:  # zeros above γ_K with density log(h/2π)/(2π), both signs of height
        def dens(h): return log(h/(2*pi))/(2*pi)
        def term(h):
            out = mpc(0)
            for rho in (mpc(0.5, h), mpc(0.5, -h)):
                w = (rho - c)/(s - rho); om = 1/((s - rho)*(rho - c))
                out += om*(1 + w*z)/(1 - w*z)
            return dens(h)*out
        tot += quad(term, [gam[-1], 2*gam[-1], 10*gam[-1], inf])
    return tot
for s in [mpc('0.40','23.02'), mpc('0.30','39.25'), mpc('0.45','30.47')]:
    c = 1 - conj(s); d = s - c
    print("anchor s = %s" % s)
    Ls = L(s)
    for z in [mpc(0,0), mpc('0.5','0'), mpc('-0.5','0'), mpc('0','0.6'), mpc('-0.8','0.3'), mpc('0.7','-0.6')]:
        sz = s_of_z(s, z)
        Phi = Phi_from_zeros(s, z)
        pred = (2/d)*(L(sz) - 1j*im(Ls))
        print("  z=%s  s_z=%s  Φ=%s  (2/d)[L(s_z) − i Im L(s)]=%s  |diff|=%.2e  ReΦ=%.6f  2ReL(s_z)/d=%.6f" % (
            mp.nstr(z,3), mp.nstr(sz,6), mp.nstr(Phi,7), mp.nstr(pred,7), fabs(Phi-pred), re(Phi), re(2*L(sz)/d)))
