# att635 — does the Γ-and-ends side ALONE satisfy a polynomial bound at anchor −1+20i?
# arch atoms (jets_archSide_series): 0 with +1, and 1+2n (n≥0) with −1; the n=0 tick cancels the end 1.
# transported modulus at s0: |w_a|² = 1 + (2a−1)(2σ0−1)/|s0−a|².
from mpmath import mp, mpc, mpf, log, pi, psi, conj, re, binomial, factorial, fabs, sqrt
import numpy as np
mp.dps = 30
s0 = mpc(-1, 20); d = 2*s0.real - 1; c = 1 - conj(s0)
def w(a): return (a - c)/(s0 - a)
def om(a): return 1/((s0 - a)*(a - c))
print("anchor %s, c = %s, d = %s" % (s0, c, d))
print("end atom a=0 : |w| = %.10f   |w|^k e-fold at k = %d" % (fabs(w(0)), round(1/float(log(fabs(w(0)))))))
for a in (1, 3, 5, 7, 21):
    print("  tick a=%2d : |w| = %.10f" % (a, fabs(w(a))))
def arch_jet(s, m):
    ww = 1 - s
    if m == 1: return -(1/ww + 1/(ww-1) - log(pi)/2 + psi(0, ww/2)/2)
    k = m - 1
    return -((-1)**k * factorial(k) * (ww**(-k-1) + (ww-1)**(-k-1)) + 2**(-k-1) * psi(k, ww/2)) / factorial(k)
M = 60
SA = [arch_jet(s0, m) for m in range(1, M+1)]
def fourier(S, N):
    mu = [2*re(S[0])/d]
    for n in range(1, N):
        mu.append(sum(binomial(n-1, m-2) * (-1)**(n+1-m) * d**(m-2) * S[m-1] for m in range(2, n+2)))
    return mu
muA = fourier(SA, M)
# atom prediction: μ̂_k(arch) = ω_0 w_0^k − Σ_{n≥1} ω_{1+2n} w_{1+2n}^k  (k ≥ 1)
def arch_atom_coeff(k):
    tot = om(0)*w(0)**k
    n = 1
    while True:
        a = 1 + 2*n
        t = om(a)*w(a)**k
        tot -= t
        if fabs(t) < mpf(10)**(-32) and n > 40: break
        n += 1
        if n > 200000: break
    return tot
print("\n  k   |μ̂_k(arch)| from jets   from atoms      |w_0|^k·|ω_0|")
for k in (1, 2, 5, 10, 20, 40, 59):
    print("  %2d   %.10e   %.10e   %.6e" % (k, float(fabs(muA[k])), float(fabs(arch_atom_coeff(k))), float(fabs(om(0))*fabs(w(0))**k)))
print("\nasymptotics: |ω_0||w_0|^k at k = 10^3, 10^4, 10^5, 10^6:",
      ["%.3e" % (float(fabs(om(0)))*float(fabs(w(0)))**kk) for kk in (10**3, 10**4, 10**5, 10**6)])
