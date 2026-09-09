# att632 — carrier-coordinate identity per prime: μ̂_k[f_p](s0) = −(ℓ/π) Σ_{m≥1} p^{−m/2} ∫ |s0−½−iy|^{−2} cos(mℓy) w(y)^k dy
# LHS from the exact Dirichlet jets of f_p(s) = Σ_k ℓ p^{k(s−1)}; RHS by dense quadrature on the carrier.
import numpy as np
from mpmath import mp, mpc, mpf, log, binomial, factorial, re, conj
mp.dps = 25
s0 = mpc(-1, 20); d = 2*s0.real - 1
def fp_jets(p, M):
    l = log(p); v = mp.e**((s0-1)*l)
    S = []
    for m in range(1, M+1):
        tot = mpc(0); k = 1; vk = v
        while True:
            term = l * (k*l)**(m-1) * vk
            tot += term
            if abs(term) < mpf(10)**(-30): break
            k += 1; vk *= v
        S.append(((-1)**(m-1)/factorial(m-1)) * tot)
    return S
def fourier(S, N):
    mu = [2*re(S[0])/d]
    for n in range(1, N):
        mu.append(sum(binomial(n-1, m-2) * (-1)**(n+1-m) * d**(m-2) * S[m-1] for m in range(2, n+2)))
    return mu
sig, t0 = float(s0.real), float(s0.imag); dd = float(d)
Y = np.arange(-6000.0, 6000.0, 0.0005)
z = (sig - 0.5) + 1j*(t0 - Y)          # s0 − ½ − iy
dens = 1.0/np.abs(z)**2
w = np.conj(z)/z                        # transport of ½+iy: (½+iy−c)/(s0−½−iy) = conj(z)/z
N = 6
for p in (2, 3, 5, 11):
    l = float(np.log(p))
    S = fp_jets(p, N); mu = fourier(S, N)
    # RHS
    osc = np.zeros_like(Y)
    m = 1
    while p**(-m/2) > 1e-9:
        osc += p**(-m/2) * np.cos(m*l*Y); m += 1
    print("p=%d (m ≤ %d)" % (p, m-1))
    for k in range(N):
        integ = np.trapz(dens * osc * w**k, Y)
        rhs = -(l/np.pi) * integ
        lhs = complex(mu[k])
        print("   k=%d  jets: %+.6f%+.6fi   carrier: %+.6f%+.6fi   |diff|=%.1e" % (k, lhs.real, lhs.imag, rhs.real, rhs.imag, abs(lhs-rhs)))
# and the uniform check: ∫ dens dy = π/(½−σ)  and ∫ dens w^k dy = 0 for k ≥ 1
print("uniform: ∫dens = %.6f vs π/(½−σ) = %.6f ; ∫dens·w = %.2e ; ∫dens·w² = %.2e" % (np.trapz(dens, Y), np.pi/(0.5-sig), abs(np.trapz(dens*w, Y)), abs(np.trapz(dens*w**2, Y))))
