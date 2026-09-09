# att628 — the explicit anchor: jets of ξ'/ξ at s0 (Re s0 < 0) = arch jets + prime jets (absolutely convergent),
# and the Toeplitz coefficients / form built from primes and Γ alone.
from mpmath import mp, mpf, mpc, zeta, gamma, log, pi, psi, diff, conj, re, im, fabs, gammainc, binomial, factorial
import numpy as np, math
mp.dps = 30
def xi(s): return s*(s-1)/2 * pi**(-s/2) * gamma(s/2) * zeta(s)
def L(s):  return diff(xi, s) / xi(s)
def weilArch(w): return 1/w + 1/(w-1) - log(pi)/2 + psi(0, w/2)/2
def arch(s): return -weilArch(1 - s)
# von Mangoldt by sieve
X = 300000
spf = list(range(X+1))
for i in range(2, int(X**0.5)+1):
    if spf[i] == i:
        for j in range(i*i, X+1, i):
            if spf[j] == j: spf[j] = i
Lam = [0.0]*(X+1)
for n in range(2, X+1):
    p = spf[n]; m = n
    while m % p == 0: m //= p
    if m == 1: Lam[n] = math.log(p)
def prime_jet(s, m):
    # Σ_n Λ(n) (log n)^m n^{s-1}  (truncated) + tail ∫_X^∞ (log x)^m x^{s-1} dx = Γ(m+1,(1-s)logX)/(1-s)^{m+1}
    tot = mpc(0)
    for n in range(2, X+1):
        if Lam[n]:
            ln = math.log(n)
            tot += Lam[n] * (ln**m) * mp.e**((s-1)*ln)
    a = (1 - s)*log(X)
    tail = gammainc(m+1, a) / (1 - s)**(m+1)
    return tot + tail, tail
s0 = mpc(-1, 20)
d = 2*s0.real - 1
M = 9
print("att628 — explicit anchor s0 = %s, d = %s, X = %d" % (s0, d, X))
SL = [L(s0)] + [((-1)**(m-1)/factorial(m-1)) * diff(L, s0, m-1) for m in range(2, M+1)]
SA = [arch(s0)] + [((-1)**(m-1)/factorial(m-1)) * diff(arch, s0, m-1) for m in range(2, M+1)]
SP = []
for m in range(1, M+1):
    pj, tail = prime_jet(s0, m-1)
    SP.append(((-1)**(m-1)/factorial(m-1)) * pj)
    print("  m=%d  prime jet tail fraction %.2e" % (m, fabs(tail)/fabs(pj)))
for m in range(1, M+1):
    print("  m=%d  S_m(ξ'/ξ)=%s   arch+prime=%s   |diff|=%.2e" % (m, mp.nstr(SL[m-1], 8), mp.nstr(SA[m-1]+SP[m-1], 8), fabs(SL[m-1] - SA[m-1] - SP[m-1])))
def fourier(S, d, N):
    mu = [2*re(S[0])/d]
    for n in range(1, N):
        mu.append(sum(binomial(n-1, m-2) * (-1)**(n+1-m) * d**(m-2) * S[m-1] for m in range(2, n+2)))
    return mu
muE = fourier([SA[i]+SP[i] for i in range(M)], d, M)
muL = fourier(SL, d, M)
N = M
T = np.zeros((N, N), dtype=complex)
for j in range(N):
    for k in range(N):
        n = j-k; T[j,k] = complex(muE[n]) if n >= 0 else complex(conj(muE[-n]))
ev = np.linalg.eigvalsh((T+T.conj().T)/2)
print("  μ̂_k explicit vs zero-side: max |diff| = %.2e" % max(fabs(muE[k]-muL[k]) for k in range(M)))
print("  DC = %.6f ; T_%d from primes+Γ: min eig = %.6f, max eig = %.6f" % (re(muE[0]), N, ev.min(), ev.max()))
