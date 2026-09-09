# att631 — the leaf, attempted: are the partial Euler sums' Toeplitz forms positive at the explicit anchor?
# μ̂_k(P) from arch jets (exact polygamma) + prime-power jets over p ≤ P (exact finite sums).
from mpmath import mp, mpf, mpc, log, pi, psi, conj, re, im, fabs, binomial, factorial, gammainc
import numpy as np, math
mp.dps = 30
def arch_jet(s, m):
    w = 1 - s
    if m == 1: return -(1/w + 1/(w-1) - log(pi)/2 + psi(0, w/2)/2)
    k = m - 1
    return -((-1)**k * factorial(k) * (w**(-k-1) + (w-1)**(-k-1)) + 2**(-k-1) * psi(k, w/2)) / factorial(k)
def primes_upto(n):
    sieve = bytearray([1])*(n+1); sieve[0]=sieve[1]=0
    for i in range(2, int(n**0.5)+1):
        if sieve[i]: sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
    return [i for i in range(n+1) if sieve[i]]
def prime_jets_upto(s, M, P, plist):
    # S_m^P = (-1)^{m-1}/(m-1)! Σ_{p≤P} Σ_{k≥1} ℓ (kℓ)^{m-1} p^{k(s-1)}
    sums = [mpc(0)]*M
    for p in plist:
        if p > P: break
        l = log(p); v = mp.e**((s-1)*l)   # p^{s-1}
        k = 1; vk = v
        while True:
            base = l * vk
            if fabs(base) < mpf(10)**(-40): break
            for m in range(M):
                sums[m] += base * (k*l)**m
            k += 1; vk *= v
            if k > 200: break
    return [((-1)**m / factorial(m)) * sums[m] for m in range(M)]
def fourier(S, d, N):
    mu = [2*re(S[0])/d]
    for n in range(1, N):
        mu.append(sum(binomial(n-1, m-2) * (-1)**(n+1-m) * d**(m-2) * S[m-1] for m in range(2, n+2)))
    return mu
def mineig(mu, N):
    T = np.zeros((N, N), dtype=complex)
    for j in range(N):
        for l in range(N):
            n = j-l; T[j,l] = complex(mu[n]) if n >= 0 else complex(conj(mu[-n]))
    return np.linalg.eigvalsh((T+T.conj().T)/2).min()
s0 = mpc(-1, 20); d = 2*s0.real - 1; M = 6
plist = primes_upto(2_000_000)
SA = [arch_jet(s0, m) for m in range(1, M+1)]
print("att631 — partial Euler sums at s0 = %s (M=%d jets)" % (s0, M))
muA = fourier(SA, d, M)
print("  Γ + ends alone: DC=%.6f  min eig N=2: %+.6f  N=3: %+.6f  N=4: %+.6f  N=6: %+.6f" % (re(muA[0]), mineig(muA,2), mineig(muA,3), mineig(muA,4), mineig(muA,6)))
for P in [2, 3, 5, 10, 30, 100, 300, 1000, 3000, 10000, 30000, 100000, 300000, 1000000, 2000000]:
    SP = prime_jets_upto(s0, M, P, plist)
    mu = fourier([SA[i]+SP[i] for i in range(M)], d, M)
    print("  P=%8d  DC=%.6f  min eig N=2: %+.6f  N=3: %+.6f  N=4: %+.6f  N=6: %+.6f" % (P, re(mu[0]), mineig(mu,2), mineig(mu,3), mineig(mu,4), mineig(mu,6)))
