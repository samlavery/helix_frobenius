# att628b — explicit anchor with EXACT jets: arch jets by polygamma, prime jets by the absolutely convergent
# series (+ incomplete-gamma tail), zero-side jets by the sum over 3000 zeros (+ smooth tail) for m ≥ 2.
from mpmath import mp, mpf, mpc, zeta, gamma, log, pi, psi, diff, conj, re, im, fabs, gammainc, binomial, factorial, zetazero, quad, inf
import numpy as np, math
mp.dps = 30
def xi(s): return s*(s-1)/2 * pi**(-s/2) * gamma(s/2) * zeta(s)
def L(s):  return diff(xi, s) / xi(s)
def arch_jet(s, m):
    # S_m^{arch} = -(1/(m-1)!) d^{m-1}/dw^{m-1} weilArch(w) at w = 1-s, for m ≥ 2; S_1 = -weilArch(1-s)
    w = 1 - s
    if m == 1: return -(1/w + 1/(w-1) - log(pi)/2 + psi(0, w/2)/2)
    k = m - 1
    dk = (-1)**k * factorial(k) * (w**(-k-1) + (w-1)**(-k-1)) + 2**(-k-1) * psi(k, w/2)
    return -dk / factorial(k)
X = 300000
spf = list(range(X+1))
for i in range(2, int(X**0.5)+1):
    if spf[i] == i:
        for j in range(i*i, X+1, i):
            if spf[j] == j: spf[j] = i
Lam = [0.0]*(X+1)
for n in range(2, X+1):
    p = spf[n]; q = n
    while q % p == 0: q //= p
    if q == 1: Lam[n] = math.log(p)
def prime_jets(s, M):
    # returns S_m^{prime} for m = 1..M: (-1)^{m-1}/(m-1)! Σ Λ(n)(log n)^{m-1} n^{s-1}
    sums = [mpc(0)]*M
    for n in range(2, X+1):
        if Lam[n]:
            ln = math.log(n); base = Lam[n] * mp.e**((s-1)*ln)
            pw = mpf(1)
            for m in range(M):
                sums[m] += base * pw
                pw *= ln
    out = []
    for m in range(M):
        a = (1 - s)*log(X)
        tail = gammainc(m+1, a) / (1 - s)**(m+1)
        out.append(((-1)**m / factorial(m)) * (sums[m] + tail))
    return out
K = 3000
gam = [zetazero(n).imag for n in range(1, K+1)]
def zero_jet(s, m):
    tot = mpc(0)
    for g in gam:
        tot += (s - mpc(0.5, g))**(-m) + (s - mpc(0.5, -g))**(-m)
    dens = lambda h: log(h/(2*pi))/(2*pi)
    tot += quad(lambda h: dens(h)*((s - mpc(0.5, h))**(-m) + (s - mpc(0.5, -h))**(-m)), [gam[-1], 2*gam[-1], 10*gam[-1], inf])
    return tot
def fourier(S, d, N):
    mu = [2*re(S[0])/d]
    for n in range(1, N):
        mu.append(sum(binomial(n-1, m-2) * (-1)**(n+1-m) * d**(m-2) * S[m-1] for m in range(2, n+2)))
    return mu
for s0 in [mpc(-1, 20), mpc(-0.5, 20)]:
    d = 2*s0.real - 1; M = 10
    print("\natt628b — explicit anchor s0 = %s, d = %s, X = %d, K = %d zeros" % (s0, d, X, K))
    SA = [arch_jet(s0, m) for m in range(1, M+1)]
    SP = prime_jets(s0, M)
    SL = [L(s0)] + [zero_jet(s0, m) for m in range(2, M+1)]
    for m in range(1, M+1):
        e = SA[m-1] + SP[m-1]
        print("  m=%2d  zero-side S_m=%s   arch+prime=%s   |diff|=%.2e   rel=%.2e" % (m, mp.nstr(SL[m-1], 9), mp.nstr(e, 9), fabs(SL[m-1]-e), fabs(SL[m-1]-e)/fabs(e)))
    muE = fourier([SA[i]+SP[i] for i in range(M)], d, M); muL = fourier(SL, d, M)
    print("  μ̂_k: explicit vs zero-side |diff|:", "  ".join("k=%d:%.1e" % (k, fabs(muE[k]-muL[k])) for k in range(M)))
    N = M
    T = np.zeros((N, N), dtype=complex)
    for j in range(N):
        for k in range(N):
            n = j-k; T[j,k] = complex(muE[n]) if n >= 0 else complex(conj(muE[-n]))
    ev = np.linalg.eigvalsh((T+T.conj().T)/2)
    print("  DC = %.6f ; T_%d from primes+Γ alone: min eig = %.6f, max eig = %.6f" % (re(muE[0]), N, ev.min(), ev.max()))
    print("  arch DC part 2Re(arch)/d = %.6f, prime DC part 2Re(prime)/d = %.6f" % (2*re(SA[0])/d, 2*re(SP[0])/d))
