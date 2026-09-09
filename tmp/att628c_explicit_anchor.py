# att628c — explicit anchor, exact jets; prime sums vectorized to X = 5e6 with the CORRECT tail
# ∫_X^∞ (log x)^k x^{s-1} dx = ∫_{log X}^∞ u^k e^{s u} du = Γ(k+1, −s log X)/(−s)^{k+1}   (Re s < 0).
from mpmath import mp, mpf, mpc, zeta, gamma, log, pi, psi, diff, conj, re, im, fabs, gammainc, binomial, factorial, zetazero, quad, inf
import numpy as np
mp.dps = 30
def xi(s): return s*(s-1)/2 * pi**(-s/2) * gamma(s/2) * zeta(s)
def L(s):  return diff(xi, s) / xi(s)
def arch_jet(s, m):
    w = 1 - s
    if m == 1: return -(1/w + 1/(w-1) - log(pi)/2 + psi(0, w/2)/2)
    k = m - 1
    dk = (-1)**k * factorial(k) * (w**(-k-1) + (w-1)**(-k-1)) + 2**(-k-1) * psi(k, w/2)
    return -dk / factorial(k)
X = 5_000_000
spf = np.arange(X+1, dtype=np.int64)
for i in range(2, int(X**0.5)+1):
    if spf[i] == i:
        seg = spf[i*i::i]; mask = (seg == np.arange(i*i, X+1, i)); seg[mask] = i; spf[i*i::i] = seg
n = np.arange(2, X+1, dtype=np.int64)
p = spf[2:]
q = n.copy()
# strip all factors p from q
for _ in range(23):
    div = (q % p == 0); q = np.where(div, q // p, q)
Lam = np.where(q == 1, np.log(p.astype(np.float64)), 0.0)
logn = np.log(n.astype(np.float64))
def prime_jets(s, M):
    sc = complex(s)
    base = Lam * np.exp((sc - 1) * logn)
    out = []
    pw = np.ones_like(logn)
    for m in range(M):
        tot = np.sum(base * pw)
        a = (-s) * log(X)
        tail = gammainc(m+1, a) / (-s)**(m+1)
        out.append(((-1)**m / factorial(m)) * (mpc(tot.real, tot.imag) + tail))
        pw = pw * logn
    return out
K = 3000
gam = [zetazero(k).imag for k in range(1, K+1)]
def zero_jet(s, m):
    tot = mpc(0)
    for g in gam:
        tot += (s - mpc(0.5, g))**(-m) + (s - mpc(0.5, -g))**(-m)
    dens = lambda h: log(h/(2*pi))/(2*pi)
    tot += quad(lambda h: dens(h)*((s - mpc(0.5, h))**(-m) + (s - mpc(0.5, -h))**(-m)), [gam[-1], 2*gam[-1], 10*gam[-1], inf])
    return tot
def fourier(S, d, N):
    mu = [2*re(S[0])/d]
    for k in range(1, N):
        mu.append(sum(binomial(k-1, m-2) * (-1)**(k+1-m) * d**(m-2) * S[m-1] for m in range(2, k+2)))
    return mu
for s0 in [mpc(-1, 20), mpc(-0.5, 20)]:
    d = 2*s0.real - 1; M = 12
    print("\natt628c — explicit anchor s0 = %s, d = %s, X = %d, K = %d zeros" % (s0, d, X, K))
    SA = [arch_jet(s0, m) for m in range(1, M+1)]
    SP = prime_jets(s0, M)
    SL = [L(s0)] + [zero_jet(s0, m) for m in range(2, M+1)]
    for m in range(1, M+1):
        e = SA[m-1] + SP[m-1]
        print("  m=%2d  zero-side S_m=%s   arch+prime=%s   rel diff=%.2e" % (m, mp.nstr(SL[m-1], 9), mp.nstr(e, 9), fabs(SL[m-1]-e)/fabs(e)))
    muE = fourier([SA[i]+SP[i] for i in range(M)], d, M); muL = fourier(SL, d, M)
    print("  μ̂_k explicit vs zero-side |diff|:", "  ".join("k=%d:%.1e" % (k, fabs(muE[k]-muL[k])) for k in range(M)))
    print("  |μ̂_k| explicit:", "  ".join("k=%d:%.3e" % (k, fabs(muE[k])) for k in range(M)))
    for N in (4, 8, 12):
        T = np.zeros((N, N), dtype=complex)
        for j in range(N):
            for k in range(N):
                nn = j-k; T[j,k] = complex(muE[nn]) if nn >= 0 else complex(conj(muE[-nn]))
        ev = np.linalg.eigvalsh((T+T.conj().T)/2)
        print("  T_%d from primes+Γ alone: min eig = %.6f, max eig = %.6f   (DC = %.6f)" % (N, ev.min(), ev.max(), re(muE[0])))
    print("  arch DC part 2Re(arch)/d = %.6f, prime DC part 2Re(prime)/d = %.6f" % (2*re(SA[0])/d, 2*re(SP[0])/d))
