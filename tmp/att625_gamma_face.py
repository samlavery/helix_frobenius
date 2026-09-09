# att625 — the Γ face −T^E at every degree: DC, far-field atoms, growth, positivity range.
# Pre-registered prediction: −T^E ≻ 0 for N ≪ t/(1−2σ); loses positivity at N0 ~ (t/(1−2σ)) log t.
from mpmath import mp, mpf, mpc, zeta, log, pi, psi, conj, re, im, binomial, fabs, sqrt
import numpy as np, sys
mp.dps = 60

def E(s):   return 1/s + 1/(s-1) - log(pi)/2 + psi(0, s/2)/2
def jetsE(s, M):
    # S_1 = E(s); S_m = (s-1)^{-m} - Σ_{n≥1} (s+2n)^{-m} = (s-1)^{-m} - 2^{-m}(ζ(m, s/2) - (s/2)^{-m}), m ≥ 2
    S = [E(s)]
    for m in range(2, M+1):
        S.append((s-1)**(-m) - 2**(-m) * (zeta(m, s/2) - (s/2)**(-m)))
    return S
def jetsPair(s, M):
    # F(s) = -E(s) - E(1-s): jets S_m^F(s) = -S_m^E(s) - (-1)^{m}... derivative of E(1-s): d^{k}/ds^k E(1-s) = (-1)^k E^{(k)}(1-s)
    # S_m^F = (-1)^{m-1}/(m-1)! F^{(m-1)}(s) = -S_m^E(s) - (-1)^{m-1}/(m-1)! (-1)^{m-1} E^{(m-1)}(1-s) = -S_m^E(s) - (-1)^{m-1} S_m^E(1-s)
    SE = jetsE(s, M); SEr = jetsE(1-s, M)
    return [-SE[m-1] - (-1)**(m-1) * SEr[m-1] for m in range(1, M+1)]
def cond(q, s): return log(q) * q**(1-s) / (1 - q**(1-s))
def jetsCond(q, s, M):
    # atoms at 1 + 2πik/ℓ (residue +1), S_m = Σ_k (s - a_k)^{-m}: use closed form via derivatives? use the Dirichlet form:
    # logDeriv cond = -ℓ Σ_{j≥0} e^{jℓ(s-1)} ; ∂^{k} = -ℓ Σ_j (jℓ)^k e^{jℓ(s-1)}
    l = log(q); v = mp.e**(l*(s-1))
    S = [cond(q, s)]
    for m in range(2, M+1):
        k = m-1
        tot = mpc(0); j = 1; term = 1
        while True:
            term = (j*l)**k * v**j
            tot += term
            if fabs(term) < mpf(10)**(-mp.dps+5) and j > k: break
            j += 1
        S.append(((-1)**(m-1) / mp.factorial(m-1)) * (-l) * tot)
    return S
def fourier(S, d, N):
    mu = [2*re(S[0])/d]
    for n in range(1, N):
        mu.append(sum(binomial(n-1, m-2) * (-1)**(n+1-m) * d**(m-2) * S[m-1] for m in range(2, n+2)))
    return mu
def toeplitz(mu, N):
    T = np.zeros((N, N), dtype=complex)
    for j in range(N):
        for k in range(N):
            n = j - k
            T[j, k] = complex(mu[n]) if n >= 0 else complex(conj(mu[-n]))
    return T
def mineig(T):
    return np.linalg.eigvalsh((T + T.conj().T)/2).min()

Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 256
anchors = [mpc('0.40', '23.02'), mpc('0.45', '30.47'), mpc('0.30', '39.25'), mpc('0.40', '100'), mpc('0.40', '300')]
degrees = [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
degrees = [N for N in degrees if N <= Nmax]
print("att625 — the Γ face −T^E at every degree (dps=%d, Nmax=%d)" % (mp.dps, Nmax))
for s in anchors:
    sig, t = s.real, s.imag
    d = 2*sig - 1
    S = jetsE(s, Nmax)
    mu = fourier(S, d, Nmax)
    DC = -mu[0]
    print("\nanchor s = %s   d = %s   DC(−T^E) = −2Re E/d = %.6f   log(t/2π)/(1−2σ) = %.6f" % (s, mp.nstr(d,4), DC, log(t/(2*pi))/(1-2*sig)))
    # far-field atom growth: predicted ratio max_n |w_{-2n}|
    rat = max(sqrt(1 + (1-2*sig)*(4*n+1-2*sig)/((sig+2*n)**2 + t**2)) for n in range(1, 4000))
    print("  predicted growth ratio max_n |w_{-2n}| = %.6f   (1 + (1-2σ)/(2t)) = %.6f" % (rat, 1 + (1-2*sig)/(2*t)))
    ks = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1023]
    print("  |μ̂_k|:", "  ".join("k=%d:%.3e" % (k, fabs(mu[k])) for k in ks if k < Nmax))
    for N in degrees:
        T = -toeplitz(mu, N)
        me = mineig(T)
        gersh = DC - 2*sum(fabs(mu[k]) for k in range(1, N))
        print("  N=%4d  min eig(−T^E) = %+.6f   (DC − 2Σ|μ̂_k| = %+.6f)" % (N, me, gersh))
    # the E-pair (reflected reading U·I + D) at the same anchor
    SF = jetsPair(s, Nmax)
    muF = fourier(SF, d, Nmax)
    print("  E-pair F = −E(s) − E(1−s): DC = %.6f" % muF[0])
    for N in degrees:
        print("  N=%4d  min eig(T^F) = %+.6f" % (N, mineig(toeplitz(muF, N))))
    # −T^E + Σ_q T^{cond_q}, Q = {2, 3}
    if t < 200:
        muQ = [mu[k] for k in range(Nmax)]
        for q in (2, 3):
            Sq = jetsCond(q, s, Nmax); muq = fourier(Sq, d, Nmax)
            muQ = [-muQ[k] + muq[k] if k == 0 else 0 for k in range(1)] + [ -mu[k] + 0 for k in range(1, Nmax)]  # placeholder
        # recompute cleanly
        tot = [-x for x in mu]
        for q in (2, 3):
            Sq = jetsCond(q, s, Nmax); muq = fourier(Sq, d, Nmax)
            tot = [tot[k] + muq[k] for k in range(Nmax)]
        print("  −T^E + T^{cond_2} + T^{cond_3}: DC = %.6f" % tot[0])
        for N in degrees:
            print("  N=%4d  min eig = %+.6f" % (N, mineig(toeplitz(tot, N))))
