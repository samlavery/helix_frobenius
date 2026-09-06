"""att622b — the degree-N seat marriage in the TOEPLITZ (Cayley) register on the channel.

  anchor s (sigma < 1/2), mirror c = 1 - conj s, d = s - c = 2 sigma - 1 < 0.
  x = 1/(s-rho), x' = 1/(rho-c);  w_rho := x/x' = (rho - c)/(s - rho)  (|w| = 1 iff Re rho = 1/2).
  mu_s := sum_rho |x_rho|^2-weight at w_rho, where on the line |x|^2 = x x'.
  Fourier coefficients (identities, from 1/x' = d - 1/x):
     mu_0 = sum x x' = 2 Re S_1 / d = seatMass(s)
     mu_n = sum x^{n+1} x'^{1-n} = sum_{m=2}^{n+1} C(n-1, m-2) (-1)^{n+1-m} d^{m-2} S_m(s),  n >= 1
  The degree-N seat form is congruent to the Toeplitz matrix T_{jk} = mu_{j-k} (mu_{-n} = conj mu_n).
  RH  <=>  T^{(N)} >= 0 at every anchor and degree  (Caratheodory-Toeplitz: mu_s a positive measure).
  Marriage: S_m = S_m^E + S_m^M + S_m^A  =>  T = T^E + T^M + T^A, each with its own DC (mass) on the diagonal.

MEASURED (pre-registered):
  (T1) mu_n from jets vs mu_n from the zero side (first K zeros): control of the identity.
  (T2) eigen-ranges of T, T^E, T^M, T^A for N = 2,3,4.  PREDICTION: T PSD; T^E ~ mass_E * I (E's higher
       jets negligible at these heights); T^A PSD-dominant; T^M NSD-dominant (clock face).
  (T3) the coherence |mu_n|/mu_0 of the transported zero measure at each anchor.
"""
import sys
from mpmath import mp, mpf, mpc, zeta, log, pi, psi, diff, conj, re, im, zetazero, binomial
import numpy as np
mp.dps = 30
def E(s):   return 1/s + 1/(s-1) - log(pi)/2 + psi(0, s/2)/2
def zlog(s): return zeta(s, derivative=1)/zeta(s)
def logdxi(s): return E(s) + zlog(s)
def MQ(Q, s): return -sum(log(q) * q**(1-s) / (1 - q**(1-s)) for q in Q)
def AQ(Q, s): return zlog(s) - MQ(Q, s)
def jets(f, s, M):
    return [((-1)**(m-1) / mp.factorial(m-1)) * (diff(f, s, m-1) if m > 1 else f(s)) for m in range(1, M+1)]
def fourier_from_jets(S, d, N):
    mu = [2*re(S[0])/d]
    for n in range(1, N):
        tot = mpc(0)
        for m in range(2, n+2):
            tot += binomial(n-1, m-2) * (-1)**(n+1-m) * d**(m-2) * S[m-1]
        mu.append(tot)
    return mu
def toeplitz(mu, N):
    T = np.zeros((N, N), dtype=complex)
    for j in range(N):
        for k in range(N):
            n = j - k
            T[j, k] = complex(mu[n]) if n >= 0 else complex(conj(mu[-n]))
    return T
def eigrange(T):
    Th = (T + T.conj().T)/2
    ev = np.linalg.eigvalsh(Th)
    return ev.min(), ev.max()

K = int(sys.argv[1]) if len(sys.argv) > 1 else 120
zeros = [zetazero(k).imag for k in range(1, K+1)]
def fourier_zero_side(s, c, N):
    mu = [mpc(0)]*N
    for g in zeros:
        for sg in (1, -1):
            rho = mpc(0.5, sg*g)
            x = 1/(s-rho); xp = 1/(rho-c); w = x/xp
            for n in range(N):
                mu[n] += x*xp * w**n
    return mu

first13 = [14.134725141734693, 21.022039638771555, 25.010857580145688, 30.424876125859513,
           32.935061587739190, 37.586178158825671, 40.918719012147495, 43.327073280914999,
           48.005150881167160, 49.773832477672302, 52.970321477714461, 56.446247697063395,
           59.347044002602353]
mids = [(first13[i] + first13[i+1]) / 2 for i in range(len(first13)-1)]
Nmax = 4
Qsets = [(), (2,), (2, 3), (2, 3, 5)]
print("att622b — Toeplitz (Cayley) register of the seat marriage on the channel (dps=%d, K=%d)" % (mp.dps, K))
for sigma in [mpf('0.45'), mpf('0.40'), mpf('0.30')]:
    d = 2*sigma - 1
    print("\n" + "="*110 + "\nsigma = %s, d = %s" % (sigma, d))
    for t in mids[:6] + [mpf(first13[3]) + mpf('0.05')]:   # six midpoints and one point 0.05 above the 4th zero
        s = mpc(sigma, t); c = 1 - conj(s)
        S = jets(logdxi, s, Nmax)
        mu = fourier_from_jets(S, d, Nmax)
        muz = fourier_zero_side(s, c, Nmax)
        ctrl = " ".join("%.1e" % float(abs(mu[n]-muz[n])) for n in range(Nmax))
        coh = " ".join("%.3f" % float(abs(mu[n])/mu[0]) for n in range(1, Nmax))
        print("t=%6.2f  mu_0=seatMass=%+.5f   |mu_n - zero side| n=0..%d: %s   coherence |mu_n|/mu_0: %s" %
              (float(t), mu[0], Nmax-1, ctrl, coh))
        SE = jets(E, s, Nmax); muE = fourier_from_jets(SE, d, Nmax)
        for Q in Qsets:
            SM = jets(lambda w, Q=Q: MQ(Q, w), s, Nmax); SA = jets(lambda w, Q=Q: AQ(Q, w), s, Nmax)
            muM = fourier_from_jets(SM, d, Nmax); muA = fourier_from_jets(SA, d, Nmax)
            for N in (2, 3, 4):
                T = toeplitz(mu, N); TE = toeplitz(muE, N); TM = toeplitz(muM, N); TA = toeplitz(muA, N)
                r = eigrange(T); rE = eigrange(TE); rM = eigrange(TM); rA = eigrange(TA)
                print("   Q=%-9s N=%d  T:[%+8.4f,%+8.4f]  E:[%+8.4f,%+8.4f]  clock:[%+8.4f,%+8.4f]  ordered:[%+8.4f,%+8.4f]" %
                      (str(Q), N, r[0], r[1], rE[0], rE[1], rM[0], rM[1], rA[0], rA[1]))
