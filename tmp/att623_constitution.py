"""att623 — the ordered face's constitution in the Toeplitz register (checks before any claim).

  A_Q(s) = zeta'/zeta(s) + sum_q logDeriv(1 - q^{1-s})                       (definition, channel)
         = -sum_q log q - E(s) - E(1-s) + P_Q(1-s)                            (compiled marriage; P_Q = Q-free von Mangoldt)
  Reflection law of the Toeplitz functional:  T[f(1-.)](s) = - T[f](1-s)        (jets flip sign, d flips sign)
  Constitution:  T^A(s) = U(s) I + D(s) - T^{P_Q}(1-s),
      U = (2/d)( -sum_q log q - Re E(s) - Re E(1-s) ) > 0 on the channel (d<0),   D = E-pair's higher coefficients (dipoles),
      T^{P_Q}(w) = sum_{p not in Q} T^{Euler_p}(w) at w = 1-s, Re w in (1/2,1): each Euler factor = Poisson barycenter of
      unitary clocks (compiled, right of the line) => PSD at every degree.
  And on the channel each conduction clock logDeriv(1 - q^{1-s}) = Poisson barycenter (left) => PSD at every degree,
      so the clock face M_Q = -sum_q logDeriv(1-q^{1-s}) is NSD (measured 622).

CHECKS (pre-registered):
  (C1) reflection law numerically:  T[P_Q(1-.)](s) + T[P_Q](1-s) = 0.
  (C2) constitution:  T^A(s) - (U I + D - T^{P_Q}(1-s)) = 0.
  (C3) T^{Euler_p}(w) PSD for w right of the line, p = 2,3,5,7,11, N = 2,3,4  (prediction: yes, all).
  (C4) T^{cond_q}(s) PSD on the channel, N = 2,3,4 (prediction: yes).
  (C5) the leaf in constitutional form: min eig of [U I + D - T^{P_Q}(1-s)] > 0 (RH region) and its margin vs mass.
"""
from mpmath import mp, mpf, mpc, zeta, log, pi, psi, diff, conj, re, im, binomial
import numpy as np
mp.dps = 30
def E(s):   return 1/s + 1/(s-1) - log(pi)/2 + psi(0, s/2)/2
def zlog(s): return zeta(s, derivative=1)/zeta(s)
def cond(q, s): return log(q) * q**(1-s) / (1 - q**(1-s))        # logDeriv(1 - q^{1-s})
def euler(p, w): return log(p) * p**(-w) / (1 - p**(-w))         # logDeriv(1 - p^{-w})
def PQ(Q, w):   return -zlog(w) - sum(euler(q, w) for q in Q)     # Q-free von Mangoldt series (continued)
def AQ(Q, s):   return zlog(s) + sum(cond(q, s) for q in Q)
def jets(f, s, M):
    return [((-1)**(m-1) / mp.factorial(m-1)) * (diff(f, s, m-1) if m > 1 else f(s)) for m in range(1, M+1)]
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
def Tform(f, s, N):
    d = 2*s.real - 1
    return toeplitz(fourier(jets(f, s, N), d, N), N)
def eigr(T):
    ev = np.linalg.eigvalsh((T + T.conj().T)/2); return ev.min(), ev.max()

N = 4
anchors = [mpc('0.45', 17.58), mpc('0.45', 31.68), mpc('0.40', 23.02), mpc('0.30', 39.25), mpc('0.45', 30.47)]
Q = (2, 3)
print("att623 — constitution checks (dps=30, N=%d, Q=%s)" % (N, Q))
for s in anchors:
    w = 1 - s
    d = 2*s.real - 1
    TA = Tform(lambda z: AQ(Q, z), s, N)
    Trefl = Tform(lambda z: PQ(Q, 1 - z), s, N)          # T[P_Q(1-.)](s)
    TPQw = Tform(lambda z: PQ(Q, z), w, N)                # T[P_Q](1-s)
    c1 = np.abs(Trefl + TPQw).max()
    TEpair = Tform(lambda z: -E(z) - E(1-z), s, N)        # includes its DC on the diagonal
    Uconst = Tform(lambda z: -sum(log(q) for q in Q) + 0*z, s, N)   # DC of the clock constant
    recon = Uconst + TEpair + Trefl
    c2 = np.abs(TA - recon).max()
    U = float(2*(-sum(log(q) for q in Q) - re(E(s)) - re(E(w)))/d)
    print("s=%s  (C1) reflection law resid %.1e   (C2) constitution resid %.1e   U=%.4f  E-dipole spread=%.4f" %
          (s, c1, c2, U, eigr(TEpair)[1]-eigr(TEpair)[0]))
    for Nn in (2, 3, 4):
        sl = slice(0, Nn)
        print("    N=%d  T^A:[%+8.4f,%+8.4f]   T^{P_Q}(1-s):[%+8.4f,%+8.4f]   U+D-T^{P_Q}:[%+8.4f,%+8.4f]" %
              (Nn, *eigr(TA[sl, sl]), *eigr(TPQw[sl, sl]), *eigr((Uconst+TEpair-TPQw)[sl, sl])))
print()
print("(C3) Euler factors RIGHT of the line, T^{Euler_p}(w), w = 1 - s:")
for s in anchors[:3]:
    w = 1 - s
    for p in (2, 3, 5, 7, 11):
        T = Tform(lambda z, p=p: euler(p, z), w, N)
        print("   w=%s p=%2d  N=2:[%+8.4f,%+8.4f] N=3:[%+8.4f,%+8.4f] N=4:[%+8.4f,%+8.4f]" %
              (w, p, *eigr(T[:2,:2]), *eigr(T[:3,:3]), *eigr(T)))
print()
print("(C4) conduction clocks ON the channel, T^{cond_q}(s):")
for s in anchors[:3]:
    for q in (2, 3, 5, 7):
        T = Tform(lambda z, q=q: cond(q, z), s, N)
        print("   s=%s q=%2d  N=2:[%+8.4f,%+8.4f] N=3:[%+8.4f,%+8.4f] N=4:[%+8.4f,%+8.4f]" %
              (s, q, *eigr(T[:2,:2]), *eigr(T[:3,:3]), *eigr(T)))
print()
print("(C3') Euler factors on the WRONG side (channel anchor s, Re s < 1/2), T^{Euler_p}(s):")
for s in anchors[:2]:
    for p in (2, 3):
        T = Tform(lambda z, p=p: euler(p, z), s, N)
        print("   s=%s p=%2d  N=2:[%+8.4f,%+8.4f] N=4:[%+8.4f,%+8.4f]" % (s, p, *eigr(T[:2,:2]), *eigr(T)))
