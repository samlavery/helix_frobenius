"""att622 — THE DEGREE-N SEAT MARRIAGE ON THE CHANNEL, CLOSED-CELL REGISTER.

Compiled objects read (FaceMarriageIdentity.lean, SeatingMassWrap.lean, HermFormJets.lean):
  endsArch E(s) = 1/s + 1/(s-1) - (log pi)/2 + psi(s/2)/2;   logDeriv xi = E + zeta'/zeta.
  conduction clock 1 - q^{1-s};  logDeriv_conductionClock: logDeriv(1-q^{1-s}) = -log q + log q/(1-q^{1-s}).
  face split on the channel:  zeta'/zeta = M_Q + A_Q,
      M_Q = - sum_q logDeriv(1-q^{1-s})   (clock face, DC sum log q inside),
      A_Q = logDeriv( prod_q (1-q^{1-s}) zeta )  (closed-cell ordered face).
  closedCellBank_marriage: A_Q(s) + sum_q log q = -(E(s)+E(1-s)) - (zeta'/zeta(1-s) + refl_Q(s)),
      refl_Q(s) = sum_q log q q^{s-1}/(1-q^{s-1}).
  seat form at anchor s, mirror c = 1 - conj(s), d = s - c = 2 sigma - 1 (< 0 on the channel):
      x = 1/(s-rho), x' = 1/(rho-c), x + x' = d x x';  H_{jk} = sum_rho x^j x'^k  (j,k >= 1);
      Q_R = sum_{jk} conj(R_j) R_k H_{jk} = sum_rho |R(conj x)|^2 under RH.  Q_1 = H_11 = seatMass.
  jets: S_m(s) = sum_rho (s-rho)^{-m} = (-1)^{m-1}/(m-1)! d^{m-1}/ds^{m-1} logDeriv xi (s);
        sum_rho (rho-c)^{-m} = conj(S_m(s))  (zero set symmetric under rho -> 1 - conj rho).
  Pascal reduction: x^j x'^k = [x^j x'^{k-1} + x^{j-1} x'^k]/d.

MEASURED (pre-registered):
  (M1) consistency: jets from logDeriv xi (mpmath) vs zero side (first K zeros, both conjugates).
  (M2) the marriage identity at each anchor (|lhs - rhs| tiny).
  (M3) degree-N matrices H^(N), N = 1,2,3, at channel anchors: H = H^E + H^M + H^A (faces = jets of
       E, M_Q, A_Q through the same reduction).  PREDICTIONS: H PSD at every anchor (RH region);
       H^A carries the positivity (its minimal eigenvalue dominates), H^M and H^E negative-dominated,
       as at degree 1 (att530).  DECISION: confirmed if min eig H >= -1e-12 everywhere and the
       ordered face's min eigenvalue exceeds the total's at every anchor for N = 2,3; refuted otherwise.
  (M4) H_11 vs seatMass (att530 control).
"""
import sys
from mpmath import mp, mpf, mpc, zeta, log, pi, psi, diff, conj, re, im, zetazero, matrix, eigh
import numpy as np
mp.dps = 30
I = mpc(0, 1)

def E(s):   return 1/s + 1/(s-1) - log(pi)/2 + psi(0, s/2)/2
def zlog(s): return zeta(s, derivative=1)/zeta(s)
def logdxi(s): return E(s) + zlog(s)
def MQ(Q, s): return -sum(log(q) * q**(1-s) / (1 - q**(1-s)) for q in Q)
def AQ(Q, s): return zlog(s) - MQ(Q, s)
def refl(Q, s): return sum(log(q) * q**(s-1) / (1 - q**(s-1)) for q in Q)
def AQ_marriage(Q, s):
    return -sum(log(q) for q in Q) - (E(s) + E(1-s)) - (zlog(1-s) + refl(Q, s))

def jets(f, s, M):
    """S_m = (-1)^{m-1}/(m-1)! f^{(m-1)}(s), m = 1..M"""
    out = []
    for m in range(1, M+1):
        d = diff(f, s, m-1) if m > 1 else f(s)
        out.append((-1)**(m-1) / mp.factorial(m-1) * d)
    return out

def reduce_monomial(j, k, d, memo):
    """x^j x'^k -> ({m: a_m}, {m: b_m}) meaning sum a_m x^m + b_m x'^m"""
    key = (j, k)
    if key in memo: return memo[key]
    if k == 0: r = ({j: mpf(1)}, {})
    elif j == 0: r = ({}, {k: mpf(1)})
    else:
        a1, b1 = reduce_monomial(j, k-1, d, memo)
        a2, b2 = reduce_monomial(j-1, k, d, memo)
        a = {}; b = {}
        for m, c in a1.items(): a[m] = a.get(m, 0) + c/d
        for m, c in a2.items(): a[m] = a.get(m, 0) + c/d
        for m, c in b1.items(): b[m] = b.get(m, 0) + c/d
        for m, c in b2.items(): b[m] = b.get(m, 0) + c/d
        r = (a, b)
    memo[key] = r
    return r

def H_from_jets(S, d, N):
    """S: list S_1..S_{2N} of jets at s; returns N x N complex matrix H_{jk} = sum_rho x^j x'^k"""
    memo = {}
    H = np.zeros((N, N), dtype=complex)
    for j in range(1, N+1):
        for k in range(1, N+1):
            a, b = reduce_monomial(j, k, d, memo)
            val = mpc(0)
            for m, c in a.items(): val += c * S[m-1]
            for m, c in b.items(): val += c * conj(S[m-1])
            H[j-1, k-1] = complex(val)
    return H

def mineig(H):
    Hh = (H + H.conj().T) / 2
    return float(np.linalg.eigvalsh(Hh).min())

# zeros for the consistency control
K = int(sys.argv[1]) if len(sys.argv) > 1 else 120
zeros = [zetazero(k).imag for k in range(1, K+1)]
def jets_zero_side(s, M):
    out = []
    for m in range(1, M+1):
        tot = mpc(0)
        for g in zeros:
            for sg in (1, -1):
                tot += (s - mpc(0.5, sg*g))**(-m)
        out.append(tot)
    return out

N = 3; M = 2*N
Qsets = [(), (2,), (2, 3), (2, 3, 5)]
first13 = [14.134725141734693, 21.022039638771555, 25.010857580145688, 30.424876125859513,
           32.935061587739190, 37.586178158825671, 40.918719012147495, 43.327073280914999,
           48.005150881167160, 49.773832477672302, 52.970321477714461, 56.446247697063395,
           59.347044002602353]
mids = [(first13[i] + first13[i+1]) / 2 for i in range(len(first13)-1)]

print("att622 — degree-N seat marriage on the channel (dps=%d, K=%d zeros for the control, N=%d)" % (mp.dps, K, N))
for sigma in [mpf('0.45'), mpf('0.40')]:
    print("\n" + "="*100)
    print("sigma = %s   d = 2 sigma - 1 = %s" % (sigma, 2*sigma-1))
    d = 2*sigma - 1
    for t in mids[:6]:
        s = mpc(sigma, t)
        S = jets(logdxi, s, M)
        Sz = jets_zero_side(s, M)
        errs = [float(abs(S[m]-Sz[m])) for m in range(M)]
        SE = jets(E, s, M)
        line = "t=%6.2f  |S_m - zero side| m=1..%d: %s" % (float(t), M, " ".join("%.1e" % e for e in errs))
        print(line)
        Htot = H_from_jets(S, d, N)
        print("   seatMass check: H_11 = %+.6f  vs Re(logdxi)/(sigma-1/2) = %+.6f" %
              (Htot[0,0].real, float(re(logdxi(s))/(sigma - mpf(1)/2))))
        for Q in Qsets:
            fM = lambda w, Q=Q: MQ(Q, w)
            fA = lambda w, Q=Q: AQ(Q, w)
            SM = jets(fM, s, M); SA = jets(fA, s, M)
            marriage_err = float(abs(AQ(Q, s) - AQ_marriage(Q, s)))
            HE = H_from_jets(SE, d, N); HM = H_from_jets(SM, d, N); HA = H_from_jets(SA, d, N)
            split_err = float(np.abs(Htot - (HE + HM + HA)).max())
            for n in (1, 2, 3):
                sl = slice(0, n)
                print("   Q=%-9s N=%d  min eig: total %+9.4f | E %+9.4f | clock %+9.4f | ordered %+9.4f   (marriage err %.1e, split err %.1e)" %
                      (str(Q), n, mineig(Htot[sl, sl]), mineig(HE[sl, sl]), mineig(HM[sl, sl]), mineig(HA[sl, sl]),
                       marriage_err, split_err))
