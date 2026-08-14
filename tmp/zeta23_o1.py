"""TASKS 2-4.  Push lambda past 1, split the prime side into D and O_1, and test whether
O_1 has a computable common mode.

Section 5 decomposition.  With a_n = Lambda(n)/sqrt(n), u_n = log n, and
    P_kl = -2 sum_n a_n R(u_n, delta_kl) cos(mbar_kl u_n)
    Q_kl = -2 sum_n a_n R(u_n, delta_kl) sin(mbar_kl u_n)
one has  cos A cos B = (cos(A-B) + cos(A+B))/2  and  sin A sin B = (cos(A-B) - cos(A+B))/2, so

    sum_kl (P^2 + Q^2)/2 = 2 sum_{n,m} a_n a_m sum_kl R_n R_m cos(mbar (u_n - u_m))   [D + O_1]
    sum_kl (P^2 - Q^2)/2 = 2 sum_{n,m} a_n a_m sum_kl R_n R_m cos(mbar (u_n + u_m))   [O_2]

    D   = 2 sum_n a_n^2 sum_kl R(u_n, delta_kl)^2        (the n = m term; cos 0 = 1)
    O_1 = (P^2+Q^2)/2 summed  -  D
    O_2 = (P^2-Q^2)/2 summed

Consistency: sum_kl R(u,delta_kl)^2 ~ (T L^2 / 2pi) g(u) by Parseval, so
D / L^2 ~ (T/pi) sum_n a_n^2 g(log n), which is exactly their Proposition 5.6.

THE PREDICTION UNDER TEST.  Their (5.12) keeps M[mu,mu] + D and bounds O_1 by |O_1| << L^2 X.
That gives C/N -> F(lambda_1) = lambda_1/(1+lambda_1^2/3), which DECREASES past lambda_1=sqrt3.
The measured zero side instead follows 3 lambda_1^2/(1+3 lambda_1^2).  Forcing the two to agree
determines the common mode of the off-diagonal:

    O_1^main = -(T / 6 pi) (L - l_1)_+^3        (l_1 = l + 2 log 2 - 1)

zero below lambda_1 = 1 and turning on as a cubic.
"""
import time
import numpy as np
from scipy.integrate import quad

from zeta23_bench import phihat, phi
from zeta23_prime import prime_powers, R_amb


def g_corr(y, L, w):
    """g = phi^2 star phi^2, i.e. g(y) = int phi(t)^2 phi(t+y)^2 dt."""
    y = np.atleast_1d(y)
    out = np.zeros(y.size)
    for i, yy in enumerate(y):
        a, b = max(-L/2, -L/2 - yy), min(L/2, L/2 - yy)
        if b <= a:
            continue
        out[i] = quad(lambda t: phi(t, L, w)**2 * phi(t + yy, L, w)**2, a, b,
                      limit=400, epsabs=1e-14)[0]
    return out


def split(T, L, w, lam, u, c=1.0):
    """Return d, sumP2, D, O1, O2 for the given band."""
    h = c * 2 * np.pi / L
    d = int(np.floor(T / h))
    tau = T + np.arange(d) * h
    keep = u < L
    a = (lam * np.exp(-0.5 * u))[keep]
    uu = u[keep]
    deltas = np.arange(-(d - 1), d) * h
    idx = (np.arange(d)[:, None] - np.arange(d)[None, :]) + (d - 1)
    P = np.zeros((d, d))
    Q = np.zeros((d, d))
    D = 0.0
    for j in range(uu.size):
        Rv = R_amb(uu[j], deltas, L, w)
        Rm = Rv[idx]
        ang = tau * (uu[j] / 2)
        cs, sn = np.cos(ang), np.sin(ang)
        P -= 2 * a[j] * Rm * (np.outer(cs, cs) - np.outer(sn, sn))
        Q -= 2 * a[j] * Rm * (np.outer(sn, cs) + np.outer(cs, sn))
        D += 2 * a[j]**2 * float(np.sum(Rm**2))
    sP2 = float(np.sum(P**2))
    sQ2 = float(np.sum(Q**2))
    minus = 0.5 * (sP2 + sQ2)
    O2 = 0.5 * (sP2 - sQ2)
    return d, sP2, D, minus - D, O2, P


if __name__ == "__main__":
    import sys
    T = float(sys.argv[1]) if len(sys.argv) > 1 else 600.0
    ETA = float(sys.argv[2]) if len(sys.argv) > 2 else 0.05
    l = np.log(T / (2 * np.pi))
    l1 = l + 2 * np.log(2) - 1
    NI = T * l1 / (2 * np.pi)
    print(f"T={T}  l={l:.5f}  l1={l1:.5f}  N(I)={NI:.2f}  eta={ETA}")
    print(f"{'lam':>5} {'lam1':>6} {'L':>7} {'X':>10} {'Npp':>7} {'d':>5} "
          f"{'D/L^2':>12} {'D_paper':>12} {'O1/L^2':>12} {'O1_main':>12} "
          f"{'ratio':>7} {'O2/L^2':>10} {'|O1|/D':>8} {'bound L^2X':>11}  [s]")
    for lam in [0.6, 0.8, 1.0, 1.1, 1.25, 1.5, 1.75, 2.0, 2.25, 2.5]:
        t0 = time.time()
        L = lam * l
        w = ETA * L / 2
        if ETA * L > 2 * np.log(2):
            print(f"{lam:5.2f}  SKIP: eta*L={ETA*L:.3f} > 2log2, R closed form invalid")
            continue
        X = np.exp(L)
        lamv, u = prime_powers(X)
        d, sP2, D, O1, O2, _ = split(T, L, w, lamv, u)
        a2 = (lamv[u < L]**2) * np.exp(-u[u < L])
        Dpaper = (T / np.pi) * float(np.sum(a2 * g_corr(u[u < L], L, w)))
        lam1 = L / l1
        pred = -(T / (6 * np.pi)) * max(L - l1, 0.0)**3
        print(f"{lam:5.2f} {lam1:6.3f} {L:7.3f} {X:10.0f} {u.size:7d} {d:5d} "
              f"{D/L**2:12.2f} {Dpaper:12.2f} {O1/L**2:12.2f} {pred:12.2f} "
              f"{(O1/L**2)/pred if pred != 0 else float('nan'):7.3f} {O2/L**2:10.3f} "
              f"{abs(O1/D):8.4f} {L**2*X:11.3e}  [{time.time()-t0:.0f}]")
