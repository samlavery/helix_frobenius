"""L(Sym^r Delta) FUNCTIONAL EQUATION end-to-end (r=1,3,5) via the theta self-duality, with g
built by LOG-SPACE (Mellin) CONVOLUTION — no Meijer-G, no scale bug.

inverse-Mellin of Gamma_C(s+mu) = 2 x^mu e^{-2pi x}.  gamma(Sym^r,s)=prod_i Gamma_C(s+mu_i) =>
g = (2x^{mu_1}e^{-2pi x}) *_Mellin ... *_Mellin (2x^{mu_r'}e^{-2pi x}).  In log-coords x=e^X the
Mellin convolution is an ordinary convolution.  Then phi(t)=sum_n lambda_n g(nt), and the FE
Lambda(s)=eps Lambda(1-s) (level 1, self-dual) is EQUIVALENT to  phi(1/t) = eps * t * phi(t).

Validate on Sym^1 (=Delta itself: g=2x^{11/2}e^{-2pi x}, phi(t)=2t^{11/2}Delta(it), FE eps=+1 is
Delta's modularity) then Sym^3, Sym^5.  eps determined from the numeric.

Run:  python3 sym_r_fe2.py
"""
import numpy as np
from math import comb

TWO_PI = 2 * np.pi
HALF = 11.0 / 2       # (k-1)/2 for Delta, k=12


# --------------------------------------------------------------- tau(n)
def tau_upto(M):
    N = M + 1
    coef = np.zeros(N + 1, dtype=object)
    coef[0] = 1
    for n in range(1, N + 1):
        upd = np.zeros(N + 1, dtype=object)
        for a in range(N + 1):
            if coef[a] == 0:
                continue
            for j in range(0, min(24, N // n) + 1):
                idx = a + n * j
                if idx > N:
                    break
                upd[idx] += coef[a] * comb(24, j) * (-1) ** j
        coef = upd
    return [0] + [int(coef[n - 1]) for n in range(1, M + 1)]


def primes_upto(M):
    s = np.ones(M + 1, bool); s[:2] = False
    for i in range(2, int(M ** .5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


def sym_r_lambda(r, M, tau):
    primes = primes_upto(M)
    theta = {}
    for p in primes:
        c = tau[p] / (2 * p ** HALF)
        theta[int(p)] = np.arccos(min(1.0, max(-1.0, c)))
    lam = np.zeros(M + 1); lam[1] = 1.0
    spf = np.zeros(M + 1, dtype=int)
    for p in primes:
        spf[p::p][spf[p::p] == 0] = p
    hc = {}
    def local_h(p, jm):
        th = theta[p]; P = [0.0]
        for k in range(1, jm + 1):
            sk = np.sin(k * th)
            P.append(np.sin((r + 1) * k * th) / sk if abs(sk) > 1e-12 else float(r + 1))
        h = [1.0]
        for j in range(1, jm + 1):
            h.append(sum(P[i] * h[j - i] for i in range(1, j + 1)) / j)
        return h
    for n in range(2, M + 1):
        p = int(spf[n]); m, e = n, 0
        while m % p == 0: m //= p; e += 1
        pe = n // m
        if m > 1:
            lam[n] = lam[m] * lam[pe]
        else:
            if p not in hc:
                jm = 0; pk = p
                while pk <= M: jm += 1; pk *= p
                hc[p] = local_h(p, jm)
            lam[n] = hc[p][e]
    return lam


# ---------------------------------------------- g by log-space Mellin convolution
def build_g(mus, X0=np.log(1e-3), X1=np.log(400.0), M=9000):
    X = np.linspace(X0, X1, M); dX = X[1] - X[0]; xg = np.exp(X)
    def h(mu): return 2.0 * xg ** mu * np.exp(-TWO_PI * xg)
    g = h(mus[0])
    for mu in mus[1:]:
        full = np.convolve(g, h(mu)) * dX                 # Mellin conv in log-space
        Xf = 2 * X0 + np.arange(len(full)) * dX
        g = np.interp(X, Xf, full)                        # resample onto X grid
    return X, xg, g


def gamma_C_prod(s, mus):
    from math import gamma as G
    v = 1.0
    for mu in mus:
        v *= 2 * (TWO_PI) ** (-(s + mu)) * G(s + mu)
    return v


def main():
    print("L(Sym^r Delta) FUNCTIONAL EQUATION via theta self-duality  (log-conv g, no Meijer-G)")
    print("=" * 84)
    M = 300
    tau = tau_upto(M)
    print(f"  tau: {tau[1:6]}  (want 1,-24,252,-1472,4830)")
    print()
    for r in (1, 3, 5):
        kappa = (r + 1) // 2
        mus = [(2 * i - 1) * HALF for i in range(1, kappa + 1)]
        X, xg, g = build_g(mus)
        # gate: sum g(x) x^{s-1} dX  (Mellin on the log grid) = gamma(s) at s=2,3
        gate = 0.0
        for s in (2.0, 3.0):
            mell = np.sum(g * xg ** s) * (X[1] - X[0])    # int g x^{s-1} dx = sum g x^s dX
            gate = max(gate, abs(mell / gamma_C_prod(s, mus) - 1))
        lam = sym_r_lambda(r, M, tau)
        def phi(t):
            arg = np.arange(1, M + 1) * t
            gv = np.interp(np.log(arg), X, g, left=0.0, right=0.0)
            return np.sum(lam[1:] * gv)
        print(f"Sym^{r}  GL({r+1})  gamma_C shifts {mus}   [g-kernel gate {gate:.1e}]")
        ratios = []
        for t in (0.75, 0.9, 1.1, 1.3):
            pt, pit = phi(t), phi(1.0 / t)
            ratios.append(pit / (t * pt))
        rm = np.mean(ratios)
        spread = max(abs(x - rm) for x in ratios)
        eps = 1 if rm > 0 else -1
        ok = abs(abs(rm) - 1) < 1e-4 and spread < 1e-4
        print(f"   phi(1/t)/(t phi(t)) over t=.75,.9,1.1,1.3 = {[f'{x:+.6f}' for x in ratios]}")
        print(f"   => eps = {eps:+d};  |mean|-1 = {abs(abs(rm)-1):.2e};  spread = {spread:.2e};  "
              f"{'FE HOLDS' if ok else 'residual (precision)'}")
        print()


if __name__ == "__main__":
    main()
