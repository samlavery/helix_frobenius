#!/usr/bin/env python3
"""
att590 — Sam's item 7: the multi-degree defect of the Track S form, ACTUAL phases vs FREE phases (2026-09-04).
  Form: Q_w(r) = Σ r̄_j r_k M_{jk}, M_{jk} = Σ_ρ m_ρ (w−ρ)^{−j}(ρ−c)^{−k}, w = σ₀+iγ, c = 1−w̄, d = 2σ₀−1.
  Prime/jet side (residues): Q_w(r) = −2 Re Σ_{i=1}^N f_{−i}(r) g_i,  g_i = (ξ′/ξ)^{(i−1)}(w)/(i−1)!,
    f_{−i}(r) = (−1)^i Σ_{j≥i,k} r̄_j r_k C(k+j−i−1, j−i) d^{−(k+j−i)}.
  Clock normalisation: H_{jk} = C(j+k−2, j−1)/d^{j+k−1} (Pascal, PD); defect D_N := min_r Re Q(r)/H(r).
  FREE phases: primes p ≤ X0 get phases θ_p (powers tied θ_{p^k} = kθ_p), remainder of the prime side = jets − truncated
    actual sum; alternate (r ← argmin over r; θ ← argmin over θ given r) to estimate D_N^free ≤ D_N.
PRE-REGISTERED: (1) jet-side Q matches zero-side (Re parts) to 1% for N ≤ 3 at γ = 50, 200;
  (2) actual D_N(γ) > 0 at all tested (N, γ) (RH range);
  (3) free-phase D_N^free(γ) < 0 and decreasing in N roughly geometrically with base ≈ d/(4(σ₀−1)) (= 1.75 at σ₀ = 1.2);
  (4) at σ₀ = 1.45 the free-phase decrease in N is much slower (base ≈ 1.05).
"""
import numpy as np, mpmath as mp, math, os, time
from math import comb
mp.mp.dps = 20
t0 = time.time()
# ---- zeros (cached)
zf = "tmp/zeros1500.npy"
if os.path.exists(zf): gam = np.load(zf)
else:
    gam = np.array([float(mp.zetazero(k).imag) for k in range(1, 1501)]); np.save(zf, gam)
print("zeros loaded: %d up to %.1f [%.0fs]" % (len(gam), gam[-1], time.time()-t0))
# ---- primes and Λ up to X0
X0 = 20000
sieve = np.ones(X0+1, bool); sieve[:2] = False
for p in range(2, int(X0**0.5)+1):
    if sieve[p]: sieve[p*p::p] = False
primes = np.nonzero(sieve)[0]
pp, lam, base = [], [], []   # prime powers, Λ, base prime index
for i, p in enumerate(primes):
    q = p
    while q <= X0: pp.append(q); lam.append(math.log(p)); base.append(i); q *= p
pp = np.array(pp, float); lam = np.array(lam); base = np.array(base); kpow = np.round(np.log(pp)/np.log(primes[base])).astype(int)
u = np.log(pp)
def xi_logderiv_jets(w, N):
    f = lambda s: mp.log(mp.zeta(s)) + mp.log(mp.gamma(s/2)) - s/2*mp.log(mp.pi) + mp.log(s*(s-1)/2)
    return [mp.diff(f, w, m)/mp.factorial(m-1) if m >= 1 else 0 for m in range(0, N+1)]  # g_i = f^{(i)}/(i−1)!, index i=1..N
def f_coeffs(N, d):
    # c[i][j][k] = C(k+j−i−1, j−i) d^{−(k+j−i)} for j ≥ i, else 0  (1-indexed i,j,k)
    c = np.zeros((N+1, N+1, N+1))
    for i in range(1, N+1):
        for j in range(i, N+1):
            for k in range(1, N+1):
                c[i][j][k] = comb(k+j-i-1, j-i) * d**(-(k+j-i))
    return c
def Q_matrix_from_jets(gs, N, d, c):
    # Q(r) = −2 Re Σ_i f_{−i}(r) g_i, f_{−i} = (−1)^i Σ_{jk} r̄_j r_k c[i][j][k]  ⇒ B_{jk} = Σ_i (−1)^i c[i][j][k] g_i ; Q = −(B + B^H)
    B = np.zeros((N, N), complex)
    for j in range(1, N+1):
        for k in range(1, N+1):
            B[j-1, k-1] = sum(((-1)**i) * c[i][j][k] * complex(gs[i]) for i in range(1, N+1))
    return -(B + B.conj().T)
def M_zero_side(w, c_, N):
    M = np.zeros((N, N), complex)
    for j in range(1, N+1):
        for k in range(1, N+1):
            s = 0
            for t in gam:
                for rho in (0.5+1j*t, 0.5-1j*t):
                    s += (w-rho)**(-j) * (rho-c_)**(-k)
            M[j-1, k-1] = s
    return M
def H_matrix(N, d):
    return np.array([[comb(j+k-2, j-1) * d**(-(j+k-1)) for k in range(1, N+1)] for j in range(1, N+1)], float)
def gen_min(Q, H):
    # min_r r^H Q r / r^H H r  (Q Hermitian, H PD)
    Lc = np.linalg.cholesky(H); Li = np.linalg.inv(Lc)
    A = Li @ Q @ Li.conj().T; A = (A + A.conj().T)/2
    vals, vecs = np.linalg.eigh(A); r = Li.conj().T @ vecs[:, 0]
    return vals[0], r
def prime_side_split(w, N, sig0, gam_):
    # returns per-prime-power contribution coefficients so that prime part Π(r) = 2 Re Σ_n Λ n^{−σ₀} e^{−iγu} A_r(u)
    # A_r(u) = Σ_i f_{−i}(r) (−u)^{i−1}/(i−1)!  — we return, for each i, the vector of (−u)^{i−1}/(i−1)! Λ n^{−σ₀} (weights)
    return np.array([lam * pp**(-sig0) * ((-u)**(i-1))/math.factorial(i-1) for i in range(1, N+1)])  # shape (N, npp)
for sig0 in (1.2, 1.45):
    d = 2*sig0 - 1
    print("\n=== σ₀ = %.2f, d = %.2f, free-phase growth base d/(4(σ₀−1)) = %.3f" % (sig0, d, d/(4*(sig0-1))))
    for g0 in (50, 200, 1000):
        w = mp.mpc(sig0, g0); c_ = 1 - complex(w).conjugate(); wc = complex(w)
        gs = xi_logderiv_jets(w, 6)
        for N in (1, 2, 3, 4, 5, 6):
            c = f_coeffs(N, d); Q = Q_matrix_from_jets(gs, N, d, c); H = H_matrix(N, d)
            line = "γ=%4d N=%d: actual D_N = %+.4f" % (g0, N, gen_min(Q, H)[0])
            if N <= 3 and g0 in (50, 200):
                M = M_zero_side(wc, c_, N); Mh = (M + M.conj().T)/2
                rr = np.random.default_rng(1).normal(size=N) + 1j*np.random.default_rng(2).normal(size=N)
                qz = (rr.conj() @ Mh @ rr).real; qj = (rr.conj() @ Q @ rr).real
                line += "  [zero-side check: form %.4f vs jets %.4f, rel %.1e]" % (qz, qj, abs(qz-qj)/abs(qj))
            # free phases: alternate
            W = prime_side_split(wc, N, sig0, g0)           # (N, npp) weights for A_r(u) contributions
            # actual prime part per power: 2Re[ e^{−iγu} Σ_i f_{−i}(r) W_i ]
            theta = (g0*np.log(primes)) % (2*np.pi)          # start at the actual phases
            Dfree, r = gen_min(Q, H)
            for it in range(12):
                # f_{−i}(r)
                f = np.array([((-1)**i) * sum(np.conj(r[j-1])*r[k-1]*c[i][j][k] for j in range(1, N+1) for k in range(1, N+1)) for i in range(1, N+1)])
                a = f @ W                                        # A_r(u_n) Λ n^{−σ₀}   (complex per power)
                # actual contribution with current θ: 2Re[e^{−i kθ_p} a_n]; optimal θ_p minimises Σ_{k} 2Re[e^{−ikθ} a_{p^k}] — scan θ on a grid
                th_grid = np.linspace(0, 2*np.pi, 360, endpoint=False)
                newtheta = theta.copy()
                for pi_ in range(len(primes)):
                    idx = np.nonzero(base == pi_)[0]
                    if len(idx) == 0: continue
                    vals = np.array([np.sum(2*(np.exp(-1j*kpow[idx]*th)*a[idx]).real) for th in th_grid])
                    newtheta[pi_] = th_grid[int(np.argmin(vals))]
                theta = newtheta
                # rebuild Q with these phases: Q_free = Q + (free prime part − actual prime part)
                ph_act = np.exp(-1j*g0*u); ph_free = np.exp(-1j*kpow*theta[base])
                # prime part as a Hermitian matrix in r: Π(r) = 2Re Σ_i f_{−i}(r) Σ_n W_i[n] e^{−iθ_n}  ⇒ same structure as jets with g_i replaced by Σ_n W_i e^{−iθ}
                gact = [0] + [complex(np.sum(W[i-1]*ph_act)) for i in range(1, N+1)]
                gfree = [0] + [complex(np.sum(W[i-1]*ph_free)) for i in range(1, N+1)]
                # Q(r) = −2Re Σ f_{−i} g_i with g_i = (ξ′/ξ)^{(i−1)}/(i−1)! = arch-jet − Σ_n Λ n^{−w}(−u)^{i−1}/(i−1)!  ⇒ replacing actual truncated prime jets by free ones:
                Qfree = Q_matrix_from_jets([0]+[complex(gs[i]) + (gact[i] - gfree[i]) for i in range(1, N+1)], N, d, c)
                Dfree_new, r = gen_min(Qfree, H)
                if abs(Dfree_new - Dfree) < 1e-6: Dfree = Dfree_new; break
                Dfree = Dfree_new
            line += "  free-phase D_N ≤ %+.4f" % Dfree
            print(line, flush=True)
print("[%.0fs]" % (time.time()-t0))
