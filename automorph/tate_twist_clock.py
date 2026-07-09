"""Tate-twist-clock completion: the CONVERGENT multi-strand incomplete-Mellin kernel.

The completed L is  Lambda(s) = sum_n A_n [ (B/n)^s K(s,n/B) + eps (B/n)^{1-s} K(1-s,n/B) ],
  K(s,y) = int_y^inf u^{s-1} f_d(u) du,   f_d = inverse-Mellin of prod_j Gamma(s+mu_j)
         = MeijerG G^{d,0}_{0,d}(u | mu_1..mu_d)   [the d Tate-twist strands, mu_j the Hodge shifts]
Each strand CONVERGES (K(s,y)->0 fast as y->inf), unlike a bare Dirichlet sum — this is the point.
eps is NOT fed: for eps=+-1 we form Lambda and test which makes arg Lambda(1/2+it) a PINNED (flat)
ray. The pinned ray = the functional equation holding; its value gives eps (0/pi->+1, pi/2->-1).

SANITY (d=1, mu=[1/2]): weight-2 GL(2) (E11 eps=+1, E37 eps=-1) must reproduce bsd_weld.
Then Sym^3 (d=2, mu=[1/2,3/2]) and Sym^5 (d=3, mu=[1/2,3/2,5/2]).
"""
import math, sys
import numpy as np
import mpmath as mp

mp.mp.dps = 20

# ---------- arithmetic: a_p by point counting ----------
def sieve(n):
    s = np.ones(n+1, bool); s[:2] = False
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

CURVES = {  # y^2+y = x^3 + A2 x^2 + A4 x + A6 ; conductor
    "E11": ((-1, -10, -20), 11),
    "E37": ((0, -1, 0), 37),   # 37a: y^2+y=x^3-x
}

def ap(p, A):
    A2, A4, A6 = A
    if p == 2:
        return 2+1 - (sum(1 for x in range(2) for y in range(2)
                          if (y*y+y-(x**3+A2*x*x+A4*x+A6)) % 2 == 0)+1)
    x = np.arange(p, dtype=np.int64)
    z = (4*(x**3 % p)+4*A2 % p*(x*x % p)+4*A4 % p*x+(4*A6+1)) % p
    isq = np.zeros(p, bool); isq[(x*x) % p] = True
    chi = np.where(z == 0, 0, np.where(isq[z], 1, -1))
    return int(-chi.sum())

def sym_coeffs(curve, M, nmax):
    """Sym^M normalized Dirichlet coeffs A_n (analytic norm), odd M; bad prime = Steinberg."""
    A, cond = CURVES[curve]
    primes = sieve(nmax)
    exps = [M-2*j for j in range((M+1)//2)]  # M,M-2,...,1
    spf = np.zeros(nmax+1, np.int64)
    for p in primes[::-1]:
        spf[p::p] = p
    a_bad = ap(cond, A) if cond <= nmax else 1
    loc = {}
    for p in primes:
        p = int(p); kmax = int(math.log(nmax)/math.log(p))+1
        if p == cond:
            al = a_bad/math.sqrt(cond)
            loc[p] = [al**(M*k) for k in range(kmax+1)]
        else:
            th = math.acos(max(-1.0, min(1.0, ap(p, A)/(2*math.sqrt(p)))))
            pm = [2.0*sum(math.cos(e*m*th) for e in exps) for m in range(1, kmax+1)]
            h = [1.0]
            for k in range(1, kmax+1):
                h.append(sum(pm[m-1]*h[k-m] for m in range(1, k+1))/k)
            loc[p] = h
    An = np.zeros(nmax+1); An[1] = 1.0
    for n in range(2, nmax+1):
        p = int(spf[n]); m, k = n, 0
        while m % p == 0: m //= p; k += 1
        An[n] = An[m]*An[n//m] if m > 1 else loc[p][k]
    return An, cond

# ---------- Tate-twist-clock kernel f_d and incomplete Mellin K(s,y) ----------
def tabulate_f(mus, ug):
    """f_d(u) = G^{d,0}_{0,d}(u | mus) on grid ug (float)."""
    f = np.empty(len(ug))
    for i, u in enumerate(ug):
        f[i] = float(mp.meijerg([[], []], [list(mus), []], u))
    return f

def K_on_grid(s, ug, f):
    """K(s,y)=int_y^inf u^{s-1} f(u) du for y = each grid point, via cumulative trapz from the top."""
    integ = (ug**(s-1.0))*f                       # complex
    du = np.diff(ug)
    mid = 0.5*(integ[1:]+integ[:-1])*du            # trapezoid pieces
    tail = np.concatenate([np.cumsum(mid[::-1])[::-1], [0.0]])  # int_{ug[i]}^{ug[-1]}
    return tail                                    # K at each grid point (approx; drops u>umax)

def lam_ray(An, cond, mus, ts):
    d = len(mus)
    B = math.sqrt(cond)/(2*math.pi)**d
    N = len(An)-1
    n = np.arange(1, N+1, dtype=float)
    u = n/N
    w = np.where(u < 1.0, np.exp(1.0-1.0/np.clip(1.0-u*u, 1e-300, None)), 0.0)
    y = n/B                                         # kernel arguments
    ug = np.geomspace(min(y.min(), 1e-3), max(y.max()*1.0, 50.0), 4000)
    fg = tabulate_f(mus, ug)
    rays = {+1: [], -1: []}
    spreads = {}
    for eps in (+1, -1):
        ph = []
        for t in ts:
            Ks = np.interp_complex if False else None
            # K(1/2+it, y) and K(1/2-it, y) by interpolating the grid cumulative integral
            Kp = K_on_grid(0.5+1j*t, ug, fg)
            Km = K_on_grid(0.5-1j*t, ug, fg)
            Kpy = np.interp(y, ug, Kp.real)+1j*np.interp(y, ug, Kp.imag)
            Kmy = np.interp(y, ug, Km.real)+1j*np.interp(y, ug, Km.imag)
            S = np.sum(An[1:]*w*(B/n)**(0.5+1j*t)*Kpy)
            R = np.sum(An[1:]*w*(B/n)**(0.5-1j*t)*Kmy)
            ph.append(np.angle(S+eps*R))
        ph = np.array(ph)
        phm = np.mod(ph, math.pi)
        z = np.exp(2j*phm); z = z*np.conj(np.mean(z))
        spreads[eps] = float(np.std(np.angle(z)))
        rays[eps] = float(np.median(phm))/math.pi
    best = min(spreads, key=spreads.get)
    return best, spreads, rays

def run(curve, M, nmax):
    mus = [ (2*j+1)/2.0 for j in range((M+1)//2) ]   # 1/2,3/2,...,M/2
    An, cond = sym_coeffs(curve, M, nmax)
    ts = np.linspace(-2.5, 2.5, 41)
    best, spreads, rays = lam_ray(An, cond**M if M > 1 else cond, mus, ts)
    print(f"[{curve} Sym^{M}]  d={len(mus)} mus={mus} cond={cond}^{M}")
    print(f"   eps=+1: ray {rays[+1]:.4f}pi spread {spreads[+1]:.3e} | "
          f"eps=-1: ray {rays[-1]:.4f}pi spread {spreads[-1]:.3e}")
    print(f"   -> selected eps={best:+d} (min spread {spreads[best]:.3e}); "
          f"{'PINS (FE closes)' if spreads[best] < 3e-2 else 'no clean pin'}")

if __name__ == "__main__":
    run("E11", 1, 8000)   # sanity: degree-2, expect eps=+1
    run("E37", 1, 8000)   # sanity: degree-2, expect eps=-1
