#!/usr/bin/env python3
"""att706 — BRING IN THE WINDING: the two-ended MULTIPLICATIVE fiber (the Euler product read from both ends).
   E_x(s) = exp(L_x(s)),  L_x(s) = Σ_{n<x} w_x(n) Λ(n)/log n · n^{−s}   (w_x = Riesz taper 1 − log n/log x, or sharp 1),
   G_x(s) = E_x(s) + χ(s) E_x(1−s),  χ = ζ's FE factor.  Two-end ratio R_x = χ E_x(1−s)/E_x(s):
      log|R_x(s)| = log|χ(s)| + Re L_x(1−s) − Re L_x(s)     — EXACT, explicit in the prime windings.
   First order off the axis (σ = ½ + δ):  ∂_δ log|R_x| at δ=0  =  κ(t) := Re(χ′/χ)(½+it) + 2 Σ w Λ(n) n^{−½} cos(t log n)
      and  κ(t) = −2π·D_{R,x}(t)  with  D_{R,x} = ϑ′/π − (1/π) Σ w Λ n^{−½} cos(t log n)  (the density register, 568).
   PRE-REGISTERED: (1) Riesz-tapered fronts x = 10², 10³, 10⁴: far-side domination log|R_x| < 0 at EVERY sampled (δ, t),
   κ(t) < 0 everywhere (⟺ D_{R,x} > 0, measured positive at every front in 567), and every zero of G_x in the box
   [0.2, 0.8]×[10, 50] is on the axis (argument-principle count = sign changes of u_x = 2Re(e^{iϑ}E_x(½+it))).
   (2) Sharp cutoff (w ≡ 1): κ(t) > 0 somewhere (532's negative Dirichlet lobes), domination fails there.
   Decision: prediction (1) refuted if any sampled log|R_x| ≥ 0 at δ > 0 or any off-axis zero at a Riesz front."""
import numpy as np, mpmath as mp
mp.mp.dps = 25
out = open("tmp/att706_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def vonmangoldt_upto(x):
    N = int(x) + 1
    lam = np.zeros(N); 
    sieve = np.ones(N, dtype=bool); sieve[:2] = False
    for p in range(2, N):
        if sieve[p]:
            sieve[p*p::p] = False
            q = p
            while q < N:
                lam[q] = np.log(p); q *= p
    return lam
def make_L(x, riesz=True):
    lam = vonmangoldt_upto(x - 1)
    n = np.arange(2, len(lam)); ln = np.log(n)
    w = (1 - ln/np.log(x)) if riesz else np.ones_like(ln)
    w = np.clip(w, 0, None)
    coef = w * lam[2:] / ln          # w Λ(n)/log n
    def L(s):
        s = np.asarray(s, dtype=complex)
        return np.einsum('n,ns->s', coef, np.exp(-np.outer(ln, s)))
    def Lprime_re_axis(t):            # 2 Σ w Λ n^{−½} cos(t log n)   (for κ)
        t = np.asarray(t, dtype=float)
        return 2*np.einsum('n,nt->t', w*lam[2:]/np.sqrt(n), np.cos(np.outer(ln, t)))
    return L, Lprime_re_axis
def chi(s):
    s = mp.mpc(s)
    return complex(2**s * mp.pi**(s-1) * mp.sin(mp.pi*s/2) * mp.gamma(1-s))
def logabs_chi(s): return float(mp.log(abs(mp.mpc(chi(s)))))
def re_chi_logderiv_axis(t, h=1e-5):   # ∂_σ log|χ| at σ = ½ by central difference
    return (logabs_chi(0.5+h+1j*t) - logabs_chi(0.5-h+1j*t))/(2*h)
def theta(t): return mp.siegeltheta(mp.mpf(t))
def count_box(Gfun, s0, s1, t0, t1, h=0.004):
    b = np.concatenate([np.linspace(s0, s1, int((s1-s0)/h)+1) + 1j*t0,
                        s1 + 1j*np.linspace(t0, t1, int((t1-t0)/h)+1),
                        np.linspace(s1, s0, int((s1-s0)/h)+1) + 1j*t1,
                        s0 + 1j*np.linspace(t1, t0, int((t1-t0)/h)+1)])
    g = Gfun(b); ang = np.angle(g); d = np.diff(ang); d = (d + np.pi) % (2*np.pi) - np.pi
    return np.sum(d)/(2*np.pi), np.max(np.abs(d)), np.min(np.abs(g))
ts = np.arange(10.0, 50.0, 0.01)
chi_slope = np.array([re_chi_logderiv_axis(t) for t in ts[::20]])   # coarse for the κ check
for riesz, label in ((True, "RIESZ taper"), (False, "SHARP cutoff")):
    for x in (100, 1000, 10000):
        L, Lp = make_L(x, riesz)
        def E(s): return np.exp(L(s))
        def G(s_arr):
            s_arr = np.asarray(s_arr, dtype=complex)
            ce = np.array([chi(s) for s in s_arr])
            return E(s_arr) + ce*E(1 - s_arr)
        # first-order slope κ(t) on a coarse grid, and D_{R,x}
        tc = ts[::20]
        kappa = chi_slope + Lp(tc)
        # far-side domination at finite δ
        rows = []
        for d in (0.01, 0.05, 0.1, 0.2):
            s = 0.5 + d + 1j*ts
            lr = np.array([logabs_chi(z) for z in s[::5]]) + np.real(L(1 - s[::5])) - np.real(L(s[::5]))
            rows.append((d, np.mean(lr < 0), np.max(lr)))
        # zeros in the box vs sign changes on the axis
        Nb, jmp, gmin = count_box(G, 0.2, 0.8, 10.0, 50.0)
        Nf, _, _ = count_box(G, 0.52, 0.8, 10.0, 50.0)
        tt = np.arange(10.0, 50.0, 0.002)
        ph = np.array([complex(mp.exp(1j*theta(t))) for t in tt])
        u = 2*np.real(ph*E(0.5 + 1j*tt))
        Ns = int(np.sum(np.sign(u[:-1])*np.sign(u[1:]) < 0))
        say(f"[{label}] x={x:6d}  κ<0 on {np.mean(kappa<0):.3f} of heights (max κ={np.max(kappa):+.3f})  |  "
            f"domination: " + "  ".join(f"δ={d}: frac={f:.3f}, max log|R|={m:+.2e}" for d,f,m in rows))
        say(f"        zeros in box: N_box={Nb:+.3f} (max step {jmp:.2f}, min|G| {gmin:.2e})  N_far={Nf:+.3f}  "
            f"axis sign changes={Ns}")
