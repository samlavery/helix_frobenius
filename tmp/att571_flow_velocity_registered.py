#!/usr/bin/env python3
"""
att571 — THE INITIAL VELOCITY FIELD OF THE de BRUIJN–NEWMAN FLOW IS A REGISTERED PRIME QUANTITY (2026-09-03).
  Zero dynamics (Csordas–Smith–Varga): ẋ_k = H″/H′(x_k) = 2 Σ_{j≠k} 1/(x_k − x_j)  (sum over all zeros ±x_j).
  At t = 0 with ρ_k = ½ + i x_k:  ẋ_k = 2i·FP_k,  FP_k := finite part of ξ′/ξ at ρ_k = ξ″(ρ_k)/(2ξ′(ρ_k)),
  and by the COMPILED Riesz truncated formula (truncated_explicit_formula_riesz, s₀ → ρ_k):
     FP_k = (1/2π)[∫_b K(b+it−ρ_k)E(b+it)dt + ∫_a K(a+it−ρ_k)E(1−a−it)dt] − Σ_{n≤x}(1−log n/L)Λ(n)n^{−ρ_k}
            − Σ_{ρ≠ρ_k} m_ρ K(ρ−ρ_k) − L/2                (K = (x^w−1)/(Lw²); K − 1/w → G′(0) = L/2)
  Gap closing rate at t=0:  d(g_k²)/dt = 2 g_k (ẋ_{k+1} − ẋ_k) = 8 − (screening by all other zeros), EXACT.
PRE-REGISTERED: P1 |(i) zero-sum − (ii) ξ″/ξ′| < 1e-3 (k ≤ 30);  P2 |(iii) prime side − (ii)| < 2e-3;
  P3 initial d(g²)/dt at ranks 23, 26, 33 within 30% of att559's secant slopes 3.96, 3.95, 4.69, all < 8.
"""
import math, time, numpy as np, mpmath as mp
from scipy.special import digamma
mp.mp.dps = 25
t0 = time.time()
NZ = 800
zs = np.array([float(mp.zetazero(k).imag) for k in range(1, NZ+1)]); print("zeros: %d up to %.1f  [%.0fs]" % (NZ, zs[-1], time.time()-t0))
# (i) zero-sum velocity with density tail
def v_zero_sum(k):
    xk = zs[k]; others = np.delete(zs, k)
    s = np.sum(2*xk/(xk**2 - others**2)) + 1/(2*xk)   # Σ_{j≠k}[1/(x_k−x_j)+1/(x_k+x_j)] + partner −x_k
    U = zs[-1]
    tail = -mp.quad(lambda x: 2*xk/(x*x - xk*xk) * mp.log(x/(2*mp.pi))/(2*mp.pi), [U, mp.inf])
    return 2*(s + float(tail))
# (ii) i ξ''/ξ' at ρ_k
xi = lambda s: mp.mpf(1)/2*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
def v_xi(k):
    rho = mp.mpc(0.5, zs[k])
    d1 = mp.diff(xi, rho, 1); d2 = mp.diff(xi, rho, 2)
    return complex(1j*d2/d1)
# (iii) prime side, Riesz front x = 1e4
L = math.log(1e4); X = 10000
def Kr(w):
    w = np.asarray(w, dtype=complex)
    return (np.exp(L*w) - 1)/(L*w*w)
def E(s):
    return 1/s + 1/(s-1) - math.log(math.pi)/2 + digamma(s/2)/2
# von Mangoldt
N = X; lam = np.zeros(N+1)
sieve = np.ones(N+1, bool); sieve[:2] = False
for p in range(2, int(N**0.5)+1):
    if sieve[p]: sieve[p*p::p] = False
for p in np.nonzero(sieve)[0]:
    q = p
    while q <= N: lam[q] = math.log(p); q *= p
ns = np.arange(2, N+1); Wn = np.maximum(1 - np.log(ns)/L, 0); Ln = lam[2:]
b, a = 2.0, -1.0; T = 4000.0; dt = 0.005; ts = np.arange(-T, T, dt) + dt/2
def v_prime(k):
    s0 = 0.5 + 1j*zs[k]
    lb = np.sum(Kr(b + 1j*ts - s0)*E(b + 1j*ts))*dt
    la = np.sum(Kr(a + 1j*ts - s0)*E(1 - (a + 1j*ts)))*dt
    lines = (lb + la)/(2*math.pi)
    prime = np.sum(Wn*Ln*ns**(-s0))
    others = np.delete(zs, k)
    zsum = np.sum(Kr(1j*(others - zs[k]))) + np.sum(Kr(1j*(-others - zs[k]))) + Kr(1j*(-2*zs[k]))
    FP = lines - prime - zsum - L/2
    return complex(2j*FP)
print("k    x_k        (i) zero-sum      (ii) i xi''/xi'          (iii) prime side        |i-ii|    |iii-ii|")
V = {}
for k in range(30):
    vi = v_zero_sum(k); vii = v_xi(k); viii = v_prime(k); V[k] = vii.real
    print("%2d  %9.4f   %+.6f   %+.6f%+.1e i   %+.6f%+.1e i   %.1e   %.1e" % (k+1, zs[k], vi, vii.real, vii.imag, viii.real, viii.imag, abs(vi - vii.real), abs(viii.real - vii.real)))
print("[%.0fs]" % (time.time()-t0))
# P3: initial closing rates for att559's tracked ranks (rank r = pair (x_r, x_{r+1}) counted from zero index 1 at 14.13? att559 rank 33 = (111.03, 111.87))
for r, slope in ((23, 3.96), (26, 3.95), (33, 4.69)):
    k = int(np.argmin(np.abs(zs - {23: 87.4253, 26: 94.6513, 33: 111.0295}[r])))
    g = zs[k+1] - zs[k]; vk = v_xi(k).real; vk1 = v_xi(k+1).real
    rate = 2*g*(vk1 - vk)
    print("rank %d pair (%.4f, %.4f): g = %.4f ; ẋ_k = %+.4f ẋ_{k+1} = %+.4f ; d(g²)/dt|₀ = %.3f  (att559 secant %.2f ; two-body 8 ; screening %.3f)" % (r, zs[k], zs[k+1], g, vk, vk1, rate, slope, 8 - rate))
# distribution of initial closing rates over the first 300 pairs
rates = []
for k in range(300):
    g = zs[k+1] - zs[k]; rates.append(2*g*(v_xi(k+1).real - v_xi(k).real))
rates = np.array(rates)
print("first 300 pairs: d(g²)/dt|₀ mean %.3f  min %.3f  max %.3f  ; fraction < 8: %.3f ; fraction < 0: %.3f" % (rates.mean(), rates.min(), rates.max(), np.mean(rates < 8), np.mean(rates < 0)))
print("[%.0fs]" % (time.time()-t0))
