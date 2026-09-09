#!/usr/bin/env python3
"""
att658 — the seat mass on the channel as the generating function of the fiber's PAIR-DENSITY moment forms.

Fiber kernel: Ξ(t) = ξ(½+it) = ∫Φ(u)e^{itu}du, Φ(u) = Σ_n (2π²n⁴e^{9u/2} − 3πn²e^{5u/2})e^{−πn²e^{2u}} (even, positive).
Tilt: ξ(½+x+it) = ∫Φ(u)e^{xu}e^{itu}du.  Seat mass m = −Re ξ′/ξ = −∂_x log|ξ|.
Claim (derived by hand, tested here):
   m(½+x+it)·|ξ(½+x+it)|² = −½ ∬ (u+v) e^{x(u+v)} Φ(u)Φ(v) cos(t(u−v)) du dv
                          = ½ Σ_{n≥1} J_n(t) |x|^{2n−1}/(2n−1)!      for x < 0 (the channel),
   J_n(t) = ∬ (u+v)^{2n} Φ(u)Φ(v) cos(t(u−v)) du dv = (−1)^n Σ_k (−1)^k C(2n,k) Ξ^{(k)}(t) Ξ^{(2n−k)}(t)
   (J_1 = 2(Ξ′² − ΞΞ″), the Laguerre form of ledger 648).
So RH ⟺ m ≥ 0 on the channel ⟸ J_n(t) ≥ 0 ∀ n, t  (and ⟹, by the x → 0 and higher-order limits).
J_n(t) = cosine transform in d of κ_n(d) = ∫ (2v+d)^{2n} Φ(v)Φ(v+d) dv, the (u+v)^{2n}-weighted autocorrelation of Φ.
PRE-REGISTERED
  P1 identity: LHS vs series (N = 8 terms) agree to 1e−8 at (x,t) ∈ {(−0.1,5),(−0.25,20),(−0.4,33),(−0.45,50)}.
  P2 J_n(t) > 0 for n = 1..4 on t ∈ [0.5, 60] (RH in range; the classical Laguerre hierarchy).
  P3 κ_n(d) is log-concave on d ∈ [0, 6] for n = 0..3 (prediction: yes).
  P4 κ_n(d) is NOT convex near d = 0 (prediction: bell-shaped; Pólya's criterion does not apply as is).
OUTPUT tmp/att658_results.txt
"""
import math, time
import mpmath as mp
mp.mp.dps = 22
out = open("tmp/att658_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()

def Phi(u):
    u = mp.mpf(u); tot = mp.mpf(0)
    for n in range(1, 9):
        e2 = mp.exp(2*u)
        tot += (2*mp.pi**2*n**4*mp.exp(mp.mpf(9)/2*u) - 3*mp.pi*n**2*mp.exp(mp.mpf(5)/2*u))*mp.exp(-mp.pi*n**2*e2)
    return tot
PTS = [0, 0.5, 1, 1.5, 2, 2.5, 3, 4]
def I(f):   # ∫_0^4 f
    return mp.quad(f, PTS)

# normalization check
Xi0 = 2*I(lambda u: Phi(u))
xi_half = mp.mpf(1)/2*mp.mpf(1)/2*(-mp.mpf(1)/2)*mp.pi**(-mp.mpf(1)/4)*mp.gamma(mp.mpf(1)/4)*mp.zeta(mp.mpf(1)/2)
say("normalization: Ξ(0) from kernel = %s ; ξ(½) from ζ = %s ; Φ(0) = %s" % (mp.nstr(Xi0, 12), mp.nstr(xi_half, 12), mp.nstr(Phi(0), 10)))

def F(k, t):   # ∫ u^k Φ(u) e^{itu} du
    if k % 2 == 0: return 2*I(lambda u: u**k*Phi(u)*mp.cos(t*u))
    return 2j*I(lambda u: u**k*Phi(u)*mp.sin(t*u))
def J(n, t):
    Fs = [F(k, t) for k in range(2*n+1)]
    return sum(mp.binomial(2*n, k)*(Fs[k]*mp.conj(Fs[2*n-k])) for k in range(2*n+1)).real

def xi_tilt(x, t):     # ξ(½+x+it) and ξ′ from the kernel
    x = mp.mpf(x); t = mp.mpf(t)
    v = I(lambda u: Phi(u)*(mp.exp(x*u)*mp.expj(t*u) + mp.exp(-x*u)*mp.expj(-t*u)))
    dv = I(lambda u: u*Phi(u)*(mp.exp(x*u)*mp.expj(t*u) - mp.exp(-x*u)*mp.expj(-t*u)))
    return v, dv

say("\nP1 seat identity on the channel: m|ξ|² = −Re[ξ′ conj ξ] vs ½Σ J_n|x|^{2n−1}/(2n−1)!")
t0 = time.time(); p1 = True
for (x, t) in [(-0.1, 5), (-0.25, 20), (-0.4, 33), (-0.45, 50)]:
    v, dv = xi_tilt(x, t)
    lhs = -(dv*mp.conj(v)).real
    Js = [J(n, t) for n in range(1, 9)]
    ser = mp.mpf(1)/2*sum(Js[n-1]*abs(mp.mpf(x))**(2*n-1)/mp.factorial(2*n-1) for n in range(1, 9))
    # cross-check ξ against mpmath
    s = mp.mpf(1)/2 + x + 1j*t
    xi_mp = mp.mpf(1)/2*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
    rel = abs(lhs - ser)/abs(lhs)
    say("   x=%+.2f t=%4.0f  m|ξ|² = %+.8e  series = %+.8e  rel.diff %.1e  (m = %+.5f; ξ kernel vs ζ: %.1e)"
        % (x, t, lhs, ser, rel, lhs/abs(v)**2, abs(v - xi_mp)/abs(xi_mp)))
    if rel > 1e-8: p1 = False
say("   P1 %s (%.0fs)" % ("CONFIRMED" if p1 else "DID NOT HOLD", time.time() - t0))

say("\nP2 sign of J_n(t), n = 1..4, t ∈ [0.5, 60] step 0.5")
t0 = time.time(); p2 = True; minJ = {}
for n in range(1, 5):
    vals = [(t, J(n, t)) for t in [0.5*i for i in range(1, 121)]]
    mn = min(vals, key=lambda p: p[1]/ (1 + abs(p[1])))
    neg = [t for t, v in vals if v <= 0]
    minJ[n] = mn
    say("   n=%d  min J_n over grid at t=%.1f: %+.3e ; nonpositive at %d grid points" % (n, mn[0], mn[1], len(neg)))
    if neg: p2 = False
say("   P2 %s (%.0fs)" % ("CONFIRMED" if p2 else "DID NOT HOLD", time.time() - t0))

say("\nP3/P4 structure of κ_n(d) = ∫(2v+d)^{2n} Φ(v)Φ(v+d) dv, d ∈ [0, 6]")
def kappa(n, d):
    d = mp.mpf(d)
    return mp.quad(lambda v: (2*v + d)**(2*n)*Phi(v)*Phi(v + d), [-4 - d, -2, -1, 0, 1, 2, 4])
ds = [0.1*i for i in range(0, 61)]
for n in range(0, 4):
    ks = [kappa(n, d) for d in ds]
    lk = [mp.log(k) for k in ks]
    dec = all(ks[i+1] <= ks[i] for i in range(len(ks)-1))
    conv2 = [ks[i+1] - 2*ks[i] + ks[i-1] for i in range(1, len(ks)-1)]
    logc2 = [lk[i+1] - 2*lk[i] + lk[i-1] for i in range(1, len(lk)-1)]
    first_convex = next((ds[i+1] for i, c in enumerate(conv2) if c > 0), None)
    say("   n=%d  κ_n(0)=%.4e  decreasing on grid: %s ; log-concave (2nd diff of log ≤ 0) at all grid points: %s (max %.2e) ; convex from d ≈ %s onward; concave near 0: %s"
        % (n, ks[0], dec, all(c <= 1e-12 for c in logc2), max(logc2), first_convex, conv2[0] < 0))
say("   (P3 log-concavity, P4 non-convexity near 0: read off above)")
