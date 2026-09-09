#!/usr/bin/env python3
"""
att659 — forward attempt on rung 1 of the Laguerre hierarchy (658: RH ⟺ all rungs).
(A) Close 658's next object: do the two-ended site cusps cancel at EVERY odd order?  Σ_m g_m^{(2j+1)}(0⁺), j = 0..4.
    Prediction: yes, to 1e−20 (Φ is smooth and even), so the cusp expansion carries no positivity information.
(B) Rung 1 in fiber terms.  ξ(½+it) = A(t)·Z(t), A(t) = −½(¼+t²)π^{−1/4}|Γ(¼+it/2)| (far end), Z = Hardy's function.
    Exact split: L(Ξ) = A² L(Z) + Z² L(A), L(f) := f′² − f f″, and L(A)/A² = −(log A)″ = ¼Re ψ′(¼+it/2) − (½−2t²)/(¼+t²)².
    So rung 1 ⟺ L(Z)/Z² ≥ (log A)″ ≈ −9/(4t²).  Bank DC: Z = Σ_{n≤N_t} 2n^{−½}cos(ϑ − t log n) + R gives
    L(Z) = Σ_n (4/n)ω_n² + AC, ω_n = ½log(t/2π) − log n (exact diagonal), AC = interference.
    Pre-registered: P1 L(Ξ) > 0 on t ∈ [10, 1000] (RH in range).  P2 (prediction) L(Z) < 0 occurs at a small
    fraction (< 5 %) of grid points, at positive local minima of |Z| (near-miss configurations).  P3 the far end is
    load-bearing there: min_t L(Ξ)/(A²Z²) is attained where L(Z) < 0.  P4 Lehmer's pair (t ≈ 7005.06/7005.10):
    L(Z) > 0 at the midpoint (an extremum that crosses), reported with the margin.
OUTPUT tmp/att659_results.txt
"""
import math, time
import mpmath as mp
mp.mp.dps = 20
out = open("tmp/att659_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()

# ---- (A)
def g(m, u):
    u = mp.mpf(u)
    return (2*mp.pi**2*m**4*mp.exp(mp.mpf(9)/2*u) - 3*mp.pi*m**2*mp.exp(mp.mpf(5)/2*u))*mp.exp(-mp.pi*m**2*mp.exp(2*u))
say("(A) cusp cancellation at the weld: Σ_{m≤10} g_m^{(2j+1)}(0⁺) and the largest single term")
okA = True
for j in range(0, 5):
    terms = [mp.diff(lambda u, m=m: g(m, u), 0, 2*j+1) for m in range(1, 11)]
    s = sum(terms); big = max(abs(x) for x in terms)
    say("   order %d: sum = %+.3e  (largest term %.3e, ratio %.1e)" % (2*j+1, s, big, abs(s)/big))
    if abs(s)/big > 1e-15: okA = False
say("   (A) %s — the cusps cancel at every odd order; the remainder is Ξ itself (exponentially small)" % ("CONFIRMED" if okA else "DID NOT HOLD"))

# ---- (B)
def A(t):
    t = mp.mpf(t)
    return -mp.mpf(1)/2*(mp.mpf(1)/4 + t*t)*mp.pi**(-mp.mpf(1)/4)*abs(mp.gamma(mp.mpf(1)/4 + 1j*t/2))
def curvA(t):     # −(log A)″ = L(A)/A²
    t = mp.mpf(t); z = mp.mpf(1)/4 + 1j*t/2
    return (mp.polygamma(1, z)).real/4 - (mp.mpf(1)/2 - 2*t*t)/(mp.mpf(1)/4 + t*t)**2
def LZ(t):
    z0 = mp.siegelz(t); z1 = mp.diff(mp.siegelz, t); z2 = mp.diff(mp.siegelz, t, 2)
    return z0, z1*z1 - z0*z2
def DC(t):
    t = mp.mpf(t); N = int(mp.floor(mp.sqrt(t/(2*mp.pi)))); w0 = mp.log(t/(2*mp.pi))/2
    return sum(4/mp.mpf(n)*(w0 - mp.log(n))**2 for n in range(1, N+1))
# sanity: the exact split at one point
t = mp.mpf(37.5)
xi = lambda tt: mp.mpf(1)/2*(mp.mpf(1)/2+1j*tt)*(mp.mpf(1)/2+1j*tt-1)*mp.pi**(-(mp.mpf(1)/2+1j*tt)/2)*mp.gamma((mp.mpf(1)/2+1j*tt)/2)*mp.zeta(mp.mpf(1)/2+1j*tt)
LXi = (mp.diff(xi, t)**2 - xi(t)*mp.diff(xi, t, 2)).real
z0, lz = LZ(t)
say("\n(B) split check at t=37.5: L(Ξ) = %.6e ; A²L(Z) + Z²L(A) = %.6e ; Ξ/(A·Z) = %s" % (LXi, A(t)**2*lz + z0**2*A(t)**2*curvA(t), mp.nstr(xi(t).real/(A(t)*z0), 8)))

t0 = time.time()
grid = [10 + 0.25*i for i in range(0, 3961)]
neg = []; worst = None; p1 = True; ratio_min = None
for t in grid:
    z0, lz = LZ(t)
    c = curvA(t)
    LXi_norm = lz/(z0*z0) + c          # = L(Ξ)/(A²Z²)
    if LXi_norm <= 0: p1 = False
    if lz < 0: neg.append((t, float(lz), float(lz/(z0*z0)), float(c)))
    if ratio_min is None or LXi_norm < ratio_min[1]: ratio_min = (t, float(LXi_norm), float(lz/(z0*z0)), float(c))
say("   grid t∈[10,1000] step 0.25 (%d points, %.0fs): P1 L(Ξ)>0 everywhere: %s" % (len(grid), time.time()-t0, p1))
say("   L(Z) < 0 at %d points (%.2f%%)" % (len(neg), 100*len(neg)/len(grid)))
for t, lz, r, c in neg[:12]:
    say("      t=%8.2f  L(Z)=%+.3e  L(Z)/Z²=%+.3e  far-end curvature −(log A)″=%+.3e  → L(Ξ)/(A²Z²)=%+.3e" % (t, lz, r, c, r + c))
say("   min over grid of L(Ξ)/(A²Z²) = %+.3e at t=%.2f (there L(Z)/Z² = %+.3e, curvature %+.3e)" % (ratio_min[1], ratio_min[0], ratio_min[2], ratio_min[3]))
# DC vs AC at a few points and at the negatives
say("   bank DC Σ(4/n)ω_n² vs L(Z) at sample t:")
for t in [50, 100, 300, 600, 1000] + [n[0] for n in neg[:3]]:
    z0, lz = LZ(t); d = DC(t)
    say("      t=%8.2f  DC=%.3e  L(Z)=%+.3e  AC=L−DC=%+.3e  Z=%+.3e" % (t, d, lz, lz - d, z0))
# Lehmer pair
say("   Lehmer pair region:")
for t in [7005.0, 7005.06, 7005.08, 7005.10, 7005.2]:
    z0, lz = LZ(t); c = curvA(t)
    say("      t=%.3f  Z=%+.3e  L(Z)=%+.3e  L(Z)/Z²=%+.3e  curvature=%+.3e" % (t, z0, lz, lz/(z0*z0) if z0 != 0 else float('nan'), c))
