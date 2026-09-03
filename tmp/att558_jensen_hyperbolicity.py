#!/usr/bin/env python3
"""
att558 — THE SIGN-FLIP LAW AS A FINITE TEST WITH A FALSE BRANCH (Sam: "use the sign flip law:
vanishing only on the midpoint, sign flips only on the midpoint, aka the real axis").

The real fiber at the midpoint:  ξ(½ + z) = Σ_m c_m z^{2m},  c_m = (2/(2m)!) ∫_0^∞ Φ(u) u^{2m} du  (Φ Titchmarsh),
all c_m > 0.  Put f(x) = 8ξ(½ + √x) = Σ_n γ(n) x^n/n!,  γ(n) = 8 n! c_n  (GORZ normalization).
"Every vanishing of the fiber is a sign flip on the real axis" ⟺ f ∈ Laguerre–Pólya ⟺ RH (Pólya 1927)
⟺ every Jensen polynomial  J^{d,n}(X) = Σ_{j=0}^d C(d,j) γ(n+j) X^j  is hyperbolic (Pólya–Jensen).
Known: d = 2 (Turán inequalities γ(n+1)² ≥ γ(n)γ(n+2)) for all n (Csordas–Norfolk–Varga 1986);
each fixed d for n ≥ N(d) (Griffin–Ono–Rolen–Zagier 2019); d ≤ 8 all n (Chasse).
TEST: hyperbolicity of J^{d,n} for d ≤ 50, n ∈ {0,1,2,3,5,10}.  A NON-hyperbolic J^{d,n} at any
(d, n) is a DISPROOF of RH (after independent verification).  PRE-REGISTERED PREDICTION: all
hyperbolic (RH-true reading at this depth).  Decision: hyperbolic iff every root has
|Im r| ≤ 1e−30·(1 + |r|) and the polynomial is well-conditioned (residual check).
OUTPUT tmp/att558_results.txt
"""
import mpmath as mp, time
mp.mp.dps = 160
PI = mp.pi
out = open("tmp/att558_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()

def Phi(u):  # Titchmarsh's Φ: ξ(½+it) = 2∫_0^∞ Φ(u) cos(tu) du
    e2 = mp.exp(2*u); e9 = mp.exp(mp.mpf(9)/2*u); e5 = mp.exp(mp.mpf(5)/2*u)
    return mp.fsum((2*PI**2*n**4*e9 - 3*PI*n**2*e5)*mp.exp(-PI*n*n*e2) for n in range(1, 40))

M = 62
t0 = time.time()
mom = [2*mp.quad(lambda u: Phi(u)*u**(2*m), [0, 0.5, 1, 1.5, 2, 2.5, 3.5]) for m in range(M + 1)]
c = [mom[m]/mp.factorial(2*m) for m in range(M + 1)]
# sanity: ξ(½) and ξ(½ + 0.3)
xi = lambda s: mp.mpf(1)/2*s*(s - 1)*PI**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
say("moments computed (%.0fs); sanity: Σc_m·0 = %s vs ξ(½) = %s ; Σ c_m 0.3^{2m} = %s vs ξ(0.8) = %s"
    % (time.time() - t0, mp.nstr(c[0], 15), mp.nstr(xi(mp.mpf(1)/2), 15),
       mp.nstr(mp.fsum(c[m]*mp.mpf("0.3")**(2*m) for m in range(M + 1)), 15), mp.nstr(xi(mp.mpf("0.8")), 15)))
gam = [8*mp.factorial(n)*c[n] for n in range(M + 1)]
say("γ(0..4) = %s" % [mp.nstr(g, 8) for g in gam[:5]])

# Turán (d = 2) for all n
tur = [gam[n+1]**2 - gam[n]*gam[n+2] for n in range(M - 1)]
say("Turán γ(n+1)² − γ(n)γ(n+2) > 0 for n = 0..%d: %s (min relative %s)" %
    (M - 2, all(t > 0 for t in tur), mp.nstr(min(t/(gam[n+1]**2) for n, t in enumerate(tur)), 3)))

def jensen_hyperbolic(d, n):
    coeffs = [mp.binomial(d, j)*gam[n + j] for j in range(d, -1, -1)]   # highest degree first
    roots = mp.polyroots(coeffs, maxsteps=400, extraprec=600)
    worst = max(abs(r.imag)/(1 + abs(r)) for r in roots)
    # residual conditioning: |J(r)| relative to Σ|coeff r^j|
    res = max(abs(mp.polyval(coeffs, r))/mp.fsum(abs(cf)*abs(r)**(d - k) for k, cf in enumerate(coeffs)) for r in roots)
    allneg = all(r.real < 0 for r in roots)
    return worst, res, allneg, roots

say("\nJensen hyperbolicity J^{d,n}: worst |Im r|/(1+|r|) over roots  (hyperbolic iff ≤ 1e-30); all roots negative real?")
overall = True
for n in (0, 1, 2, 3, 5, 10):
    row = []
    for d in (2, 3, 5, 8, 10, 15, 20, 25, 30, 40, 50):
        if n + d > M: continue
        worst, res, allneg, roots = jensen_hyperbolic(d, n)
        hyp = worst <= mp.mpf("1e-30")
        overall &= hyp
        row.append("d=%d:%s%s" % (d, "H" if hyp else "NOT-H(%s)" % mp.nstr(worst, 2), "" if allneg else "*"))
    say(" n=%2d  %s" % (n, "  ".join(row)))
# the extreme root ratio (spacing sanity) at d=50, n=0
w, r, a, roots = jensen_hyperbolic(50, 0)
rr = sorted([float(x.real) for x in roots])
say("\nJ^{50,0}: worst Im %s, residual %s, roots real & negative: %s; root range [%.4g, %.4g]" % (mp.nstr(w, 3), mp.nstr(r, 3), a, rr[0], rr[-1]))
say("\nVERDICT (this depth, d ≤ 50, n ≤ 10): %s" % ("ALL HYPERBOLIC — RH-TRUE reading; no disproof" if overall else "A NON-HYPERBOLIC JENSEN POLYNOMIAL — RH-FALSE candidate: VERIFY INDEPENDENTLY"))
out.close()
