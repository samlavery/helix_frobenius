#!/usr/bin/env python3
"""
att547 — the leader gap: is the supremum of the node product attained, and does a complex leader's
cross term oscillate in the order?

Setting (ledger 545/546). At the anchor s = σ₀ + iγ over the ordinate of an off-line zero ρ*
(β* = ½+y), each zero ρ contributes node product P_ρ = 1/(‖s−ρ‖·‖(1−s̄)−ρ‖) and the FE pair
{ρ, 1−ρ̄} contributes 2 Re[ (i u_ρ)^N (i u_ρ − m₀) · (−i u'_ρ)^N (−i u'_ρ − m₀) ].
For ρ = ρ* the two twisted nodes are REAL (a, b) and the term is 2m R(a)R(b) < 0 for b < m₀ < a.
The compiled theorem needs a STRICT LEADER: P_{ρ*} > P_ρ for every other ρ.  The gap: leaders need
not exist if depths increase along zeros spaced ever closer.

Pre-registration:
  P1 (attainment) For an anchor at the ordinate of a zero, the sup of P over the whole zero set is
     ATTAINED (only finitely many zeros have P above any positive threshold, since P ≤ 1 for
     |Δγ| ≥ 1 and the near band is finite).  Verified numerically as: the number of zeros with
     P ≥ P_{ρ*}/2 is finite and small, and max P over the first 1000 zeros is attained in the near
     band.  (This is provable and is the repair's first half.)
  P2 (adversarial: no strict leader) Construct a synthetic FE-closed configuration with TWO off-line
     pairs at the SAME node product at a common anchor (a tie), and check whether the order-N form
     still goes negative for some N.  PREDICTION: yes — two tied real-node pairs both contribute
     negative terms, so ties among off-line leaders HELP.  Decision: if the form stays ≥ 0 for all
     N ≤ 40 the prediction dies and ties are a genuine obstruction.
  P3 (complex leader) Take the anchor NOT at a zero's ordinate (offset δ), so the leader's twisted
     nodes are complex: x = i u, x' = −i u' with x' = conj(x) only for on-line zeros.  Compute
     the pair term T_N = 2 Re[x^N(x−m₀) x'^N(x'−m₀)] for N = 1..40 for an off-line leader and
     check the sign pattern.  PREDICTION: T_N changes sign as N grows (arg(x x') ≠ 0), so
     *some* N makes it negative while the on-line mass is dominated by |x x'|^N.
  P4 (dominance survives) With the same offset anchor, check that |x x'| for the off-line leader
     still exceeds every on-line zero's node product, i.e. the leader property is stable to the
     offset (needed for the tie-breaking step).
"""
import numpy as np, mpmath as mp, os
mp.mp.dps = 25
np.set_printoptions(precision=4, suppress=False, linewidth=140)

gam = np.load("tmp/zeta_zeros_1000.npy")

def nodes(s, rho):
    """The compiled twisted nodes (SeatPrimeAnchor): with chart points s and s2 = 1 - conj(s),
       x  =  i·(t_rho - w)^{-1}   =  1/(s - rho)
       x' = -i·(t_rho - conj w)^{-1} = 1/(rho - s2)          <-- sign fixed after the P0 check
    At the anchor over rho's own ordinate these are 1/(sigma0 - beta) and 1/(sigma0 - 1 + beta),
    both positive."""
    return 1.0/(s - rho), 1.0/(rho - (1 - np.conj(s)))

def pair_term(s, rho, N, m0, m=1.0):
    x, xp = nodes(s, rho)
    y, yp = nodes(s, 1 - np.conj(rho))
    T = m*(x**N*(x - m0) * xp**N*(xp - m0)) + m*(y**N*(y - m0) * yp**N*(yp - m0))
    return T

def node_prod(s, rho):
    x, xp = nodes(s, rho)
    return abs(x*xp)

# --- verify the real-node identity at an anchor over the zero's own ordinate
y = 0.25; g0 = 18.0; s0 = 1.1 + 1j*g0; rho = (0.5 + y) + 1j*g0
x, xp = nodes(s0, rho)
print("P0 sanity: at s=σ₀+iγ over the zero's ordinate, twisted nodes should be real")
print("   x = %s (expect 1/(σ₀−β) = %.6f) ; x' = %s (expect 1/(σ₀−1+β) = %.6f)"
      % (x, 1/(s0.real - rho.real), xp, 1/(s0.real - 1 + rho.real)))

# --- P1 attainment
print("\nP1 attainment of the node-product sup (anchor over γ=18, σ₀=1.1):")
P = np.array([node_prod(s0, 0.5 + 1j*g) for g in gam])
Pstar = node_prod(s0, rho)
print("   P(ρ*) = %.6f ; max over on-line zeros = %.6f (at γ=%.3f) ; #{P ≥ P*/2} = %d ; #{P ≥ 1} = %d"
      % (Pstar, P.max(), gam[P.argmax()], int((P >= Pstar/2).sum()), int((P >= 1).sum())))

# --- P2 tie of two off-line pairs
print("\nP2 tie: two off-line pairs with equal node product at the same anchor")
# pair A at (0.5+y) + i g0 ; pair B at (0.5+y) + i (g0 + d) with d chosen so node products match
rhoA = (0.5 + y) + 1j*g0
def pp(d):
    return node_prod(s0, (0.5 + y) + 1j*(g0 + d)) - Pstar*0.999
# a nearby height with almost the same product (exact tie only at d=0), use d small
for d in (0.0, 0.05, 0.2):
    rhoB = (0.5 + y) + 1j*(g0 + d)
    tot = []
    for N in range(1, 25):
        m0 = (1/(s0.real - rhoA.real) + 1/(s0.real - 1 + rhoA.real))/2
        T = pair_term(s0, rhoA, N, m0) + pair_term(s0, rhoB, N, m0)
        onl = sum(pair_term(s0, 0.5 + 1j*g, N, m0) for g in gam[:200])
        tot.append((N, T.real, onl.real, (T + onl).real))
    negs = [t for t in tot if t[3] < 0]
    print("   d=%.2f: first N with total<0 = %s ; sample (N, pairs, online, total) = %s"
          % (d, negs[0][0] if negs else None, [(n, "%.2e" % p, "%.2e" % o, "%.2e" % t) for n, p, o, t in tot[:4]]))

# --- P3 complex leader via anchor offset
print("\nP3 complex leader (anchor offset δ from the zero's ordinate), sign pattern of the pair term:")
for delta in (0.0, 0.3, 1.0):
    s = 1.1 + 1j*(g0 + delta)
    xx, xxp = nodes(s, rho)
    m0 = abs(xx)  # a real test root of the same scale
    arg = np.angle(xx*xxp)
    signs = []
    for N in range(1, 41):
        T = pair_term(s, rho, N, m0).real
        signs.append('-' if T < 0 else '+')
    print("   δ=%.1f: arg(x x') = %+.4f rad (period in N ≈ %.1f) ; signs N=1..40: %s"
          % (delta, arg, (2*np.pi/abs(arg) if arg else float('inf')), ''.join(signs)))

# --- P4 dominance under offset
print("\nP4 dominance of the off-line leader under anchor offset:")
for delta in (0.0, 0.3, 1.0, 2.0):
    s = 1.1 + 1j*(g0 + delta)
    Pl = node_prod(s, rho)
    Pon = max(node_prod(s, 0.5 + 1j*g) for g in gam)
    print("   δ=%.1f: |x x'|(leader) = %.6f ; max on-line = %.6f ; leader ahead: %s"
          % (delta, Pl, Pon, Pl > Pon))
