#!/usr/bin/env python3
"""
att548 — closing the attainment gap of ledger 547 by widening the test family.

Setting.  Anchor s = σ₀ + iγ (1 < σ₀ < 3/2), chart partner s₂ = 1 − s̄.  For each zero ρ the
twisted nodes are x_ρ = 1/(s − ρ), x'_ρ = 1/(ρ − s₂).  The order-n FE-paired Hermitian form along a
polynomial R with R(0) = 0 is

    Q_s(R) = Σ_ρ m_ρ · conj(R(conj x_ρ)) · R(x'_ρ).

For a REAL polynomial R this is the compiled form Σ m_ρ R(x_ρ) R(x'_ρ) (SeatPrimeAnchor.lean).
Facts: on-line zeros have x'_ρ = conj x_ρ, so their term is m|R(conj x_ρ)|² ≥ 0 for ANY complex R.
The FE partner ρ' = 1 − ρ̄ has (x_ρ', x'_ρ') = (conj x'_ρ, conj x_ρ), so the partner's term is the
complex conjugate of ρ's term and the pair contributes 2 Re[...].

The 547 gap: the compiled ⟸ direction needs a zero of MAXIMAL depth (so that it strictly leads at
its own anchor).  This script tests the repair: at the anchor over ANY off-line zero ρ₀ (real nodes
a = 1/(σ₀−β₀) > b = 1/(σ₀−1+β₀) > 0), take

    R_N(y) = y^N · A(y) · (y − μ),   A(y) = Π_{ρ' ∈ F'} (y − x'_ρ'),

with F' = all zeros within height 1 of γ except the pair {ρ₀, 1−ρ̄₀}.  Then every ρ' ∈ F' AND its
partner have R_N(x'_ρ') = 0 or conj(R_N(conj x_ρ')) = 0 — annihilated exactly; far zeros have node
product ≤ 1; the pair gives 2m(ab)^N Re[G₀ (a − μ̄)(b − μ)] with G₀ = conj(A(a)) A(b) ≠ 0, and the
choice μ = b − η, η = −r·conj(G₀)/|G₀|, r = (a−b)/2 makes Re[...] ≤ −|G₀|(a−b)²/4 < 0.

PRE-REGISTERED (decision rules fixed before running):
  P1  Configuration: an off-line zero ρ₀ (depth 0.10) at ordinate γ, a DEEPER zero ρ₁ (depth 0.20)
      at offset +0.15 and a deeper still ρ₂ (depth 0.25) at +0.45, all with FE partners and
      conjugates, on top of the first 1000 on-line zeros (± conjugates).  PREDICT: at the anchor
      over ρ₀ the node product of ρ₁ EXCEEDS ρ₀'s (ρ₀ is NOT a leader; MaxDepth fails for it), so the
      compiled 547 argument does not apply at this anchor.
  P2  OLD family y^N(y − m₀), m₀ = (a+b)/2, at ρ₀'s anchor: PREDICT the total is NOT eventually
      negative (the leading ρ₁ pair oscillates in sign with period 2π/|arg(x₁x'₁)|); record the sign
      string N = 1..60.
  P3  NEW family: (i) every annihilated zero's term is < 1e−9 relative to the pair term;
      (ii) the pair term equals 2m(ab)^N Re[G₀(a−μ̄)(b−μ)] and is ≤ −2m(ab)^N |G₀|(a−b)²/4 (identity
      check < 1e−9 relative); (iii) the TOTAL is negative for all N ≥ N₁ with N₁ ≤ 60.  If the total
      is ≥ 0 for some N in [N₁, 60] after first going negative, P3 DIES.
  P4  CONTROL q = 0 (all planted zeros removed, SAME R_N): PREDICT total ≥ 0 for every N = 1..60
      (every term is |R(conj x)|²).  Any negative value = a bug in the harness, stop.
  P5  CONTROL planted bug (roots of A at x_ρ' instead of x'_ρ'): PREDICT annihilation FAILS for the
      off-ordinate near zeros (relative size of ρ₁'s term ≥ 1e−3), i.e. the check in P3(i) is a live
      instrument and not a tautology.
  P6  Chain (no maximal depth anywhere in the configuration): repeat P3 with the anchor at the
      ordinate of EACH planted zero ρ₀, ρ₁, ρ₂ in turn (each has a deeper or equal competitor
      nearby except ρ₂): PREDICT the new family goes negative at every one of the three anchors.
"""
import numpy as np, sys
np.set_printoptions(precision=4, linewidth=140)

gam = np.load("tmp/zeta_zeros_1000.npy")
sigma0 = 1.25
A = sigma0 - 0.5
U = 1.0/(sigma0 - 1.0)

# choose an anchor height with several on-line zeros in the ±1 band (so the annihilator does real work)
cands = np.arange(100.0, 900.0, 0.5)
counts = np.array([((np.abs(gam - g) <= 1.0)).sum() for g in cands])
g0 = float(cands[counts.argmax()])
print("anchor ordinate γ = %.1f chosen: %d on-line zeros within ±1" % (g0, counts.max()))

def fe_close(plants):
    """FE-close a list of planted zeros: add 1−conj ρ, conj ρ, 1−ρ."""
    out = []
    for r in plants:
        for z in (r, 1 - np.conj(r), np.conj(r), 1 - r):
            if all(abs(z - w) > 1e-12 for w in out):
                out.append(z)
    return out

def zero_set(plants):
    onl = list(0.5 + 1j*gam) + list(0.5 - 1j*gam)
    return np.array(onl + fe_close(plants))

def nodes(s, rho):
    return 1.0/(s - rho), 1.0/(rho - (1 - np.conj(s)))

def polyval(coeffs, y):
    # coeffs high→low (np.poly convention)
    return np.polyval(coeffs, y)

def herm_terms(s, zeros, R):
    """m=1 for all planted/on-line zeros here (simple zeros); returns per-zero terms."""
    x, xp = nodes(s, zeros)
    return np.conj(polyval(R, np.conj(x))) * polyval(R, xp)

def build_R(N, roots, mu):
    # R(y) = y^N * Π(y - root) * (y - mu)
    S = np.poly(np.array(list(roots) + [mu]))
    return np.concatenate([S, np.zeros(N)])   # multiply by y^N

def run(anchor_rho, plants, label, bug=False, verbose=True, Nmax=60):
    zeros = zero_set(plants)
    g = anchor_rho.imag
    s = sigma0 + 1j*g
    beta = anchor_rho.real
    a = 1.0/(sigma0 - beta); b = 1.0/(sigma0 - 1 + beta)
    partner = 1 - np.conj(anchor_rho)
    x_all, xp_all = nodes(s, zeros)
    P = np.abs(x_all*xp_all)
    is_pair = (np.abs(zeros - anchor_rho) < 1e-12) | (np.abs(zeros - partner) < 1e-12)
    near = (np.abs(zeros.imag - g) <= 1.0) & (~is_pair)
    Fp = zeros[near]
    roots = (x_all if bug else xp_all)[near]
    Aa = np.prod(a - roots); Ab = np.prod(b - roots)
    G0 = np.conj(Aa)*Ab
    r = (a - b)/2.0
    eta = -r*np.conj(G0)/abs(G0)
    mu = b - eta
    lead = float(P[~is_pair].max()); lead_idx = int(np.argmax(np.where(~is_pair, P, -1)))
    if verbose:
        print("\n== %s: anchor over ρ₀ = %s, σ₀ = %.2f; a = %.4f, b = %.4f, ab = %.4f" % (label, anchor_rho, sigma0, a, b, a*b))
        print("   |F'| = %d near zeros annihilated (%d on-line, %d planted); max node product among others = %.4f at %s  (pair's own = %.4f)"
              % (len(Fp), int((np.abs(Fp.real-0.5) < 1e-12).sum()), int((np.abs(Fp.real-0.5) >= 1e-12).sum()),
                 lead, zeros[lead_idx], a*b))
        print("   G₀ = %s ; μ = %s ; predicted pair Re-factor bound = −|G₀|(a−b)²/4 = %.6e"
              % (G0, mu, -abs(G0)*(a-b)**2/4))
    results = []
    for N in range(1, Nmax+1):
        R = build_R(N, roots, mu)
        T = herm_terms(s, zeros, R)
        pair = T[is_pair].sum()
        annih = np.abs(T[near]).max() if near.any() else 0.0
        far = T[~is_pair & ~near].sum()
        pred_pair = 2*(a*b)**N*(G0*(a - np.conj(mu))*(b - mu)).real
        results.append((N, pair.real, pred_pair, annih/abs(pair.real), far.real, (pair+far).real, T.sum().real))
    return results, (a, b, G0, mu, lead, a*b)

def report(results, tag):
    negN = [N for (N, p, pp, an, far, tot, full) in results if full < 0]
    first = negN[0] if negN else None
    eventually = first is not None and all(N in negN for N in range(first, results[-1][0]+1))
    max_annih = max(an for (_, _, _, an, _, _, _) in results)
    max_iderr = max(abs(p - pp)/abs(pp) for (_, p, pp, _, _, _, _) in results)
    print("   [%s] first N with total<0: %s ; negative for ALL N ≥ first: %s ; max annihilated/pair = %.2e ; pair identity rel err = %.2e"
          % (tag, first, eventually, max_annih, max_iderr))
    print("   [%s] N, pair, far-tail, total (selected):" % tag)
    for (N, p, pp, an, far, tot, full) in results:
        if N in (1, 2, 3, 5, 10, 20, 30, 40, 50, 60):
            print("       N=%2d  pair=%+.3e  tail=%+.3e  total=%+.3e" % (N, p, far, full))
    return first, eventually, max_annih, max_iderr

y0, y1, y2 = 0.10, 0.20, 0.25
rho0 = (0.5 + y0) + 1j*g0
rho1 = (0.5 + y1) + 1j*(g0 + 0.15)
rho2 = (0.5 + y2) + 1j*(g0 + 0.45)
plants = [rho0, rho1, rho2]

# ---- P1: ρ₀ is not a leader at its own anchor
zeros = zero_set(plants)
s0 = sigma0 + 1j*g0
x_all, xp_all = nodes(s0, zeros)
P = np.abs(x_all*xp_all)
def Pof(z):
    x, xp = nodes(s0, z); return abs(x*xp)
print("\nP1: node products at the anchor over ρ₀: P(ρ₀)=%.4f  P(ρ₁)=%.4f  P(ρ₂)=%.4f  max on-line=%.4f  → ρ₀ leads: %s"
      % (Pof(rho0), Pof(rho1), Pof(rho2), P[np.abs(zeros.real-0.5)<1e-12].max(), Pof(rho0) > Pof(rho1)))

# ---- P2: old family at ρ₀'s anchor
a = 1/(sigma0 - rho0.real); b = 1/(sigma0 - 1 + rho0.real); m0 = (a+b)/2
signs = ''
for N in range(1, 61):
    R = np.concatenate([np.array([1.0, -m0]), np.zeros(N)])
    T = herm_terms(s0, zeros, R)
    signs += '-' if T.sum().real < 0 else '+'
x1, xp1 = nodes(s0, rho1)
print("P2: OLD family y^N(y−m₀) at ρ₀'s anchor, signs N=1..60: %s" % signs)
print("    arg(x₁x'₁) = %+.4f rad → period ≈ %.1f ; eventually negative: %s"
      % (np.angle(x1*xp1), 2*np.pi/abs(np.angle(x1*xp1)), all(c == '-' for c in signs[-20:])))

# ---- P3: new family at ρ₀'s anchor
res, info = run(rho0, plants, "P3 NEW family (annihilator + complex μ)")
p3 = report(res, "P3")

# ---- P4: control q=0 — same R (same roots, same μ) but no planted zeros
print("\n== P4 CONTROL q=0: planted zeros removed, SAME polynomial R_N as P3")
zeros_c = zero_set([])
a, b, G0, mu, lead, ab = info
x_all, xp_all = nodes(s0, zeros)
near_full = (np.abs(zeros.imag - g0) <= 1.0) & ~((np.abs(zeros - rho0) < 1e-12) | (np.abs(zeros - (1-np.conj(rho0))) < 1e-12))
roots = xp_all[near_full]
minval = +np.inf; minN = None
for N in range(1, 61):
    R = build_R(N, roots, mu)
    T = herm_terms(s0, zeros_c, R)
    v = T.sum().real
    if v < minval: minval, minN = v, N
    if N in (1, 5, 10, 20, 40, 60):
        print("       N=%2d  total=%+.3e  (min term = %+.3e)" % (N, v, T.real.min()))
print("   [P4] min total over N=1..60 = %+.3e at N=%d ; all ≥ 0: %s" % (minval, minN, minval >= 0))

# ---- P5: planted bug — roots at x instead of x'
res_bug, _ = run(rho0, plants, "P5 CONTROL planted bug (roots at x_ρ' instead of x'_ρ')", bug=True)
p5 = report(res_bug, "P5")

# ---- P6: chain — anchor at each planted zero in turn
print("\n== P6 chain: new family at the anchor over each planted zero")
p6 = []
for k, r0 in enumerate(plants):
    res_k, info_k = run(r0, plants, "P6 anchor over ρ%d" % k, verbose=False)
    first, ev, an, ide = report(res_k, "P6 ρ%d (depth %.2f, leader among others has P=%.4f vs own %.4f)" % (k, abs(r0.real-0.5), info_k[4], info_k[5]))
    p6.append((first, ev))

print("\nSUMMARY")
print("  P1 ρ₀ not a leader (MaxDepth argument inapplicable here): %s" % (Pof(rho0) < Pof(rho1)))
print("  P2 old family eventually negative: %s (predicted: no)" % all(c == '-' for c in signs[-20:]))
print("  P3 new family: first negative N = %s, negative for all N beyond: %s, annihilation ≤ %.1e, pair identity err %.1e" % p3)
print("  P4 q=0 control all ≥ 0: %s" % (minval >= 0))
print("  P5 bug control: annihilation residual = %.2e (predicted ≥ 1e-3)" % p5[2])
print("  P6 chain anchors negative: %s" % p6)
