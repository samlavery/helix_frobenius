# W1 spec: numerical injectivity gate for the mu_3 Prym-Petri maps

Goal (gate for the semiregularity program): test, at explicit members over F_q,
whether the mu_3-analogs of Welters' Prym-Petri map are injective — the input that
controls (W2) smoothness/lci of the Abel-Prym cycle W_n and (W3) the semiregularity
map of W_n in the split-Weil moduli.

## Objects

Tower: E0 <- C <- C~, with C the genus-g base (v2 sixfold curve g=4 SMOOTH first,
eightfold tuned curve g=5 with 2 nodes second), C~ = {t^3 = y} etale mu_3, deck
sigma: t -> zeta*t; ~C genus 3g-2.  epsilon in Pic^0(C)[3] the defining class
(div(y)/3 pulled back).

Welters (Z/2, ASENS 1985): beta: Lambda^2 H^0(L) -> H^0(omega_C(eps)),
s^t -> (s.(iota t) - (iota s).t)/2 = the anti-invariant component of the Petri
multiplication; T_{V^r}(L) = (Im beta)^perp; beta injective => strata smooth of
expected dimension.  Mu_3 transposition: the Petri multiplication
  alpha: H^0(L) (x) H^0(omega_{C~} (x) L^dual) -> H^0(omega_{C~})
splits under sigma into THREE isotypic blocks; the two nontrivial-character blocks
beta_1, beta_2 (landing in H^0(omega_C (x) eps) and H^0(omega_C (x) eps^2), each of
dim g-1) are the mu_3-Prym-Petri maps.  Test: their ranks at sample L.

## Representation of sections (no function-field package)

Everything is bigraded by the two decks (u-cover of E0, t-cover of C):
  H^0(C~, M) = (+)_{i=0..2, j=0..2} { a(x,y) * u^i * t^j : pole conditions }
with a(x,y) in the function field of E0 (finite-dim spaces L(D_E0) — elliptic RR,
trivial: bases {1, x, y, x^2, xy, ...} by pole order at O).  Pole bookkeeping at the
special fibers comes from the recorded Newton data:
  - v2 curve (g=4): O unramified (3 branches, residual w^3+w+1), 6 simple branch pts;
  - eightfold curve (g=5): O-polygon slopes 1,2; nodes at x^2+x+1=0 (normalize:
    separate branches by the two u-values at each node);
  - t-order: div(t) on C~ = (1/3) pullback of div(y) = places over T minus places
    over O with known multiplicities.
Multiplication: polynomial arithmetic mod (E0 relation, u^3 = -Au - B, t^3 = y);
reduction to the graded basis; all coefficient arithmetic in F_q (q = p, p = 1 mod 3,
good reduction: p not in {2,3,19,31,...} per curve).

## Test T1 (the Welters-analog gate)

1. Sample L in Nm^{-1}(omega_C) subset Pic^{2g-2}(C~): construct as
   L = O(D) with D = (1-sigma)-adjusted effective divisors + a fixed reference
   solving the norm condition; verify Nm L ~ omega_C by RR ranks.
2. Compute h^0(L); keep samples with h^0(L) = 2, 3 (the first strata).
3. Build the full Petri matrix alpha in the graded bases; project to the three
   sigma-blocks (the sigma-action permutes basis monomials by zeta^j on t^j).
4. Record: rank(beta_1), rank(beta_2) vs full rank = dim domain (injectivity);
   repeat over >= 40 samples per stratum, two primes.
PASS = generic injectivity at both primes on all sampled strata (Zariski-openness
then makes one exact-verified point a certificate over F_p-bar, Welters 2.1 style).
FAIL = reproducible rank drop => the mu_3 wall differs from Z/2 — a finding either
way (record which block drops; the epsilon vs epsilon^2 asymmetry is meaningful).

## Test T2 (W_n smoothness statistics)

Sample degree-n effective divisors D on C~(F_q) (n = g-1); compute the AP-fiber
jump statistics: h^0-jumps of the associated (1-sigma)-twisted bundles; estimate
dim of the jumping locus vs expected (empty or codim >= 2 in Sym^n needed for lci
of W_n away from small loci).

## Order of work

1. v2 sixfold curve (g=4, smooth, all data in repo): implement bases + T1.
   Calibration: the sixfold's Weil classes ARE algebraic (Schoen/P-Z), so a healthy
   Petri here is consistent-expected; a sick one would be a red flag for the method.
2. Eightfold curve (g=5, nodes): normalize (branch labels at the two nodes = the
   node-correction bookkeeping already validated in the counting), rerun T1 + T2.
3. Then (W3): assemble the semiregularity matrix of W_n from the same section
   spaces (H^1(N) via Serre duality on the graded pieces; target H^{n+1}(Omega^{n-1})
   explicit on the abelian side via the wedge basis) — decide injectivity numerically
   before attempting any general proof.

Register: numerical ranks at finite places are falsification gates and existence
certificates for Zariski-open conditions (exact linear algebra over F_p = a proof of
nonvanishing at that member); they are NOT the generic-injectivity theorem itself —
that needs the E-H degeneration argument (the W1 theory item) IF the gates pass.
