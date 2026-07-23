# W2 spec: consume W1 at g = 4 (2026-07-19)

Goal: deformation control of the Abel-Prym cycle in the sixfold Prym,
feeding W3 (semiregularity matrix) and W4.  Work items:

(i)   IDENTIFY the depth-one locus V^1 = {L in Nm^{-1}(omega): h^0 >= 1}
      (dim expected g-1 = 3, middle-dimensional in the 6-dim torsor) with
      (a translate of) the Abel-Prym threefold W_3 — or determine the true
      relation.  This is the mu_3 analogue of the Z/2 Prym-BN geometry
      (Welters/dJ-circle "Geometry of BN loci on Prym varieties").
(ii)  W1 => V^1 smooth of dim 3 at every depth-one point: T_L V^1 =
      ann(Im beta-bar), codim = rank beta-bar = g-1 (write the standard
      determinantal tangent-space lemma in the Prym-torsor properly).
(iii) V^2 = {h^0 >= 2}: expected dim 0 (the h=2 dimensional balance) =>
      W_3 has isolated singularities at general (C, eps); lci status of
      the AP-cycle to be settled for Bloch semiregularity.
(iv)  H^1(N_{V^1 | torsor}) via the same section spaces (W3's input).

INSTRUMENT PREREQUISITE (this file's sibling script): the old tower is
thetanull BY CONSTRUCTION — in the trinomial normal form u^3 + xu + B the
derivative F_u = 3u^2 + x has all poles on the O-fiber, div(F_u) =
R - 2*(O-fiber), hence omega = O(R) ~ 2N identically.  No coefficient
tweak in that normal form escapes.  ESCAPE = bielliptic specimen:
  C: u^2 = h(x,y) over E0 (h in L(6O), 6 simple branch zeros, genus 4),
  C~: t^3 = y on top (etale mu_3; eps = pi*[T-O] != 0 GUARANTEED:
  ker(pi*) for a double cover is 2-torsion, coprime to 3).
Closed-form canonical: H^0(omega_C) = < omega0, omega0/u, x omega0/u,
y omega0/u >, canonical map [u : 1 : x : y], canonical quadric
z0^2 = Q(z1,z2,z3) where u^2 = h reduces mod the E0 relation
(x^3 = y^2+2xy+y) to a quadratic form Q in (1, x, y).  NON-THETANULL
CERTIFIED ALGEBRAICALLY: rank(Q) = 3 <=> quadric rank 4 <=> two distinct
trigonal pencils (the two rulings, explicit!).  Positive control for
Lemma C: colliding W over trigonal fibers must now give NO kernel jump
(h^0(omega - E_0) = 1 since omega - 2N = the OTHER ruling class - N != 0).

Order of work: 1. specimen scan + gates (4/3/3 certifies genus 4 AND
connected C~ i.e. eps != 0).  2. depth-one battery on the specimen
(expect 100% injective INCLUDING constructed collisions — Lemma C acting
positively).  3. V^1 point-count / tangent-rank probes over F_7 (dim-3 +
smoothness read).  4. The (i)/(ii) write-ups.

STATUS 2026-07-19: step 1 DONE (tmp/w2_specimen.sage).
  SPECIMEN: h = -2x^3 + x^2 - xy + 3x + 1 over E0/F_7;
  Q = x^2 + 2xy - 2y^2 + 3x - 2y + 1, rank 3 => canonical quadric rank 4:
  NON-THETANULL CERTIFIED (algebraic, closed-form, no sampling);
  gates [4,3,3] pass => genus 4 + connected etale mu_3 + eps != 0.
  Engine notes: conditions needed at T/T'-places too (p<0 monomials);
  j=2 eigenspace needs pool down to x^-2.  Two structural facts found en
  route: (a) the OLD tower is thetanull STRUCTURALLY (trinomial form
  forces omega = 2N via div(F_u) = R - 2*O-fiber) — no coefficient tweak
  escapes; (b) for the bielliptic specimen omega - 2N = the difference of
  the two rulings, nonzero by rank-4.
  NEXT: step 2 — port the petri battery (L-configs + alpha/beta blocks)
  to the bielliptic tower; then the trigonal-collision positive control.

STATUS 2026-07-19 (later): step 2 DONE (tmp/w2_battery.sage).  100-config
O-family battery (splittings (a|b), sum 3 per u-branch, pi~_* = 3O+ + 3O-):
  * chi-check h0M = h0L + 3 in ALL 100 configs;
  * ALL 54 depth-one configs: rank beta-bar = 3, ker = T exactly.
    Lemma-A failures: ZERO.  W1 machine-validated POSITIVELY on a curve
    where it applies (first time — the old tower was on the excluded locus);
  * the structural bielliptic bad config ((1,1,1)^2, moving pencil
    E = 2O+ + 2O-, pred_ker 2) sits at h^0(L) = 3 — far outside the
    depth-one stratum, as hand-predicted ({1,t,...} in L(D~)).  VERDICT:
    SPECIMEN DEPTH-ONE-CLEAN.  With the thetanull tower's constructed
    failure, the instrument has now seen BOTH sides of the theorem's
    boundary.
  * h=2 data logged: rank 5 of 10 (kernel 5 > forced 4) — input for the
    h>=2 extension theory.
  * Engine trap fixed: M-space allowance must be v(A/u) >= mult (NOT
    3-mult; eta regular everywhere + vanishing on D~); symptom h0M = 21.
  * Discovery en route: on bielliptic curves the Lemma-C bad datum exists
    STRUCTURALLY (E = 2O+ + 2O- moves in pi*|2O|, K = 3(O+ + O-)
    canonical); covers of elliptic curves are chronically Lemma-C-special.
    (1,1,1)^2-configs over 3-torsion fibers are the ONLY torsor-valid bad
    shapes (reduced pencil profiles fail Z1 degree arithmetic).  The
    program's deliberate elliptic-cover specimens live on/near excluded
    loci; W1 covers the general member, which is what W4's propagation
    uses.  ALSO: the 2-of-3-preimage trigonal-collision W has Nm = 2N,
    only canonical on thetanull curves — the "control" is that no such L
    exists in the torsor on the specimen (checked by class arithmetic).
NEXT (step 3): V^1 probes — tangent-rank = beta-rank at sampled depth-one
points is ALREADY the smoothness read (all rank 3 = smooth dim 3); remaining:
V^1 <-> W_3 identification write-up + the tangent lemma (spec items i, ii).
