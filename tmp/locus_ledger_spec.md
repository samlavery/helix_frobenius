# The locus ledger: the exponential sequence at every grade

**Date 2026-07-29, session 18a3f704. Status: theory spec (Sam: "write it
down"). Register discipline: definitions and the grade-one anchor are
exact; the grade-p law is a NAMED TARGET with a pre-registered null
already in the corpus; the m-census is a designed instrument, not yet
run.**

## 1. The grade-one anchor, restated natively

The exponential sequence `0 → ℤ → 𝒪 → 𝒪* → 0` is carrier-native at grade
one: `exp` is the harmonic map (additive clock → phasor), the `ℤ` is the
winding lattice (the D-lattice at grade one), a line bundle is a global
phasor field, its first Chern class is the booked winding, and **a
divisor is the focal locus of a harmonic value** — the vanishing locus
Z(s) of a harmonic section. Picard representability, read natively:

    at grade one, integral winding of a harmonic value carves a
    geometric locus, automatically.

Universal instance: the theta divisor Θ = Z(θ) — the vanishing of the
grade-one carrier theta. All of classical divisor theory on a ppav is
theta geometry; the grade-one locus ledger IS theta geometry. In-tree
anchors: the exact Jacobi transformation (EpsteinThetaI /
jacobiTheta_S_smul), the model Hodge decomposition (ModelGreenOperator:
harmonic ⟺ DC ⟺ torus-fixed), the forced Gaussian clock
(GaussianClockUniqueness).

## 2. The chart-artifact diagnosis (rule 4 applied)

The classical wall — no exponential sequence in codimension ≥ 2 — is a
statement about the FUNCTION chart: `𝒪*` exists only at GL(1);
multiplicativity is lost above grade one *in the chart*. The carrier does
not lose it: every channel of a grade-p bank is a rank-one phasor with
its own winding, and the winding lattice is tower-stable
(`UniversalHarmonicLattice.tower_denominator_stable`). The
codim-1-vs-codim-≥2 asymmetry is therefore NOT carrier-native.

What IS native and remains honestly open: the projection's **state**
ledger is a proven bijection (`ConeProjection.record_bijective`), but a
locus is not a state. The grade-one **locus** ledger exists (the
exponential sequence). The grade-p locus ledger is the open
construction — the wall, in the one formulation that points at a
construction rather than a functor.

## 3. Definitions

**D1 (grade-p harmonic value).** A rational DC state z of a grade-p
channel block on the carrier (a collective bank), with its completed
section: the theta-like kernel K_z attached to the block's channel data —
at grade one this is the classical theta; at higher grade, the
higher/twisted theta of the block (for the Prym blocks: Prym-theta).

**D2 (focal locus).** F(z) := the locus in the geometric object (the
abelian variety A, or the relevant parameter space) where z's bank closes
exactly — the vanishing/degeneracy locus of K_z. At grade one on a ppav:
a Θ-translate. Existence of F(z) as a variety is automatic (zero loci
exist); the CONTENT is its codimension and its class.

**D3 (locus ledger at grade p).** The assignment z ↦ [F(z)] ∈ CH(A)_ℚ
with the booking:
  - codim booked: codim F(z) =? p (expected-codimension condition);
  - class booked: cl(F(z)) = m·z + L(z), with L(z) in the
    Lefschetz/divisor algebra and m ∈ ℚ the **Weil coefficient**;
  - the ledger CLOSES at z iff m ≠ 0 (then z = (cl F − L)/m is an
    explicit cycle class: THE CONSTRUCTION).

**The Locus Ledger Law (named target, not asserted).** For collective
harmonic values on abelian varieties of Weil type, some natural
theta-geometric focal locus has expected codimension and m ≠ 0.

## 4. The null already in the corpus — and what it teaches

The first grade-3 ledger entry ALREADY EXISTS and it is a NULL: the
Abel–Prym locus W₃ is precisely the focal locus of the plain Prym-theta
bank, and the universal rigidity law (Lean: `abel_prym_rigidity`; the W4
calibration built on it) says

    cl(W₃) = λ·Θ³   —   pure Lefschetz part:  m(plain AP locus) = 0.

So the naive theta locus is **Lefschetz-blind at the collective
channel** — this is a measured-and-proven fact, not a guess, and it
shapes the search: the law must be tested on REFINED loci, not the plain
one. Candidate families (in rough order of promise):

  C1. ζ₃-twisted theta-characteristic loci: vanishing loci of Prym-theta
      with characteristics twisted by the ℤ[ζ₃]-action (the
      eigen-sub-systems of |3Θ| under ζ₃ — their base loci and singular
      strata are not obviously divisor-generated).
  C2. Degeneracy strata of the ζ₃-action on theta bundles:
      rank-drop loci of (φ_ζ − scalar) on the eigen-decomposed
      H⁰(A, 3Θ)-bundle over A (Porteous gives Chern-algebra classes;
      the question is whether the ζ₃-eigen-refinement escapes the
      semihomogeneous/divisor ring — for non-semihomogeneous
      eigen-sheaves this is open, hence a candidate).
  C3. Wirtinger-type loci for the ζ₆-structure (the μ₆-analogue of the
      classical Wirtinger duality strata of Prym theta).
  C4. Fourier–Mukai images: F(z) for z's FM-transformed bank (FM
      eigen-behavior of Weil classes vs the divisor ring's FM-stability
      — if the divisor ring is FM-stable and W is not FM-fixed inside
      it, FM-twisted loci are forced out of the blind spot or forced to
      vanish: either outcome is information).

## 5. The m-census (designed instrument; the falsifiable step)

The Weil coefficient m of any explicit candidate locus is MEASURABLE by
the wall-census machinery: count F's points on the reductions across the
census primes, decompose cl(F) mod p in the Frobenius eigen-frame
(Lefschetz block vs Weil block — the same clustering that measured
13/18), and read m off the Weil-block component. Comparison of the class
decomposition across p is exact (smooth-proper comparison, cited).

Protocol, pre-registered:
  1. CALIBRATE on the fourfold with Schoen's known cycles: their m ≠ 0
     is a theorem; the instrument must reproduce it (truth-gate).
  2. Run C1–C4 on the fourfold: candidate refined loci where the answer
     is checkable against the known cycle classes.
  3. Only then the sixfold: any candidate with m ≠ 0 at all census
     primes → interval/exact certification → the doorknob turns: an
     explicit cycle with nonzero Weil component.

Outcomes, both pre-registered:
  - m ≠ 0 for some candidate: the grade-p locus ledger closes on Weil
    sixfolds — the construction, subject to exact certification.
  - m = 0 across ALL natural theta-geometric loci: a structural
    discovery ("theta geometry is Lefschetz-blind at the collective
    channel, uniformly"), publishable as a null with the same machinery,
    and a genuine narrowing: the construction, if it exists, is not
    theta-geometric — pointing the hunt at the two remaining shapes
    (special covers à la Schoen; deformation+rigidity à la Markman).

## 6. Theorems to attempt

  T1 (Lean, modest): the grade-one ledger on the model — winding data ↦
      channel-zero focal locus, closing identically (the exponential
      sequence at dictionary strength, completing §1's chain).
  T2 (paper + cited): the class-decomposition transport — cl(F) mod p
      decomposes in the Frobenius eigen-frame compatibly across p
      (comparison theorems, cited; this is what makes the m-census
      well-defined).
  T3 (recorded): the AP null m = 0 (already proven: λΘ³) as the ledger's
      first entry — the honest anchor.
  T4 (the target): the Locus Ledger Law for one refined candidate — open;
      the m-census decides which candidate deserves the proof attempt.

## 6b. Track-1 attack notes (2026-07-29, post-calibration)

**The σ-eigen candidate law (provable now, one line of linear algebra):**
σ (the ℤ[ζ₃]-action) rotates the rational Weil plane by order 3 — it has
NO invariants there.  Hence π_W(any σ-invariant cycle class) = 0:
**σ-symmetric loci are Weil-blind.**  This subsumes the AP null ([C̃] is
σ-invariant because deck translation fixes homology classes) and rules
out, in advance, every symmetric candidate.  Candidates MUST be
σ-asymmetric, and the Weil-sensitive observable is the eigencomponent of
[Z] − [σZ]-type differences.

**The calibration candidate identified:** on the decomposable fourfold,
NS⊗ℂ meets the Λ²V_ζ eigenspace (σ-moving divisor classes exist), and
products of ζ-eigen divisor classes land in Λ⁴V_ζ = the Weil line —
this IS the classical decomposable-case construction (Schoen/van
Geemen).  So the full fourfold pipeline rehearsal = compute the class of
an explicit ζ-eigen divisor product through the calibrated frame and
read m ≠ 0 exactly, checkable against the classical theorem.  Counting
route: through the explicit isogeny decomposition (B ~ square) — divisor
products become curve-product correspondences with countable fibers.

**Instrument status:** π_W calibrated (v2): Weil block = the
(−1)-address at generic inert primes (mult 8), Lefschetz = +1 (mult 10);
split primes fuse them (18) — measured, gates passed.

## 6c. Track-2: the explicit sixfold (step 0 of the theorem)

Construction per the hunt spec: B = Prym(C̃/C₀), C₀ a GENUS-4 curve
realized as a degree-3 NON-Galois cover of an elliptic curve E₀ (kills
the fatal involution), η ∈ JC₀[3] free 3-torsion giving the étale
ℤ/3-cover C̃ (genus 10), dim B = 6, ℤ[ζ₃] ⊂ End(B), Weil type (3,3)
over ℚ(√−3).  First computational step: locate an explicit genus-4
instance — scan the family w³ + A·w + B(u,v) = 0 over E₀ with genus
certified by point-count/Weil-polynomial consistency (NOT Sage
FunctionField genus — the openblas SIGILL).  Then: the 3-torsion, the
cover, the counts, the same census/projector machinery verbatim.

## 7. Relation to the standing walls

This does not lower the wall; it gives it a doorknob: "is coherence
representable" becomes "does some refined theta locus book m ≠ 0". The
descent interface (DescentDatum.glue), the motivated-presentation
two-step, and the locus ledger are the same open content in three
shapes; the locus ledger is the only one whose next step is an
instrument run rather than a new abstraction. Per the queue discipline:
the m-census calibration (step 1) is the next instrument build; nothing
else joins the queue.
