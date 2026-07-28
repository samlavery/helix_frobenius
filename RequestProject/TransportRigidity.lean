import Mathlib
import RequestProject.NonabelianCable

/-!
# Transport rigidity: the overdetermined system and the two-sided squeeze

The correspondent's chosen program (2026-07-27): *"You don't explicitly construct the
object — you prove that any object satisfying enough independent constraints is forced to
be unique."*  This file formalizes the rigidity skeleton at its exact strength.

Let `C` be the space of transport operators satisfying the compatibility stack — Hodge
(morphism of Hodge structures), Frobenius (Galois-equivariance of the ℓ-adic
realization), polarization — and `Aalg` the span of the algebraic transports.  Three
registers:

1. `Aalg ≤ C` — algebraic correspondences satisfy every compatibility (cited, standard;
   the easy inclusions).
2. `finrank C` is bounded ABOVE by finite computation: `C` embeds into the
   Frobenius-fixed part of the transport Künneth block of `X × X`; the commutant of
   finitely many Frobenii is computed exactly from census eigenvalue data, is monotone
   decreasing in the prime set, and converges to the true Galois commutant by Chebotarev.
   This uses the comparison bridge in its EASY, theorem-backed direction (characteristic
   zero into characteristic `p` as a constraint), not the hard construction direction
   that gates the glue.  The house occupancy/`multW` machinery already computes these
   bounds.
3. `finrank Aalg` is bounded BELOW by exhibiting correspondences — the known-cycle side.

* `rigidity_squeeze` — if the bounds MEET (`finrank C ≤ finrank Aalg`), then `C = Aalg`:
  every compatible transport is algebraic.  Pure squeeze.
* `hodge_of_transport_rigidity` — the meet, plus the Deligne register on abelian
  specimens (Hodge transports are absolutely Hodge, hence Galois-invariant, hence in `C`
  — the typed field `hodgeInC`), plus the free seed, close the block: **a specimen's
  Hodge conjecture closes by finite computation the moment the census upper bound
  touches the known-correspondence lower bound.**  No cycle is constructed anywhere in
  the closing step.

**The falsifier register, pre-committed**: if the bounds stabilize APART, the gap
`finrank C − finrank Aalg` is a measured integer — the number of phantom compatible
transports; on the non-split sixfold the expected gap is `2` unless a Weil-sensitive
cycle exists.  Either outcome is information: meet ⟹ theorem; stable gap ⟹ the
conjecture's residue displayed as a number, per specimen.

**Honesty note**: per specimen, "the bounds meet" is equivalent to a Tate-block
algebraicity statement on `X × X` — rigidity is not a free lunch.  What distinguishes it
from "assume every projector is algebraic" is epistemic access: the hypothesis is a
NUMBER MEET between two convergent, independently computable estimators, checkable and
falsifiable prime by prime, and its failure mode is itself a measurement.  Scope: does
not assume or prove the Hodge conjecture; the meet is consumed, never asserted.
No `sorry`, no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {H : Type*} [AddCommGroup H] [Module ℚ H]

/-- **The rigidity squeeze**: if the compatible-transport space contains the algebraic
transport algebra (theorem-backed inclusions) and the census upper bound on its
dimension meets the known-correspondence lower bound, the two spaces coincide — every
compatible transport is algebraic.  Overdetermination, made exact. -/
theorem rigidity_squeeze [FiniteDimensional ℚ H]
    (Aalg C : Submodule ℚ (H →ₗ[ℚ] H))
    (hsub : Aalg ≤ C)
    (hmeet : Module.finrank ℚ C ≤ Module.finrank ℚ Aalg) :
    C = Aalg :=
  (Submodule.eq_of_le_of_finrank_le hsub hmeet).symm

/-- **Hodge from the meet**: on a specimen where (i) the compatibility stack contains the
algebraic transports (`hsub`, cited), (ii) the census upper bound meets the known lower
bound (`hmeet` — THE rigidity field, a finite computation), (iii) Hodge-shaped transports
satisfy the compatibilities (`hodgeInC` — on abelian specimens this is Deligne's
absolutely-Hodge theorem plus comparison, cited; open in general), and (iv) algebraic
transports preserve algebraicity (`stab`, cited), the free seed closes the whole block.
**The closing step constructs no cycle: it is a squeeze between two measured numbers.** -/
theorem hodge_of_transport_rigidity [FiniteDimensional ℚ H]
    (Alg T N : Submodule ℚ H) (hcompl : IsCompl T N)
    (Aalg C : Submodule ℚ (H →ₗ[ℚ] H))
    (hsub : Aalg ≤ C)
    (hmeet : Module.finrank ℚ C ≤ Module.finrank ℚ Aalg)
    (hodgeInC : ∀ g : H →ₗ[ℚ] H, (∀ x, g x ∈ T) → (∀ x ∈ N, g x = 0) → g ∈ C)
    (stab : ∀ g ∈ Aalg, ∀ x ∈ Alg, g x ∈ Alg)
    (F : H) (hF : F ∈ Alg) (hFT : F ∈ T) (hFne : F ≠ 0) :
    T ≤ Alg := by
  have hCA : C = Aalg := rigidity_squeeze Aalg C hsub hmeet
  refine block_closed_of_algebraic_transport Alg T (hodgeTransport T N) ?_
    (hodge_block_irreducible T N hcompl) F hF hFT hFne
  rintro f ⟨g, rfl, hgT, hgN⟩ x hx
  have hgC : g ∈ C := hodgeInC g hgT hgN
  rw [hCA] at hgC
  exact stab g hgC x hx

/-- **The phantom count**: when the bounds stabilize apart, the gap is the measured
integer residue of the conjecture on the specimen — zero iff rigidity holds.  Stated so
the falsifier register has a name: the census's output is `finrank C − finrank Aalg`,
and `hodge_of_transport_rigidity` consumes exactly the statement that it is zero. -/
noncomputable def phantomCount (Aalg C : Submodule ℚ (H →ₗ[ℚ] H)) : ℕ :=
  Module.finrank ℚ C - Module.finrank ℚ Aalg

/-- The meet, restated through the phantom count: rigidity is exactly
`phantomCount = 0`. -/
theorem meet_iff_phantomCount_eq_zero
    (Aalg C : Submodule ℚ (H →ₗ[ℚ] H)) :
    Module.finrank ℚ C ≤ Module.finrank ℚ Aalg ↔ phantomCount Aalg C = 0 := by
  unfold phantomCount
  omega

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.rigidity_squeeze
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.hodge_of_transport_rigidity
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.meet_iff_phantomCount_eq_zero
