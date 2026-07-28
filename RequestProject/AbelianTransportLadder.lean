import RequestProject.HodgeCompression

/-!
# The abelian discharge: on abelian specimens the cable narrows to the André gap

The correspondent's ladder (2026-07-27):

    prime-independent spectral projector data
      ⟹ motivated/absolute-Hodge projector
      ⟹ algebraic correspondence          ← "the dangerous step"
      ⟹ transitivity on the Tate block
      ⟹ Hodge conjecture

with the warning that asserting the third step universally would simply rename Hodge.
Correct in general.  **On abelian varieties — which is every specimen in this program:
the fourfold, the sixfold, the eightfold — the dangerous step splits, and both closable
halves close by cited classical theorems:**

* *Hodge ⟹ absolutely Hodge* on abelian varieties: Deligne's theorem (cited).  Our
  transports are Hodge classes on `X × X` (proven, semisimplicity + Künneth/PD dictionary);
  `X × X` is abelian; so the transports are absolutely Hodge FOR FREE.
* *Motivated (with abelian auxiliaries) ⟹ algebraic* on abelian varieties: standard
  conjecture B is a THEOREM for abelian varieties (Lieberman; via the Fourier–Mukai
  transform, Beauville — cited), and products of abelian varieties are abelian, so the
  Lefschetz-involution factor in any motivated presentation over abelian auxiliaries is
  itself algebraic.  This file formalizes exactly that composition:
  `MotivatedPresentation` (an algebraic sandwich around one Lefschetz factor),
  `motivated_stab` (given the B-discharge `hB`, the sandwich preserves algebraicity), and
  `hodge_of_motivated_glue` (motivated transitivity + seed ⟹ the block is algebraic).
  `abelian_cable_iff` states the residue as an equivalence.

**What remains — the single cable on the abelian class, narrowed:** manufacture a
MOTIVATED presentation (abelian auxiliaries) of the Tate-block transports from the glue
data — i.e. *absolutely Hodge ⟹ motivated* for this one operator class.  That is the
André gap, NOT the whole conjecture: strictly weaker than manufacturing the cycle
outright (the algebraicity of the Lefschetz factor is already banked), and it is the one
rung of the ladder with known nontrivial successful instances (André's motivated theory:
the Kuga–Satake correspondence, CM classes — cited at use).  The `glue` hypothesis below
types it; nothing asserts it.

Register: `hB` enters as a hypothesis so the theorems are exact; on abelian specimens it
is supplied by the cited theorem (B(AV)), on general `X` it is open — the file never
blurs the two.  Scope: does not assume or prove the Hodge conjecture.  No `sorry`,
no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {H : Type*} [AddCommGroup H] [Module ℚ H]

/-- **A motivated presentation** of an operator: an algebraic sandwich around one
Lefschetz-involution factor — the abstract shape of André's `pr_*(α ∪ *_L β)` with the
algebraic pieces as the bread and the Lefschetz factor isolated.  The auxiliaries-abelian
condition lives in the register: on abelian specimens the `lef` factor is algebraic by
B(AV) (Lieberman; Beauville–Fourier–Mukai), supplied to the theorems as `hB`. -/
structure MotivatedPresentation (Alg : Submodule ℚ H) (f : H → H) where
  /-- The incoming algebraic piece. -/
  pre : H → H
  /-- The Lefschetz-involution factor — algebraic on abelian varieties (cited), open in
  general. -/
  lef : H → H
  /-- The outgoing algebraic piece. -/
  post : H → H
  /-- The factorization. -/
  factor : f = post ∘ lef ∘ pre
  /-- The incoming piece preserves algebraicity. -/
  pre_alg : ∀ x ∈ Alg, pre x ∈ Alg
  /-- The outgoing piece preserves algebraicity. -/
  post_alg : ∀ x ∈ Alg, post x ∈ Alg

/-- **The B-discharge**: given algebraicity of the Lefschetz factor (`hB` — a THEOREM on
abelian varieties, an open conjecture in general), a motivated operator preserves
algebraicity.  Composition, made exact. -/
theorem motivated_stab {Alg : Submodule ℚ H} {f : H → H}
    (P : MotivatedPresentation Alg f)
    (hB : ∀ x ∈ Alg, P.lef x ∈ Alg) :
    ∀ x ∈ Alg, f x ∈ Alg := by
  intro x hx
  rw [P.factor]
  exact P.post_alg _ (hB _ (P.pre_alg x hx))

/-- **The abelian ladder, assembled**: if every needed transport admits a motivated
presentation whose Lefschetz factor is B-discharged (the `glue` hypothesis — the single
remaining cable on the abelian class), then with the free seed the whole Tate block is
algebraic. -/
theorem hodge_of_motivated_glue
    (Alg T : Submodule ℚ H)
    (glue : ∀ w₀ ∈ T, w₀ ≠ 0 → ∀ w ∈ T, ∃ f : H → H,
      (∃ P : MotivatedPresentation Alg f, ∀ x ∈ Alg, P.lef x ∈ Alg) ∧ f w₀ = w)
    (F : H) (hF : F ∈ Alg) (hFT : F ∈ T) (hFne : F ≠ 0) :
    T ≤ Alg :=
  block_closed_of_algebraic_transport Alg T
    {f | ∃ P : MotivatedPresentation Alg f, ∀ x ∈ Alg, P.lef x ∈ Alg}
    (fun _ hf => motivated_stab hf.choose hf.choose_spec)
    glue F hF hFT hFne

/-- **The cable, as an equivalence on the abelian class**: given the splitting and the
free seed, the block is algebraic IF AND ONLY IF the needed transports admit B-discharged
motivated presentations.  Forward: an algebraic block makes every transport trivially
motivated (identity Lefschetz factor).  Backward: the assembled ladder.  The residue of
the Hodge conjecture for an abelian specimen is exactly the `glue` side — absolutely
Hodge ⟹ motivated, for one operator class. -/
theorem abelian_cable_iff
    (Alg T N : Submodule ℚ H) (hcompl : IsCompl T N)
    (F : H) (hF : F ∈ Alg) (hFT : F ∈ T) (hFne : F ≠ 0) :
    T ≤ Alg ↔
      ∀ w₀ ∈ T, w₀ ≠ 0 → ∀ w ∈ T, ∃ f : H → H,
        (∃ P : MotivatedPresentation Alg f, ∀ x ∈ Alg, P.lef x ∈ Alg) ∧ f w₀ = w := by
  constructor
  · intro hT w₀ hw₀ hne w hw
    obtain ⟨f, hfmem, hfw⟩ := transport_exists T N hcompl w₀ hw₀ hne w hw
    obtain ⟨g, hgf, hgT, -⟩ := hfmem
    refine ⟨f, ⟨⟨f, id, id, rfl, ?_, fun x hx => hx⟩, fun x hx => hx⟩, hfw⟩
    intro x _
    rw [← hgf]
    exact hT (hgT x)
  · intro glue
    exact hodge_of_motivated_glue Alg T glue F hF hFT hFne

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.motivated_stab
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.hodge_of_motivated_glue
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.abelian_cable_iff
