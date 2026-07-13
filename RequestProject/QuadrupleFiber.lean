import RequestProject.CompletedReflectionFiber
import RequestProject.StrandExchange

/-!
# The primitive quadruple's degree-16 fiber: carrier niceness by tensor composition

Grade 4's object is the primitive quadruple `M = H¹(E₁) ⊗ H¹(E₂) ⊗ H¹(E₃) ⊗ H¹(E₄)` —
the first unnamed rung: degree 16, four pairwise-distinct elliptic curves, unitarised so
each `H¹(Eᵢ)` carries the unit Satake conjugate pair `{αᵢ, αᵢ⁻¹}`.  Its admissible fiber
is **not a new construction**: it is the iterated Rankin–Selberg tensor
`tensorFiber (tensorFiber W₁ W₂) (tensorFiber W₃ W₄)` of four degree-2 fibers, and the
whole carrier-niceness package of `FiniteWeightFiber` transports through the composition
verbatim — the rung-4 campaign's Lean brick (ii), closed here as the "nearly free"
composition it was priced as.

* `quadFiber` / `quadFiber_weight` — the 4-fold tensor fiber on the product index, weights
  the 4-fold products `λᵢμⱼνₖρₗ`, duality the product involution;
* `quadFiber_det_one` — the determinant/modulus ledger of the quadruple: `∏ weights = 1`;
* `quadFiber_localPoly_reciprocal` — the per-place functional equation of the quadruple's
  local numerator, exponent the product of the four degrees;
* `quadFiber_warp_det_one` — the quadruple survives every dual-compatible unit warp
  (the converse-theorem twist family), keeping its ledger;
* `quadCompleted` / `quadCompleted_FE` — the quadruple's admissible **local** completed
  reflection `Λ(s) = (εfin·εarch)(s)·Λ^∨(1-s)`, step (1) of `prop:completedFE`, by
  `fiberCompleted` at the composed fiber;
* `quadBank_exchange` / `quadCompletedBank_exchange` — the global strand exchange
  `E*(z̄) = ε·E(z)`, `‖ε‖ = 1`, of the finite bank over the quadruple's weight channels
  (bare and completed), step (2)'s finite stage, by `StrandExchange` at the composed fiber;
* `curveFiber` / `curveQuadFiber` — the concrete primitive quadruple: four unitarised
  `H¹` fibers (`symFiber 1`, the degree-2 conjugate pair), tensored;
* `curveQuadFiber_card` — the composed index has cardinality **16**;
* `curveQuadFiber_det_one` / `curveQuadFiber_localPoly_reciprocal` — ledger and per-place
  FE of the degree-16 fiber, reflection exponent `(-X)^16` explicit;
* `curveQuadCompleted` / `curveQuadCompleted_FE` / `curveQuadCompleted_εfin` — the
  degree-16 completed local reflection, with reflection factor `(-(c^{s-1/2}))^16`.

**Scope.**  Everything here is the finite/per-place algebra and the finite-stage bank of the
degree-16 fiber: fiber admissibility packaged at the completed-object level (step (1)) and the
finite-bank conjugation exchange (step (2)'s finite stage).  The **global** `L`-function of
the quadruple is *not* claimed — the infinite-bank limit and the arithmetic identification
(`prop:localid` for this fiber: conductor `(11·37·53·61)⁸`, the global root number `ε = +1`,
provisional in the ledger) are the campaign's separate targets, not consumed and not proven
here.  The coefficient-level continuation input is fiber-independent
(`TransferContinuation.transfer_analytic`) and needs no quadruple instance.  Nothing here
assumes or proves RH/GRH, Beilinson–Bloch, or the Hodge conjecture.  No `axiom`, no `sorry`.
-/

open Complex Finset
open scoped BigOperators

namespace CriticalLinePhasor.QuadrupleFiber

open CriticalLinePhasor.FiniteWeightFiber

variable {ι₁ ι₂ ι₃ ι₄ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] [Fintype ι₄]

/-- **The 4-fold tensor fiber**: the primitive quadruple's fiber shape, as the iterated
Rankin–Selberg tensor `(W₁ ⊗ W₂) ⊗ (W₃ ⊗ W₄)` of four finite duality-stable weight fibers.
No new construction: two applications of `tensorFiber`. -/
def quadFiber (W₁ : FiniteWeightFiber ι₁) (W₂ : FiniteWeightFiber ι₂)
    (W₃ : FiniteWeightFiber ι₃) (W₄ : FiniteWeightFiber ι₄) :
    FiniteWeightFiber ((ι₁ × ι₂) × (ι₃ × ι₄)) :=
  tensorFiber (tensorFiber W₁ W₂) (tensorFiber W₃ W₄)

/-- The quadruple's weights are the 4-fold products `λᵢ·μⱼ·νₖ·ρₗ` — the Satake data of
`H¹(E₁) ⊗ H¹(E₂) ⊗ H¹(E₃) ⊗ H¹(E₄)` read channel by channel. -/
theorem quadFiber_weight (W₁ : FiniteWeightFiber ι₁) (W₂ : FiniteWeightFiber ι₂)
    (W₃ : FiniteWeightFiber ι₃) (W₄ : FiniteWeightFiber ι₄)
    (p : (ι₁ × ι₂) × (ι₃ × ι₄)) :
    (quadFiber W₁ W₂ W₃ W₄).weight p
      = W₁.weight p.1.1 * W₂.weight p.1.2 * W₃.weight p.2.1 * W₄.weight p.2.2 :=
  (mul_assoc _ _ _).symm

/-- **The quadruple's determinant/modulus ledger**: the product of the sixteen (in general,
`|ι₁|·|ι₂|·|ι₃|·|ι₄|`) weights is one — `fiber_det_one` transported through the composition,
for free. -/
theorem quadFiber_det_one (W₁ : FiniteWeightFiber ι₁) (W₂ : FiniteWeightFiber ι₂)
    (W₃ : FiniteWeightFiber ι₃) (W₄ : FiniteWeightFiber ι₄) :
    ∏ p, (quadFiber W₁ W₂ W₃ W₄).weight p = 1 :=
  (quadFiber W₁ W₂ W₃ W₄).fiber_det_one

/-- The composed index counts as the product of the four degrees. -/
theorem quadFiber_card :
    Fintype.card ((ι₁ × ι₂) × (ι₃ × ι₄))
      = Fintype.card ι₁ * Fintype.card ι₂ * Fintype.card ι₃ * Fintype.card ι₄ := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, ← mul_assoc]

/-- **The quadruple's per-place functional equation**: the local numerator of the 4-fold
tensor is self-reciprocal, `localPoly X = (-X)^{d₁d₂d₃d₄} · localPoly X⁻¹` —
`localPoly_reciprocal` transported through the composition, for free. -/
theorem quadFiber_localPoly_reciprocal (W₁ : FiniteWeightFiber ι₁)
    (W₂ : FiniteWeightFiber ι₂) (W₃ : FiniteWeightFiber ι₃) (W₄ : FiniteWeightFiber ι₄)
    {X : ℂ} (hX : X ≠ 0) :
    (quadFiber W₁ W₂ W₃ W₄).localPoly X
      = (-X) ^ (Fintype.card ι₁ * Fintype.card ι₂ * Fintype.card ι₃ * Fintype.card ι₄)
        * (quadFiber W₁ W₂ W₃ W₄).localPoly X⁻¹ := by
  rw [(quadFiber W₁ W₂ W₃ W₄).localPoly_reciprocal hX, quadFiber_card]

/-- **The quadruple survives every dual-compatible unit warp**: warping the composed fiber
by any unit amplitude respecting its (product) duality keeps the determinant ledger — the
functional equation survives the whole converse-theorem twist family at degree 16, exactly
as at degree 2 (`warpFiber_det_one`, for free). -/
theorem quadFiber_warp_det_one (W₁ : FiniteWeightFiber ι₁) (W₂ : FiniteWeightFiber ι₂)
    (W₃ : FiniteWeightFiber ι₃) (W₄ : FiniteWeightFiber ι₄)
    (A : DualWarp (quadFiber W₁ W₂ W₃ W₄)) :
    ∏ p, ((quadFiber W₁ W₂ W₃ W₄).warpFiber A).weight p = 1 :=
  warpFiber_det_one _ A

/-- **The quadruple's completed local reflection** (step (1) of `prop:completedFE` for the
grade-4 fiber): `fiberCompleted` at the composed fiber — completed object `Λ = γ·L` with
finite part the quadruple's local numerator at the reflecting variable `c^{s-1/2}` and
completion the self-dual clock. -/
noncomputable def quadCompleted (W₁ : FiniteWeightFiber ι₁) (W₂ : FiniteWeightFiber ι₂)
    (W₃ : FiniteWeightFiber ι₃) (W₄ : FiniteWeightFiber ι₄)
    (c : ℂ) (hc : c ≠ 0) (β : ℂ) (ℓ : ℝ) : CompletedReflection :=
  fiberCompleted (quadFiber W₁ W₂ W₃ W₄) c hc β ℓ

/-- **The quadruple's completed local reflection FE**: `Λ(s) = (εfin·εarch)(s)·Λ^∨(1-s)` for
the composed degree-`d₁d₂d₃d₄` fiber — the finite reflection is
`quadFiber_localPoly_reciprocal`, the completion self-duality is the self-dual clock, and the
assembly is `CompletedReflection.completed_FE`.  This certifies the quadruple's fiber
admissibility; the **global** `L`-function FE of the quadruple is not claimed here. -/
theorem quadCompleted_FE (W₁ : FiniteWeightFiber ι₁) (W₂ : FiniteWeightFiber ι₂)
    (W₃ : FiniteWeightFiber ι₃) (W₄ : FiniteWeightFiber ι₄)
    (c : ℂ) (hc : c ≠ 0) (β : ℂ) (ℓ : ℝ) (s : ℂ) :
    (quadCompleted W₁ W₂ W₃ W₄ c hc β ℓ).Λ s
      = ((quadCompleted W₁ W₂ W₃ W₄ c hc β ℓ).εfin s
          * (quadCompleted W₁ W₂ W₃ W₄ c hc β ℓ).εarch s)
        * (quadCompleted W₁ W₂ W₃ W₄ c hc β ℓ).Λdual (1 - s) :=
  CompletedReflection.completed_FE _ s

/-- **The quadruple's strand exchange** (step (2), finite stage): the finite bank over the
composed fiber's weight channels obeys `E*(z̄) = ε·E(z)` with `‖ε‖ = 1` — the clock faces are
the quadruple's weights, unit by the composed `unit` field, so `bankProduct_exchange` applies
for free. -/
theorem quadBank_exchange (W₁ : FiniteWeightFiber ι₁) (W₂ : FiniteWeightFiber ι₂)
    (W₃ : FiniteWeightFiber ι₃) (W₄ : FiniteWeightFiber ι₄)
    (ℓ : (ι₁ × ι₂) × (ι₃ × ι₄) → ℝ) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z : ℂ,
      (starRingEnd ℂ) (StrandExchange.bankProduct Finset.univ
          (quadFiber W₁ W₂ W₃ W₄).weight ℓ ((starRingEnd ℂ) z))
        = ε * StrandExchange.bankProduct Finset.univ (quadFiber W₁ W₂ W₃ W₄).weight ℓ z :=
  StrandExchange.bankProduct_exchange Finset.univ _
    (fun i _ => (quadFiber W₁ W₂ W₃ W₄).unit i) ℓ

/-- **The quadruple's completed strand exchange**: the same conjugation exchange for the
completed bank `E·γ` over the composed fiber's weight channels, exchange constant still
unimodular — `completedBank_exchange` at the composed fiber, for free. -/
theorem quadCompletedBank_exchange (W₁ : FiniteWeightFiber ι₁) (W₂ : FiniteWeightFiber ι₂)
    (W₃ : FiniteWeightFiber ι₃) (W₄ : FiniteWeightFiber ι₄)
    (ℓ : (ι₁ × ι₂) × (ι₃ × ι₄) → ℝ) (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ : ℝ) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z : ℂ,
      (starRingEnd ℂ) (StrandExchange.completedBank Finset.univ
          (quadFiber W₁ W₂ W₃ W₄).weight ℓ β ℓ₀ ((starRingEnd ℂ) z))
        = ε * StrandExchange.completedBank Finset.univ
            (quadFiber W₁ W₂ W₃ W₄).weight ℓ β ℓ₀ z :=
  StrandExchange.completedBank_exchange Finset.univ _
    (fun i _ => (quadFiber W₁ W₂ W₃ W₄).unit i) ℓ β hβ ℓ₀

/-! ## The concrete primitive quadruple: four `H¹`'s, degree 16 -/

/-- **The unitarised `H¹(E)` fiber**: the degree-2 conjugate-pair fiber `{α, α⁻¹}` of an
elliptic curve at a good place (`‖α‖ = 1` is Hasse, unitarised) — `symFiber 1`. -/
noncomputable def curveFiber (α : ℂ) (hα : ‖α‖ = 1) : FiniteWeightFiber (Fin 2) :=
  symFiber 1 α hα

/-- **The primitive quadruple's degree-16 fiber**: `quadFiber` at four unitarised `H¹`
fibers — the carrier home of `M = H¹(E₁) ⊗ H¹(E₂) ⊗ H¹(E₃) ⊗ H¹(E₄)`, channel data the
sixteen products `α₁^{±1}α₂^{±1}α₃^{±1}α₄^{±1}`. -/
noncomputable def curveQuadFiber (α₁ α₂ α₃ α₄ : ℂ)
    (h₁ : ‖α₁‖ = 1) (h₂ : ‖α₂‖ = 1) (h₃ : ‖α₃‖ = 1) (h₄ : ‖α₄‖ = 1) :
    FiniteWeightFiber ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :=
  quadFiber (curveFiber α₁ h₁) (curveFiber α₂ h₂) (curveFiber α₃ h₃) (curveFiber α₄ h₄)

/-- The primitive quadruple's index has cardinality **16**: degree 2⁴. -/
theorem curveQuadFiber_card : Fintype.card ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) = 16 := by
  simp

/-- The degree-16 ledger: the sixteen channel weights multiply to one. -/
theorem curveQuadFiber_det_one (α₁ α₂ α₃ α₄ : ℂ)
    (h₁ : ‖α₁‖ = 1) (h₂ : ‖α₂‖ = 1) (h₃ : ‖α₃‖ = 1) (h₄ : ‖α₄‖ = 1) :
    ∏ p, (curveQuadFiber α₁ α₂ α₃ α₄ h₁ h₂ h₃ h₄).weight p = 1 :=
  (curveQuadFiber α₁ α₂ α₃ α₄ h₁ h₂ h₃ h₄).fiber_det_one

/-- **The degree-16 per-place functional equation**, reflection exponent explicit: the
quadruple's local numerator satisfies `localPoly X = (-X)^16 · localPoly X⁻¹`. -/
theorem curveQuadFiber_localPoly_reciprocal (α₁ α₂ α₃ α₄ : ℂ)
    (h₁ : ‖α₁‖ = 1) (h₂ : ‖α₂‖ = 1) (h₃ : ‖α₃‖ = 1) (h₄ : ‖α₄‖ = 1)
    {X : ℂ} (hX : X ≠ 0) :
    (curveQuadFiber α₁ α₂ α₃ α₄ h₁ h₂ h₃ h₄).localPoly X
      = (-X) ^ 16 * (curveQuadFiber α₁ α₂ α₃ α₄ h₁ h₂ h₃ h₄).localPoly X⁻¹ := by
  rw [(curveQuadFiber α₁ α₂ α₃ α₄ h₁ h₂ h₃ h₄).localPoly_reciprocal hX, curveQuadFiber_card]

/-- **The degree-16 completed local reflection**: `quadCompleted` at the four unitarised
`H¹` fibers — the primitive quadruple's admissible local completed object. -/
noncomputable def curveQuadCompleted (α₁ α₂ α₃ α₄ : ℂ)
    (h₁ : ‖α₁‖ = 1) (h₂ : ‖α₂‖ = 1) (h₃ : ‖α₃‖ = 1) (h₄ : ‖α₄‖ = 1)
    (c : ℂ) (hc : c ≠ 0) (β : ℂ) (ℓ : ℝ) : CompletedReflection :=
  quadCompleted (curveFiber α₁ h₁) (curveFiber α₂ h₂) (curveFiber α₃ h₃) (curveFiber α₄ h₄)
    c hc β ℓ

/-- **The degree-16 completed local reflection FE**: the primitive quadruple's completed
carrier readout satisfies `Λ(s) = (εfin·εarch)(s)·Λ^∨(1-s)`, for any four unit Satake classes,
any conductor base `c ≠ 0`, and any self-dual clock `β, ℓ` — the grade-4 instance of the
fiber-admissibility niceness, fully composed from the degree-2 inputs.  The global FE and
its root number `ε = +1` (provisional in the ledger) are not claimed here. -/
theorem curveQuadCompleted_FE (α₁ α₂ α₃ α₄ : ℂ)
    (h₁ : ‖α₁‖ = 1) (h₂ : ‖α₂‖ = 1) (h₃ : ‖α₃‖ = 1) (h₄ : ‖α₄‖ = 1)
    (c : ℂ) (hc : c ≠ 0) (β : ℂ) (ℓ : ℝ) (s : ℂ) :
    (curveQuadCompleted α₁ α₂ α₃ α₄ h₁ h₂ h₃ h₄ c hc β ℓ).Λ s
      = ((curveQuadCompleted α₁ α₂ α₃ α₄ h₁ h₂ h₃ h₄ c hc β ℓ).εfin s
          * (curveQuadCompleted α₁ α₂ α₃ α₄ h₁ h₂ h₃ h₄ c hc β ℓ).εarch s)
        * (curveQuadCompleted α₁ α₂ α₃ α₄ h₁ h₂ h₃ h₄ c hc β ℓ).Λdual (1 - s) :=
  CompletedReflection.completed_FE _ s

/-- **The degree-16 reflection factor, explicit**: the finite reflection factor of the
primitive quadruple's completed object is `(-(c^{s-1/2}))^16` — the degree read off the
reflection, `16 = 2⁴`. -/
theorem curveQuadCompleted_εfin (α₁ α₂ α₃ α₄ : ℂ)
    (h₁ : ‖α₁‖ = 1) (h₂ : ‖α₂‖ = 1) (h₃ : ‖α₃‖ = 1) (h₄ : ‖α₄‖ = 1)
    (c : ℂ) (hc : c ≠ 0) (β : ℂ) (ℓ : ℝ) (s : ℂ) :
    (curveQuadCompleted α₁ α₂ α₃ α₄ h₁ h₂ h₃ h₄ c hc β ℓ).εfin s
      = (-(reflVar c s)) ^ 16 := by
  show (-(reflVar c s)) ^ (Fintype.card ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) = _
  rw [curveQuadFiber_card]

end CriticalLinePhasor.QuadrupleFiber

#print axioms CriticalLinePhasor.QuadrupleFiber.quadFiber_det_one
#print axioms CriticalLinePhasor.QuadrupleFiber.quadFiber_localPoly_reciprocal
#print axioms CriticalLinePhasor.QuadrupleFiber.quadFiber_warp_det_one
#print axioms CriticalLinePhasor.QuadrupleFiber.quadCompleted_FE
#print axioms CriticalLinePhasor.QuadrupleFiber.quadBank_exchange
#print axioms CriticalLinePhasor.QuadrupleFiber.quadCompletedBank_exchange
#print axioms CriticalLinePhasor.QuadrupleFiber.curveQuadFiber_det_one
#print axioms CriticalLinePhasor.QuadrupleFiber.curveQuadFiber_localPoly_reciprocal
#print axioms CriticalLinePhasor.QuadrupleFiber.curveQuadCompleted_FE
#print axioms CriticalLinePhasor.QuadrupleFiber.curveQuadCompleted_εfin
