import RequestProject.FiniteWeightFiber
import RequestProject.CompletedReflectionFiber

/-!
# General dual-pair local reciprocity (no self-duality, no determinant-one)

`FiniteWeightFiber.localPoly_reciprocal` proves the per-place functional equation in the
**self-dual, determinant-one** case: a finite weight multiset closed under `λ ↦ λ⁻¹` with
`∏ λ = 1` has a self-reciprocal local numerator, `localPoly X = (-X)^{|ι|} · localPoly X⁻¹`.

This file formalises the **general dual-pair** version of the paper's Proposition
"Completed twisted functional equation" (`prop:completedFE`, step (1), `automorph/universal.tex`),
with **no** self-duality and **no** determinant-one assumption.  For a finite index type `ι` and
nonvanishing weights `w : ι → ℂ`, the fiber numerator `P_w(X) = ∏_i (1 - w i · X)` and the dual
weights `w∨ i = (w i)⁻¹` satisfy

  `P_w(X) = (-X)^{card ι} · (∏_i w i) · P_{w∨}(X⁻¹)`   (for `X ≠ 0`),

the determinant `∏_i w i` appearing **explicitly** in the reflection factor — it is *not* forced
to one; that is the point of the general case.

**Scope.**  Everything here is the per-place algebra of the local factor numerator only: a single
polynomial identity in `X` at one place.  The **global** twisted functional equation of the
`L`-function is *not* claimed here; it is the manuscript's carrier-reflection theorem
`thm:carrierreflection` (step (2)), separate from this per-place identity.

* `dualLocalPoly`                    — the fiber numerator `∏_i (1 - w i · X)` for an arbitrary
  weight function (the `FiniteWeightFiber.localPoly` shape, freed of the structure's self-duality
  data).
* `dualPair_localPoly_reciprocal`    — the general dual-pair reciprocity above.
* `selfDual_detOne_case`             — specialisation: with an inversion-involution `d`
  (`w (d i) = (w i)⁻¹`) and `∏_i w i = 1`, the general identity collapses to the self-reciprocal
  form `dualLocalPoly w X = (-X)^{card ι} · dualLocalPoly w X⁻¹`, recovering the
  `FiniteWeightFiber.localPoly_reciprocal` shape.
* `dualPairCompleted` / `dualPairCompleted_FE` — the completed local reflection for the dual pair,
  reusing the self-dual completion clock of `CompletedReflectionFiber`; the reflection factor
  `εfin` carries the determinant `∏_i w i`.  This certifies the fiber's admissible **local**
  completed reflection (the input to step (1)); it is **not** the global carrier reflection.

No `axiom`, no `sorry`.
-/

open Complex Finset
open scoped BigOperators

namespace CriticalLinePhasor.DualPairFiber

open CriticalLinePhasor.FiniteWeightFiber

variable {ι : Type*} [Fintype ι]

/-- The **dual weights** `w∨ i = (w i)⁻¹`: the contragredient Satake data read on the anti-helix. -/
noncomputable def dualWeights (w : ι → ℂ) : ι → ℂ := fun i => (w i)⁻¹

/-- The **fiber numerator** `P_w(X) = ∏_i (1 - w i · X)` for an arbitrary weight function `w`.
Same shape as `FiniteWeightFiber.localPoly`, but taking a bare weight function — no self-duality
involution and no determinant-one ledger are assumed. -/
noncomputable def dualLocalPoly (w : ι → ℂ) (X : ℂ) : ℂ := ∏ i, (1 - w i * X)

/-- **General dual-pair local reciprocity.**  For nonvanishing weights `w` and `X ≠ 0`,
`P_w(X) = (-X)^{card ι} · (∏_i w i) · P_{w∨}(X⁻¹)`, with the determinant `∏_i w i` carried
explicitly in the reflection factor — it is **not** assumed to be `1`.  The one-line algebra is
`1 - w X = (-w X)(1 - w⁻¹ X⁻¹)` for `w, X ≠ 0`, taken over `ι`.

Per-place algebra only: a polynomial identity at a single place.  The global functional equation
of the `L`-function is **not** claimed here. -/
theorem dualPair_localPoly_reciprocal (w : ι → ℂ) (hw : ∀ i, w i ≠ 0) {X : ℂ} (hX : X ≠ 0) :
    dualLocalPoly w X
      = (-X) ^ (Fintype.card ι) * (∏ i, w i) * dualLocalPoly (dualWeights w) X⁻¹ := by
  simp only [dualLocalPoly, dualWeights]
  rw [show ((-X) ^ (Fintype.card ι) : ℂ) = ∏ _i : ι, (-X) by
      rw [Finset.prod_const, Finset.card_univ]]
  rw [mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  linear_combination -(X * X⁻¹) * mul_inv_cancel₀ (hw i) - mul_inv_cancel₀ hX

/-- **The self-dual, determinant-one specialisation.**  If the weights are closed under inversion
via an involution `d` (`w (d i) = (w i)⁻¹`) and their product is `1`, the general dual-pair
reciprocity collapses to the self-reciprocal form
`dualLocalPoly w X = (-X)^{card ι} · dualLocalPoly w X⁻¹` — the shape of
`FiniteWeightFiber.localPoly_reciprocal`.  The determinant factor `∏_i w i` drops out precisely
because it is `1` here, and the dual polynomial `P_{w∨}` reindexes back to `P_w` through the
involution.  Per-place algebra only. -/
theorem selfDual_detOne_case (w : ι → ℂ) (hw : ∀ i, w i ≠ 0)
    (d : ι → ι) (hd : Function.Involutive d) (hbal : ∀ i, w (d i) = (w i)⁻¹)
    (hdet : ∏ i, w i = 1) {X : ℂ} (hX : X ≠ 0) :
    dualLocalPoly w X = (-X) ^ (Fintype.card ι) * dualLocalPoly w X⁻¹ := by
  have hreindex : dualLocalPoly (dualWeights w) X⁻¹ = dualLocalPoly w X⁻¹ := by
    have h1 : ∀ i, (1 : ℂ) - (w i)⁻¹ * X⁻¹ = 1 - w (d i) * X⁻¹ := fun i => by rw [hbal i]
    simp only [dualLocalPoly, dualWeights]
    rw [Finset.prod_congr rfl (fun i _ => h1 i)]
    exact Equiv.prod_comp hd.toPerm (fun i => 1 - w i * X⁻¹)
  rw [dualPair_localPoly_reciprocal w hw hX, hdet, mul_one, hreindex]

/-- **The dual-pair completed local reflection.**  For nonvanishing weights `w`, conductor base
`c ≠ 0`, and self-dual clock face `α` / rate `ℓ`, the completed object `Λ = γ·L` with finite part
`L(s) = P_w(c^{s-1/2})`, dual finite part `Ldual(s) = P_{w∨}(c^{s-1/2})`, completion the self-dual
clock (`CompletedReflectionFiber.clockCompletion`), and reflection factor
`εfin(s) = (-c^{s-1/2})^{card ι} · (∏_i w i)` — carrying the determinant — fits
`CompletedReflection`.  The finite reflection is `dualPair_localPoly_reciprocal`; the completion
self-duality is the self-dual clock.

This certifies the fiber's admissible **local** completed reflection (the input to step (1) of
`prop:completedFE`).  It is **not** the global carrier reflection of step (2). -/
noncomputable def dualPairCompleted (w : ι → ℂ) (hw : ∀ i, w i ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (α : ℂ) (ℓ : ℝ) : CompletedReflection where
  L s := dualLocalPoly w (reflVar c s)
  Ldual s := dualLocalPoly (dualWeights w) (reflVar c s)
  γ s := clockCompletion α ℓ s
  εfin s := (-(reflVar c s)) ^ (Fintype.card ι) * (∏ i, w i)
  εarch _ := 1
  finite_FE s := by
    show dualLocalPoly w (reflVar c s)
      = ((-(reflVar c s)) ^ (Fintype.card ι) * (∏ i, w i))
        * dualLocalPoly (dualWeights w) (reflVar c (1 - s))
    rw [dualPair_localPoly_reciprocal w hw (reflVar_ne_zero hc s), reflVar_one_sub s]
  completion_selfdual s := clockCompletion_selfdual α ℓ s

/-- **The dual-pair completed local reflection FE.**  Composing `dualPair_localPoly_reciprocal`
(finite reflection, via `finite_FE`) with the self-dual clock completion
(`clockCompletion_selfdual`, via `completion_selfdual`) through `CompletedReflection.completed_FE`:
`Λ(s) = (εfin(s)·εarch(s)) · Λ^∨(1-s)` for the **local** object `Λ = γ·P_w(c^{s-1/2})`, with `Λ^∨`
built from the dual weights `w∨` and `εfin` carrying the determinant `∏_i w i`.  This is the
per-place completed reflection of the dual pair; the global twisted `L`-function FE is the
carrier-reflection theorem `thm:carrierreflection`, not this identity. -/
theorem dualPairCompleted_FE (w : ι → ℂ) (hw : ∀ i, w i ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (α : ℂ) (ℓ : ℝ) (s : ℂ) :
    (dualPairCompleted w hw c hc α ℓ).Λ s
      = ((dualPairCompleted w hw c hc α ℓ).εfin s * (dualPairCompleted w hw c hc α ℓ).εarch s)
        * (dualPairCompleted w hw c hc α ℓ).Λdual (1 - s) :=
  CompletedReflection.completed_FE _ s

end CriticalLinePhasor.DualPairFiber

#print axioms CriticalLinePhasor.DualPairFiber.dualPair_localPoly_reciprocal
#print axioms CriticalLinePhasor.DualPairFiber.selfDual_detOne_case
#print axioms CriticalLinePhasor.DualPairFiber.dualPairCompleted_FE
