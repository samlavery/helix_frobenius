import RequestProject.FrobeniusSimilitude
import RequestProject.WeilDuality

/-!
# Finite duality-stable weight fibers and the carrier reflection

The general interface behind the symmetric-power construction.  The carrier's reflection/FE
transport needs only a *finite duality-stable weight multiset*, not the Chebyshev string
`{r, r-2, …, -r}`.  A `FiniteWeightFiber ι` is a finite family (indexed by a `Fintype ι`) of
unit-modulus Satake weights `λᵢ` closed under a duality involution `w ↦ -w` (multiplicatively
`λ ↦ λ⁻¹`), with the balanced determinant ledger: the only self-dual channel is the trivial
weight `1`.

* `fiber_det_one`        — the determinant/modulus ledger: `∏ᵢ weight i = 1`.
* `localPoly_reciprocal` — the per-place functional equation: the local factor's numerator
  `∏ᵢ (1 - λᵢ X)` is self-reciprocal, `= (-X)^|ι| · localPoly X⁻¹`, using the ledger.
* `fiber_reflection_axis` — the reflection `s ↦ 1 - s` fixes exactly `Re s = ½`
  (`FrobeniusSimilitude.reflection_fixes_iff`, fiber-independent).
* `warpFiber`            — every dual-compatible unit warp preserves the fiber, its ledger, and
  its reciprocity (generalising `AutomorphicCandidate.warpedBlock_det_one_of_warp`).

`symFiber` (the Chebyshev string) and `tensorFiber` (Rankin–Selberg) are instances; the Maass
case is `symFiber` with the *same* finite algebra (only the archimedean clock differs, which is
not part of this finite reflection).  No `sorry`, no `axiom`.
-/

open Complex Finset
open scoped BigOperators

namespace CriticalLinePhasor

/-- A **finite duality-stable weight fiber** on the finite index `ι`: unit-modulus Satake weights
`λᵢ` with an involution `dual` pairing each channel to its dual `λ ↦ λ⁻¹`, and the balanced
ledger that the only self-dual channel carries the trivial weight `1`. -/
structure FiniteWeightFiber (ι : Type*) [Fintype ι] where
  /-- the Satake weights (eigenvalues) of the channels. -/
  weight : ι → ℂ
  /-- the duality involution `w ↦ -w` on channels. -/
  dual : ι → ι
  /-- `dual` is an involution. -/
  dual_invol : Function.Involutive dual
  /-- every weight is unit-modulus (the compact/reality locus). -/
  unit : ∀ i, ‖weight i‖ = 1
  /-- the dual channel carries the inverse weight: `λ ↦ λ⁻¹`. -/
  balanced : ∀ i, weight (dual i) = (weight i)⁻¹
  /-- balanced determinant ledger: a self-dual channel carries the trivial weight `1`. -/
  center_trivial : ∀ i, dual i = i → weight i = 1

namespace FiniteWeightFiber

variable {ι : Type*} [Fintype ι] (W : FiniteWeightFiber ι)

/-- Weights are nonzero (they are unit-modulus). -/
theorem weight_ne_zero (i : ι) : W.weight i ≠ 0 := by
  intro h
  have h1 := W.unit i
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- **The determinant / modulus ledger**: the product of the weights is one.  The dual
involution pairs `λᵢ · λ_{dual i} = 1`, and self-dual channels carry the trivial weight. -/
theorem fiber_det_one : ∏ i, W.weight i = 1 := by
  apply Finset.prod_involution (fun i _ => W.dual i)
  · intro i _
    rw [W.balanced i]
    exact mul_inv_cancel₀ (W.weight_ne_zero i)
  · intro i _ hne hfix
    exact hne (W.center_trivial i hfix)
  · intro i _
    exact Finset.mem_univ _
  · intro i _
    exact W.dual_invol i

/-- The **local factor numerator** of the fiber at `X = q^{-s}`:
`∏ᵢ (1 - λᵢ X) = det(1 - diag(λ)·X)` — the numerator of `det(1 - r(φ)·q^{-s})⁻¹`, the shadow. -/
noncomputable def localPoly (X : ℂ) : ℂ := ∏ i, (1 - W.weight i * X)

/-- Reindexing by the dual involution: `∏ᵢ f(weight i) = ∏ᵢ f(weight (dual i))`. -/
theorem prod_reindex_dual (f : ℂ → ℂ) :
    ∏ i, f (W.weight i) = ∏ i, f (W.weight (W.dual i)) :=
  (Equiv.prod_comp (W.dual_invol.toPerm) (fun i => f (W.weight i))).symm

/-- **The per-place functional equation**: the local numerator is self-reciprocal,
`localPoly X = (-X)^|ι| · localPoly X⁻¹`.  This is the carrier reflection transported to the
local factor: it uses only that the weights are closed under `λ ↦ λ⁻¹` (self-duality) and that
their product is `1` (`fiber_det_one`, the ledger). -/
theorem localPoly_reciprocal {X : ℂ} (hX : X ≠ 0) :
    W.localPoly X = (-X) ^ (Fintype.card ι) * W.localPoly X⁻¹ := by
  have hstep1 : W.localPoly X = ∏ i, (1 - (W.weight i)⁻¹ * X) := by
    unfold localPoly
    rw [prod_reindex_dual W (fun w => 1 - w * X)]
    exact Finset.prod_congr rfl (fun i _ => by rw [W.balanced i])
  have hstep2 : ∏ i, (1 - (W.weight i)⁻¹ * X)
      = (∏ i, (W.weight i)⁻¹) * ∏ i, (W.weight i - X) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by
      linear_combination (-inv_mul_cancel₀ (W.weight_ne_zero i))
  have hprodinv : ∏ i, (W.weight i)⁻¹ = 1 := by
    rw [Finset.prod_inv_distrib, W.fiber_det_one, inv_one]
  have hstep3 : ∏ i, (W.weight i - X) = (-X) ^ (Fintype.card ι) * W.localPoly X⁻¹ := by
    unfold localPoly
    rw [show ((-X) ^ (Fintype.card ι) : ℂ) = ∏ _i : ι, (-X) by
        rw [Finset.prod_const, Finset.card_univ]]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by
      linear_combination (-W.weight i) * mul_inv_cancel₀ hX
  rw [hstep1, hstep2, hprodinv, one_mul, hstep3]

/-- **The reflection axis** (fiber-independent): the dualizing reflection `s ↦ 1 - s` fixes
exactly the critical line `Re s = ½`.  Re-exported from `FrobeniusSimilitude`. -/
theorem fiber_reflection_axis (s : ℂ) : (1 - s).re = s.re ↔ s.re = 1 / 2 :=
  FrobeniusSimilitude.reflection_fixes_iff s

/-- The **local Euler factor** of the fiber: `∏ᵢ (1 - λᵢ q^{-s})⁻¹ = det(1 - diag(λ)·q^{-s})⁻¹`.
This is the shadow `det(1 - r(φ_v(Frob_v))·q_v^{-s})⁻¹` read off the carrier; its numerator
`localPoly` carries the per-place functional equation `localPoly_reciprocal`. -/
noncomputable def localFactor (q : ℝ) (s : ℂ) : ℂ := (W.localPoly ((q : ℂ) ^ (-s)))⁻¹

/-- A **dual-compatible unit warp** of a fiber: a per-channel unit-modulus amplitude respecting
the duality (`amp (dual i) = (amp i)⁻¹`) and fixing self-dual channels.  Generalises the paper's
`z ↦ A z`, `|A| = 1`. -/
structure DualWarp {κ : Type*} [Fintype κ] (V : FiniteWeightFiber κ) where
  /-- the per-channel unit-modulus warp amplitude. -/
  amp : κ → ℂ
  /-- the amplitude is unit-modulus. -/
  unit : ∀ i, ‖amp i‖ = 1
  /-- the amplitude respects the duality involution. -/
  dual_compat : ∀ i, amp (V.dual i) = (amp i)⁻¹
  /-- the amplitude fixes self-dual channels. -/
  center_fix : ∀ i, V.dual i = i → amp i = 1

/-- **The fiber survives every dual-compatible unit warp**: the warped weights form a fiber with
the same duality data.  Hence the ledger (`fiber_det_one`) and the reciprocity
(`localPoly_reciprocal`) are preserved — the functional equation survives the whole twist family.
Generalises `AutomorphicCandidate.warpedBlock_det_one_of_warp` to the weight multiset. -/
def warpFiber {κ : Type*} [Fintype κ] (V : FiniteWeightFiber κ) (A : DualWarp V) :
    FiniteWeightFiber κ where
  weight i := A.amp i * V.weight i
  dual := V.dual
  dual_invol := V.dual_invol
  unit i := by rw [norm_mul, A.unit i, V.unit i, mul_one]
  balanced i := by rw [A.dual_compat i, V.balanced i, mul_inv]
  center_trivial i hi := by rw [A.center_fix i hi, V.center_trivial i hi, mul_one]

/-- The warp preserves the determinant/modulus ledger. -/
theorem warpFiber_det_one {κ : Type*} [Fintype κ] (V : FiniteWeightFiber κ) (A : DualWarp V) :
    ∏ i, (V.warpFiber A).weight i = 1 :=
  (V.warpFiber A).fiber_det_one

/-- **The symmetric-power instance**: `Sym^r` of a unit Satake class `α` (`‖α‖ = 1`, `αβ = 1`).
The weight channels are the Chebyshev string `α^{r-2k}` (`k = 0..r`), the duality involution is
`Fin.rev` (`k ↦ r-k`), and the self-dual centre (`r` even, `k = r/2`) carries `α⁰ = 1`.  So the
Chebyshev string is one instance of a finite duality-stable weight multiset — the construction
does not use it.  (Maass: identical finite fiber; only the archimedean clock differs.) -/
noncomputable def symFiber (r : ℕ) (α : ℂ) (hα : ‖α‖ = 1) : FiniteWeightFiber (Fin (r + 1)) where
  weight k := α ^ ((r : ℤ) - 2 * (k.val : ℤ))
  dual := Fin.rev
  dual_invol := Fin.rev_rev
  unit k := by rw [norm_zpow, hα, one_zpow]
  balanced k := by
    have hle : k.val ≤ r := by have := k.isLt; omega
    rw [Fin.val_rev, ← zpow_neg]
    congr 1
    omega
  center_trivial k hk := by
    have hle : k.val ≤ r := by have := k.isLt; omega
    have hv : (Fin.rev k).val = k.val := by rw [hk]
    rw [Fin.val_rev] at hv
    have hz : (r : ℤ) - 2 * (k.val : ℤ) = 0 := by omega
    rw [hz, zpow_zero]

/-- `Sym^r` really is a finite duality-stable fiber, so its ledger and per-place functional
equation are the general `fiber_det_one` / `localPoly_reciprocal`. -/
theorem symFiber_det_one (r : ℕ) (α : ℂ) (hα : ‖α‖ = 1) :
    ∏ k, (symFiber r α hα).weight k = 1 :=
  (symFiber r α hα).fiber_det_one

/-- **The Rankin–Selberg (tensor) instance**: the tensor of two finite duality-stable fibers is
one, on the product index, weights `λᵢ · μⱼ`, involution `dual₁ × dual₂`.  So Rankin–Selberg
convolutions are instances of the same reflection theorem — no symmetric-power structure used. -/
def tensorFiber {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W₁ : FiniteWeightFiber ι) (W₂ : FiniteWeightFiber κ) : FiniteWeightFiber (ι × κ) where
  weight p := W₁.weight p.1 * W₂.weight p.2
  dual p := (W₁.dual p.1, W₂.dual p.2)
  dual_invol p := Prod.ext (W₁.dual_invol p.1) (W₂.dual_invol p.2)
  unit p := by rw [norm_mul, W₁.unit p.1, W₂.unit p.2, mul_one]
  balanced p := by rw [W₁.balanced p.1, W₂.balanced p.2, mul_inv]
  center_trivial p hp := by
    have h1 : W₁.dual p.1 = p.1 := congrArg Prod.fst hp
    have h2 : W₂.dual p.2 = p.2 := congrArg Prod.snd hp
    rw [W₁.center_trivial p.1 h1, W₂.center_trivial p.2 h2, mul_one]

/-- The Rankin–Selberg tensor is a finite duality-stable fiber: its ledger and per-place
functional equation are again the general `fiber_det_one` / `localPoly_reciprocal`. -/
theorem tensorFiber_det_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W₁ : FiniteWeightFiber ι) (W₂ : FiniteWeightFiber κ) :
    ∏ p, (tensorFiber W₁ W₂).weight p = 1 :=
  (tensorFiber W₁ W₂).fiber_det_one

end FiniteWeightFiber

end CriticalLinePhasor
