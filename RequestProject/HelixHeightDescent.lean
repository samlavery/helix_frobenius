import RequestProject.HelixHeightCorrespondence

/-!
# Reflection averaging and the height projection

The unchanged full target is K A f = H K f for every finitely supported
analytic-zero state f. Here K sends e_ρ to the geometric basis at Im ρ,
A e_ρ = (Im ρ - i (Re ρ - 1/2)) e_ρ, and H multiplies by real height.

What would I do without a prior expectation? Test descent on the kernel of K
and test the Green identity in the actual pulled-back carrier pairing.
First Lean lines: `intro f hf` for kernel preservation, and
`rw [UnconditionalFrobenius.inner_def]` for the pairing computation.
The reflection average is computed first so the two tests retain both modes.

Search commands used:
`rg -n 'zeroHeightCorrespondence|semiconj_of|height_intertwining|
heightIntertwining|HeightIntertwining|ker.*xiZeroLedger|xiZeroLedger.*ker'
RequestProject --glob '*.lean'`
`rg -n -i 'reflection.*(even|fixed|involutive)|reflected.*(odd|difference)|
height.*(green|pairing)|correspondence.*(kernel|ker|symmetric)|reflect.*positive|
positive.*reflect' RequestProject --glob '*.lean'`
`rg -n -i 'Function.Semiconj|ker.*(invariant|stable)|invariant.*ker|
map.*ker.*le|inner.*map.*map|isSymmetric.*ker'
.lake/packages/mathlib/Mathlib/LinearAlgebra
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace --glob '*.lean'`
Semantic searches: LeanSearch for a symmetric operator preserving the kernel
of a positive semidefinite form; Loogle `LinearMap, "ker", "invariant"`.
For the pairing expansion, repository and Mathlib searches used
`inner_single|single_inner|inner.*sum|sum.*inner|lmapDomain_apply|
mapDomain_apply|mapDomain_eq_sum|mapDomain.*sum|sum.*mapDomain`.
LeanSearch queried noninjective reindexing of finitely supported inner
products; Loogle queried `Finsupp.mapDomain, Finsupp.sum`.
-/

open Complex
open scoped Classical

namespace CriticalLinePhasor.XiChannel

open ThreeDFocal

/-- Average of an analytic state and its completed-reflection partner. -/
noncomputable def xiReflectionEvenProjection :
    (XiZeroIndex →₀ ℂ) →ₗ[ℂ] (XiZeroIndex →₀ ℂ) :=
  (1 / 2 : ℂ) • (LinearMap.id + xiZeroReflectionOperator)

theorem xiReflectionEvenProjection_idempotent (f : XiZeroIndex →₀ ℂ) :
    xiReflectionEvenProjection (xiReflectionEvenProjection f) =
      xiReflectionEvenProjection f := by
  ext ρ
  simp [xiReflectionEvenProjection, xiZeroReflectionOperator_apply]
  ring

/-- Averaging does not change the geometric height readout. -/
theorem zeroHeightCorrespondence_evenProjection :
    zeroHeightCorrespondence.comp xiReflectionEvenProjection =
      zeroHeightCorrespondence := by
  apply LinearMap.ext
  intro f
  ext s
  have hj := congrArg (fun L => L f) zeroHeightCorrespondence_reflection
  simp only [LinearMap.comp_apply] at hj
  simp only [LinearMap.comp_apply, xiReflectionEvenProjection,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    map_smul, map_add, hj]
  simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul]
  ring

/-- The averaged input has exact first-order height correspondence on every finite state. -/
theorem zeroHeightCorrespondence_averaged_intertwining :
    (zeroHeightCorrespondence.comp xiZeroLedgerOperator).comp
        xiReflectionEvenProjection =
      (carrierThreeDOperator 1 1).comp zeroHeightCorrespondence := by
  apply Finsupp.lhom_ext
  intro ρ c
  simp only [LinearMap.comp_apply, xiReflectionEvenProjection,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    map_smul, map_add, xiZeroReflectionOperator_single,
    xiZeroLedgerOperator_single', zeroHeightCorrespondence_single,
    carrierState3D_reflected_height, carrierThreeDOperator_single',
    ← Finsupp.single_add, Finsupp.smul_single, smul_eq_mul]
  congr 1
  apply Complex.ext <;>
    simp [HelixLimit.poleParam, xiZeroReflection, carrierState3D,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- The antisymmetric difference of the two zero modes. -/
noncomputable def reflectedDifferenceMode (ρ : XiZeroIndex) : XiZeroIndex →₀ ℂ :=
  Finsupp.single ρ 1 - Finsupp.single (xiZeroReflection ρ) 1

theorem zeroHeightCorrespondence_difference (ρ : XiZeroIndex) :
    zeroHeightCorrespondence (reflectedDifferenceMode ρ) = 0 := by
  simp [reflectedDifferenceMode]

/-- Apply the analytic operator before projecting the antisymmetric mode. -/
theorem zeroHeightCorrespondence_ledger_difference (ρ : XiZeroIndex) :
    zeroHeightCorrespondence (xiZeroLedgerOperator (reflectedDifferenceMode ρ)) =
      Finsupp.single (carrierState3D 1 1 ρ.val.im)
        (-2 * Complex.I * ((ρ.val.re - 1 / 2 : ℝ) : ℂ)) := by
  simp only [reflectedDifferenceMode, map_sub, xiZeroLedgerOperator_single',
    zeroHeightCorrespondence_single, mul_one, carrierState3D_reflected_height,
    ← Finsupp.single_sub]
  congr 1
  apply Complex.ext <;>
    simp [HelixLimit.poleParam, xiZeroReflection, Complex.mul_re, Complex.mul_im]
  ring

/-- Exact Green defect for the carrier pairing, on a kernel mode and a basis mode. -/
theorem zeroHeightCorrespondence_green_defect (ρ : XiZeroIndex) :
    inner ℂ
        (zeroHeightCorrespondence (xiZeroLedgerOperator (reflectedDifferenceMode ρ)))
        (zeroHeightCorrespondence (Finsupp.single ρ 1)) -
      inner ℂ (zeroHeightCorrespondence (reflectedDifferenceMode ρ))
        (zeroHeightCorrespondence
          (xiZeroLedgerFormalAdjoint (Finsupp.single ρ 1))) =
      2 * Complex.I * ((ρ.val.re - 1 / 2 : ℝ) : ℂ) := by
  rw [zeroHeightCorrespondence_difference, inner_zero_left, sub_zero,
    zeroHeightCorrespondence_ledger_difference, zeroHeightCorrespondence_single]
  rw [UnconditionalFrobenius.inner_def, Finsupp.sum_single_index (by simp)]
  simp only [Finsupp.single_eq_same, mul_one, map_mul, map_neg,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- The carrier basis pairing keeps all pairs of source indices at the same height. -/
theorem carrier_height_basis_inner (ρ τ : XiZeroIndex) (a b : ℂ) :
    inner ℂ (Finsupp.single (carrierState3D 1 1 ρ.val.im) a)
        (Finsupp.single (carrierState3D 1 1 τ.val.im) b) =
      if ρ.val.im = τ.val.im then (starRingEnd ℂ) a * b else 0 := by
  rw [UnconditionalFrobenius.inner_def, Finsupp.sum_single_index (by simp)]
  by_cases h : ρ.val.im = τ.val.im
  · simp only [h, Finsupp.single_eq_same, ite_true]
  · have hs : carrierState3D 1 1 τ.val.im ≠ carrierState3D 1 1 ρ.val.im := by
      intro he
      exact h (congrArg CarrierState3D.ordinate he).symm
    simp [Ne.symm hs, h]

/-- Full finite expansion of the pulled-back carrier pairing. -/
theorem zeroHeightCorrespondence_inner_pairs (f g : XiZeroIndex →₀ ℂ) :
    inner ℂ (zeroHeightCorrespondence f) (zeroHeightCorrespondence g) =
      f.sum (fun ρ a => g.sum (fun τ b =>
        if ρ.val.im = τ.val.im then (starRingEnd ℂ) a * b else 0)) := by
  change inner ℂ
      (f.sum fun ρ a => Finsupp.single (carrierState3D 1 1 ρ.val.im) a)
      (g.sum fun τ b => Finsupp.single (carrierState3D 1 1 τ.val.im) b) = _
  rw [Finsupp.sum_inner]
  simp only [Finsupp.inner_sum, carrier_height_basis_inner]

/-- The individual cross term in the carrier Green identity. -/
theorem zeroHeightCorrespondence_green_basis (ρ τ : XiZeroIndex) (a b : ℂ) :
    inner ℂ (zeroHeightCorrespondence (xiZeroLedgerOperator (Finsupp.single ρ a)))
        (zeroHeightCorrespondence (Finsupp.single τ b)) -
      inner ℂ (zeroHeightCorrespondence (Finsupp.single ρ a))
        (zeroHeightCorrespondence (xiZeroLedgerFormalAdjoint (Finsupp.single τ b))) =
      if ρ.val.im = τ.val.im then
        Complex.I * ((ρ.val.re - τ.val.re : ℝ) : ℂ) * (starRingEnd ℂ) a * b
      else 0 := by
  simp only [xiZeroLedgerOperator_single', xiZeroLedgerFormalAdjoint_single',
    zeroHeightCorrespondence_single, carrier_height_basis_inner]
  by_cases h : ρ.val.im = τ.val.im
  · simp only [h, ite_true, map_mul]
    have hp : (starRingEnd ℂ) (HelixLimit.poleParam ρ.val) -
        (starRingEnd ℂ) (HelixLimit.poleParam τ.val) =
        Complex.I * ((ρ.val.re - τ.val.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [HelixLimit.poleParam, h]
    rw [← hp]
    ring
  · simp only [h, ite_false, sub_self]

end CriticalLinePhasor.XiChannel

#print axioms CriticalLinePhasor.XiChannel.xiReflectionEvenProjection_idempotent
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_evenProjection
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_averaged_intertwining
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_difference
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_ledger_difference
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_green_defect
#print axioms CriticalLinePhasor.XiChannel.carrier_height_basis_inner
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_inner_pairs
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_green_basis
