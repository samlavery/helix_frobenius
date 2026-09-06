import RequestProject.XiZeroLedgerResolvent3D

/-!
# A correspondence from analytic modes to geometric carrier modes

Unfolded map: send the basis indexed by an analytic zero ρ to the independent
3D carrier basis at ordinate Im ρ and physical height exp(Im ρ). The map is
linear and nonzero on each basis vector; injectivity is not assumed. Reflection
pairs map to the same height. We compute the first and second operator moments
on such a pair, retaining the radial term in the second moment.

What would I do without a prior expectation? Construct the correspondence,
then apply the operator before and after it. Two concrete decompositions:
`simp [Finsupp.lmapDomain]` on basis modes, and `ext s` followed by the
diagonal operator formula. This tests intertwining without equating states
in different spaces.

Searches: `rg -n -i 'height.*pushforward|pushforward.*height|
intertwine.*[Zz]eroLedger|[Zz]eroLedger.*intertwine|schur.*radial|
radial.*schur' RequestProject --glob '*.lean'`;
`rg -n 'lmapDomain_apply|lmapDomain_comp|lmapDomain_single|sum_smul_index|
sum_single_index' .lake/packages/mathlib/Mathlib/LinearAlgebra/Finsupp
.lake/packages/mathlib/Mathlib/Data/Finsupp --glob '*.lean'`.
Semantic searches: LeanSearch on injective reindexing of Finsupp inner products;
Loogle `Finsupp.domLCongr` (the present correspondence needs only lmapDomain).
-/

open Complex

namespace CriticalLinePhasor.XiChannel

open ThreeDFocal

/-- The actual height correspondence into the event-independent spatial carrier. -/
noncomputable def zeroHeightCorrespondence :
    (XiZeroIndex →₀ ℂ) →ₗ[ℂ] CarrierThreeDMode 1 1 :=
  Finsupp.lmapDomain ℂ ℂ (fun ρ => carrierState3D 1 1 ρ.val.im)

@[simp] theorem zeroHeightCorrespondence_single (ρ : XiZeroIndex) (c : ℂ) :
    zeroHeightCorrespondence (Finsupp.single ρ c) =
      Finsupp.single (carrierState3D 1 1 ρ.val.im) c := by
  simp [zeroHeightCorrespondence]

theorem zeroHeightCorrespondence_basis_ne_zero (ρ : XiZeroIndex) :
    zeroHeightCorrespondence (Finsupp.single ρ 1) ≠ 0 := by
  simp

/-- This correspondence retains the paper's physical-height/log-ordinate relation. -/
theorem zeroHeightCorrespondence_log_height (ρ : XiZeroIndex) :
    Real.log (carrierState3D 1 1 ρ.val.im).physicalHeight = ρ.val.im := by
  rw [CarrierState3D.physicalHeight_eq_exp (by norm_num), Real.log_exp]
  rfl

@[simp] theorem carrierState3D_reflected_height (ρ : XiZeroIndex) :
    carrierState3D 1 1 (xiZeroReflection ρ).val.im = carrierState3D 1 1 ρ.val.im := by
  simp [xiZeroReflection]

/-- The two analytic modes of a reflected pair, including two copies at a fixed point. -/
noncomputable def reflectedPairMode (ρ : XiZeroIndex) : XiZeroIndex →₀ ℂ :=
  Finsupp.single ρ 1 + Finsupp.single (xiZeroReflection ρ) 1

theorem zeroHeightCorrespondence_pair (ρ : XiZeroIndex) :
    zeroHeightCorrespondence (reflectedPairMode ρ) =
      Finsupp.single (carrierState3D 1 1 ρ.val.im) 2 := by
  simp [reflectedPairMode, ← Finsupp.single_add, one_add_one_eq_two]

@[simp] theorem complexDiagOp_single' {ι : Type*} (d : ι → ℂ) (i : ι) (c : ℂ) :
    complexDiagOp d (Finsupp.single i c) = Finsupp.single i (d i * c) := by
  classical
  ext j
  simp only [complexDiagOp_apply]
  by_cases h : i = j
  · subst j; simp
  · simp [Ne.symm h]

@[simp] theorem xiZeroLedgerOperator_single' (ρ : XiZeroIndex) (c : ℂ) :
    xiZeroLedgerOperator (Finsupp.single ρ c) =
      Finsupp.single ρ (HelixLimit.poleParam ρ.val * c) := by
  exact complexDiagOp_single' _ _ _

@[simp] theorem xiZeroLedgerFormalAdjoint_single' (ρ : XiZeroIndex) (c : ℂ) :
    xiZeroLedgerFormalAdjoint (Finsupp.single ρ c) =
      Finsupp.single ρ ((starRingEnd ℂ) (HelixLimit.poleParam ρ.val) * c) := by
  exact complexDiagOp_single' _ _ _

@[simp] theorem carrierThreeDOperator_single' (s : CarrierState3D 1 1) (c : ℂ) :
    carrierThreeDOperator 1 1 (Finsupp.single s c) =
      Finsupp.single s ((s.ordinate : ℂ) * c) := by
  exact UnconditionalFrobenius.diagOp_single _ _ _

/-- The full geometric height operator is intertwined on every finitely supported state. -/
theorem zeroHeightCorrespondence_height_intertwining :
    zeroHeightCorrespondence.comp xiCarrierHeightOperator =
      (carrierThreeDOperator 1 1).comp zeroHeightCorrespondence := by
  apply Finsupp.lhom_ext
  intro ρ c
  simp only [LinearMap.comp_apply, xiCarrierHeightOperator,
    UnconditionalFrobenius.diagOp_single, zeroHeightCorrespondence_single,
    carrierThreeDOperator_single']
  rfl

/-- The correspondence identifies reflection partners at their common physical height. -/
theorem zeroHeightCorrespondence_reflection :
    zeroHeightCorrespondence.comp xiZeroReflectionOperator = zeroHeightCorrespondence := by
  apply Finsupp.lhom_ext
  intro ρ c
  simp

/-- Reflection alone gives first-moment correspondence at the shared geometric height. -/
theorem zeroHeightCorrespondence_first_moment (ρ : XiZeroIndex) :
    zeroHeightCorrespondence (xiZeroLedgerOperator (reflectedPairMode ρ)) =
      carrierThreeDOperator 1 1 (zeroHeightCorrespondence (reflectedPairMode ρ)) := by
  rw [zeroHeightCorrespondence_pair]
  simp only [reflectedPairMode, map_add, xiZeroLedgerOperator_single', mul_one,
    zeroHeightCorrespondence_single, carrierState3D_reflected_height,
    ← Finsupp.single_add, carrierThreeDOperator_single']
  congr 1
  apply Complex.ext <;> simp [HelixLimit.poleParam, xiZeroReflection, carrierState3D] <;> ring

/-- The first unretained moment is an explicit negative squared radial displacement. -/
theorem zeroHeightCorrespondence_second_moment_residual (ρ : XiZeroIndex) :
    zeroHeightCorrespondence
        (xiZeroLedgerOperator (xiZeroLedgerOperator (reflectedPairMode ρ))) -
      carrierThreeDOperator 1 1
        (carrierThreeDOperator 1 1 (zeroHeightCorrespondence (reflectedPairMode ρ))) =
      Finsupp.single (carrierState3D 1 1 ρ.val.im)
        ((-2 * (ρ.val.re - 1 / 2) ^ 2 : ℝ) : ℂ) := by
  rw [zeroHeightCorrespondence_pair]
  simp only [reflectedPairMode, map_add, xiZeroLedgerOperator_single', mul_one,
    zeroHeightCorrespondence_single, carrierState3D_reflected_height,
    ← Finsupp.single_add, carrierThreeDOperator_single', ← Finsupp.single_sub]
  congr 1
  apply Complex.ext <;>
    simp [HelixLimit.poleParam, xiZeroReflection, carrierState3D, pow_two,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- The positive adjoint product retains the opposite, positive squared displacement. -/
theorem zeroHeightCorrespondence_adjoint_moment_residual (ρ : XiZeroIndex) :
    zeroHeightCorrespondence
        (xiZeroLedgerFormalAdjoint (xiZeroLedgerOperator (reflectedPairMode ρ))) -
      carrierThreeDOperator 1 1
        (carrierThreeDOperator 1 1 (zeroHeightCorrespondence (reflectedPairMode ρ))) =
      Finsupp.single (carrierState3D 1 1 ρ.val.im)
        ((2 * (ρ.val.re - 1 / 2) ^ 2 : ℝ) : ℂ) := by
  rw [zeroHeightCorrespondence_pair]
  simp only [reflectedPairMode, map_add, xiZeroLedgerOperator_single', mul_one,
    xiZeroLedgerFormalAdjoint_single', zeroHeightCorrespondence_single,
    carrierState3D_reflected_height, ← Finsupp.single_add,
    carrierThreeDOperator_single', ← Finsupp.single_sub]
  congr 1
  apply Complex.ext <;>
    simp [HelixLimit.poleParam, xiZeroReflection, carrierState3D, pow_two,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem zeroHeightCorrespondence_adjoint_moment_nonneg (ρ : XiZeroIndex) :
    0 ≤ ((zeroHeightCorrespondence
        (xiZeroLedgerFormalAdjoint (xiZeroLedgerOperator (reflectedPairMode ρ))) -
      carrierThreeDOperator 1 1
        (carrierThreeDOperator 1 1 (zeroHeightCorrespondence (reflectedPairMode ρ))))
      (carrierState3D 1 1 ρ.val.im)).re := by
  rw [zeroHeightCorrespondence_adjoint_moment_residual]
  simp only [Finsupp.single_eq_same, Complex.ofReal_re]
  positivity

/-- A genuine correspondence of second moments derives area-law balance.
No equality of analytic modes with geometric modes, or injectivity of the map, is needed. -/
theorem scaleBalanced_of_second_moment_correspondence (ρ : XiZeroIndex)
    (h : zeroHeightCorrespondence
        (xiZeroLedgerOperator (xiZeroLedgerOperator (reflectedPairMode ρ))) =
      carrierThreeDOperator 1 1
        (carrierThreeDOperator 1 1 (zeroHeightCorrespondence (reflectedPairMode ρ)))) :
    CarrierScaleBalanced ρ.val.re := by
  have hr := zeroHeightCorrespondence_second_moment_residual ρ
  rw [h, sub_self] at hr
  have hval := congrArg (fun f : CarrierThreeDMode 1 1 =>
    (f (carrierState3D 1 1 ρ.val.im)).re) hr
  simp only [Finsupp.zero_apply, Finsupp.single_eq_same, Complex.zero_re,
    Complex.ofReal_re] at hval
  apply (carrierScaleBalanced_iff _).2
  nlinarith [sq_nonneg (ρ.val.re - 1 / 2)]

/-- An intertwining correspondence suffices; no identification of the two state spaces occurs. -/
theorem scaleBalanced_of_height_intertwining
    (h : Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator
      (carrierThreeDOperator 1 1)) (ρ : XiZeroIndex) :
    CarrierScaleBalanced ρ.val.re := by
  apply scaleBalanced_of_second_moment_correspondence ρ
  exact (h.iterate_right 2) (reflectedPairMode ρ)

end CriticalLinePhasor.XiChannel

#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_basis_ne_zero
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_log_height
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_height_intertwining
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_reflection
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_first_moment
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_second_moment_residual
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_adjoint_moment_residual
#print axioms CriticalLinePhasor.XiChannel.zeroHeightCorrespondence_adjoint_moment_nonneg
#print axioms CriticalLinePhasor.XiChannel.scaleBalanced_of_second_moment_correspondence
#print axioms CriticalLinePhasor.XiChannel.scaleBalanced_of_height_intertwining
