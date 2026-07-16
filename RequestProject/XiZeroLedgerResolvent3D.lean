import RequestProject.XiPartialFraction
import RequestProject.XiChannelReceiver
import RequestProject.CarrierUnboundedResolvent3D
import RequestProject.ZetaContourArgument

/-!
# The completed ξ-channel as a native zero-ledger 3D resolvent trace

This file performs the missing coordinate-level operator identification.  The spectral
coordinate of a nontrivial zero `ρ` is the carrier parameter

`poleParam ρ = ρ.im - I * (ρ.re - 1/2)`.

Consequently the affine chart satisfies

`(1/2 + I*z) - ρ = I * (z - poleParam ρ)`.

After this geometric change of coordinates, the multiplicity-weighted Hadamard partial
fraction for `ξ'/ξ` is literally a regularized diagonal resolvent trace.  In particular,
the `1/2` in the chart is not inserted into a zero certificate: it is the half-unit in the
affine carrier readout, and the theorem below derives the exact analytic/operator coupling
from the independently proved partial fraction identity.
-/

open Complex Filter Topology Set

namespace CriticalLinePhasor.XiChannel

/-- The affine half-unit chart converts a zero displacement into the corresponding carrier
spectral displacement. -/
theorem chart_sub_zero_eq_I_mul (z ρ : ℂ) :
    (1 / 2 + Complex.I * z) - ρ =
      Complex.I * (z - HelixLimit.poleParam ρ) := by
  apply Complex.ext <;>
    simp [HelixLimit.poleParam, Complex.mul_re, Complex.mul_im] <;> ring

/-- Multiplication by `I` rotates the scalar resolvent by `I` after applying the channel's
overall minus sign. -/
theorem neg_I_mul_inv (x : ℂ) :
    -((Complex.I * x)⁻¹) = Complex.I * x⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  · field_simp
    ring_nf
    simp

/-- Pointwise form of the chart/resolvent conversion at an arbitrary complex parameter. -/
theorem neg_chart_sub_zero_inv (z ρ : ℂ) :
    -((1 / 2 + Complex.I * z - ρ)⁻¹) =
      Complex.I * (z - HelixLimit.poleParam ρ)⁻¹ := by
  rw [chart_sub_zero_eq_I_mul]
  exact neg_I_mul_inv _

/-- The regularized scalar trace of the zero-indexed diagonal 3D carrier resolvent.  The
subtraction by `ρ⁻¹` is the canonical Hadamard convergence counterterm, and
`xiOrderNat ρ` is the analytic multiplicity. -/
noncomputable def xiZeroResolventTrace (z : ℂ) : ℂ :=
  ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
    (ZD.xiOrderNat ρ.val : ℂ) *
      (Complex.I * (z - HelixLimit.poleParam ρ.val)⁻¹ - 1 / ρ.val)

/-- **Exact analytic/operator identification.**  Away from the zero set, the independently
continued completed channel `-ξ'/ξ(1/2+Iz)` is, up to its single Hadamard constant, exactly
the regularized trace of the diagonal 3D resolvent with eigenparameters `poleParam ρ`.

No zero-location premise occurs in the statement.  The result is obtained by transporting
the proved Hadamard partial fraction through the carrier chart. -/
theorem xiChannel_eq_constant_add_zeroResolventTrace :
    ∃ C : ℂ, ∀ z : ℂ, (1 / 2 + Complex.I * z) ∉ ZD.NontrivialZeros →
      xiChannel z = C + xiZeroResolventTrace z := by
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
  refine ⟨-A, ?_⟩
  intro z hz
  rw [xiChannel, logDeriv_apply, hA _ hz]
  unfold xiZeroResolventTrace
  rw [neg_add]
  congr 1
  rw [← tsum_neg]
  apply tsum_congr
  intro ρ
  calc
    -((ZD.xiOrderNat ρ.val : ℂ) *
        (1 / (1 / 2 + Complex.I * z - ρ.val) + 1 / ρ.val)) =
      (ZD.xiOrderNat ρ.val : ℂ) *
        (-(1 / (1 / 2 + Complex.I * z - ρ.val) + 1 / ρ.val)) := by ring
    _ = (ZD.xiOrderNat ρ.val : ℂ) *
        (Complex.I * (z - HelixLimit.poleParam ρ.val)⁻¹ - 1 / ρ.val) := by
      rw [neg_add]
      simp only [one_div]
      have h := neg_chart_sub_zero_inv z ρ.val
      simp only [one_div] at h
      rw [h]
      ring

/-- Basiswise parameter-preserving resolvent identification.  The analytic zero-pole receiver
agrees with the real carrier-height receiver at one spectral parameter exactly when that zero
fiber is area-law scale balanced.  Because inversion and multiplication by `I` are injective,
neither another zero mode nor a reflected partner can manufacture this equality. -/
theorem zeroPoleResolvent_eq_carrierHeightResolvent_iff_scaleBalanced
    (rho z : ℂ) :
    Complex.I * (z - HelixLimit.poleParam rho)⁻¹ =
        Complex.I * (z - (rho.im : ℂ))⁻¹ ↔
      ThreeDFocal.CarrierScaleBalanced rho.re := by
  constructor
  · intro hreadout
    have hinv : (z - HelixLimit.poleParam rho)⁻¹ =
        (z - (rho.im : ℂ))⁻¹ :=
      mul_left_cancel₀ Complex.I_ne_zero hreadout
    have hshift : z - HelixLimit.poleParam rho = z - (rho.im : ℂ) :=
      inv_injective hinv
    have hpole : HelixLimit.poleParam rho = (rho.im : ℂ) := by
      linear_combination -hshift
    apply (ThreeDFocal.carrierScaleBalanced_iff rho.re).2
    have him := congrArg Complex.im hpole
    simp [HelixLimit.poleParam] at him
    linarith
  · intro hbalance
    have hre := (ThreeDFocal.carrierScaleBalanced_iff rho.re).1 hbalance
    simp [HelixLimit.poleParam, hre]

/-- The same criterion using the independently defined event-free 3D carrier state and its
actual basis resolvent matrix coefficient. -/
theorem zeroPoleResolvent_eq_carrierBasisReadout_iff_scaleBalanced
    (rho z : ℂ) :
    Complex.I * (z - HelixLimit.poleParam rho)⁻¹ =
        Complex.I * ThreeDFocal.carrierBasisResolventReadout
          (ThreeDFocal.carrierState3D 1 1 rho.im) z ↔
      ThreeDFocal.CarrierScaleBalanced rho.re := by
  rw [ThreeDFocal.carrierBasisResolventReadout_eq]
  simpa [ThreeDFocal.carrierState3D] using
    zeroPoleResolvent_eq_carrierHeightResolvent_iff_scaleBalanced rho z

/-! ## The zero-ledger diagonal operator and its exact symmetry criterion -/

/-- The analytic zero index, carrying membership but no geometric event certificate. -/
abbrev XiZeroIndex := {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}

/-! ## Basis-resolved analytic/carrier resolvent bridge

The scalar `tsum` in `xiZeroResolventTrace` is useful for the completed analytic channel, but a
summed equality can conceal cancellation between different modes.  The kernels below retain the
analytic-zero basis index.  The carrier kernel is the matrix coefficient of the independently
defined real carrier-height operator pulled back along `ρ ↦ ρ.im`; it contains no event
certificate and no asserted carrier-point equality.
-/

/-- One multiplicity-weighted, Hadamard-regularized analytic zero-resolvent summand. -/
noncomputable def xiZeroResolventKernel (z : ℂ) (ρ : XiZeroIndex) : ℂ :=
  (ZD.xiOrderNat ρ.val : ℂ) *
    (Complex.I * (z - HelixLimit.poleParam ρ.val)⁻¹ - 1 / ρ.val)

/-- The corresponding basis coefficient of the event-independent real carrier-height
resolvent.  Only the real height `ρ.im` is used in the pole term. -/
noncomputable def xiCarrierHeightResolventKernel (z : ℂ) (ρ : XiZeroIndex) : ℂ :=
  (ZD.xiOrderNat ρ.val : ℂ) *
    (Complex.I * (z - (ρ.val.im : ℂ))⁻¹ - 1 / ρ.val)

/-- The regularized carrier-height resolvent trace, formed only after the basis coefficients have
been kept separate. -/
noncomputable def xiCarrierHeightResolventTrace (z : ℂ) : ℂ :=
  ∑' ρ : XiZeroIndex, xiCarrierHeightResolventKernel z ρ

/-- The analytic trace is definitionally the sum of its basis-resolved kernels. -/
theorem xiZeroResolventTrace_eq_tsum_kernel (z : ℂ) :
    xiZeroResolventTrace z = ∑' ρ : XiZeroIndex, xiZeroResolventKernel z ρ := by
  rfl

/-- A single analytic kernel equals its real carrier-height kernel exactly at the area-law
fixed point.  Analytic multiplicity is positive, so it can be cancelled; no other zero mode is
available in this statement. -/
theorem xiZeroResolventKernel_eq_carrierHeightKernel_iff_scaleBalanced
    (z : ℂ) (ρ : XiZeroIndex) :
    xiZeroResolventKernel z ρ = xiCarrierHeightResolventKernel z ρ ↔
      ThreeDFocal.CarrierScaleBalanced ρ.val.re := by
  constructor
  · intro hkernel
    have horder : (ZD.xiOrderNat ρ.val : ℂ) ≠ 0 := by
      exact_mod_cast ZD.xiOrderNat_pos_of_mem_NontrivialZeros ρ.property |>.ne'
    have hregularized :
        Complex.I * (z - HelixLimit.poleParam ρ.val)⁻¹ - 1 / ρ.val =
          Complex.I * (z - (ρ.val.im : ℂ))⁻¹ - 1 / ρ.val := by
      exact mul_left_cancel₀ horder (by simpa [xiZeroResolventKernel,
        xiCarrierHeightResolventKernel] using hkernel)
    apply (zeroPoleResolvent_eq_carrierHeightResolvent_iff_scaleBalanced ρ.val z).1
    linear_combination hregularized
  · intro hbalanced
    unfold xiZeroResolventKernel xiCarrierHeightResolventKernel
    rw [(zeroPoleResolvent_eq_carrierHeightResolvent_iff_scaleBalanced ρ.val z).2 hbalanced]

/-- Basiswise scale balance transports the complete analytic zero trace to the independent
carrier-height trace. -/
theorem xiZeroResolventTrace_eq_carrierHeightResolventTrace_of_all_scaleBalanced
    (hall : ∀ ρ : XiZeroIndex, ThreeDFocal.CarrierScaleBalanced ρ.val.re) (z : ℂ) :
    xiZeroResolventTrace z = xiCarrierHeightResolventTrace z := by
  rw [xiZeroResolventTrace_eq_tsum_kernel]
  unfold xiCarrierHeightResolventTrace
  apply tsum_congr
  intro ρ
  exact (xiZeroResolventKernel_eq_carrierHeightKernel_iff_scaleBalanced z ρ).2 (hall ρ)

/-- Once the basis-resolved bridge is established, the already proved Hadamard trace identity
becomes a literal trace formula for the event-independent real carrier-height receiver. -/
theorem xiChannel_eq_constant_add_carrierHeightResolventTrace_of_all_scaleBalanced
    (hall : ∀ ρ : XiZeroIndex, ThreeDFocal.CarrierScaleBalanced ρ.val.re) :
    ∃ C : ℂ, ∀ z : ℂ, (1 / 2 + Complex.I * z) ∉ ZD.NontrivialZeros →
      xiChannel z = C + xiCarrierHeightResolventTrace z := by
  obtain ⟨C, hC⟩ := xiChannel_eq_constant_add_zeroResolventTrace
  refine ⟨C, ?_⟩
  intro z hz
  rw [hC z hz, xiZeroResolventTrace_eq_carrierHeightResolventTrace_of_all_scaleBalanced hall z]

/-- Completed reflection on the analytic zero index.  Membership is transported by the entire
xi functional equation; no carrier event or real-coordinate premise occurs here. -/
noncomputable def xiZeroReflection (ρ : XiZeroIndex) : XiZeroIndex :=
  ⟨1 - (starRingEnd ℂ) ρ.val, by
    apply (ZD.riemannXi_eq_zero_iff _).mp
    rw [CriticalLinePhasor.ContourArgument.riemannXi_one_sub_conj,
      (ZD.riemannXi_eq_zero_iff ρ.val).mpr ρ.property, map_zero]⟩

/-- Completed reflection is an involution on the genuine analytic zero set. -/
@[simp] theorem xiZeroReflection_involutive (ρ : XiZeroIndex) :
    xiZeroReflection (xiZeroReflection ρ) = ρ := by
  apply Subtype.ext
  simp [xiZeroReflection]

theorem xiZeroReflection_injective : Function.Injective xiZeroReflection :=
  Function.LeftInverse.injective xiZeroReflection_involutive

/-- Completed reflection preserves the carrier height and reverses only the radial displacement:
the reflected analytic pole parameter is the complex adjoint of the original parameter. -/
theorem poleParam_xiZeroReflection (ρ : XiZeroIndex) :
    HelixLimit.poleParam (xiZeroReflection ρ).val =
      (starRingEnd ℂ) (HelixLimit.poleParam ρ.val) := by
  apply Complex.ext <;>
    simp [xiZeroReflection, HelixLimit.poleParam] <;> ring

/-- The completed-reflection involution acting on the finitely supported analytic zero state
space.  It is defined before any event certificate and simply transports basis modes. -/
noncomputable def xiZeroReflectionOperator :
    (XiZeroIndex →₀ ℂ) →ₗ[ℂ] (XiZeroIndex →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ xiZeroReflection

@[simp] theorem xiZeroReflectionOperator_single (ρ : XiZeroIndex) (c : ℂ) :
    xiZeroReflectionOperator (Finsupp.single ρ c) =
      Finsupp.single (xiZeroReflection ρ) c := by
  simp [xiZeroReflectionOperator]

@[simp] theorem xiZeroReflectionOperator_apply (f : XiZeroIndex →₀ ℂ)
    (ρ : XiZeroIndex) :
    xiZeroReflectionOperator f ρ = f (xiZeroReflection ρ) := by
  have h := Finsupp.mapDomain_apply xiZeroReflection_injective f (xiZeroReflection ρ)
  simpa [xiZeroReflectionOperator] using h

/-- The diagonal zero-ledger operator selected by the already identified resolvent poles.  Its
state space is the free finitely supported Hilbert space on analytic zeros; no `ThreeDZero`, focal
event, carrier-point equality, or midpoint premise appears in its construction. -/
noncomputable def xiZeroLedgerOperator :
    (XiZeroIndex →₀ ℂ) →ₗ[ℂ] (XiZeroIndex →₀ ℂ) :=
  ThreeDFocal.complexDiagOp fun ρ => HelixLimit.poleParam ρ.val

/-- Every diagonal coefficient of a complex diagonal operator has its canonical basis
eigenvector. -/
theorem complexDiagOp_hasEigenvalue {ι : Type*} (d : ι → ℂ) (i : ι) :
    Module.End.HasEigenvalue (ThreeDFocal.complexDiagOp d) (d i) := by
  refine fun h => ?_
  simp_all only [Submodule.eq_bot_iff]
  specialize h (Finsupp.single i 1)
  simp_all [ThreeDFocal.complexDiagOp]

/-- Each analytic zero contributes its chart parameter as an actual eigenvalue of the
zero-ledger operator. -/
theorem xiZeroLedgerOperator_hasEigenvalue (ρ : XiZeroIndex) :
    Module.End.HasEigenvalue xiZeroLedgerOperator (HelixLimit.poleParam ρ.val) :=
  complexDiagOp_hasEigenvalue _ ρ

/-- Symmetry of the identified zero-ledger operator forces every chart eigenparameter to be
real, by the standard inner-product eigenvalue argument. -/
theorem xiZeroLedgerOperator_symmetric_imp_poleParam_real
    (h : xiZeroLedgerOperator.IsSymmetric) (ρ : XiZeroIndex) :
    (HelixLimit.poleParam ρ.val).im = 0 :=
  UnconditionalFrobenius.symmetric_eigenvalue_real h
    (xiZeroLedgerOperator_hasEigenvalue ρ)

/-- Operator symmetry therefore produces area-law scale balance for every canonical analytic
zero fiber.  The half-unit is obtained only after spectral reality is converted through
`poleParam_im` and the independently proved carrier area law. -/
theorem xiZeroLedgerOperator_symmetric_imp_scaleBalanced
    (h : xiZeroLedgerOperator.IsSymmetric) (ρ : XiZeroIndex) :
    ThreeDFocal.CarrierScaleBalanced ρ.val.re := by
  apply (ThreeDFocal.carrierScaleBalanced_iff ρ.val.re).2
  have hp := xiZeroLedgerOperator_symmetric_imp_poleParam_real h ρ
  rw [HelixLimit.poleParam_im] at hp
  linarith

/-- Exact symmetry criterion for the identified operator: it is symmetric precisely when the
chart eigenparameters selected by the analytic resolvent are real.  The reverse direction
identifies it with the standard real-diagonal carrier operator. -/
theorem xiZeroLedgerOperator_isSymmetric_iff :
    xiZeroLedgerOperator.IsSymmetric ↔
      ∀ ρ : XiZeroIndex, (HelixLimit.poleParam ρ.val).im = 0 := by
  constructor
  · exact xiZeroLedgerOperator_symmetric_imp_poleParam_real
  · intro h
    have hop : xiZeroLedgerOperator =
        UnconditionalFrobenius.diagOp
          (fun ρ : XiZeroIndex => (HelixLimit.poleParam ρ.val).re) := by
      apply LinearMap.ext
      intro f
      apply Finsupp.ext
      intro ρ
      rw [xiZeroLedgerOperator, ThreeDFocal.complexDiagOp_apply,
        UnconditionalFrobenius.diagOp_apply]
      have hreal : ((HelixLimit.poleParam ρ.val).re : ℂ) =
          HelixLimit.poleParam ρ.val := by
        apply Complex.ext
        · simp
        · simp [h ρ]
      rw [hreal]
    rw [hop]
    exact UnconditionalFrobenius.diagOp_symmetric _

/-! ## Exact carrier-height/radial-drift decomposition -/

/-- The real carrier-height operator on the same analytic zero-indexed state space.  Its
coefficient is only the ordinate of the zero, so this operator is the pullback of the ambient
event-independent helix height operator along the height map. -/
noncomputable def xiCarrierHeightOperator :
    (XiZeroIndex →₀ ℂ) →ₗ[ℂ] (XiZeroIndex →₀ ℂ) :=
  UnconditionalFrobenius.diagOp fun ρ => ρ.val.im

/-- The real diagonal radial-drift operator.  Its coefficient is the displacement from the
area-law half-unit; the definition does not assert that this displacement vanishes. -/
noncomputable def xiRadialDriftOperator :
    (XiZeroIndex →₀ ℂ) →ₗ[ℂ] (XiZeroIndex →₀ ℂ) :=
  UnconditionalFrobenius.diagOp fun ρ => ρ.val.re - 1 / 2

/-- The analytically identified complex pole operator is exactly carrier height minus `I` times
radial drift.  This is the literal three-dimensional split of every resolvent pole parameter. -/
theorem xiZeroLedgerOperator_eq_height_sub_I_smul_radialDrift :
    xiZeroLedgerOperator =
      xiCarrierHeightOperator - Complex.I • xiRadialDriftOperator := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro ρ
  simp [xiZeroLedgerOperator, xiCarrierHeightOperator, xiRadialDriftOperator,
    HelixLimit.poleParam, UnconditionalFrobenius.diagOp_apply]
  ring

/-- Both geometric components in the split are symmetric real-diagonal operators. -/
theorem xiCarrierHeightOperator_isSymmetric : xiCarrierHeightOperator.IsSymmetric := by
  exact UnconditionalFrobenius.diagOp_symmetric _

theorem xiRadialDriftOperator_isSymmetric : xiRadialDriftOperator.IsSymmetric := by
  exact UnconditionalFrobenius.diagOp_symmetric _

/-- Vanishing of the radial operator is exactly scale balance of every canonical analytic
zero-indexed carrier fiber. -/
theorem xiRadialDriftOperator_eq_zero_iff_all_scaleBalanced :
    xiRadialDriftOperator = 0 ↔
      ∀ ρ : XiZeroIndex, ThreeDFocal.CarrierScaleBalanced ρ.val.re := by
  constructor
  · intro hzero ρ
    apply (ThreeDFocal.carrierScaleBalanced_iff ρ.val.re).2
    have happ := LinearMap.congr_fun hzero (Finsupp.single ρ (1 : ℂ))
    have hρ := congrArg (fun f : XiZeroIndex →₀ ℂ => f ρ) happ
    simp [xiRadialDriftOperator, UnconditionalFrobenius.diagOp_apply] at hρ
    have hρre := congrArg Complex.re hρ
    norm_num at hρre
    linarith
  · intro hall
    apply LinearMap.ext
    intro f
    apply Finsupp.ext
    intro ρ
    have hre := (ThreeDFocal.carrierScaleBalanced_iff ρ.val.re).1 (hall ρ)
    simp [xiRadialDriftOperator, UnconditionalFrobenius.diagOp_apply, hre]

/-- Exact operator form of the no-drift projection: the zero-ledger operator is the real carrier
height operator precisely when its radial component vanishes. -/
theorem xiZeroLedgerOperator_eq_carrierHeight_iff_radialDrift_eq_zero :
    xiZeroLedgerOperator = xiCarrierHeightOperator ↔ xiRadialDriftOperator = 0 := by
  rw [xiRadialDriftOperator_eq_zero_iff_all_scaleBalanced]
  constructor
  · intro hop ρ
    have hsym : xiZeroLedgerOperator.IsSymmetric := by
      rw [hop]
      exact xiCarrierHeightOperator_isSymmetric
    exact xiZeroLedgerOperator_symmetric_imp_scaleBalanced hsym ρ
  · intro hall
    apply LinearMap.ext
    intro f
    apply Finsupp.ext
    intro ρ
    have hre := (ThreeDFocal.carrierScaleBalanced_iff ρ.val.re).1 (hall ρ)
    simp [xiZeroLedgerOperator, xiCarrierHeightOperator,
      UnconditionalFrobenius.diagOp_apply, HelixLimit.poleParam, hre]

/-- Symmetry of the analytically identified operator is exactly extinction of the independent
radial-drift component; thus no cancellation among distinct zero modes can hide drift. -/
theorem xiZeroLedgerOperator_isSymmetric_iff_radialDrift_eq_zero :
    xiZeroLedgerOperator.IsSymmetric ↔ xiRadialDriftOperator = 0 := by
  rw [xiRadialDriftOperator_eq_zero_iff_all_scaleBalanced,
    xiZeroLedgerOperator_isSymmetric_iff]
  constructor
  · intro hall ρ
    apply (ThreeDFocal.carrierScaleBalanced_iff ρ.val.re).2
    have hp := hall ρ
    rw [HelixLimit.poleParam_im] at hp
    linarith
  · intro hall ρ
    have hre := (ThreeDFocal.carrierScaleBalanced_iff ρ.val.re).1 (hall ρ)
    rw [HelixLimit.poleParam_im, hre]
    ring

/-! ## Canonical no-drift projection of the analytic pole operator -/

/-- The coefficientwise formal adjoint of the analytic zero-ledger operator.  It is defined on
the same algebraic finite-support domain, so no boundedness assertion is required. -/
noncomputable def xiZeroLedgerFormalAdjoint :
    (XiZeroIndex →₀ ℂ) →ₗ[ℂ] (XiZeroIndex →₀ ℂ) :=
  ThreeDFocal.complexDiagOp fun ρ => starRingEnd ℂ (HelixLimit.poleParam ρ.val)

/-- The completed-reflection action intertwines the analytic zero-ledger operator with its formal
adjoint.  Thus the full functional-equation pair is represented on the analytic zero-ledger state space as an
operator/adjoint pair; the radial component changes sign while the carrier height is fixed. -/
theorem xiZeroReflectionOperator_intertwines_formalAdjoint :
    xiZeroReflectionOperator.comp xiZeroLedgerOperator =
      xiZeroLedgerFormalAdjoint.comp xiZeroReflectionOperator := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro ρ
  simp [xiZeroLedgerOperator, xiZeroLedgerFormalAdjoint,
    ThreeDFocal.complexDiagOp_apply, poleParam_xiZeroReflection]

/-- The formal adjoint satisfies the exact Green identity on the finite-support zero state space. -/
theorem xiZeroLedgerFormalAdjoint_green (f g : XiZeroIndex →₀ ℂ) :
    inner ℂ (xiZeroLedgerOperator f) g =
      inner ℂ f (xiZeroLedgerFormalAdjoint g) := by
  have hsupport : (xiZeroLedgerOperator f).support ⊆ f.support := by
    intro ρ hρ
    rw [Finsupp.mem_support_iff] at hρ ⊢
    intro hf
    apply hρ
    simp [xiZeroLedgerOperator, ThreeDFocal.complexDiagOp_apply, hf]
  rw [UnconditionalFrobenius.inner_eq_sum_of_subset _ _ hsupport,
    UnconditionalFrobenius.inner_eq_sum_of_subset _ _ (Finset.Subset.refl _)]
  apply Finset.sum_congr rfl
  intro ρ _hρ
  simp [xiZeroLedgerOperator, xiZeroLedgerFormalAdjoint,
    ThreeDFocal.complexDiagOp_apply, map_mul]
  ring

/-- The Hermitian part is the canonical no-radial-drift projection of the analytic pole
operator.  It is defined without an event certificate or a zero-location assertion. -/
noncomputable def xiZeroLedgerNoDriftProjection :
    (XiZeroIndex →₀ ℂ) →ₗ[ℂ] (XiZeroIndex →₀ ℂ) :=
  (1 / 2 : ℂ) • (xiZeroLedgerOperator + xiZeroLedgerFormalAdjoint)

/-- The no-drift projection is exactly the independently defined real carrier-height operator. -/
theorem xiZeroLedgerNoDriftProjection_eq_carrierHeight :
    xiZeroLedgerNoDriftProjection = xiCarrierHeightOperator := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro ρ
  simp [xiZeroLedgerNoDriftProjection, xiZeroLedgerOperator,
    xiZeroLedgerFormalAdjoint, xiCarrierHeightOperator,
    ThreeDFocal.complexDiagOp_apply, UnconditionalFrobenius.diagOp_apply,
    HelixLimit.poleParam]
  rw [map_ofNat]
  norm_num
  ring

/-- The canonical no-drift projection is symmetric because its computed value is the real
carrier-height operator. -/
theorem xiZeroLedgerNoDriftProjection_isSymmetric :
    xiZeroLedgerNoDriftProjection.IsSymmetric := by
  rw [xiZeroLedgerNoDriftProjection_eq_carrierHeight]
  exact xiCarrierHeightOperator_isSymmetric

/-- The complementary anti-Hermitian part recovers the radial-drift operator exactly. -/
theorem xiRadialDriftOperator_eq_I_half_smul_adjointDefect :
    xiRadialDriftOperator =
      (Complex.I / 2) • (xiZeroLedgerOperator - xiZeroLedgerFormalAdjoint) := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro ρ
  simp [xiRadialDriftOperator, xiZeroLedgerOperator, xiZeroLedgerFormalAdjoint,
    ThreeDFocal.complexDiagOp_apply, UnconditionalFrobenius.diagOp_apply,
    HelixLimit.poleParam]
  rw [map_ofNat]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The residual discarded by the canonical Hermitian projection is exactly `-I` times the
radial-drift operator, coefficient by coefficient. -/
theorem xiZeroLedgerOperator_sub_noDriftProjection_eq_neg_I_smul_radialDrift :
    xiZeroLedgerOperator - xiZeroLedgerNoDriftProjection =
      (-Complex.I) • xiRadialDriftOperator := by
  rw [xiZeroLedgerNoDriftProjection_eq_carrierHeight]
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro ρ
  simp [xiZeroLedgerOperator, xiCarrierHeightOperator, xiRadialDriftOperator,
    ThreeDFocal.complexDiagOp_apply, UnconditionalFrobenius.diagOp_apply,
    HelixLimit.poleParam]
  ring

/-- Exact residual on one analytic-zero basis state.  The only surviving coordinate is that
mode's own radial displacement; no other zero contributes. -/
theorem xiZeroLedgerProjectionResidual_on_basis (ρ : XiZeroIndex) :
    (xiZeroLedgerOperator - xiZeroLedgerNoDriftProjection)
        (Finsupp.single ρ (1 : ℂ)) =
      Finsupp.single ρ ((-Complex.I) * (ρ.val.re - 1 / 2)) := by
  rw [xiZeroLedgerOperator_sub_noDriftProjection_eq_neg_I_smul_radialDrift]
  ext i
  by_cases hi : i = ρ
  · subst i
    simp [xiRadialDriftOperator, UnconditionalFrobenius.diagOp_apply]
  · simp [xiRadialDriftOperator, UnconditionalFrobenius.diagOp_apply, hi]

/-- A canonical zero basis mode is fixed by the no-drift projection exactly when its literal
three-dimensional carrier exponent satisfies the area-law scale balance. -/
theorem xiZeroLedgerProjectionResidual_on_basis_eq_zero_iff_scaleBalanced
    (ρ : XiZeroIndex) :
    (xiZeroLedgerOperator - xiZeroLedgerNoDriftProjection)
        (Finsupp.single ρ (1 : ℂ)) = 0 ↔
      ThreeDFocal.CarrierScaleBalanced ρ.val.re := by
  constructor
  · intro hzero
    apply (ThreeDFocal.carrierScaleBalanced_iff ρ.val.re).2
    rw [xiZeroLedgerProjectionResidual_on_basis] at hzero
    have hρ := congrArg (fun f : XiZeroIndex →₀ ℂ => f ρ) hzero
    simp at hρ
    have hρre := congrArg Complex.re hρ
    norm_num at hρre
    have hre : ρ.val.re - 1 / 2 = 0 := by linarith
    linarith
  · intro hbalance
    have hre := (ThreeDFocal.carrierScaleBalanced_iff ρ.val.re).1 hbalance
    rw [xiZeroLedgerProjectionResidual_on_basis, hre]
    simp

/-- The analytic pole operator is fixed by the canonical no-drift projection exactly when it is
the real carrier-height operator. -/
theorem xiZeroLedgerOperator_eq_noDriftProjection_iff_carrierHeight :
    xiZeroLedgerOperator = xiZeroLedgerNoDriftProjection ↔
      xiZeroLedgerOperator = xiCarrierHeightOperator := by
  rw [xiZeroLedgerNoDriftProjection_eq_carrierHeight]

/-- Equivalently, the analytic pole operator is fixed by no-drift projection exactly when the
radial component vanishes. -/
theorem xiZeroLedgerOperator_eq_noDriftProjection_iff_radialDrift_eq_zero :
    xiZeroLedgerOperator = xiZeroLedgerNoDriftProjection ↔
      xiRadialDriftOperator = 0 := by
  rw [xiZeroLedgerOperator_eq_noDriftProjection_iff_carrierHeight,
    xiZeroLedgerOperator_eq_carrierHeight_iff_radialDrift_eq_zero]

/-- Fixedness under the canonical no-drift projection is exactly symmetry of the independently
identified analytic pole operator. -/
theorem xiZeroLedgerOperator_eq_noDriftProjection_iff_isSymmetric :
    xiZeroLedgerOperator = xiZeroLedgerNoDriftProjection ↔
      xiZeroLedgerOperator.IsSymmetric := by
  rw [xiZeroLedgerOperator_eq_noDriftProjection_iff_radialDrift_eq_zero,
    xiZeroLedgerOperator_isSymmetric_iff_radialDrift_eq_zero]

/-- The no-drift residual vanishes as an operator exactly when it vanishes on every canonical
zero basis mode.  This is the formal no-offline-cancellation statement. -/
theorem xiZeroLedgerResidual_eq_zero_iff_each_basis :
    xiZeroLedgerOperator - xiZeroLedgerNoDriftProjection = 0 ↔
      ∀ ρ : XiZeroIndex,
        (xiZeroLedgerOperator - xiZeroLedgerNoDriftProjection)
            (Finsupp.single ρ (1 : ℂ)) = 0 := by
  rw [xiZeroLedgerOperator_sub_noDriftProjection_eq_neg_I_smul_radialDrift]
  constructor
  · intro hzero ρ
    rw [hzero]
    rfl
  · intro heach
    apply LinearMap.ext
    intro f
    apply Finsupp.ext
    intro ρ
    have hρ := congrArg (fun g : XiZeroIndex →₀ ℂ => g ρ) (heach ρ)
    simp [xiRadialDriftOperator, UnconditionalFrobenius.diagOp_apply] at hρ ⊢
    exact Or.inl hρ

#print axioms chart_sub_zero_eq_I_mul
#print axioms neg_I_mul_inv
#print axioms neg_chart_sub_zero_inv
#print axioms xiChannel_eq_constant_add_zeroResolventTrace
#print axioms zeroPoleResolvent_eq_carrierHeightResolvent_iff_scaleBalanced
#print axioms zeroPoleResolvent_eq_carrierBasisReadout_iff_scaleBalanced
#print axioms xiZeroResolventTrace_eq_tsum_kernel
#print axioms xiZeroResolventKernel_eq_carrierHeightKernel_iff_scaleBalanced
#print axioms xiZeroResolventTrace_eq_carrierHeightResolventTrace_of_all_scaleBalanced
#print axioms xiChannel_eq_constant_add_carrierHeightResolventTrace_of_all_scaleBalanced
#print axioms xiZeroReflection_involutive
#print axioms poleParam_xiZeroReflection
#print axioms xiZeroReflectionOperator_single
#print axioms complexDiagOp_hasEigenvalue
#print axioms xiZeroLedgerOperator_hasEigenvalue
#print axioms xiZeroLedgerOperator_symmetric_imp_poleParam_real
#print axioms xiZeroLedgerOperator_symmetric_imp_scaleBalanced
#print axioms xiZeroLedgerOperator_isSymmetric_iff
#print axioms xiZeroLedgerOperator_eq_height_sub_I_smul_radialDrift
#print axioms xiCarrierHeightOperator_isSymmetric
#print axioms xiRadialDriftOperator_isSymmetric
#print axioms xiRadialDriftOperator_eq_zero_iff_all_scaleBalanced
#print axioms xiZeroLedgerOperator_eq_carrierHeight_iff_radialDrift_eq_zero
#print axioms xiZeroLedgerOperator_isSymmetric_iff_radialDrift_eq_zero
#print axioms xiZeroLedgerFormalAdjoint_green
#print axioms xiZeroReflectionOperator_intertwines_formalAdjoint
#print axioms xiZeroLedgerNoDriftProjection_eq_carrierHeight
#print axioms xiZeroLedgerNoDriftProjection_isSymmetric
#print axioms xiRadialDriftOperator_eq_I_half_smul_adjointDefect
#print axioms xiZeroLedgerOperator_sub_noDriftProjection_eq_neg_I_smul_radialDrift
#print axioms xiZeroLedgerProjectionResidual_on_basis
#print axioms xiZeroLedgerProjectionResidual_on_basis_eq_zero_iff_scaleBalanced
#print axioms xiZeroLedgerOperator_eq_noDriftProjection_iff_carrierHeight
#print axioms xiZeroLedgerOperator_eq_noDriftProjection_iff_radialDrift_eq_zero
#print axioms xiZeroLedgerOperator_eq_noDriftProjection_iff_isSymmetric
#print axioms xiZeroLedgerResidual_eq_zero_iff_each_basis

end CriticalLinePhasor.XiChannel
