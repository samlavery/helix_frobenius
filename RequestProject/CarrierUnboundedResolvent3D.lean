import RequestProject.ThreeDFocalEvent

/-!
# The event-independent unbounded 3D carrier resolvent

The ambient carrier height operator is diagonal on the geometric state space
`CarrierState3D p r`, which was defined before any zero or event certificate.  Its ordinate is
unbounded, so its native receiver is an algebraic unbounded resolvent rather than a bounded
C-star-algebra element.  This file constructs that resolvent directly and proves its two-sided
inverse law at every nonreal spectral parameter.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.ThreeDFocal

variable {ι : Type*}

/-- Complex diagonal multiplication on finitely supported modes. -/
noncomputable def complexDiagOp (d : ι → ℂ) : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ) :=
  Finsupp.lsum ℂ (fun i => d i • Finsupp.lsingle i)

@[simp] theorem complexDiagOp_apply (d : ι → ℂ) (f : ι →₀ ℂ) (i : ι) :
    complexDiagOp d f i = d i * f i := by
  unfold complexDiagOp
  simp +decide [Finsupp.sum]
  rw [Finset.sum_eq_single i] <;> aesop

/-- The spectral shift `z - H` of the event-independent ambient carrier operator. -/
noncomputable def carrierThreeDShift (p r : ℝ) (z : ℂ) :
    CarrierThreeDMode p r →ₗ[ℂ] CarrierThreeDMode p r :=
  complexDiagOp fun s => z - (s.ordinate : ℂ)

/-- The algebraic resolvent of the full ambient carrier height operator. -/
noncomputable def carrierThreeDResolvent (p r : ℝ) (z : ℂ) :
    CarrierThreeDMode p r →ₗ[ℂ] CarrierThreeDMode p r :=
  complexDiagOp fun s => (z - (s.ordinate : ℂ))⁻¹

/-- The shift is literally `z·I - H` on every finitely supported carrier wave. -/
theorem carrierThreeDShift_eq_sub_operator (p r : ℝ) (z : ℂ) :
    carrierThreeDShift p r z = z • LinearMap.id - carrierThreeDOperator p r := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro s
  simp [carrierThreeDShift, carrierThreeDOperator, complexDiagOp_apply,
    UnconditionalFrobenius.diagOp_apply]
  ring

/-- A nonreal parameter misses every real ordinate of the ambient carrier. -/
theorem carrierThreeD_nonreal_sub_ordinate_ne_zero {p r : ℝ} {z : ℂ}
    (hz : z.im ≠ 0) (s : CarrierState3D p r) :
    z - (s.ordinate : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at him
  exact hz him

/-- At every nonreal parameter the ambient resolvent is a left inverse of `z - H`. -/
theorem carrierThreeDShift_comp_resolvent {p r : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    (carrierThreeDShift p r z).comp (carrierThreeDResolvent p r z) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro s
  simp only [LinearMap.comp_apply, carrierThreeDShift, carrierThreeDResolvent,
    complexDiagOp_apply, LinearMap.id_apply]
  rw [← mul_assoc, mul_inv_cancel₀ (carrierThreeD_nonreal_sub_ordinate_ne_zero hz s), one_mul]

/-- At every nonreal parameter the ambient resolvent is a right inverse of `z - H`. -/
theorem carrierThreeDResolvent_comp_shift {p r : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    (carrierThreeDResolvent p r z).comp (carrierThreeDShift p r z) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro s
  simp only [LinearMap.comp_apply, carrierThreeDShift, carrierThreeDResolvent,
    complexDiagOp_apply, LinearMap.id_apply]
  rw [← mul_assoc, inv_mul_cancel₀ (carrierThreeD_nonreal_sub_ordinate_ne_zero hz s), one_mul]

/-- The resolvent matrix coefficient at a geometric carrier basis state. -/
noncomputable def carrierBasisResolventReadout {p r : ℝ}
    (s : CarrierState3D p r) (z : ℂ) : ℂ :=
  carrierThreeDResolvent p r z (Finsupp.single s 1) s

/-- Every geometric carrier basis receiver is the expected scalar resolvent. -/
theorem carrierBasisResolventReadout_eq {p r : ℝ} (s : CarrierState3D p r) (z : ℂ) :
    carrierBasisResolventReadout s z = (z - (s.ordinate : ℂ))⁻¹ := by
  simp [carrierBasisResolventReadout, carrierThreeDResolvent, complexDiagOp_apply]

/-- Every basis receiver has a finite punctured limit at every nonreal parameter. -/
theorem carrierBasisResolventReadout_regular_off_real {p r : ℝ}
    (s : CarrierState3D p r) {z₀ : ℂ} (hz : z₀.im ≠ 0) :
    ∃ L, Tendsto (carrierBasisResolventReadout s) (𝓝[≠] z₀) (𝓝 L) := by
  have hne : z₀ - (s.ordinate : ℂ) ≠ 0 :=
    carrierThreeD_nonreal_sub_ordinate_ne_zero hz s
  have hcont : ContinuousAt (fun z : ℂ => (z - (s.ordinate : ℂ))⁻¹) z₀ := by
    fun_prop
  refine ⟨(z₀ - (s.ordinate : ℂ))⁻¹, ?_⟩
  rw [show carrierBasisResolventReadout s = fun z : ℂ => (z - (s.ordinate : ℂ))⁻¹ by
    funext z
    exact carrierBasisResolventReadout_eq s z]
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

#print axioms CriticalLinePhasor.ThreeDFocal.carrierThreeDShift_eq_sub_operator
#print axioms CriticalLinePhasor.ThreeDFocal.carrierThreeD_nonreal_sub_ordinate_ne_zero
#print axioms CriticalLinePhasor.ThreeDFocal.carrierThreeDShift_comp_resolvent
#print axioms CriticalLinePhasor.ThreeDFocal.carrierThreeDResolvent_comp_shift
#print axioms CriticalLinePhasor.ThreeDFocal.carrierBasisResolventReadout_eq
#print axioms CriticalLinePhasor.ThreeDFocal.carrierBasisResolventReadout_regular_off_real

end CriticalLinePhasor.ThreeDFocal
