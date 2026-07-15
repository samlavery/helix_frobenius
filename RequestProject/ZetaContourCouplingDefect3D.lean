import RequestProject.ZetaContourNative3D

/-!
# The global contour defect as uncoupled analytic-kernel multiplicity

The independently continued contour coordinate counts every analytic zero in its strip.  The native
coordinate counts completed carrier events.  `SpectralCarrierKernelCoupling3D` supplies the exact
same-parameter bridge between these two operator presentations whenever a zero is represented on
the carrier.

This file rewrites the already-proved off-carrier multiplicity as the total analytic order of the
full spectral kernels that have no such coupling.  Positivity of analytic orders then proves that
the two global coordinates agree exactly when every enclosed analytic kernel possesses the compiled
3D coupling object.
-/

open Complex

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.ResidueJump
open CriticalLinePhasor.SpectralFiber
open CriticalLinePhasor.SpectralCarrierCoupling
open CriticalLinePhasor.ThreeDFocal

/-- Multiplicity of full analytic zeta kernels in the independent strip census that do not possess
a parameter-preserving realization on the ambient 3D carrier. -/
noncomputable def uncoupledKernelCountMult
    (χ₁ : DirichletCharacter ℂ 1) (T : ℝ) : ℕ :=
  by
    classical
    exact ∑ ρ ∈ (stripZeroFinset T).filter (fun ρ =>
        ¬ Nonempty (SpectralCarrierKernelCoupling3D χ₁ 1 1 ρ)),
      ZD.xiOrderNat ρ

/-- Multiplicity of independent strip kernels whose radial projection has nontrivial drift at the
chosen base.  No midpoint value occurs in this predicate. -/
noncomputable def radialDriftKernelCountMult (T n : ℝ) : ℕ := by
  classical
  exact ∑ ρ ∈ (stripZeroFinset T).filter (fun ρ =>
      n ^ (ρ.re - carrierAbscissa) ≠ 1), ZD.xiOrderNat ρ

/-- Inside the independent strip census, failure of the compiled kernel coupling is exactly failure
of carrier representability.  The analytic-zero clause is supplied by membership in the strip;
the carrier abscissa is the area-law output. -/
theorem stripZero_not_coupled_iff_offCarrier
    (χ₁ : DirichletCharacter ℂ 1) {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ stripZeroFinset T) :
    (¬ Nonempty (SpectralCarrierKernelCoupling3D χ₁ 1 1 ρ)) ↔ ρ.re ≠ 1 / 2 := by
  have hstrip := (stripZeroWindow_finite T).mem_toFinset.mp hρ
  have hzero : Lspec χ₁ ρ = 0 := by
    simpa only [Lspec, DirichletCharacter.LFunction_modOne_eq] using hstrip.1.2.2
  rw [nonempty_coupling_iff]
  simp [hzero, carrierAbscissa_eq_half]

/-- The coupling defect is definitionally independent of the old line/off-line partition, but the
two finite sums coincide term for term. -/
theorem uncoupledKernelCountMult_eq_offLine
    (χ₁ : DirichletCharacter ℂ 1) (T : ℝ) :
    uncoupledKernelCountMult χ₁ T = offLineStripZeroCountMult T := by
  classical
  unfold uncoupledKernelCountMult offLineStripZeroCountMult
  have hfilter :
      (stripZeroFinset T).filter (fun ρ =>
          ¬ Nonempty (SpectralCarrierKernelCoupling3D χ₁ 1 1 ρ)) =
        (stripZeroFinset T).filter (fun ρ => ρ.re ≠ 1 / 2) := by
    apply Finset.filter_congr
    intro ρ hρ
    exact stripZero_not_coupled_iff_offCarrier χ₁ hρ
  rw [hfilter]

/-- For every base greater than one, uncoupled analytic kernels are exactly the kernels with
nontrivial radial drift.  This identifies the operator defect without inserting the half-unit. -/
theorem uncoupledKernelCountMult_eq_radialDrift
    (χ₁ : DirichletCharacter ℂ 1) (T n : ℝ) (hn : 1 < n) :
    uncoupledKernelCountMult χ₁ T = radialDriftKernelCountMult T n := by
  classical
  unfold uncoupledKernelCountMult radialDriftKernelCountMult
  apply Finset.sum_bij (fun ρ _ => ρ)
  · intro ρ hρ
    have hmem := (Finset.mem_filter.mp hρ).1
    have hstrip := (stripZeroWindow_finite T).mem_toFinset.mp hmem
    have hzero : Lspec χ₁ ρ = 0 := by
      simpa only [Lspec, DirichletCharacter.LFunction_modOne_eq] using hstrip.1.2.2
    apply Finset.mem_filter.mpr
    refine ⟨hmem, ?_⟩
    exact radialDrift_of_lspecZero_of_noCoupling χ₁ 1 1 n ρ hn hzero
      (Finset.mem_filter.mp hρ).2
  · intro ρ₁ hρ₁ ρ₂ hρ₂ heq
    exact heq
  · intro ρ hρ
    have hmem := (Finset.mem_filter.mp hρ).1
    have hstrip := (stripZeroWindow_finite T).mem_toFinset.mp hmem
    have hzero : Lspec χ₁ ρ = 0 := by
      simpa only [Lspec, DirichletCharacter.LFunction_modOne_eq] using hstrip.1.2.2
    refine ⟨ρ, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨hmem, ?_⟩
    intro hcoupling
    have hnoDrift :=
      ((nonempty_coupling_iff_zero_and_noRadialDrift χ₁ 1 1 n ρ hn).1
        ⟨Classical.choice hcoupling⟩).2
    exact (Finset.mem_filter.mp hρ).2 hnoDrift
  · intro ρ hρ
    rfl

/-- The independent contour coordinate is the native coordinate plus the exact multiplicity of
analytic kernels not represented by a same-parameter 3D coupling. -/
theorem classicalSContour_eq_Smult_add_uncoupledKernelCount
    (χ₁ : DirichletCharacter ℂ 1) {T : ℝ} (hT : GoodHeight T) :
    classicalSContour hT =
      Smult T + (uncoupledKernelCountMult χ₁ T : ℝ) := by
  rw [classicalSContour_eq_Smult_add_offLine hT,
    uncoupledKernelCountMult_eq_offLine]

/-- No-drift form of the global-coordinate law.  The entire defect is the positive multiplicity
of analytic kernels whose radial projection drifts away from the area-law carrier. -/
theorem classicalSContour_eq_Smult_add_radialDriftKernelCount
    (χ₁ : DirichletCharacter ℂ 1) {T n : ℝ} (hT : GoodHeight T) (hn : 1 < n) :
    classicalSContour hT = Smult T + (radialDriftKernelCountMult T n : ℝ) := by
  rw [classicalSContour_eq_Smult_add_uncoupledKernelCount χ₁ hT,
    uncoupledKernelCountMult_eq_radialDrift χ₁ T n hn]

/-- Vanishing of the coupling defect is equivalent to every analytic zero in the finite strip
possessing a parameter-preserving 3D kernel coupling.  Positive analytic orders rule out hidden
cancellation in the sum. -/
theorem uncoupledKernelCountMult_eq_zero_iff
    (χ₁ : DirichletCharacter ℂ 1) (T : ℝ) :
    uncoupledKernelCountMult χ₁ T = 0 ↔
      ∀ ρ ∈ stripZeroFinset T,
        Nonempty (SpectralCarrierKernelCoupling3D χ₁ 1 1 ρ) := by
  classical
  constructor
  · intro hzero ρ hρ
    by_contra hnot
    have hmem : ρ ∈ (stripZeroFinset T).filter (fun z =>
        ¬ Nonempty (SpectralCarrierKernelCoupling3D χ₁ 1 1 z)) :=
      Finset.mem_filter.mpr ⟨hρ, hnot⟩
    have hterm : ZD.xiOrderNat ρ = 0 := by
      unfold uncoupledKernelCountMult at hzero
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ => Nat.zero_le (ZD.xiOrderNat z))).mp hzero ρ hmem
    have hstrip := (stripZeroWindow_finite T).mem_toFinset.mp hρ
    exact (Nat.ne_of_gt (ZD.xiOrderNat_pos_of_mem_NontrivialZeros hstrip.1)) hterm
  · intro hall
    unfold uncoupledKernelCountMult
    have hempty :
        (stripZeroFinset T).filter (fun z =>
            ¬ Nonempty (SpectralCarrierKernelCoupling3D χ₁ 1 1 z)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro ρ hρ
      exact not_not_intro (hall ρ hρ)
    rw [hempty]
    simp

/-- Exact global-coordinate identification criterion in the coupled operator language.  At a good
height the independent and native coordinates agree precisely when every enclosed analytic kernel
has been realized by the completed focal event and both 3D/self-adjoint operator kernels at the
same parameter. -/
theorem classicalSContour_eq_Smult_iff_everyKernelCoupled
    (χ₁ : DirichletCharacter ℂ 1) {T : ℝ} (hT : GoodHeight T) :
    classicalSContour hT = Smult T ↔
      ∀ ρ ∈ stripZeroFinset T,
        Nonempty (SpectralCarrierKernelCoupling3D χ₁ 1 1 ρ) := by
  rw [classicalSContour_eq_Smult_iff_offLine_eq_zero hT,
    ← uncoupledKernelCountMult_eq_offLine χ₁ T,
    uncoupledKernelCountMult_eq_zero_iff]

/-- Midpoint-free global identification criterion: the independently continued and native
coordinates agree exactly when every enclosed analytic kernel has zero radial drift. -/
theorem classicalSContour_eq_Smult_iff_everyKernelNoRadialDrift
    (χ₁ : DirichletCharacter ℂ 1) {T n : ℝ} (hT : GoodHeight T) (hn : 1 < n) :
    classicalSContour hT = Smult T ↔
      ∀ ρ ∈ stripZeroFinset T, n ^ (ρ.re - carrierAbscissa) = 1 := by
  rw [classicalSContour_eq_Smult_iff_everyKernelCoupled χ₁ hT]
  constructor
  · intro hall ρ hρ
    exact ((nonempty_coupling_iff_zero_and_noRadialDrift χ₁ 1 1 n ρ hn).1
      (hall ρ hρ)).2
  · intro hall ρ hρ
    have hstrip := (stripZeroWindow_finite T).mem_toFinset.mp hρ
    have hzero : Lspec χ₁ ρ = 0 := by
      simpa only [Lspec, DirichletCharacter.LFunction_modOne_eq] using hstrip.1.2.2
    exact (nonempty_coupling_iff_zero_and_noRadialDrift χ₁ 1 1 n ρ hn).2
      ⟨hzero, hall ρ hρ⟩

/-- The global upper-zero dichotomy projected directly to the coupled operator object. -/
theorem upper_nontrivialZero_kernelCoupling_or_globalCoordinateDefect
    (χ₁ : DirichletCharacter ℂ 1) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (hρim : 0 < ρ.im) :
    Nonempty (SpectralCarrierKernelCoupling3D χ₁ 1 1 ρ) ∨
      ∃ T : ℝ, ∃ hT : GoodHeight T,
        ρ.im < T ∧ classicalSContour hT ≠ Smult T := by
  rcases upper_nontrivialZero_native3DCertificate_or_globalCoordinateDefect χ₁ hρ hρim with
    hC | hdefect
  · rcases hC with ⟨C⟩
    exact Or.inl ⟨C.kernelCoupling⟩
  · exact Or.inr hdefect

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.stripZero_not_coupled_iff_offCarrier
#print axioms CriticalLinePhasor.ContourArgument.uncoupledKernelCountMult_eq_offLine
#print axioms CriticalLinePhasor.ContourArgument.uncoupledKernelCountMult_eq_radialDrift
#print axioms CriticalLinePhasor.ContourArgument.classicalSContour_eq_Smult_add_uncoupledKernelCount
#print axioms CriticalLinePhasor.ContourArgument.classicalSContour_eq_Smult_add_radialDriftKernelCount
#print axioms CriticalLinePhasor.ContourArgument.uncoupledKernelCountMult_eq_zero_iff
#print axioms CriticalLinePhasor.ContourArgument.classicalSContour_eq_Smult_iff_everyKernelCoupled
#print axioms CriticalLinePhasor.ContourArgument.classicalSContour_eq_Smult_iff_everyKernelNoRadialDrift
#print axioms CriticalLinePhasor.ContourArgument.upper_nontrivialZero_kernelCoupling_or_globalCoordinateDefect
