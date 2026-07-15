import RequestProject.GlobalHelixGaussianSourceRegistration

/-!
# Gaussian source registration for the fixed completion clock

The zero-parameter completion clock is the Gaussian kernel after the geometric rescaling
`t ↦ t/2`.  Consequently every nonzero lattice mode is carried by coefficient `1/2` at height
`n²/2`; the zero lattice mode is the residual constant channel.  This file proves that this
fixed-completion 3D bank is exactly the Poisson-reflected Gaussian source bank.
-/

open Real Complex

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection

/-- The zero-parameter Gamma clock at half scale is twice the Gaussian kernel. -/
theorem gammaClock_zero_halfScale (t : ℝ) :
    gammaClock 0 (t / 2) = 2 * Real.exp (-Real.pi * t) := by
  unfold gammaClock
  norm_num
  congr 2
  ring

/-- The same identity for the prescribed singleton completion kernel. -/
theorem completionKernel_zero_halfScale (t : ℝ) :
    completionKernel [0] (t / 2) = 2 * Real.exp (-Real.pi * t) := by
  rw [completionKernel_singleton]
  exact gammaClock_zero_halfScale t

/-- The residual zero mode has coefficient one; every nonzero Gaussian mode has coefficient half. -/
noncomputable def gaussianCompletionCoeff (n : ℤ) : ℂ :=
  if n = 0 then 1 else 1 / 2

/-- The residual zero mode has unit height; every nonzero Gaussian mode has height `n²/2`. -/
noncomputable def gaussianCompletionHeight (n : ℤ) : ℝ :=
  if n = 0 then 1 else (n : ℝ) ^ 2 / 2

theorem gaussianCompletionHeight_pos (n : ℤ) : 0 < gaussianCompletionHeight n := by
  by_cases hn : n = 0
  · simp [gaussianCompletionHeight, hn]
  · simp only [gaussianCompletionHeight, hn, if_false]
    positivity

/-- The primal Gaussian bank using the prescribed fixed completion kernel off the residual mode. -/
noncomputable def gaussianFixedCompletion3DBankReadout (x : ℝ) : ℂ :=
  ∑' n : ℤ,
    if n = 0 then
      fiberPhasor
        (indexedCoefficientFiber gaussianCompletionCoeff gaussianCompletionHeight n x)
    else
      fiberPhasor
          (indexedCoefficientFiber gaussianCompletionCoeff gaussianCompletionHeight n x) *
        fixedKernelReadout [0]
          (indexedCoefficientFiber gaussianCompletionCoeff gaussianCompletionHeight n x)

/-- The fixed-completion primal bank is the Gaussian source bank, term by term in 3D. -/
theorem gaussianFixedCompletion3DBankReadout_eq_gaussian3D {x : ℝ} (hx : 0 < x) :
    gaussianFixedCompletion3DBankReadout x = gaussianLattice3DBankReadout x := by
  unfold gaussianFixedCompletion3DBankReadout gaussianLattice3DBankReadout
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [gaussianCompletionCoeff, gaussianLatticeKernelTerm,
      fiberPhasor_indexedCoefficientFiber]
  · rw [if_neg hn, fiberPhasor_indexedCoefficientFiber]
    unfold fixedKernelReadout
    rw [multiplicativeHeight_indexedCoefficientFiber
      gaussianCompletionCoeff gaussianCompletionHeight gaussianCompletionHeight_pos n hx]
    rw [fiberPhasor_indexedCoefficientFiber]
    unfold gaussianLatticeKernelTerm
    rw [if_neg hn, multiplicativeHeight_indexedCoefficientFiber
      (fun _ : ℤ => (1 : ℂ)) gaussianLatticeHeight gaussianLatticeHeight_pos n hx]
    simp only [gaussianCompletionCoeff, gaussianCompletionHeight, gaussianLatticeHeight,
      hn, if_false, one_mul]
    rw [show ((n : ℝ) ^ 2 / 2) * x = ((n : ℝ) ^ 2 * x) / 2 by ring,
      completionKernel_zero_halfScale]
    ring

/-- The transformed Gaussian bank using the prescribed fixed completion kernel. -/
noncomputable def gaussianFixedCompletion3DTransformedReadout (x : ℝ) : ℂ :=
  ∑' n : ℤ,
    if n = 0 then
      fiberPhasor
        (indexedReciprocalCoefficientFiber
          (fun n => (starRingEnd ℂ) (gaussianCompletionCoeff n))
          gaussianCompletionHeight n x)
    else
      fiberPhasor
          (indexedReciprocalCoefficientFiber
            (fun n => (starRingEnd ℂ) (gaussianCompletionCoeff n))
            gaussianCompletionHeight n x) *
        fixedKernelReadout [0]
          (indexedReciprocalCoefficientFiber
            (fun n => (starRingEnd ℂ) (gaussianCompletionCoeff n))
            gaussianCompletionHeight n x)

/-- The fixed-completion transformed bank is the transformed Gaussian source bank, term by term. -/
theorem gaussianFixedCompletion3DTransformedReadout_eq_gaussian3D
    {x : ℝ} (hx : 0 < x) :
    gaussianFixedCompletion3DTransformedReadout x =
      gaussianLattice3DTransformedReadout x := by
  unfold gaussianFixedCompletion3DTransformedReadout gaussianLattice3DTransformedReadout
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    rw [fiberPhasor_indexedReciprocalCoefficientFiber_conj]
    rw [show (fun _ : ℤ => (starRingEnd ℂ) 1) =
      fun n => (starRingEnd ℂ) ((fun _ : ℤ => (1 : ℂ)) n) by rfl,
      fiberPhasor_indexedReciprocalCoefficientFiber_conj]
    simp [gaussianCompletionCoeff, gaussianLatticeKernelTerm]
  · rw [if_neg hn, fiberPhasor_indexedReciprocalCoefficientFiber_conj]
    unfold fixedKernelReadout
    rw [multiplicativeHeight_indexedReciprocalCoefficientFiber
      _ gaussianCompletionHeight gaussianCompletionHeight_pos n hx]
    rw [show (fun _ : ℤ => (starRingEnd ℂ) 1) =
      fun n => (starRingEnd ℂ) ((fun _ : ℤ => (1 : ℂ)) n) by rfl,
      fiberPhasor_indexedReciprocalCoefficientFiber_conj]
    unfold gaussianLatticeKernelTerm
    rw [if_neg hn, multiplicativeHeight_indexedReciprocalCoefficientFiber
      _ gaussianLatticeHeight gaussianLatticeHeight_pos n hx]
    simp only [gaussianCompletionCoeff, gaussianCompletionHeight, gaussianLatticeHeight,
      hn, if_false, one_mul]
    rw [show ((n : ℝ) ^ 2 / 2) / x = (((n : ℝ) ^ 2 / x) / 2) by ring,
      completionKernel_zero_halfScale]
    ring

/-- Poisson reflection for the 3D bank with the prescribed fixed completion kernel. -/
theorem gaussianFixedCompletion3D_globalHelixReflection {x : ℝ} (hx : 0 < x) :
    gaussianFixedCompletion3DBankReadout x =
      (((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
        gaussianFixedCompletion3DTransformedReadout x := by
  rw [gaussianFixedCompletion3DBankReadout_eq_gaussian3D hx,
    gaussianFixedCompletion3DTransformedReadout_eq_gaussian3D hx]
  exact gaussianLattice3D_globalHelixReflection hx

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.gammaClock_zero_halfScale
#print axioms CriticalLinePhasor.GlobalHelix.completionKernel_zero_halfScale
#print axioms CriticalLinePhasor.GlobalHelix.gaussianCompletionHeight_pos
#print axioms CriticalLinePhasor.GlobalHelix.gaussianFixedCompletion3DBankReadout_eq_gaussian3D
#print axioms CriticalLinePhasor.GlobalHelix.gaussianFixedCompletion3DTransformedReadout_eq_gaussian3D
#print axioms CriticalLinePhasor.GlobalHelix.gaussianFixedCompletion3D_globalHelixReflection
