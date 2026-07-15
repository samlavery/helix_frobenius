import RequestProject.GlobalHelixBilateralEulerHeight

/-!
# Gaussian Poisson lifts of arbitrary 3D helix banks

The source is a bank of coefficient fibers at positive heights `H i * x`.  Gaussian Poisson
reflection is applied to each height, the index bank is transported through an arbitrary height-
reciprocal equivalence, and the result is rebuilt from sheared anti-helix fibers at heights
`H i / x`.  The scalar theta series occurs only after these 3D constructions are defined.
-/

open Real Complex

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection

/-- Coefficient transported to the reciprocal-height index, with the Gaussian half-density. -/
noncomputable def gaussianPoissonDualAmplitude {I : Type*}
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I) (i : I) : ℂ :=
  a (dual.symm i) * ((H i) ^ (1 / 2 : ℝ) : ℝ)

/-- The reciprocal Gaussian square-root scale splits into index height and external height. -/
theorem reciprocalGaussianHalfScale {H x : ℝ} (hH : 0 < H) (hx : 0 < x) :
    1 / (H⁻¹ * x) ^ (1 / 2 : ℝ) =
      H ^ (1 / 2 : ℝ) * (1 / x ^ (1 / 2 : ℝ)) := by
  rw [Real.mul_rpow (inv_nonneg.mpr hH.le) hx.le, Real.inv_rpow hH.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hH _),
    ne_of_gt (Real.rpow_pos_of_pos hx _)]

/-- Gaussian reflection at a reciprocal source height. -/
theorem gaussianLatticeTheta_reciprocal_mul {H x : ℝ} (hH : 0 < H) (hx : 0 < x) :
    gaussianLatticeTheta (H⁻¹ * x) =
      (H ^ (1 / 2 : ℝ) * (1 / x ^ (1 / 2 : ℝ))) *
        gaussianLatticeTheta (H / x) := by
  rw [gaussianLatticeTheta_reflection (mul_pos (inv_pos.mpr hH) hx)]
  rw [reciprocalGaussianHalfScale hH hx]
  congr 2
  field_simp [hH.ne', hx.ne']

/-- The primal Gaussian-weighted bank, defined from its 3D coefficient fibers. -/
noncomputable def indexedGaussian3DBankReadout {I : Type*}
    (a : I → ℂ) (H : I → ℝ) (x : ℝ) : ℂ :=
  ∑' i : I,
    fiberPhasor (indexedCoefficientFiber a H i x) *
      (gaussianLatticeTheta
        (multiplicativeHeight (indexedCoefficientFiber a H i x)) : ℂ)

/-- Its scalar projection is the indexed Gaussian theta lift. -/
theorem indexedGaussian3DBankReadout_eq_theta {I : Type*}
    (a : I → ℂ) (H : I → ℝ) (hH : ∀ i, 0 < H i)
    {x : ℝ} (hx : 0 < x) :
    indexedGaussian3DBankReadout a H x =
      indexedTheta a H (fun t => (gaussianLatticeTheta t : ℂ)) x := by
  unfold indexedGaussian3DBankReadout indexedTheta
  apply tsum_congr
  intro i
  rw [fiberPhasor_indexedCoefficientFiber,
    multiplicativeHeight_indexedCoefficientFiber a H hH i hx]

/-- The transported bank, built from the global 3D involution and exact height shear. -/
noncomputable def indexedGaussian3DTransformedReadout {I : Type*}
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I) (x : ℝ) : ℂ :=
  ∑' i : I,
    fiberPhasor
        (indexedReciprocalCoefficientFiber
          (fun j => (starRingEnd ℂ) (gaussianPoissonDualAmplitude a H dual j)) H i x) *
      (gaussianLatticeTheta
        (multiplicativeHeight
          (indexedReciprocalCoefficientFiber
            (fun j => (starRingEnd ℂ) (gaussianPoissonDualAmplitude a H dual j)) H i x)) : ℂ)

/-- Scalar projection of the transported 3D bank is the dual lift at reciprocal external height. -/
theorem indexedGaussian3DTransformedReadout_eq_theta {I : Type*}
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I) (hH : ∀ i, 0 < H i)
    {x : ℝ} (hx : 0 < x) :
    indexedGaussian3DTransformedReadout a H dual x =
      indexedTheta (gaussianPoissonDualAmplitude a H dual) H
        (fun t => (gaussianLatticeTheta t : ℂ)) (1 / x) := by
  unfold indexedGaussian3DTransformedReadout indexedTheta
  apply tsum_congr
  intro i
  rw [fiberPhasor_indexedReciprocalCoefficientFiber_conj,
    multiplicativeHeight_indexedReciprocalCoefficientFiber _ H hH i hx]
  congr 2
  ring

/-- Poisson reflection for the scalar projections of an arbitrary reciprocal-height bank. -/
theorem indexedGaussianTheta_reflection {I : Type*}
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (hrecip : ∀ i, H (dual.symm i) = (H i)⁻¹)
    {x : ℝ} (hx : 0 < x) :
    indexedTheta a H (fun t => (gaussianLatticeTheta t : ℂ)) x =
      ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        indexedTheta (gaussianPoissonDualAmplitude a H dual) H
          (fun t => (gaussianLatticeTheta t : ℂ)) (1 / x) := by
  unfold indexedTheta gaussianPoissonDualAmplitude
  calc
    (∑' i, a i * (gaussianLatticeTheta (H i * x) : ℂ)) =
        ∑' i, a (dual.symm i) *
          (gaussianLatticeTheta (H (dual.symm i) * x) : ℂ) := by
      exact (Equiv.tsum_eq dual.symm
        (fun i => a i * (gaussianLatticeTheta (H i * x) : ℂ))).symm
    _ = ∑' i, a (dual.symm i) *
          (((H i) ^ (1 / 2 : ℝ) * (1 / x ^ (1 / 2 : ℝ)) : ℝ) : ℂ) *
            (gaussianLatticeTheta (H i / x) : ℂ) := by
      apply tsum_congr
      intro i
      rw [hrecip, gaussianLatticeTheta_reciprocal_mul (hH i) hx]
      push_cast
      ring
    _ = ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ∑' i, (a (dual.symm i) * ((H i) ^ (1 / 2 : ℝ) : ℝ)) *
            (gaussianLatticeTheta (H i * (1 / x)) : ℂ) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro i
      push_cast
      ring

/-- The full identity rebuilt as equality of the primal and transformed 3D helix banks. -/
theorem indexedGaussian3D_globalHelixReflection {I : Type*}
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (hrecip : ∀ i, H (dual.symm i) = (H i)⁻¹)
    {x : ℝ} (hx : 0 < x) :
    indexedGaussian3DBankReadout a H x =
      ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        indexedGaussian3DTransformedReadout a H dual x := by
  rw [indexedGaussian3DBankReadout_eq_theta a H hH hx,
    indexedGaussian3DTransformedReadout_eq_theta a H dual hH hx]
  exact indexedGaussianTheta_reflection a H dual hH hrecip hx

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.reciprocalGaussianHalfScale
#print axioms CriticalLinePhasor.GlobalHelix.gaussianLatticeTheta_reciprocal_mul
#print axioms CriticalLinePhasor.GlobalHelix.indexedGaussian3DBankReadout_eq_theta
#print axioms CriticalLinePhasor.GlobalHelix.indexedGaussian3DTransformedReadout_eq_theta
#print axioms CriticalLinePhasor.GlobalHelix.indexedGaussianTheta_reflection
#print axioms CriticalLinePhasor.GlobalHelix.indexedGaussian3D_globalHelixReflection
