import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import RequestProject.GlobalHelixIntertwiner

/-!
# Gaussian lattice theta as a 1D projection of the global 3D involution

Mathlib's Gaussian Poisson theorem supplies the exact one-dimensional self-dual lattice clock.
Taking a finite Cartesian power gives the dimension-`d` lattice theta.  The reciprocal scale in its
reflection is then rewritten as the multiplicative height of the global helix involution `J`.
-/

open Real Complex

namespace CriticalLinePhasor.GlobalHelix

/-- The self-dual one-dimensional Gaussian lattice clock. -/
noncomputable def gaussianLatticeTheta (x : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-Real.pi * x * (n : ℝ) ^ 2)

/-- The product Gaussian theta of the standard lattice `ℤ^d`. -/
noncomputable def gaussianLatticeThetaDim (d : ℕ) (x : ℝ) : ℝ :=
  (gaussianLatticeTheta x) ^ d

/-- Exact one-dimensional Gaussian theta reflection. -/
theorem gaussianLatticeTheta_reflection {x : ℝ} (hx : 0 < x) :
    gaussianLatticeTheta x =
      (1 / x ^ (1 / 2 : ℝ)) * gaussianLatticeTheta (1 / x) := by
  simpa [gaussianLatticeTheta, div_eq_mul_inv, mul_assoc] using
    Real.tsum_exp_neg_mul_int_sq hx

/-- Exact dimension-`d` Gaussian lattice reflection, obtained by the Cartesian product bank. -/
theorem gaussianLatticeThetaDim_reflection (d : ℕ) {x : ℝ} (hx : 0 < x) :
    gaussianLatticeThetaDim d x =
      (1 / x ^ (1 / 2 : ℝ)) ^ d * gaussianLatticeThetaDim d (1 / x) := by
  unfold gaussianLatticeThetaDim
  rw [gaussianLatticeTheta_reflection hx, mul_pow]

/-- The reciprocal lattice scale is literally the multiplicative height after the global 3D
helix/anti-helix involution. -/
theorem gaussianLatticeThetaDim_globalHelixInvolution (d : ℕ) (f : ConeProjection.Fiber) :
    gaussianLatticeThetaDim d (multiplicativeHeight f) =
      (1 / (multiplicativeHeight f) ^ (1 / 2 : ℝ)) ^ d *
        gaussianLatticeThetaDim d
          (multiplicativeHeight (globalHelixInvolution f)) := by
  rw [multiplicativeHeight_globalHelixInvolution]
  exact gaussianLatticeThetaDim_reflection d (multiplicativeHeight_pos f)

/-- Complex-valued 1D readout of the same global 3D Gaussian lattice bank. -/
noncomputable def gaussianLatticeReadout (d : ℕ) (f : ConeProjection.Fiber) : ℂ :=
  gaussianLatticeThetaDim d (multiplicativeHeight f)

/-- The global `J` reflection in the complex readout channel. -/
theorem gaussianLatticeReadout_globalHelixInvolution (d : ℕ) (f : ConeProjection.Fiber) :
    gaussianLatticeReadout d f =
      (((1 / (multiplicativeHeight f) ^ (1 / 2 : ℝ)) ^ d : ℝ) : ℂ) *
        gaussianLatticeReadout d (globalHelixInvolution f) := by
  unfold gaussianLatticeReadout
  rw [gaussianLatticeThetaDim_globalHelixInvolution]
  norm_num

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.gaussianLatticeTheta_reflection
#print axioms CriticalLinePhasor.GlobalHelix.gaussianLatticeThetaDim_reflection
#print axioms CriticalLinePhasor.GlobalHelix.gaussianLatticeThetaDim_globalHelixInvolution
#print axioms CriticalLinePhasor.GlobalHelix.gaussianLatticeReadout_globalHelixInvolution
