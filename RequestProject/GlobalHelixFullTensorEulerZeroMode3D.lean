import RequestProject.GlobalHelixLocalEulerBounds
import RequestProject.GlobalHelixZeroModeGaussian
import RequestProject.GlobalHelixBilateralTensorCompletion

/-!
# The full tensor-Euler exponent lattice as a zero-mode-free 3D helix bank

The actual Euler seed is supported on the nonnegative orthant of the integral exponent lattice.
The opposite orthant is retained as the reciprocal-height index bank for the reflected anti-helix.
This module proves the geometric reflection before imposing analytic summability hypotheses.
-/

open Real Complex

namespace CriticalLinePhasor.GlobalHelix

/-- The actual full tensor-Euler source on the integral exponent lattice. -/
noncomputable def fullTensorEulerZeroMode3DBankReadout
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (c x : ℝ) : ℂ :=
  indexedZeroModeGaussian3DBankReadout
    (bilateralTensorEulerSeed S W) (bilateralEulerHeight S q) c x

/-- The reciprocal-height anti-helix indexed by the opposite exponent orthant. -/
noncomputable def fullTensorEulerZeroMode3DTransformedReadout
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (c x : ℝ) : ℂ :=
  indexedZeroModeGaussian3DTransformedReadout
    (bilateralTensorEulerSeed S W) (bilateralEulerHeight S q)
    (negExponentEquiv S) c x

/-- Exact 3D reflection on the complete integral exponent lattice. -/
theorem fullTensorEulerZeroMode3D_globalHelixReflection
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 0 < q v) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    fullTensorEulerZeroMode3DBankReadout S W q c x =
      ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        fullTensorEulerZeroMode3DTransformedReadout S W q c x := by
  exact indexedZeroModeGaussian3D_globalHelixReflection
    (bilateralTensorEulerSeed S W) (bilateralEulerHeight S q)
    (negExponentEquiv S) (bilateralEulerHeight_pos S q hq)
    (fun k => bilateralEulerHeight_neg S q k) hc hx

/-- Scalar projection of the primal full-lattice 3D bank. -/
theorem fullTensorEulerZeroMode3DBankReadout_eq_theta
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 0 < q v) (c : ℝ) {x : ℝ} (hx : 0 < x) :
    fullTensorEulerZeroMode3DBankReadout S W q c x =
      indexedZeroModeGaussianTheta
        (bilateralTensorEulerSeed S W) (bilateralEulerHeight S q) c x := by
  exact indexedZeroModeGaussian3DBankReadout_eq_theta
    (bilateralTensorEulerSeed S W) (bilateralEulerHeight S q)
    (bilateralEulerHeight_pos S q hq) c hx

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.fullTensorEulerZeroMode3D_globalHelixReflection
#print axioms CriticalLinePhasor.GlobalHelix.fullTensorEulerZeroMode3DBankReadout_eq_theta
