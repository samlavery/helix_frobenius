import RequestProject.GlobalHelixThetaTerms
import RequestProject.CarrierThetaIdentification

/-!
# Canonical 3D attribution of coefficient-theta terms

Each coefficient is stored in the 3D carrier as radius and phase, while its dilated kernel height
is stored as signed log-height.  Polar reconstruction returns the coefficient exactly.  The global
involution conjugates the coefficient and reciprocates the multiplicative height; starting from the
dual coefficient and applying the index-ledger shear reconstructs the primal reciprocal-height term.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection CriticalLinePhasor.CarrierTheta

/-- Reconstruct the complex phasor carried by a 3D fiber's radial and phase ledger. -/
noncomputable def fiberPhasor (f : Fiber) : ℂ :=
  (radial f : ℂ) * Complex.exp (I * (phase f : ℂ))

/-- The global 3D involution conjugates the fiber phasor. -/
theorem fiberPhasor_globalHelixInvolution (f : Fiber) :
    fiberPhasor (globalHelixInvolution f) = (starRingEnd ℂ) (fiberPhasor f) := by
  unfold fiberPhasor
  rw [radial_globalHelixInvolution, phase_globalHelixInvolution, map_mul,
    Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp

/-- A height shear changes only the third coordinate, so it preserves the carried phasor. -/
theorem fiberPhasor_heightShear (c : ℝ) (f : Fiber) :
    fiberPhasor (heightShear c f) = fiberPhasor f := by
  rfl

/-- The canonical 3D source point for the `n`th coefficient-theta term. -/
noncomputable def coefficientFiber (a : ℕ → ℂ) (n : ℕ) (x : ℝ) : Fiber :=
  (‖a n‖, Complex.arg (a n), Real.log (((n + 1 : ℕ) : ℝ) * x))

/-- Polar reconstruction of the canonical coefficient fiber returns the coefficient exactly. -/
theorem fiberPhasor_coefficientFiber (a : ℕ → ℂ) (n : ℕ) (x : ℝ) :
    fiberPhasor (coefficientFiber a n x) = a n := by
  simpa [fiberPhasor, coefficientFiber, radial, phase, mul_comm] using
    Complex.norm_mul_exp_arg_mul_I (a n)

/-- The coefficient fiber stores the standard dilated kernel height `(n+1)x`. -/
theorem multiplicativeHeight_coefficientFiber
    (a : ℕ → ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    multiplicativeHeight (coefficientFiber a n x) = ((n + 1 : ℕ) : ℝ) * x := by
  unfold multiplicativeHeight heightEncode coefficientFiber height
  rw [Real.exp_log]
  positivity

/-- Start from the dual coefficient, apply the global involution, then apply the exact index shear. -/
noncomputable def reciprocalCoefficientFiber
    (aDual : ℕ → ℂ) (n : ℕ) (x : ℝ) : Fiber :=
  heightShear (thetaIndexShear n)
    (globalHelixInvolution (coefficientFiber aDual n x))

/-- If the dual coefficients are conjugates, the transformed 3D fiber reconstructs the primal
coefficient. -/
theorem fiberPhasor_reciprocalCoefficientFiber_conj
    (a : ℕ → ℂ) (n : ℕ) (x : ℝ) :
    fiberPhasor
        (reciprocalCoefficientFiber (fun m => (starRingEnd ℂ) (a m)) n x) = a n := by
  rw [reciprocalCoefficientFiber, fiberPhasor_heightShear,
    fiberPhasor_globalHelixInvolution]
  rw [fiberPhasor_coefficientFiber]
  simp

/-- The same transformed coefficient fiber lands at the primal reciprocal term height `(n+1)/x`. -/
theorem multiplicativeHeight_reciprocalCoefficientFiber
    (aDual : ℕ → ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    multiplicativeHeight (reciprocalCoefficientFiber aDual n x) =
      ((n + 1 : ℕ) : ℝ) / x := by
  rw [reciprocalCoefficientFiber,
    multiplicativeHeight_heightShear (thetaIndexShear_pos n),
    multiplicativeHeight_globalHelixInvolution,
    multiplicativeHeight_coefficientFiber aDual n hx]
  unfold thetaIndexShear
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  field_simp

/-- Exact 3D attribution of one reciprocal-height primal theta term to the transformed dual fiber. -/
theorem coefficientKernelTerm_as_transformedDualFiber
    (a : ℕ → ℂ) (g : ℝ → ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    a n * g (((n + 1 : ℕ) : ℝ) / x) =
      fiberPhasor
          (reciprocalCoefficientFiber (fun m => (starRingEnd ℂ) (a m)) n x) *
        g (multiplicativeHeight
          (reciprocalCoefficientFiber (fun m => (starRingEnd ℂ) (a m)) n x)) := by
  rw [fiberPhasor_reciprocalCoefficientFiber_conj,
    multiplicativeHeight_reciprocalCoefficientFiber _ n hx]

/-- Exact 3D attribution of the full reciprocal-height primal theta to the transformed dual bank. -/
theorem theta_one_div_as_transformedDualFibers
    (a : ℕ → ℂ) (g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    theta a g (1 / x) =
      ∑' n : ℕ,
        fiberPhasor
            (reciprocalCoefficientFiber (fun m => (starRingEnd ℂ) (a m)) n x) *
          g (multiplicativeHeight
            (reciprocalCoefficientFiber (fun m => (starRingEnd ℂ) (a m)) n x)) := by
  unfold theta
  apply tsum_congr
  intro n
  rw [show ((n + 1 : ℕ) : ℝ) * (1 / x) = ((n + 1 : ℕ) : ℝ) / x by ring]
  exact coefficientKernelTerm_as_transformedDualFiber a g n hx

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.fiberPhasor_globalHelixInvolution
#print axioms CriticalLinePhasor.GlobalHelix.fiberPhasor_heightShear
#print axioms CriticalLinePhasor.GlobalHelix.fiberPhasor_coefficientFiber
#print axioms CriticalLinePhasor.GlobalHelix.multiplicativeHeight_coefficientFiber
#print axioms CriticalLinePhasor.GlobalHelix.fiberPhasor_reciprocalCoefficientFiber_conj
#print axioms CriticalLinePhasor.GlobalHelix.multiplicativeHeight_reciprocalCoefficientFiber
#print axioms CriticalLinePhasor.GlobalHelix.coefficientKernelTerm_as_transformedDualFiber
#print axioms CriticalLinePhasor.GlobalHelix.theta_one_div_as_transformedDualFibers
