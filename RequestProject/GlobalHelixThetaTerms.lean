import RequestProject.GlobalHelixThetaReflection

/-!
# Theta terms on the 3D carrier

The `n`th theta term at height `x` is placed at multiplicative carrier height `(n+1)x`.  The
global involution sends this to `1/((n+1)x)`.  The same-index term at reciprocal external height
has height `(n+1)/x`; it is obtained by the exact ledgered height shear `(n+1)^2` after applying
the global involution.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection

/-- A positive multiplicative rescaling, implemented as translation in signed log-height. -/
noncomputable def heightShear (c : ℝ) (f : Fiber) : Fiber :=
  (radial f, phase f, height f + Real.log c)

/-- A positive height shear multiplies the multiplicative carrier height by its scale. -/
theorem multiplicativeHeight_heightShear {c : ℝ} (hc : 0 < c) (f : Fiber) :
    multiplicativeHeight (heightShear c f) = c * multiplicativeHeight f := by
  unfold multiplicativeHeight heightEncode heightShear height radial phase
  rw [Real.exp_add, Real.exp_log hc]
  ring

/-- The concrete 3D point carrying the `n`th theta term at external positive height `x`. -/
noncomputable def thetaTermPoint (n : ℕ) (x : ℝ) : Fiber :=
  (0, 0, Real.log (((n + 1 : ℕ) : ℝ) * x))

/-- The `n`th theta-term point has multiplicative height `(n+1)x`. -/
theorem multiplicativeHeight_thetaTermPoint (n : ℕ) {x : ℝ} (hx : 0 < x) :
    multiplicativeHeight (thetaTermPoint n x) = ((n + 1 : ℕ) : ℝ) * x := by
  unfold multiplicativeHeight heightEncode thetaTermPoint height
  rw [Real.exp_log]
  positivity

/-- The index-ledger shear scale attached to the `n`th theta term. -/
def thetaIndexShear (n : ℕ) : ℝ := (((n + 1 : ℕ) : ℝ)) ^ 2

/-- The index-ledger shear is positive. -/
theorem thetaIndexShear_pos (n : ℕ) : 0 < thetaIndexShear n := by
  unfold thetaIndexShear
  positivity

/-- Apply the global involution first, then the exact index-ledger shear. -/
noncomputable def reciprocalThetaTermPoint (n : ℕ) (x : ℝ) : Fiber :=
  heightShear (thetaIndexShear n) (globalHelixInvolution (thetaTermPoint n x))

/-- The sheared anti-helix term lands at the precise reciprocal external height `(n+1)/x`. -/
theorem multiplicativeHeight_reciprocalThetaTermPoint (n : ℕ) {x : ℝ} (hx : 0 < x) :
    multiplicativeHeight (reciprocalThetaTermPoint n x) =
      ((n + 1 : ℕ) : ℝ) / x := by
  rw [reciprocalThetaTermPoint,
    multiplicativeHeight_heightShear (thetaIndexShear_pos n),
    multiplicativeHeight_globalHelixInvolution,
    multiplicativeHeight_thetaTermPoint n hx]
  unfold thetaIndexShear
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  field_simp

/-- Every fixed kernel reads its reciprocal-height `n`th term on the sheared anti-helix point. -/
theorem kernel_reciprocal_term_as_globalHelix
    (g : ℝ → ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    g (((n + 1 : ℕ) : ℝ) / x) =
      g (multiplicativeHeight (reciprocalThetaTermPoint n x)) := by
  rw [multiplicativeHeight_reciprocalThetaTermPoint n hx]

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.multiplicativeHeight_heightShear
#print axioms CriticalLinePhasor.GlobalHelix.multiplicativeHeight_thetaTermPoint
#print axioms CriticalLinePhasor.GlobalHelix.multiplicativeHeight_reciprocalThetaTermPoint
#print axioms CriticalLinePhasor.GlobalHelix.kernel_reciprocal_term_as_globalHelix
