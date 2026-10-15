import RequestProject.HelixHalfLineSource

/-!
# The origin interface between the two ends (ledger 1284)

Chatbibibi (via Sam, 2026-10-13): "Native origin-interface compatibility … Compute the exact boundary form of the
generator on both ends. Apply the existing J relation and cancellation equations. Check whether the resulting
interface condition constrains `v + v̄`. Do not assume the two eigenvalues agree."

Native coordinates: signed height `h`, origin `0`, measure `dh`. No `½` anywhere.

* `halfLine_boundary`: below the origin, `2 Re v · ∫_{h≤0} |e^{vh}|² dh = |e^{v·0}|²` (`= 1`). The boundary term at
  the origin is what lets the one-sided mode have `Re v ≠ 0`. The half-line generator is not skew-adjoint (1283 did
  not claim it was).
* `glued v`: the J-glued state, `e^{vh}` below the origin and its J-image `e^{−v̄h}` above.
  * `Jn_glued`: it is J-invariant.
  * `glued_zero`: it is continuous through the origin with value `1`.
  * `glued_deriv_below`, `glued_deriv_above`: its one-sided derivatives at the origin are `v` and `−v̄`;
    `interface_jump`: the jump is `−2 Re v`, the transverse displacement. (Both halves are square-integrable for
    `Re v > 0`; that is `memLp_expMode` and its J-image.)
* `glued_eq_expMode_iff`: **the J-glued state is the global mode `e_v` exactly when `Re v = 0`.**

**The test.** The cancellation (1270, `sourceConfig_cancels_iff`) pairs the bank with the GLOBAL mode `e_v` on both
halves. That is `H(v) + H(−v)` with `H` the bank's one-half transform. The J-glued state pairs it with `H(v) + H(v̄)`.
By `glued_eq_expMode_iff` the two coincide only on the axis. So the cancellation is a scalar equation that does not
involve the glued state's interface. The interface jump `−2 Re v` exists for every `v`, source or not. **J reflection
plus cancellation impose no condition on `v + v̄`.** Requiring the source state to be a single global mode with no
jump at the origin is exactly the axis condition (`glued_eq_expMode_iff`), i.e. the conclusion, so it cannot serve
as a hypothesis.
-/

open Complex Set MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixOriginInterface

open CriticalLinePhasor.HelixNativeDilation CriticalLinePhasor.HelixHalfLineSource

/-- **The half-line boundary identity**: `2 Re v · ‖e_v‖²_{h≤0} = |e_v(0)|²`. -/
theorem halfLine_boundary {v : ℂ} (hv : 0 < v.re) :
    2 * v.re * ∫ h in Iic (0 : ℝ), ‖expMode v h‖ ^ 2 = ‖expMode v 0‖ ^ 2 := by
  rw [integral_norm_sq_expMode hv, norm_expMode, mul_zero, Real.exp_zero]
  field_simp

/-- The J-glued state: the mode below the origin, its J-image above. -/
def glued (v : ℂ) (h : ℝ) : ℂ := if h ≤ 0 then expMode v h else expMode (-conj v) h

theorem expMode_zero (v : ℂ) : expMode v 0 = 1 := by
  simp [expMode]

theorem glued_zero (v : ℂ) : glued v 0 = 1 := by
  simp [glued, expMode_zero]

/-- **The J-glued state is J-invariant.** -/
theorem Jn_glued (v : ℂ) : Jn (glued v) = glued v := by
  funext h
  have h1 := congrFun (Jn_expMode v) h
  have h2 := congrFun (Jn_expMode (-conj v)) h
  simp only [Jn, map_neg, Complex.conj_conj, neg_neg] at h1 h2
  unfold Jn glued
  rcases lt_trichotomy h 0 with hneg | hzero | hpos
  · simp only [show ¬ -h ≤ 0 by linarith, show h ≤ 0 from hneg.le, ↓reduceIte]
    rw [h2]
  · subst hzero
    simp [expMode_zero]
  · simp only [show -h ≤ 0 by linarith, show ¬ h ≤ 0 by linarith, ↓reduceIte]
    rw [h1]

theorem hasDerivAt_expMode (v : ℂ) (h : ℝ) : HasDerivAt (expMode v) (v * expMode v h) h := by
  have hlin : HasDerivAt (fun y : ℝ => v * (y : ℂ)) (v * 1) h := (hasDerivAt_id h).ofReal_comp.const_mul v
  have := hlin.cexp
  unfold expMode
  convert this using 1
  ring

/-- From below, the glued state moves with eigenvalue `v`. -/
theorem glued_deriv_below (v : ℂ) : HasDerivWithinAt (glued v) v (Iic 0) 0 := by
  have h := (hasDerivAt_expMode v 0).hasDerivWithinAt (s := Iic 0)
  rw [expMode_zero, mul_one] at h
  refine h.congr (fun y hy => ?_) ?_
  · simp [glued, show y ≤ 0 from hy]
  · simp [glued]

/-- From above, the glued state moves with eigenvalue `−v̄`. -/
theorem glued_deriv_above (v : ℂ) : HasDerivWithinAt (glued v) (-conj v) (Ici 0) 0 := by
  have h := (hasDerivAt_expMode (-conj v) 0).hasDerivWithinAt (s := Ici 0)
  rw [expMode_zero, mul_one] at h
  refine h.congr (fun y hy => ?_) ?_
  · rcases (mem_Ici.mp hy).eq_or_lt with h0 | hpos
    · subst h0
      simp [glued, expMode_zero]
    · simp [glued, not_le.mpr hpos]
  · simp [glued, expMode_zero]

/-- **The interface jump is the transverse displacement**: `(−v̄) − v = −2 Re v`. -/
theorem interface_jump (v : ℂ) : -conj v - v = -((2 * v.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp
  ring

/-- **The J-glued state is a single global mode exactly on the axis.** -/
theorem glued_eq_expMode_iff (v : ℂ) : glued v = expMode v ↔ v.re = 0 := by
  constructor
  · intro h
    have h1 := congrFun h 1
    simp only [glued, show ¬ (1 : ℝ) ≤ 0 by norm_num, ↓reduceIte] at h1
    have hn := congrArg norm h1
    rw [norm_expMode, norm_expMode] at hn
    have := Real.exp_injective hn
    simp at this
    linarith
  · intro hre
    have hv : -conj v = v := by
      apply Complex.ext <;> simp [hre]
    funext h
    simp only [glued, hv]
    split_ifs <;> rfl

end CriticalLinePhasor.HelixOriginInterface

end

#print axioms CriticalLinePhasor.HelixOriginInterface.halfLine_boundary
#print axioms CriticalLinePhasor.HelixOriginInterface.Jn_glued
#print axioms CriticalLinePhasor.HelixOriginInterface.glued_deriv_below
#print axioms CriticalLinePhasor.HelixOriginInterface.glued_deriv_above
#print axioms CriticalLinePhasor.HelixOriginInterface.interface_jump
#print axioms CriticalLinePhasor.HelixOriginInterface.glued_eq_expMode_iff
