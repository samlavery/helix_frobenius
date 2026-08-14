import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Sato--Tate distribution function and its inverse

The corpus's Sato--Tate machinery is missing exactly one thing: a **witness** — an explicit
sequence of angles whose empirical measure converges to `angleMeasure`.  Every route to one goes
through the quantile map, i.e. the inverse of the distribution function

  **`F(θ) = (2θ − sin 2θ)/(2π)`,   `F(0) = 0`,  `F(π) = 1`,**

which is `∫_0^θ (2/π)·sin²t dt` — the Sato--Tate density's own antiderivative.  Mathlib has no
equidistribution API and no inverse-CDF construction, so this is built here.

Why the quantile map and not quadrature: Mathlib's Gauss--Chebyshev
(`Polynomial.Chebyshev.integral_eq_sumZeroes`) is **first kind** — equal weights against the
*arcsine* density `1/√(1−x²)`, not the Sato--Tate density `√(1−x²)`.  Equal-weight quadrature for
the latter is obstructed at high degree (Bernstein), so an exact finite construction is
unavailable and the witness must be asymptotic.  The quantile nodes `F(θ) = (i+½)/n` are the
equal-weight nodes that do exist.

**What is proved here.**  `F` is strictly monotone on `[0,π]`, continuous, and hits every value in
`[0,1]` — so the quantile angle exists and is unique for each level.  That is the inverse-CDF
brick.

**Scope.**  This file constructs the quantile map only.  Convergence of the resulting empirical
measures is *not* proved here, and no claim is made about any arithmetic family.
-/

open Set intervalIntegral

namespace CriticalLinePhasor.ThreeDConverse

/-- The Sato--Tate distribution function `F(θ) = (2θ − sin 2θ)/(2π)`. -/
noncomputable def satoTateCDF (θ : ℝ) : ℝ := (2 * θ - Real.sin (2 * θ)) / (2 * Real.pi)

lemma satoTateCDF_hasDerivAt (θ : ℝ) :
    HasDerivAt satoTateCDF ((1 - Real.cos (2 * θ)) / Real.pi) θ := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hnum : HasDerivAt (fun t : ℝ => 2 * t - Real.sin (2 * t))
      (2 - Real.cos (2 * θ) * 2) θ := hlin.sub (hlin.sin)
  have := hnum.div_const (2 * Real.pi)
  refine this.congr_deriv ?_
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **`F` is the Sato--Tate density's antiderivative.** -/
theorem satoTateCDF_eq_integral (θ : ℝ) :
    satoTateCDF θ = ∫ t in (0:ℝ)..θ, (2 / Real.pi) * Real.sin t ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [intervalIntegral.integral_const_mul, integral_sin_sq]
  rw [satoTateCDF]
  simp only [Real.sin_zero, Real.cos_zero]
  rw [Real.sin_two_mul]
  field_simp
  ring

@[simp] theorem satoTateCDF_zero : satoTateCDF 0 = 0 := by
  simp [satoTateCDF]

@[simp] theorem satoTateCDF_pi : satoTateCDF Real.pi = 1 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [satoTateCDF, Real.sin_two_pi]
  field_simp
  ring

theorem satoTateCDF_continuous : Continuous satoTateCDF := by
  unfold satoTateCDF
  fun_prop

/-- **Strict monotonicity**: the density `2sin²θ/π` is positive on the open interval. -/
theorem satoTateCDF_strictMonoOn : StrictMonoOn satoTateCDF (Icc 0 Real.pi) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    satoTateCDF_continuous.continuousOn ?_
  intro θ hθ
  rw [interior_Icc] at hθ
  rw [(satoTateCDF_hasDerivAt θ).deriv]
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hcos : Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
    rw [Real.cos_two_mul, Real.cos_sq']
    ring
  rw [hcos]
  have : (0:ℝ) < 2 * Real.sin θ ^ 2 := by positivity
  exact div_pos (by linarith) Real.pi_pos

/-- **The quantile angle exists**: every level in `[0,1]` is attained. -/
theorem satoTateCDF_surjOn {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    ∃ θ ∈ Icc (0:ℝ) Real.pi, satoTateCDF θ = u := by
  have hmem : u ∈ Icc (satoTateCDF 0) (satoTateCDF Real.pi) := by
    rw [satoTateCDF_zero, satoTateCDF_pi]; exact hu
  obtain ⟨θ, hθmem, hθ⟩ :=
    intermediate_value_Icc Real.pi_pos.le satoTateCDF_continuous.continuousOn hmem
  exact ⟨θ, hθmem, hθ⟩

/-- **The quantile angle is unique.** -/
theorem satoTateCDF_injOn : InjOn satoTateCDF (Icc 0 Real.pi) :=
  satoTateCDF_strictMonoOn.injOn

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.satoTateCDF_strictMonoOn
#print axioms CriticalLinePhasor.ThreeDConverse.satoTateCDF_surjOn
