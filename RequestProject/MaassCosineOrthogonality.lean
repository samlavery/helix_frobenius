import Mathlib

/-!
# Cosine orthogonality on the period interval

The strip-side input for the Maass Rankin--Selberg unfolding.  `waveForm` writes the even Maass
wave as `√y · ∑ₙ aₙ·cos(2π(n+1)x)·K((n+1)y)`, so the horizontal energy readout `∫₀¹ ‖u‖² dx` is
governed by orthogonality of the cosines `cos(2πmx)` on `[0,1]`.

Unlike the holomorphic case (`ParsevalExact`), no one-sidedness is needed.  The holomorphic
argument must prove the negative Fourier modes vanish, because a `q`-expansion is one-sided; the
even Maass expansion is already written in the real cosine basis, so the orthogonality is the
elementary product-to-sum computation and nothing else.

Scope: the `tsum` form, and hence the full strip evaluation, needs the summability supplied by the
Bessel decay in `radial_normalization`.  That is not proven here.
-/

open Real intervalIntegral MeasureTheory

namespace CriticalLinePhasor.MaassParseval

/-- Antiderivative form: `∫₀¹ cos(cx) dx = sin c / c` for `c ≠ 0`. -/
theorem integral_cos_mul {c : ℝ} (hc : c ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.cos (c * x) = Real.sin c / c := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => Real.sin (c * t) / c) (Real.cos (c * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => c * t) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have h2 : HasDerivAt (fun t : ℝ => Real.sin (c * t)) (Real.cos (c * x) * c) x := h1.sin
    have h3 := h2.div_const c
    rwa [mul_div_assoc, div_self hc, mul_one] at h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  simp

/-- `∫₀¹ cos(2πjx) dx = 0` for every nonzero integer `j`. -/
theorem integral_cos_two_pi_int {j : ℤ} (hj : j ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.cos (2 * Real.pi * (j : ℝ) * x) = 0 := by
  have hjR : (j : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hj
  have hc : (2 * Real.pi * (j : ℝ)) ≠ 0 := by
    have := Real.pi_ne_zero
    simpa using mul_ne_zero (mul_ne_zero two_ne_zero this) hjR
  rw [integral_cos_mul hc]
  have hsin : Real.sin (2 * Real.pi * (j : ℝ)) = 0 := by
    have hrw : (2 * Real.pi * (j : ℝ)) = ((2 * j : ℤ) : ℝ) * Real.pi := by
      push_cast; ring
    rw [hrw, Real.sin_int_mul_pi]
  rw [hsin, zero_div]

/-- **Cosine orthogonality on the period interval.**  For positive integers the cosines
`cos(2πmx)` are orthogonal on `[0,1]`, with squared norm `1/2`. -/
theorem integral_cos_mul_cos {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (∫ x in (0:ℝ)..1,
      Real.cos (2 * Real.pi * (m : ℝ) * x) * Real.cos (2 * Real.pi * (n : ℝ) * x)) =
      if m = n then 1 / 2 else 0 := by
  set j₁ : ℤ := (m : ℤ) - (n : ℤ) with hj1
  set j₂ : ℤ := (m : ℤ) + (n : ℤ) with hj2
  have hprod : ∀ x : ℝ,
      Real.cos (2 * Real.pi * (m : ℝ) * x) * Real.cos (2 * Real.pi * (n : ℝ) * x) =
        (Real.cos (2 * Real.pi * (j₁ : ℝ) * x) +
          Real.cos (2 * Real.pi * (j₂ : ℝ) * x)) / 2 := by
    intro x
    have e1 : 2 * Real.pi * (j₁ : ℝ) * x =
        2 * Real.pi * (m : ℝ) * x - 2 * Real.pi * (n : ℝ) * x := by
      rw [hj1]; push_cast; ring
    have e2 : 2 * Real.pi * (j₂ : ℝ) * x =
        2 * Real.pi * (m : ℝ) * x + 2 * Real.pi * (n : ℝ) * x := by
      rw [hj2]; push_cast; ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]
    ring
  have hint1 : IntervalIntegrable
      (fun x : ℝ => Real.cos (2 * Real.pi * (j₁ : ℝ) * x)) volume 0 1 :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun x : ℝ => Real.cos (2 * Real.pi * (j₂ : ℝ) * x)) volume 0 1 :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hsplit :
      (∫ x in (0:ℝ)..1,
        (Real.cos (2 * Real.pi * (j₁ : ℝ) * x) +
          Real.cos (2 * Real.pi * (j₂ : ℝ) * x)) / 2) =
        ((∫ x in (0:ℝ)..1, Real.cos (2 * Real.pi * (j₁ : ℝ) * x)) +
          ∫ x in (0:ℝ)..1, Real.cos (2 * Real.pi * (j₂ : ℝ) * x)) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add hint1 hint2]
  have hj2ne : j₂ ≠ 0 := by
    rw [hj2]
    omega
  rw [intervalIntegral.integral_congr (g := fun x =>
    (Real.cos (2 * Real.pi * (j₁ : ℝ) * x) +
      Real.cos (2 * Real.pi * (j₂ : ℝ) * x)) / 2) (fun x _ => hprod x), hsplit,
    integral_cos_two_pi_int hj2ne]
  by_cases hmn : m = n
  · have hj1zero : j₁ = 0 := by rw [hj1, hmn]; ring
    rw [if_pos hmn, hj1zero]
    norm_num
  · have hj1ne : j₁ ≠ 0 := by
      rw [hj1]
      omega
    rw [if_neg hmn, integral_cos_two_pi_int hj1ne]
    norm_num

end CriticalLinePhasor.MaassParseval

#print axioms CriticalLinePhasor.MaassParseval.integral_cos_mul
#print axioms CriticalLinePhasor.MaassParseval.integral_cos_two_pi_int
#print axioms CriticalLinePhasor.MaassParseval.integral_cos_mul_cos
