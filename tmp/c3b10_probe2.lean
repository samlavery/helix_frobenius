import Mathlib

open MeasureTheory Set

-- Q1: integral of an odd function vanishes
example (f : ℝ → ℝ) (h : ∀ x, f (-x) = -f x) : (∫ x : ℝ, f x) = 0 := by
  exact?

-- Q2: even function, full line vs half line
example (f : ℝ → ℝ) (hf : Integrable f) (h : ∀ x, f (-x) = f x) :
    (∫ x : ℝ, f x) = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  exact?

-- Q3: half line, other form
example (f : ℝ → ℝ) (hf : Integrable f) (h : ∀ x, f (-x) = f x) :
    (∫ x in Ioi (0 : ℝ), f x) = 2⁻¹ * ∫ x : ℝ, f x := by
  exact?

-- Q4: Gaussian-with-linear-term integrability, Mathlib native
example (b c : ℝ) (hb : 0 < b) : Integrable (fun w : ℝ => Real.exp (c * w - b * w ^ 2)) := by
  exact?
