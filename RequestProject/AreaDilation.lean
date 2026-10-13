import Mathlib

/-!
# Dilations of the area measure: the exponent ½ from unitarity (ledger 1219)

Sites counted uniformly in `n` are the cone's area measure (`h_n² ~ n/9`, `PhysicalHeightLaw`). In the
continuum this is Lebesgue measure on `(0, ∞)`. Dilating heights by `e^t` and weighting by `e^{ct}`:

* `dilW_isometry_iff`: `f ↦ e^{ct} f(e^t ·)` preserves `∫ ‖f‖²` over `(0, ∞)` for every `t` (and some
  `f` of nonzero norm) iff `c = ½`. The exponent ½ is forced by the area measure, not inserted.
* `dil_power`: the unitary dilation acts on the power function `x^{−a}` by the scalar `e^{t(½ − a)}`.
* `dil_power_unimodular_iff`: that scalar is unimodular for every `t` iff `Re a = ½`.
* `dilGen_power`: the generator `−i(x d/dx + ½)` has the power function `x^{−s}` as a generalized
  eigenfunction with eigenvalue `i(s − ½)`. With `s = ½ + δ + iy` this is `−y + iδ`: real part the
  height, imaginary part the transverse displacement.
-/

open Complex MeasureTheory Set Real

noncomputable section

namespace CriticalLinePhasor.AreaDilation

/-- The weighted dilation `f ↦ e^{ct} f(e^t x)`. -/
def dilW (c t : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := (Real.exp (c * t) : ℂ) * f (Real.exp t * x)

theorem integral_norm_sq_dilW (c t : ℝ) (f : ℝ → ℂ) :
    ∫ x in Ioi 0, ‖dilW c t f x‖ ^ 2 = Real.exp ((2 * c - 1) * t) * ∫ x in Ioi 0, ‖f x‖ ^ 2 := by
  have hb : 0 < Real.exp t := Real.exp_pos t
  have hcomp := integral_comp_mul_left_Ioi (fun x => ‖f x‖ ^ 2) 0 hb
  simp only [mul_zero] at hcomp
  have hpt : ∀ x, ‖dilW c t f x‖ ^ 2 = Real.exp (c * t) ^ 2 * ‖f (Real.exp t * x)‖ ^ 2 := by
    intro x
    rw [dilW, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  simp_rw [hpt]
  rw [integral_const_mul, hcomp, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- **The exponent ½ is forced by the area measure.** -/
theorem dilW_isometry_iff (c : ℝ) (f : ℝ → ℂ) (hf : ∫ x in Ioi 0, ‖f x‖ ^ 2 ≠ 0) :
    (∀ t : ℝ, ∫ x in Ioi 0, ‖dilW c t f x‖ ^ 2 = ∫ x in Ioi 0, ‖f x‖ ^ 2) ↔ c = 1 / 2 := by
  constructor
  · intro h
    have h1 := h 1
    rw [integral_norm_sq_dilW] at h1
    have h2 : Real.exp ((2 * c - 1) * 1) = 1 := by
      have := mul_right_cancel₀ hf (h1.trans (one_mul _).symm)
      exact this
    rw [Real.exp_eq_one_iff] at h2
    linarith
  · intro hc t
    rw [integral_norm_sq_dilW, hc]
    simp

/-- **The unitary dilation acts on a power function by a scalar.** -/
theorem dil_power (a : ℂ) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    dilW (1 / 2) t (fun x => (x : ℂ) ^ (-a)) x =
      Complex.exp ((t : ℂ) * (1 / 2 - a)) * (x : ℂ) ^ (-a) := by
  have hex : (0 : ℝ) < Real.exp t := Real.exp_pos t
  show ((Real.exp (1 / 2 * t) : ℝ) : ℂ) * (((Real.exp t * x : ℝ) : ℂ)) ^ (-a) = _
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hex.le hx.le]
  have hlog : Complex.log ((Real.exp t : ℝ) : ℂ) = (t : ℂ) := by
    rw [← Complex.ofReal_log hex.le, Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero (show ((Real.exp t : ℝ) : ℂ) ≠ 0 by exact_mod_cast hex.ne'),
    hlog, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Unimodular for every `t` iff `Re a = ½`.** -/
theorem dil_power_unimodular_iff (a : ℂ) :
    (∀ t : ℝ, ‖Complex.exp ((t : ℂ) * (1 / 2 - a))‖ = 1) ↔ a.re = 1 / 2 := by
  constructor
  · intro h
    have h1 := h 1
    rw [Complex.norm_exp] at h1
    have : ((1 : ℝ) : ℂ) * (1 / 2 - a) = 1 / 2 - a := by push_cast; ring
    rw [this, Real.exp_eq_one_iff] at h1
    simp at h1
    linarith
  · intro ha t
    rw [Complex.norm_exp]
    have : ((t : ℂ) * (1 / 2 - a)).re = t * (1 / 2 - a.re) := by simp
    rw [this, ha]
    simp

/-- **The dilation generator on power functions**: `−i(x·d/dx + ½) x^{−s} = i(s − ½)·x^{−s}`,
stated through the derivative `d/dx x^{−s} = −s·x^{−s−1}`. -/
theorem dilGen_power (s : ℂ) {x : ℝ} (hx : 0 < x) :
    -I * ((x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) + 1 / 2 * (x : ℂ) ^ (-s)) =
      I * (s - 1 / 2) * (x : ℂ) ^ (-s) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpow : (x : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) := by
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
    field_simp
  have : (x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) = -s * (x : ℂ) ^ (-s) := by
    rw [← hpow]
    ring
  rw [this]
  ring

end CriticalLinePhasor.AreaDilation

end

#print axioms CriticalLinePhasor.AreaDilation.dilW_isometry_iff
#print axioms CriticalLinePhasor.AreaDilation.dil_power
#print axioms CriticalLinePhasor.AreaDilation.dil_power_unimodular_iff
#print axioms CriticalLinePhasor.AreaDilation.dilGen_power
