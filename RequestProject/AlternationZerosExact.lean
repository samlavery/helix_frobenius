import RequestProject.ClosedForm

/-!
# The alternation zeros are exact (ledger 691)

`η(s) = (1 − 2^{1−s}) ζ(s)` vanishes at `s_k = 1 + 2πik/log 2` for every integer `k`, because `2^{1−s_k} = e^{−2πik} = 1`
exactly.  These are zeros of the fiber's limit function on `Re s = 1`, off the midpoint line, produced by no rounding,
truncation or precision error.
-/

open Complex
open scoped Real

namespace CriticalLinePhasor.EtaTrivial

/-- The alternation point of index `k`. -/
noncomputable def alternationPoint (k : ℤ) : ℂ := 1 + 2 * π * I * k / Real.log 2

theorem alternationPoint_eq (k : ℤ) :
    alternationPoint k = 1 + ((2 * π * k / Real.log 2 : ℝ) : ℂ) * I := by
  unfold alternationPoint
  push_cast
  ring

theorem alternationPoint_re (k : ℤ) : (alternationPoint k).re = 1 := by
  rw [alternationPoint_eq]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- `2^{1 − s_k} = 1` exactly. -/
theorem two_cpow_one_sub_alternationPoint (k : ℤ) :
    (2 : ℂ) ^ (1 - alternationPoint k) = 1 := by
  unfold alternationPoint
  have hlog : (Real.log 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
  rw [show (1 : ℂ) - (1 + 2 * π * I * k / Real.log 2) = -(2 * π * I * k / Real.log 2) by ring,
    Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0)]
  have h2 : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2)]
  rw [h2, show (Real.log 2 : ℂ) * -(2 * π * I * k / Real.log 2) = ((-k : ℤ) : ℂ) * (2 * π * I) by
    field_simp; push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I (-k)

/-- **The alternation zeros are exact:** `η(s_k) = 0` for every integer `k`. -/
theorem etaTrivial_alternationPoint (k : ℤ) : etaTrivial (alternationPoint k) = 0 := by
  unfold etaTrivial
  rw [two_cpow_one_sub_alternationPoint, sub_self, zero_mul]

/-- They are off the midpoint line. -/
theorem alternationPoint_re_ne_half (k : ℤ) : (alternationPoint k).re ≠ 1 / 2 := by
  rw [alternationPoint_re]; norm_num

/-- And `ζ` itself does not vanish there (`Re s = 1`): the zero is the alternation factor's alone. -/
theorem riemannZeta_alternationPoint_ne_zero (k : ℤ) (hk : k ≠ 0) :
    riemannZeta (alternationPoint k) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  rw [alternationPoint_re]

end CriticalLinePhasor.EtaTrivial

#print axioms CriticalLinePhasor.EtaTrivial.etaTrivial_alternationPoint
#print axioms CriticalLinePhasor.EtaTrivial.riemannZeta_alternationPoint_ne_zero
