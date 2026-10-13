import Mathlib

/-!
# The archimedean factor from the carrier's arclength heat kernel (ledger 1219)

Site `n` sits at arclength `ℓ_n = n·π/3` from the native origin (the tick rule, `spinAngle n`). The
Gaussian `e^{−t ℓ²}` is the heat profile in arclength. Its Mellin transform in the heat variable `t`
produces the archimedean factor at each site. No Γ-factor, kernel or functional equation is inserted:
`Γ` comes out of the integral (Mathlib `integral_cpow_mul_exp_neg_mul_Ioi`).

* `siteHeat_mellin`: `∫₀^∞ t^{s/2−1} e^{−t ℓ_n²} dt = ℓ_n^{−s}·Γ(s/2)` for `Re s > 0`, `n ≥ 1`.
* `headHeat_mellin`: summed over the sites up to a head `N`, `Γ(s/2)·(π/3)^{−s}·Σ_{n ≤ N} n^{−s}`.
-/

open Complex MeasureTheory Set Finset

noncomputable section

namespace CriticalLinePhasor.CarrierHeat

/-- The arclength of site `n` from the native origin. -/
def siteArc (n : ℕ) : ℝ := n * (Real.pi / 3)

theorem siteArc_pos {n : ℕ} (hn : 1 ≤ n) : 0 < siteArc n := by
  unfold siteArc
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  positivity

/-- **The archimedean factor at one site, from the heat profile.** -/
theorem siteHeat_mellin {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 0 < s.re) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s / 2 - 1) * Complex.exp (-((siteArc n ^ 2 : ℝ) * t)) =
      ((siteArc n : ℝ) : ℂ) ^ (-s) * Complex.Gamma (s / 2) := by
  have hℓ := siteArc_pos hn
  have hr : 0 < siteArc n ^ 2 := by positivity
  have ha : 0 < (s / 2).re := by simpa using half_pos hs
  rw [integral_cpow_mul_exp_neg_mul_Ioi ha hr]
  congr 1
  have hx : (1 / ((siteArc n ^ 2 : ℝ) : ℂ)) = ((1 / siteArc n ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hx0 : ((1 / siteArc n ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 / siteArc n ^ 2 : ℝ) ≠ 0 by positivity)
  have hl0 : ((siteArc n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  rw [hx, Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hl0,
    ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log hℓ.le]
  congr 1
  rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_pow]
  push_cast
  ring

/-- **Summed over the sites up to the head**: `Γ(s/2)·(π/3)^{−s}·Σ_{n ≤ N} n^{−s}`. -/
theorem headHeat_mellin (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ∑ n ∈ Icc 1 N, ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (s / 2 - 1) * Complex.exp (-((siteArc n ^ 2 : ℝ) * t)) =
      Complex.Gamma (s / 2) * ((Real.pi / 3 : ℝ) : ℂ) ^ (-s) * ∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [siteHeat_mellin hn1 hs, siteArc, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), Complex.ofReal_natCast]
  ring
end CriticalLinePhasor.CarrierHeat

end

#print axioms CriticalLinePhasor.CarrierHeat.siteHeat_mellin
#print axioms CriticalLinePhasor.CarrierHeat.headHeat_mellin
