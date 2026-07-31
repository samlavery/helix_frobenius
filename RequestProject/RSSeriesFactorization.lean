import RequestProject.MoebiusTransfer

/-!
# Series factorization: the Rankin square readout in the `ζ · Sym²` display

Chart bookkeeping for the right-hand side of the master equation.  The Rankin–Selberg
series produced by the compiled weld, `∑' n, ‖a_n‖²/(4πn)^w`, is — term by term — the
`(4π)^{-w}`-scaled L-series of the Rankin square bank (`rsSeries_eq_LSeries`): the `n = 0`
term contributes nothing on either side (the phasor enters at zero magnitude, and
`LSeries.term` vanishes at `n = 0`), while each `n ≥ 1` term splits its harmonic scale
`(4πn)^w` into the carrier constant `(4π)^w` times the clock `n^w`.  Composing with the
compiled Möbius transfer (`rankin_sym2_transfer`) puts the readout in the
`ζ(w) · L(μ ⋆ ‖a‖², w)` display (`rsSeries_zeta_sym2`).  Instantiated at `w = s + k - 1`
the hypothesis `k + 1 < Re w` is exactly `2 < Re s`, the chart's readout locus for the
master equation.  Both statements are definitional bookkeeping on the readout chart; the
analytic content (convergence, the ζ-peel) is consumed from `MoebiusTransfer`.
-/

open ArithmeticFunction LSeries UpperHalfPlane Complex
open scoped LSeries.notation MatrixGroups Real ArithmeticFunction.Moebius

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- **Series-to-L-series bookkeeping**: on the readout chart `k + 1 < Re w`, the Rankin
square series is the `(4π)^{-w}`-scaled L-series of the Rankin square bank.  The `n = 0`
term vanishes on both sides; each `n ≥ 1` term splits `(4πn)^w` into carrier constant
times clock. -/
theorem rsSeries_eq_LSeries (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {w : ℂ}
    (hw : (k : ℝ) + 1 < w.re) :
    ∑' n : ℕ, ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) / ((4 * π * n : ℝ) : ℂ) ^ w =
      ((4 * π : ℝ) : ℂ) ^ (-w) * LSeries (⇑(rankinSquare f)) w := by
  have hk' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hw1 : 1 < w.re := by linarith
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw1
    linarith
  rw [LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [LSeries.term_zero, mul_zero, Nat.cast_zero, mul_zero, Complex.ofReal_zero,
      Complex.zero_cpow hw0, div_zero]
  · rw [LSeries.term_of_ne_zero hn]
    have hcoe : (⇑(rankinSquare f) : ℕ → ℂ) n =
        ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) := by
      rw [rankinSquare, toArithmeticFunction]
      simp only [ArithmeticFunction.coe_mk, if_neg hn]
    rw [hcoe, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (Nat.cast_nonneg n) w,
      Complex.ofReal_natCast, Complex.cpow_neg, div_mul_eq_div_div_swap, div_eq_inv_mul]

/-- **The `ζ · Sym²` display**: on the readout chart the Rankin square series factors as
`(4π)^{-w} · ζ(w) · L(μ ⋆ ‖a‖², w)` — `rsSeries_eq_LSeries` composed with the compiled
Möbius transfer.  At `w = s + k - 1` the hypothesis is exactly `2 < Re s`. -/
theorem rsSeries_zeta_sym2 (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {w : ℂ}
    (hw : (k : ℝ) + 1 < w.re) :
    ∑' n : ℕ, ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) / ((4 * π * n : ℝ) : ℂ) ^ w =
      ((4 * π : ℝ) : ℂ) ^ (-w) *
        (riemannZeta w * LSeries (⇑((μ : ArithmeticFunction ℂ) * rankinSquare f)) w) := by
  rw [rsSeries_eq_LSeries f hk hw, rankin_sym2_transfer f hk hw]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.rsSeries_eq_LSeries
#print axioms CriticalLinePhasor.Unfolding.rsSeries_zeta_sym2
