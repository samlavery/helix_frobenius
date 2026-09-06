import RequestProject.RegistrationDensity

/-!
# The Riesz strain is the antiderivative of the prime bank (ledger 607, continued)

`d/dt rieszStrain L t = −(1/π) Re P_L(½ + it)`, where `P_L` is the finite Riesz-tapered prime bank of
`density_on_line`. Termwise: `Re(Λ(n) n^{−½−it}) = Λ(n) n^{−½} cos(t log n)` and
`d/dt [Λ(n) sin(t log n)/(√n log n)] = Λ(n) cos(t log n)/√n` (the `n = 0, 1` terms vanish with `Λ`).

With this, integrating the density identity over a station gap of the Riesz-strained clock turns
the prime bank into the strain difference, and the station equation makes the smoothed count exactly
one plus the integrated remainders.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Real

namespace CriticalLinePhasor.ContourArgument

/-- The real part of a bank term on the line: `Λ(n) n^{−½} cos(t log n)`. -/
theorem re_term_line (t : ℝ) (n : ℕ) :
    (LSeries.term vonMangoldtC (1 / 2 + (t : ℂ) * I) n).re
      = (ArithmeticFunction.vonMangoldt n) * Real.exp (-(1 / 2) * Real.log n) * Real.cos (t * Real.log n) := by
  unfold LSeries.term
  split_ifs with h0
  · subst h0; simp
  · have hn : (n : ℂ) ≠ 0 := by exact_mod_cast h0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h0
    -- n^{½+it} = exp((½ + it) log n), with log n real
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hnpos.le]
    have hpow : (n : ℂ) ^ (1 / 2 + (t : ℂ) * I)
        = Complex.exp (((1 / 2 * Real.log n : ℝ) : ℂ)) * Complex.exp (((t * Real.log n : ℝ) : ℂ) * I) := by
      rw [Complex.cpow_def_of_ne_zero hn, hlog, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hpow]
    have hΛ : vonMangoldtC n = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := rfl
    rw [hΛ]
    -- Λ / (e^{½ log n} · e^{iθ}) = (Λ e^{−½ log n}) · e^{−iθ}
    have hsplit : ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
          / (Complex.exp (((1 / 2 * Real.log n : ℝ) : ℂ)) * Complex.exp (((t * Real.log n : ℝ) : ℂ) * I))
        = (((ArithmeticFunction.vonMangoldt n) * Real.exp (-(1 / 2) * Real.log n) : ℝ) : ℂ)
          * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I)) := by
      have hneg1 : Complex.exp (((-(1 / 2) * Real.log n : ℝ) : ℂ))
          = (Complex.exp (((1 / 2 * Real.log n : ℝ) : ℂ)))⁻¹ := by
        rw [← Complex.exp_neg]
        congr 1
        push_cast
        ring
      have f1 : (((ArithmeticFunction.vonMangoldt n) * Real.exp (-(1 / 2) * Real.log n) : ℝ) : ℂ)
          = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
            * (Complex.exp (((1 / 2 * Real.log n : ℝ) : ℂ)))⁻¹ := by
        rw [Complex.ofReal_mul, Complex.ofReal_exp, hneg1]
      have f2 : Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I))
          = (Complex.exp (((t * Real.log n : ℝ) : ℂ) * I))⁻¹ := Complex.exp_neg _
      rw [f1, f2, div_eq_mul_inv, mul_inv]
      ring
    rw [hsplit, Complex.re_ofReal_mul, Complex.exp_re]
    have hre : (-(((t * Real.log n : ℝ) : ℂ) * I)).re = 0 := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have him : (-(((t * Real.log n : ℝ) : ℂ) * I)).im = -(t * Real.log n) := by
      simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [hre, him, Real.exp_zero, one_mul, Real.cos_neg]

/-- One clock is the antiderivative of its bank term. -/
theorem strainClock_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (strainClock n)
      ((ArithmeticFunction.vonMangoldt n) * Real.exp (-(1 / 2) * Real.log n) * Real.cos (t * Real.log n)) t := by
  unfold strainClock
  by_cases hn : n ≤ 1
  · -- Λ(0) = Λ(1) = 0: both sides are the zero function
    have hΛ : ArithmeticFunction.vonMangoldt n = 0 := by
      interval_cases n <;> simp [ArithmeticFunction.vonMangoldt_apply]
    simp only [hΛ, zero_mul, zero_div]
    exact hasDerivAt_const t 0
  · push_neg at hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    have hden : Real.sqrt n * Real.log n ≠ 0 := by positivity
    have h1 : HasDerivAt (fun t : ℝ => t * Real.log n) (Real.log n) t := by
      simpa using (hasDerivAt_id t).mul_const (Real.log n)
    have h2 : HasDerivAt (fun t : ℝ => Real.sin (t * Real.log n)) (Real.cos (t * Real.log n) * Real.log n) t :=
      (Real.hasDerivAt_sin _).comp t h1
    have h3 := (h2.const_mul (ArithmeticFunction.vonMangoldt n)).div_const (Real.sqrt n * Real.log n)
    refine h3.congr_deriv ?_
    have hsq : Real.sqrt n = Real.exp ((1 / 2) * Real.log n) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnpos]
      ring_nf
    rw [hsq, show Real.exp (-(1 / 2) * Real.log n) = (Real.exp ((1 / 2) * Real.log n))⁻¹ by
      rw [← Real.exp_neg]; ring_nf]
    field_simp

/-- **The Riesz strain is the antiderivative of `−Re P_L/π`.** -/
theorem rieszStrain_hasDerivAt {L : ℝ} (hL : 0 < L) (t : ℝ) :
    HasDerivAt (rieszStrain L) (-(1 / Real.pi) * (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re) t := by
  rw [rieszPrimeSum_eq_finset hL]
  unfold rieszStrain
  have hsum : HasDerivAt (fun t => ∑ n ∈ Finset.range (⌊Real.exp L⌋₊ + 1),
      rieszProfile L (Real.log n) * strainClock n t)
      (∑ n ∈ Finset.range (⌊Real.exp L⌋₊ + 1),
        rieszProfile L (Real.log n) * ((ArithmeticFunction.vonMangoldt n)
          * Real.exp (-(1 / 2) * Real.log n) * Real.cos (t * Real.log n))) t := by
    have h := HasDerivAt.sum (u := Finset.range (⌊Real.exp L⌋₊ + 1))
      (A := fun n (t : ℝ) => rieszProfile L (Real.log n) * strainClock n t)
      (A' := fun n => rieszProfile L (Real.log n) * ((ArithmeticFunction.vonMangoldt n)
          * Real.exp (-(1 / 2) * Real.log n) * Real.cos (t * Real.log n)))
      (x := t) (fun n _ => (strainClock_hasDerivAt n t).const_mul _)
    refine h.congr_of_eventuallyEq (Eventually.of_forall (fun t => ?_))
    simp [Finset.sum_apply]
  refine (hsum.const_mul _).congr_deriv ?_
  rw [Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Complex.re_ofReal_mul, re_term_line]

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.re_term_line
#print axioms CriticalLinePhasor.ContourArgument.rieszStrain_hasDerivAt
