import Mathlib
import RequestProject.WeilExplicitFormula

/-!
# Weil's explicit formula for integrable line profiles (W3a, ledger 1339)

`weil_explicit_formula` (W5, Track W) consumes compact support of the profile `g` in exactly one place: the Fourier
inversion of the line profile `g_σ(x) = g(x)e^{(σ−½)x}` (`laplaceTest_line_fourier`), which needs `g_σ` integrable
and continuous. Here the same chain is re-run with that integrability as the hypothesis, so that Gaussian-decay
profiles — the pair profiles of the Weil witness (1336–1338) — are admissible:

* `laplaceTest_line_fourier'` — the prime integral `∫F(σ+it)e^{−ity}dt = 2π g_σ(y)` for `g` continuous with
  `g_σ` integrable;
* `prime_line_term_right'`, `prime_line_term_left'` — the two line terms;
* `weil_explicit_formula'` — the strip-form explicit formula with hypotheses: `g` continuous, `g_a` and `g_b`
  integrable, `F = laplaceTest g` entire with decay of order `≥ 4` on the strip.

Proofs are those of W2/W5 with the one substitution. No `sorry`, no `axiom`, no window.
-/

open Complex MeasureTheory Filter Topology
open scoped FourierTransform Real

noncomputable section

namespace CriticalLinePhasor.WeilGauss

open CriticalLinePhasor.ContourArgument

/-- **The prime integral for an integrable line profile**: `∫ F(σ + it) e^{−ity} dt = 2π · g_σ(y)`. -/
theorem laplaceTest_line_fourier' {g : ℝ → ℂ} (hg : Continuous g) {σ : ℝ} (hint : Integrable (lineProfile g σ))
    (hF : Continuous (laplaceTest g)) {C : ℝ} {k : ℕ} (hk : 2 ≤ k) (hC : 0 ≤ C)
    (hdec : LineDecay (laplaceTest g) σ C k) (y : ℝ) :
    ∫ t : ℝ, laplaceTest g (σ + t * I) * Complex.exp (-(I * t * y))
      = 2 * π * lineProfile g σ y := by
  set G : ℝ → ℂ := fun x : ℝ =>
    Complex.exp (((-2 * π * x * y : ℝ) : ℂ) * I) • 𝓕⁻ (lineProfile g σ) x with hG
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h1 : ∀ t : ℝ, laplaceTest g (σ + t * I) * Complex.exp (-(I * t * y))
      = G ((2 * π)⁻¹ * t) := by
    intro t
    rw [hG]
    simp only [smul_eq_mul]
    rw [laplaceTest_eq_fourierInv, mul_comm]
    congr 1
    · push_cast
      field_simp
    · rw [div_eq_inv_mul]
  have h2 : ∫ t : ℝ, G ((2 * π)⁻¹ * t) = |((2 * π)⁻¹)⁻¹| • ∫ x : ℝ, G x :=
    Measure.integral_comp_mul_left G ((2 * π)⁻¹)
  have h3 : ∫ x : ℝ, G x = lineProfile g σ y := by
    rw [hG]
    have hf : 𝓕 (𝓕⁻ (lineProfile g σ)) y = lineProfile g σ y :=
      hint.fourier_fourierInv_eq
        (fourier_lineProfile_integrable hF hk hC hdec) (lineProfile_continuous hg σ).continuousAt
    rw [← hf, Real.fourier_real_eq_integral_exp_smul]
  have hfun : (fun t : ℝ => laplaceTest g (σ + t * I) * Complex.exp (-(I * t * y)))
      = fun t : ℝ => G ((2 * π)⁻¹ * t) := funext h1
  rw [hfun, h2, h3, inv_inv, abs_of_pos (by positivity), Complex.real_smul]
  push_cast
  ring

/-- The right-line prime integral for an integrable line profile. -/
theorem prime_line_term_right' {g : ℝ → ℂ} (hg : Continuous g) {b : ℝ} (hint : Integrable (lineProfile g b))
    (hF : Continuous (laplaceTest g)) {C : ℝ} {k : ℕ} (hk : 2 ≤ k) (hC : 0 ≤ C)
    (hdec : LineDecay (laplaceTest g) b C k) (n : ℕ) :
    ∫ t : ℝ, laplaceTest g (b + t * I) * LSeries.term vonMangoldtC ((b : ℂ) + t * I) n
      = 2 * π * (primeWeight n * g (Real.log n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero, primeWeight]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hfun : (fun t : ℝ => laplaceTest g (b + t * I) * LSeries.term vonMangoldtC ((b : ℂ) + t * I) n)
      = fun t : ℝ => (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((n : ℝ) ^ (-b) : ℝ) : ℂ))
          * (laplaceTest g (b + t * I) * Complex.exp (-(I * t * Real.log n))) := by
    funext t
    rw [term_line_eq b t hn]
    ring
  rw [hfun, integral_const_mul, laplaceTest_line_fourier' hg hint hF hk hC hdec]
  unfold lineProfile primeWeight
  have hprof : Real.exp ((b - 1 / 2) * Real.log n) = (n : ℝ) ^ (b - 1 / 2) := by
    rw [Real.rpow_def_of_pos hnr, mul_comm]
  rw [hprof]
  have hpow : (((n : ℝ) ^ (-b) : ℝ) : ℂ) * (((n : ℝ) ^ (b - 1 / 2) : ℝ) : ℂ)
      = (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hnr]
    congr 2
    ring
  linear_combination
    (2 * (π : ℂ) * g (Real.log n) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) * hpow

/-- The left-line prime integral for an integrable line profile. -/
theorem prime_line_term_left' {g : ℝ → ℂ} (hg : Continuous g) {a : ℝ} (hint : Integrable (lineProfile g a))
    (hF : Continuous (laplaceTest g)) {C : ℝ} {k : ℕ} (hk : 2 ≤ k) (hC : 0 ≤ C)
    (hdec : LineDecay (laplaceTest g) a C k) (n : ℕ) :
    ∫ t : ℝ, laplaceTest g (a + t * I) * LSeries.term vonMangoldtC (1 - ((a : ℂ) + t * I)) n
      = 2 * π * (primeWeight n * g (-Real.log n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero, primeWeight]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hrefl : ∀ t : ℝ, (1 - ((a : ℂ) + t * I)) = (((1 - a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    intro t
    push_cast
    ring
  have hfun : (fun t : ℝ => laplaceTest g (a + t * I)
        * LSeries.term vonMangoldtC (1 - ((a : ℂ) + t * I)) n)
      = fun t : ℝ => (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((n : ℝ) ^ (-(1 - a)) : ℝ) : ℂ))
          * (laplaceTest g (a + t * I) * Complex.exp (-(I * t * ((-Real.log n : ℝ) : ℂ)))) := by
    funext t
    rw [hrefl t, term_line_eq (1 - a) (-t) hn]
    have : Complex.exp (-(I * ((-t : ℝ) : ℂ) * Real.log n))
        = Complex.exp (-(I * t * ((-Real.log n : ℝ) : ℂ))) := by
      congr 1
      push_cast
      ring
    rw [this]
    ring
  rw [hfun, integral_const_mul, laplaceTest_line_fourier' hg hint hF hk hC hdec (-Real.log n)]
  unfold lineProfile primeWeight
  have hprof : Real.exp ((a - 1 / 2) * -Real.log n) = (n : ℝ) ^ (1 / 2 - a) := by
    rw [Real.rpow_def_of_pos hnr]
    congr 1
    ring
  rw [hprof]
  have hpow : (((n : ℝ) ^ (-(1 - a)) : ℝ) : ℂ) * (((n : ℝ) ^ (1 / 2 - a) : ℝ) : ℂ)
      = (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hnr]
    congr 2
    ring
  linear_combination
    (2 * (π : ℂ) * g (-Real.log n) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) * hpow

/-- **Weil's explicit formula, strip form, for integrable line profiles.** -/
theorem weil_explicit_formula' {g : ℝ → ℂ} (hg : Continuous g) {a b : ℝ}
    (hinta : Integrable (lineProfile g a)) (hintb : Integrable (lineProfile g b))
    (hF : Differentiable ℂ (laplaceTest g)) {C : ℝ} {k : ℕ} (hk : 4 ≤ k) (hC : 0 ≤ C)
    (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Set.Icc a b, ∀ T : ℝ, ‖laplaceTest g (x + T * I)‖ ≤ C / (1 + |T|) ^ k) :
    ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * laplaceTest g ρ.val
      = (1 / (2 * π)) * ((∫ t : ℝ, laplaceTest g (b + t * I) * weilArch (b + t * I))
          + (∫ t : ℝ, laplaceTest g (a + t * I) * weilArch (1 - ((a : ℂ) + t * I))))
        - ∑' n : ℕ, primeWeight n * (g (Real.log n) + g (-Real.log n)) := by
  set F : ℂ → ℂ := laplaceTest g with hFdef
  have hab : a ≤ b := by linarith
  have hk2 : 2 ≤ k := by omega
  have hdecb : LineDecay F b C k := fun t => hdec b ⟨hab, le_refl _⟩ t
  have hdeca : LineDecay F a C k := fun t => hdec a ⟨le_refl _, hab⟩ t
  have hFint : ∀ σ : ℝ, (σ = a ∨ σ = b) → Integrable (fun t : ℝ => F (σ + t * I)) := by
    intro σ hσ
    rcases hσ with rfl | rfl
    · exact integrable_line_of_decay hF.continuous hk2 hC hdeca
    · exact integrable_line_of_decay hF.continuous hk2 hC hdecb
  -- the zero side
  have hzero := stripBoundary_mul_logDeriv_xi hF hk hC ha hb hdec
  -- the right line
  have hθb : Continuous (fun t : ℝ => (b : ℂ) + t * I) := by fun_prop
  have hreb : ∀ t : ℝ, ((b : ℂ) + t * I).re = b := by intro t; simp
  have hLb : lineIntegral (fun s => F s * logDeriv ZD.riemannXi s) b
      = (∫ t : ℝ, F (b + t * I) * weilArch (b + t * I))
        - 2 * π * ∑' n : ℕ, primeWeight n * g (Real.log n) := by
    unfold lineIntegral
    have hpt : ∀ t : ℝ, F (b + t * I) * logDeriv ZD.riemannXi (b + t * I)
        = F (b + t * I) * weilArch (b + t * I) - F (b + t * I) * LSeries vonMangoldtC (b + t * I) := by
      intro t
      rw [logDeriv_xi_eq_arch_sub_lseries (by rw [hreb]; exact hb)]
      ring
    have hLint : Integrable (fun t : ℝ => F (b + t * I) * LSeries vonMangoldtC (b + t * I)) :=
      lseries_line_integrable (hFint b (Or.inr rfl)) hθb hreb hb
    have hAint : Integrable (fun t : ℝ => F (b + t * I) * weilArch (b + t * I)) := by
      have h := (line_mul_logDeriv_xi_integrable hF hk hC ha hb hdec (Or.inr rfl)).add hLint
      refine h.congr (Filter.Eventually.of_forall (fun t => ?_))
      simp only [Pi.add_apply]
      rw [hpt t]
      ring
    have hfun : (fun t : ℝ => F (b + t * I) * logDeriv ZD.riemannXi (b + t * I))
        = fun t : ℝ => F (b + t * I) * weilArch (b + t * I)
            - F (b + t * I) * LSeries vonMangoldtC (b + t * I) := funext hpt
    rw [hfun, integral_sub hAint hLint,
      lseries_line_exchange (hFint b (Or.inr rfl)) hθb hreb hb,
      tsum_congr (prime_line_term_right' hg hintb hF.continuous hk2 hC hdecb), tsum_mul_left]
  -- the left line
  have hθa : Continuous (fun t : ℝ => 1 - ((a : ℂ) + t * I)) := by fun_prop
  have hrea : ∀ t : ℝ, (1 - ((a : ℂ) + t * I)).re = 1 - a := by intro t; simp
  have h1a : 1 < 1 - a := by linarith
  have hLa : lineIntegral (fun s => F s * logDeriv ZD.riemannXi s) a
      = -(∫ t : ℝ, F (a + t * I) * weilArch (1 - ((a : ℂ) + t * I)))
        + 2 * π * ∑' n : ℕ, primeWeight n * g (-Real.log n) := by
    unfold lineIntegral
    have hpt : ∀ t : ℝ, F (a + t * I) * logDeriv ZD.riemannXi (a + t * I)
        = -(F (a + t * I) * weilArch (1 - ((a : ℂ) + t * I)))
          + F (a + t * I) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I)) := by
      intro t
      rw [logDeriv_xi_reflect, logDeriv_xi_eq_arch_sub_lseries (by rw [hrea]; exact h1a)]
      ring
    have hLint : Integrable (fun t : ℝ => F (a + t * I) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I))) :=
      lseries_line_integrable (hFint a (Or.inl rfl)) hθa hrea h1a
    have hAint : Integrable (fun t : ℝ => F (a + t * I) * weilArch (1 - ((a : ℂ) + t * I))) := by
      have h := hLint.sub (line_mul_logDeriv_xi_integrable hF hk hC ha hb hdec (Or.inl rfl))
      refine h.congr (Filter.Eventually.of_forall (fun t => ?_))
      simp only [Pi.sub_apply]
      rw [hpt t]
      ring
    have hfun : (fun t : ℝ => F (a + t * I) * logDeriv ZD.riemannXi (a + t * I))
        = fun t : ℝ => -(F (a + t * I) * weilArch (1 - ((a : ℂ) + t * I)))
            + F (a + t * I) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I)) := funext hpt
    have hAint' : Integrable (fun t : ℝ => -(F (a + t * I) * weilArch (1 - ((a : ℂ) + t * I)))) :=
      hAint.neg
    rw [hfun, integral_add hAint' hLint, integral_neg,
      lseries_line_exchange (hFint a (Or.inl rfl)) hθa hrea h1a,
      tsum_congr (prime_line_term_left' hg hinta hF.continuous hk2 hC hdeca), tsum_mul_left]
  -- summability of the two prime sums
  have h2π : (2 * (π : ℂ)) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hsumR : Summable (fun n : ℕ => primeWeight n * g (Real.log n)) := by
    have h := lseries_line_integrals_summable (φ := fun t : ℝ => laplaceTest g (b + t * I)) hreb hb
    refine (h.mul_left (2 * (π : ℂ))⁻¹).congr (fun n => ?_)
    show (2 * (π : ℂ))⁻¹ * ∫ t : ℝ, laplaceTest g (b + t * I)
      * LSeries.term vonMangoldtC ((b : ℂ) + t * I) n = primeWeight n * g (Real.log n)
    rw [prime_line_term_right' hg hintb hF.continuous hk2 hC hdecb n]
    field_simp
  have hsumL : Summable (fun n : ℕ => primeWeight n * g (-Real.log n)) := by
    have h := lseries_line_integrals_summable (φ := fun t : ℝ => laplaceTest g (a + t * I)) hrea h1a
    refine (h.mul_left (2 * (π : ℂ))⁻¹).congr (fun n => ?_)
    show (2 * (π : ℂ))⁻¹ * ∫ t : ℝ, laplaceTest g (a + t * I)
      * LSeries.term vonMangoldtC (1 - ((a : ℂ) + t * I)) n = primeWeight n * g (-Real.log n)
    rw [prime_line_term_left' hg hinta hF.continuous hk2 hC hdeca n]
    field_simp
  have hP : ∑' n : ℕ, primeWeight n * (g (Real.log n) + g (-Real.log n))
      = (∑' n : ℕ, primeWeight n * g (Real.log n)) + ∑' n : ℕ, primeWeight n * g (-Real.log n) := by
    rw [← hsumR.tsum_add hsumL]
    congr 1
    funext n
    ring
  -- assemble
  unfold stripBoundary at hzero
  rw [hLb, hLa] at hzero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hP]
  set S := ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * F ρ.val with hS
  set Ab := ∫ t : ℝ, F (b + t * I) * weilArch (b + t * I) with hAb
  set Aa := ∫ t : ℝ, F (a + t * I) * weilArch (1 - ((a : ℂ) + t * I)) with hAa
  set Pb := ∑' n : ℕ, primeWeight n * g (Real.log n) with hPb
  set Pa := ∑' n : ℕ, primeWeight n * g (-Real.log n) with hPa
  have h2πS : 2 * (π : ℂ) * S = (Ab + Aa) - 2 * π * (Pb + Pa) := by
    linear_combination I * hzero + (2 * π * S - Ab - Aa + 2 * π * (Pb + Pa)) * Complex.I_sq
  have hS' : S = (Ab + Aa) / (2 * π) - (Pb + Pa) := by
    rw [eq_sub_iff_add_eq, eq_div_iff h2π]
    linear_combination h2πS
  rw [hS']
  ring

end CriticalLinePhasor.WeilGauss

end

#print axioms CriticalLinePhasor.WeilGauss.laplaceTest_line_fourier'
#print axioms CriticalLinePhasor.WeilGauss.weil_explicit_formula'
