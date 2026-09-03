import Mathlib
import RequestProject.WeilZeroSide
import RequestProject.WeilPrimeSide
import RequestProject.ZetaScrewArithmetic
import RequestProject.SeatingFloorOdd

/-!
# Track W5 — Weil's explicit formula for compactly supported profiles, strip form (ledger 534)

For `g` continuous with compact support and `F = laplaceTest g` (`F(s) = ∫ g(x)e^{(s−½)x}dx`)
entire with power decay of order `≥ 4` on the strip `a ≤ Re s ≤ b`, `a < 0 < 1 < b`:

  `Σ'_ρ m_ρ F(ρ) = (1/2π)[∫ F(b+it) E(b+it) dt + ∫ F(a+it) E(1−a−it) dt]
                    − Σ_n Λ(n) n^{−½} (g(log n) + g(−log n))`,

`E(s) = 1/s + 1/(s−1) − ½ log π + ½ Γ′/Γ(s/2)` the Archimedean part of `ξ′/ξ`. The prime sum is
finite (compact support). Assembled from the zero side (`stripBoundary_mul_logDeriv_xi`), the
arithmetic form of `ξ′/ξ` right of the line (`logDeriv_riemannXi_arith`), the functional equation
in log-derivative form (`xiLogDeriv_odd`), the Dirichlet-series exchange, and the prime integral by
Fourier inversion (`laplaceTest_line_fourier`).

No `sorry`, no `axiom`.
-/

open Complex MeasureTheory Filter Topology
open scoped Real

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-- The Archimedean part of `ξ′/ξ`. -/
def weilArch (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2 + logDeriv Complex.Gamma (s / 2) / 2

theorem logDeriv_xi_eq_arch_sub_lseries {s : ℂ} (hs : 1 < s.re) :
    logDeriv ZD.riemannXi s = weilArch s - LSeries vonMangoldtC s := by
  rw [CriticalLinePhasor.HilbertPolya.logDeriv_riemannXi_arith hs]
  rfl

theorem logDeriv_xi_reflect (s : ℂ) :
    logDeriv ZD.riemannXi s = -logDeriv ZD.riemannXi (1 - s) := by
  rw [CriticalLinePhasor.SeatingLedger.xiLogDeriv_odd, neg_neg]

/-- The prime weight `Λ(n) n^{−½}`. -/
def primeWeight (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

/-- `term_n(σ + it) = Λ(n) n^{−σ} e^{−it log n}` for `n ≥ 1`. -/
theorem term_line_eq (σ t : ℝ) {n : ℕ} (hn : 0 < n) :
    LSeries.term vonMangoldtC ((σ : ℂ) + t * I) n
      = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)
          * Complex.exp (-(I * t * Real.log n)) := by
  rw [LSeries.term_of_ne_zero hn.ne']
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hσpow : ((n : ℕ) : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hnr.le, Complex.ofReal_natCast]
  rw [Complex.cpow_add _ _ hn0, Complex.cpow_def_of_ne_zero hn0 ((t : ℂ) * I),
    ← Complex.natCast_log, hσpow, Real.rpow_neg hnr.le, Complex.ofReal_inv, div_eq_mul_inv,
    mul_inv, ← Complex.exp_neg, ← mul_assoc]
  congr 2
  ring

/-- The right-line prime integral: `∫ F(b+it) term_n(b+it) dt = 2π · Λ(n) n^{−½} g(log n)`. -/
theorem prime_line_term_right {g : ℝ → ℂ} (hg : Continuous g) (hsupp : HasCompactSupport g)
    (hF : Continuous (laplaceTest g)) {b C : ℝ} {k : ℕ} (hk : 2 ≤ k) (hC : 0 ≤ C)
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
  rw [hfun, integral_const_mul, laplaceTest_line_fourier hg hsupp hF hk hC hdec]
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

/-- The left-line prime integral: `∫ F(a+it) term_n(1−a−it) dt = 2π · Λ(n) n^{−½} g(−log n)`. -/
theorem prime_line_term_left {g : ℝ → ℂ} (hg : Continuous g) (hsupp : HasCompactSupport g)
    (hF : Continuous (laplaceTest g)) {a C : ℝ} {k : ℕ} (hk : 2 ≤ k) (hC : 0 ≤ C)
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
  rw [hfun, integral_const_mul, laplaceTest_line_fourier hg hsupp hF hk hC hdec (-Real.log n)]
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

/-- The zero sum of the explicit formula is a genuinely convergent sum. -/
theorem weil_zero_sum_summable {g : ℝ → ℂ} (_hg : Continuous g) (_hsupp : HasCompactSupport g)
    (hF : Differentiable ℂ (laplaceTest g)) {a b C : ℝ} {k : ℕ} (hk : 4 ≤ k) (hC : 0 ≤ C)
    (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Set.Icc a b, ∀ T : ℝ, ‖laplaceTest g (x + T * I)‖ ≤ C / (1 + |T|) ^ k) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * laplaceTest g ρ.val) := by
  have hsumb := summable_hadamardLineTerm_integral hF.continuous hk hC ha hb hdec
    (Or.inr rfl : b = a ∨ b = b)
  have hsuma := summable_hadamardLineTerm_integral hF.continuous hk hC ha hb hdec
    (Or.inl rfl : a = a ∨ a = b)
  have hper : ∀ ρ : Zero,
      I * (∫ t : ℝ, hadamardLineTerm (laplaceTest g) b ρ t)
        - I * (∫ t : ℝ, hadamardLineTerm (laplaceTest g) a ρ t)
        = 2 * Real.pi * I * ((ZD.xiOrderNat ρ.val : ℂ) * laplaceTest g ρ.val) := by
    intro ρ
    have h := stripBoundary_hadamardTerm hF hk hC ha hb hdec ρ.property
    unfold stripBoundary lineIntegral at h
    have hb' : ∫ t : ℝ, hadamardLineTerm (laplaceTest g) b ρ t
        = (ZD.xiOrderNat ρ.val : ℂ)
          * ∫ t : ℝ, laplaceTest g (b + t * I) * hadamardTerm ρ.val (b + t * I) := by
      rw [← integral_const_mul]
      congr 1
      funext t
      unfold hadamardLineTerm
      ring
    have ha' : ∫ t : ℝ, hadamardLineTerm (laplaceTest g) a ρ t
        = (ZD.xiOrderNat ρ.val : ℂ)
          * ∫ t : ℝ, laplaceTest g (a + t * I) * hadamardTerm ρ.val (a + t * I) := by
      rw [← integral_const_mul]
      congr 1
      funext t
      unfold hadamardLineTerm
      ring
    beta_reduce at h
    linear_combination I * hb' - I * ha' + (ZD.xiOrderNat ρ.val : ℂ) * h
  have hs : Summable (fun ρ : Zero =>
      2 * Real.pi * I * ((ZD.xiOrderNat ρ.val : ℂ) * laplaceTest g ρ.val)) := by
    refine ((hsumb.mul_left I).sub (hsuma.mul_left I)).congr (fun ρ => ?_)
    exact hper ρ
  have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) I_ne_zero
  refine (hs.mul_left (2 * Real.pi * I)⁻¹).congr (fun ρ => ?_)
  field_simp

/-- **Weil's explicit formula, strip form.** -/
theorem weil_explicit_formula {g : ℝ → ℂ} (hg : Continuous g) (hsupp : HasCompactSupport g)
    (hF : Differentiable ℂ (laplaceTest g)) {a b C : ℝ} {k : ℕ} (hk : 4 ≤ k) (hC : 0 ≤ C)
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
      tsum_congr (prime_line_term_right hg hsupp hF.continuous hk2 hC hdecb), tsum_mul_left]
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
      tsum_congr (prime_line_term_left hg hsupp hF.continuous hk2 hC hdeca), tsum_mul_left]
  -- summability of the two prime sums
  have h2π : (2 * (π : ℂ)) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hsumR : Summable (fun n : ℕ => primeWeight n * g (Real.log n)) := by
    have h := lseries_line_integrals_summable (φ := fun t : ℝ => laplaceTest g (b + t * I)) hreb hb
    refine (h.mul_left (2 * (π : ℂ))⁻¹).congr (fun n => ?_)
    show (2 * (π : ℂ))⁻¹ * ∫ t : ℝ, laplaceTest g (b + t * I)
      * LSeries.term vonMangoldtC ((b : ℂ) + t * I) n = primeWeight n * g (Real.log n)
    rw [prime_line_term_right hg hsupp hF.continuous hk2 hC hdecb n]
    field_simp
  have hsumL : Summable (fun n : ℕ => primeWeight n * g (-Real.log n)) := by
    have h := lseries_line_integrals_summable (φ := fun t : ℝ => laplaceTest g (a + t * I)) hrea h1a
    refine (h.mul_left (2 * (π : ℂ))⁻¹).congr (fun n => ?_)
    show (2 * (π : ℂ))⁻¹ * ∫ t : ℝ, laplaceTest g (a + t * I)
      * LSeries.term vonMangoldtC (1 - ((a : ℂ) + t * I)) n = primeWeight n * g (-Real.log n)
    rw [prime_line_term_left hg hsupp hF.continuous hk2 hC hdeca n]
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

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.weil_explicit_formula
