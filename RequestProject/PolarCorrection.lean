import Mathlib

/-!
# The polar correction: vanishing on an interval empties the ledger

The safe half of the two-modulus program (registered 2026-08-10), compiled.
Contour shifting turns a finite pole ledger into the polar correction
`R(y) = Σ_ρ y^{−ρ} P_ρ(log y)`; in the coordinate `x = log y` this is a
finite exponential polynomial.  This file proves the discharge implication:
if the correction vanishes on an open interval, every coefficient vanishes —
so every supposed pole is removable and the ledger is empty.

* `deriv_expSum` / `iterate_deriv_expSum` — the shape lemma: the derivative
  flow of `Σ c_i e^{μ_i z}` stays in the same finite-dimensional shape,
  raising the Vandermonde weight;
* `expSum_zero_on_interval_eq_zero` — the identity bridge: an entire
  exponential sum vanishing on an open real interval vanishes on all of ℂ
  (accumulation + the identity theorem);
* `expSum_coeffs_eq_zero_of_zero` — the Vandermonde extraction: distinct
  exponents force every coefficient of an identically-zero exponential sum
  to vanish (`Matrix.det_vandermonde`);
* `polar_correction_empties_ledger` — **the headline**: distinct exponents,
  vanishing on an open interval ⟹ all coefficients zero.

Scope register.  This session compiles the SIMPLE-multiplicity case
(`P_ρ` constant): by the campaign's semisimplicity computation the
annihilation system excludes log-modes at simple denominator zeros, so this
is the operative case there; arbitrary finite multiplicities (the
`(log y)^j` Jordan blocks, with their invertible triangular relation to the
principal-part coefficients) are an explicitly registered extension, not a
hidden hypothesis.  The uncertain step remains entirely upstream and is NOT
claimed here: whether the harmonized Kl₅ transformations force the
vanishing.  No `axiom`, no `sorry`.
-/

open Complex Finset

namespace CriticalLinePhasor.PolarCorrection

variable {n : ℕ}

/-- The exponential sum at Vandermonde weight `k`:
`Σ_i c_i μ_i^k e^{μ_i z}`. -/
noncomputable def expSum (μ c : Fin n → ℂ) (k : ℕ) : ℂ → ℂ :=
  fun z => ∑ i, c i * μ i ^ k * Complex.exp (μ i * z)

lemma hasDerivAt_expSum (μ c : Fin n → ℂ) (k : ℕ) (z : ℂ) :
    HasDerivAt (expSum μ c k) (expSum μ c (k + 1) z) z := by
  have h : ∀ i ∈ Finset.univ (α := Fin n),
      HasDerivAt (fun w => c i * μ i ^ k * Complex.exp (μ i * w))
        (c i * μ i ^ (k + 1) * Complex.exp (μ i * z)) z := by
    intro i _
    have h1 : HasDerivAt (fun w : ℂ => μ i * w) (μ i) z := by
      simpa using (hasDerivAt_id z).const_mul (μ i)
    have he : HasDerivAt (fun w => Complex.exp (μ i * w))
        (Complex.exp (μ i * z) * μ i) z :=
      (Complex.hasDerivAt_exp (μ i * z)).comp z h1
    have h2 := he.const_mul (c i * μ i ^ k)
    have h3 : c i * μ i ^ k * (Complex.exp (μ i * z) * μ i)
        = c i * μ i ^ (k + 1) * Complex.exp (μ i * z) := by ring
    rw [h3] at h2
    exact h2
  have hsum := HasDerivAt.sum h
  have hfn : (∑ i, fun w => c i * μ i ^ k * Complex.exp (μ i * w))
      = fun w => ∑ i, c i * μ i ^ k * Complex.exp (μ i * w) := by
    funext w
    simp [Finset.sum_apply]
  rw [hfn] at hsum
  exact hsum

lemma differentiable_expSum (μ c : Fin n → ℂ) (k : ℕ) :
    Differentiable ℂ (expSum μ c k) :=
  fun z => (hasDerivAt_expSum μ c k z).differentiableAt

/-- The derivative flow preserves the shape and raises the weight. -/
lemma deriv_expSum (μ c : Fin n → ℂ) (k : ℕ) :
    deriv (expSum μ c k) = expSum μ c (k + 1) := by
  funext z
  exact (hasDerivAt_expSum μ c k z).deriv

lemma iterate_deriv_expSum (μ c : Fin n → ℂ) (k : ℕ) :
    deriv^[k] (expSum μ c 0) = expSum μ c k := by
  induction k with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, deriv_expSum]

/-- **The identity bridge**: an exponential sum vanishing on an open real
interval vanishes identically on ℂ. -/
theorem expSum_zero_on_interval_eq_zero (μ c : Fin n → ℂ) {a b : ℝ}
    (hab : a < b)
    (hz : ∀ x : ℝ, x ∈ Set.Ioo a b → expSum μ c 0 (x : ℂ) = 0) :
    ∀ z : ℂ, expSum μ c 0 z = 0 := by
  set x₀ : ℝ := (a + b) / 2 with hx₀
  set r : ℝ := (b - a) / 4 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hax : a < x₀ := by rw [hx₀]; linarith
  have hxb : x₀ + r < b := by rw [hx₀, hr]; linarith
  have hmem : ∀ m : ℕ, x₀ + r / (m + 1) ∈ Set.Ioo a b := by
    intro m
    have hpos : 0 < r / (m + 1) := by positivity
    have hle : r / (m + 1) ≤ r := by
      apply div_le_self hrpos.le
      have : (1 : ℝ) ≤ (m : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      exact this
    exact ⟨by linarith, by linarith⟩
  -- the sequence of real zeros accumulating at x₀ from the right
  have htend : Filter.Tendsto (fun m : ℕ => ((x₀ + r / (m + 1) : ℝ) : ℂ))
      Filter.atTop (nhdsWithin (x₀ : ℂ) {(x₀ : ℂ)}ᶜ) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hreal : Filter.Tendsto (fun m : ℕ => x₀ + r / (m + 1))
          Filter.atTop (nhds x₀) := by
        have hdiv : Filter.Tendsto (fun m : ℕ => r / (m + 1))
            Filter.atTop (nhds 0) := by
          apply Filter.Tendsto.div_atTop tendsto_const_nhds
          exact Filter.tendsto_atTop_add_const_right _ 1
            tendsto_natCast_atTop_atTop
        simpa using tendsto_const_nhds.add hdiv
      have h2 := (Complex.continuous_ofReal.tendsto x₀).comp hreal
      exact h2.congr fun m => by simp only [Function.comp_apply]
    · apply Filter.Eventually.of_forall
      intro m
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := Complex.ofReal_injective h
      have hpos : 0 < r / (m + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in nhdsWithin (x₀ : ℂ) {(x₀ : ℂ)}ᶜ, expSum μ c 0 z = 0 :=
    htend.frequently (Filter.Frequently.of_forall fun m => hz _ (hmem m))
  have han : AnalyticOnNhd ℂ (expSum μ c 0) Set.univ := fun z _ =>
    (differentiable_expSum μ c 0).analyticAt z
  have := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ ((x₀ : ℝ) : ℂ)) hfreq
  intro z
  exact this (Set.mem_univ z)

/-- Iterated derivatives of the zero function vanish. -/
lemma iterate_deriv_zero (k : ℕ) :
    deriv^[k] (fun _ : ℂ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  induction k with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      funext z
      exact deriv_const z 0

/-- **The Vandermonde extraction**: distinct exponents force all
coefficients of an identically vanishing exponential sum to vanish. -/
theorem expSum_coeffs_eq_zero_of_zero (μ c : Fin n → ℂ)
    (hμ : Function.Injective μ)
    (h : ∀ z : ℂ, expSum μ c 0 z = 0) : ∀ i, c i = 0 := by
  have hfun : expSum μ c 0 = fun _ => (0 : ℂ) := funext h
  have hk : ∀ k : ℕ, expSum μ c k = fun _ => (0 : ℂ) := by
    intro k
    rw [← iterate_deriv_expSum, hfun, iterate_deriv_zero]
  -- the Vandermonde system Σ_i c_i μ_i^k = 0 for every k
  have hsys : ∀ k : ℕ, ∑ i, c i * μ i ^ k = 0 := by
    intro k
    have := congrFun (hk k) 0
    simpa [expSum] using this
  -- package as vecMul against the Vandermonde matrix
  have hvec : Matrix.vecMul c (Matrix.vandermonde μ) = 0 := by
    funext j
    simpa [Matrix.vecMul, dotProduct, Matrix.vandermonde] using hsys (j : ℕ)
  have hdet : (Matrix.vandermonde μ).det ≠ 0 := by
    rw [Matrix.det_vandermonde]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    rw [Finset.mem_Ioi] at hj
    exact sub_ne_zero.mpr fun hc => absurd (hμ hc) hj.ne'
  have := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
  intro i
  exact congrFun this i

/-- **THE HEADLINE**: a finite exponential polynomial with distinct
exponents that vanishes on an open interval has all coefficients zero —
a vanishing polar correction empties the ledger. -/
theorem polar_correction_empties_ledger (μ c : Fin n → ℂ)
    (hμ : Function.Injective μ) {a b : ℝ} (hab : a < b)
    (hz : ∀ x : ℝ, x ∈ Set.Ioo a b → ∑ i, c i * Complex.exp (μ i * x) = 0) :
    ∀ i, c i = 0 := by
  apply expSum_coeffs_eq_zero_of_zero μ c hμ
  apply expSum_zero_on_interval_eq_zero μ c hab
  intro x hx
  simpa [expSum] using hz x hx

end CriticalLinePhasor.PolarCorrection

#print axioms CriticalLinePhasor.PolarCorrection.expSum_zero_on_interval_eq_zero
#print axioms CriticalLinePhasor.PolarCorrection.expSum_coeffs_eq_zero_of_zero
#print axioms CriticalLinePhasor.PolarCorrection.polar_correction_empties_ledger
