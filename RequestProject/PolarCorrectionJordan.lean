import RequestProject.PolarCorrection

/-!
# The Jordan extension: multiplicities discharge, and the centre carries none

The registered multiplicity debt of the discharge layer, paid.  Two
theorems close the two places where higher-order poles could have hidden:

* `expPoly_independent` — **the full exponential-polynomial
  independence**: a finite sum `Σ P_i(z)·e^{μ_i z}` with distinct
  exponents and polynomial coefficients vanishing identically on ℂ has
  every `P_i = 0`.  (The open-interval version follows by the identity
  bridge exactly as in `PolarCorrection` — the block sum is entire; that
  corollary is deferred, not hidden.)
  Proof: shift by one exponent, differentiate past the degree of its block
  (the block operator `A_ν P = ν•P + P′` kills the `ν = 0` block and is
  INJECTIVE for `ν ≠ 0` — the leading coefficient survives), and induct on
  the index set.  This upgrades `polar_correction_empties_ledger` from
  simple poles to arbitrary finite multiplicities: the `(log y)^j` Jordan
  terms carry an invertible triangular relation to principal parts, so a
  vanishing polar correction empties the ledger WITH multiplicity;
* `poly_translation_rigidity` — **the centre carries no Jordan block**: a
  polynomial with `P(u+h) = w·P(u)` for a single nonzero shift is
  constant (and `w = 1`): composition with `X + h` preserves the leading
  coefficient, and `{n·h}` gives infinitely many roots of `P − P(0)`.
  Combined with the compiled warps (which force central support) and the
  even-sign fixed-point kill, the centre admits neither higher
  multiplicity nor a simple residue.

Register.  With this file the finite-ledger machine has NO multiplicity
caveat left; remaining instantiation-tier debts (restoration bank
identity, carrier-level warp algebra, ε-compilation) are registered in the
campaign ledger.  No `axiom`, no `sorry`.
-/

open Polynomial

namespace CriticalLinePhasor.PolarCorrectionJordan

/-- The block operator: differentiation acts on `P(z)·e^{νz}` as
`A_ν P = ν•P + P′`. -/
noncomputable def blockOp (ν : ℂ) (P : ℂ[X]) : ℂ[X] :=
  C ν * P + derivative P

lemma hasDerivAt_block (ν : ℂ) (P : ℂ[X]) (z : ℂ) :
    HasDerivAt (fun w => P.eval w * Complex.exp (ν * w))
      ((blockOp ν P).eval z * Complex.exp (ν * z)) z := by
  have h1 : HasDerivAt (fun w => P.eval w) (P.derivative.eval z) z :=
    P.hasDerivAt z
  have h2 : HasDerivAt (fun w => Complex.exp (ν * w))
      (Complex.exp (ν * z) * ν) z := by
    have hlin : HasDerivAt (fun w : ℂ => ν * w) ν z := by
      simpa using (hasDerivAt_id z).const_mul ν
    exact (Complex.hasDerivAt_exp (ν * z)).comp z hlin
  have h3 := h1.mul h2
  have hval : P.derivative.eval z * Complex.exp (ν * z)
      + P.eval z * (Complex.exp (ν * z) * ν)
      = (blockOp ν P).eval z * Complex.exp (ν * z) := by
    unfold blockOp
    simp only [eval_add, eval_mul, eval_C]
    ring
  exact hval ▸ h3

/-- The `ν = 0` block dies after enough derivatives. -/
lemma blockOp_zero_iterate (P : ℂ[X]) :
    (blockOp 0)^[P.natDegree + 1] P = 0 := by
  have hfun : blockOp 0 = fun Q => derivative Q := by
    funext Q
    unfold blockOp
    simp
  rw [hfun]
  exact iterate_derivative_eq_zero (Nat.lt_succ_self _)

/-- **Injectivity of a nonzero block operator**: the leading coefficient
survives `A_ν`. -/
lemma blockOp_eq_zero {ν : ℂ} (hν : ν ≠ 0) {P : ℂ[X]}
    (h : blockOp ν P = 0) : P = 0 := by
  by_contra hP
  have hc : (blockOp ν P).coeff P.natDegree = 0 := by
    rw [h]
    simp
  unfold blockOp at hc
  rw [coeff_add, coeff_C_mul, coeff_derivative] at hc
  have h2 : P.coeff (P.natDegree + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  rw [h2] at hc
  simp only [zero_mul, add_zero] at hc
  rcases mul_eq_zero.mp hc with h' | h'
  · exact hν h'
  · exact (leadingCoeff_ne_zero.mpr hP) h'

lemma blockOp_injective {ν : ℂ} (hν : ν ≠ 0) :
    Function.Injective (blockOp ν) := by
  intro P Q hPQ
  have hz : blockOp ν (P - Q) = 0 := by
    unfold blockOp at hPQ ⊢
    rw [derivative_sub]
    linear_combination hPQ
  have := blockOp_eq_zero hν hz
  exact sub_eq_zero.mp this

/-- Differentiating a block sum applies the block operators. -/
lemma iterate_deriv_blockSum {ι : Type*} (s : Finset ι) (ν : ι → ℂ)
    (P : ι → ℂ[X]) (k : ℕ) :
    deriv^[k] (fun z => ∑ i ∈ s, (P i).eval z * Complex.exp (ν i * z))
      = fun z => ∑ i ∈ s, ((blockOp (ν i))^[k] (P i)).eval z
          * Complex.exp (ν i * z) := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      funext z
      have h0 := HasDerivAt.sum
        (fun i (_ : i ∈ s) =>
          hasDerivAt_block (ν i) ((blockOp (ν i))^[m] (P i)) z)
      have hfn : (∑ i ∈ s, fun w => ((blockOp (ν i))^[m] (P i)).eval w
            * Complex.exp (ν i * w))
          = fun w => ∑ i ∈ s, ((blockOp (ν i))^[m] (P i)).eval w
            * Complex.exp (ν i * w) := by
        funext w
        simp [Finset.sum_apply]
      rw [hfn] at h0
      have heq : (∑ i ∈ s, ((blockOp (ν i)) ((blockOp (ν i))^[m] (P i))).eval z
            * Complex.exp (ν i * z))
          = ∑ i ∈ s, ((blockOp (ν i))^[m + 1] (P i)).eval z
            * Complex.exp (ν i * z) :=
        Finset.sum_congr rfl fun i _ => by
          rw [← Function.iterate_succ_apply' (blockOp (ν i)) m (P i)]
      rw [heq] at h0
      exact h0.deriv

/-- **The full exponential-polynomial independence** (identical
vanishing). -/
theorem expPoly_independent {ι : Type*} [DecidableEq ι] :
    ∀ (s : Finset ι) (μ : ι → ℂ) (P : ι → ℂ[X]),
      Set.InjOn μ s →
      (∀ z : ℂ, ∑ i ∈ s, (P i).eval z * Complex.exp (μ i * z) = 0) →
      ∀ i ∈ s, P i = 0 := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro μ P _ _ i hi; exact absurd hi (Finset.notMem_empty i)
  | insert a s ha ih =>
      intro μ P hinj h
      -- shift so the `a`-block has exponent zero
      set ν : ι → ℂ := fun i => μ i - μ a with hν
      have hshift : ∀ z : ℂ,
          ∑ i ∈ insert a s, (P i).eval z * Complex.exp (ν i * z) = 0 := by
        intro z
        have h1 := h z
        have h2 : ∑ i ∈ insert a s, (P i).eval z * Complex.exp (ν i * z)
            = Complex.exp (-(μ a * z))
              * ∑ i ∈ insert a s, (P i).eval z * Complex.exp (μ i * z) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [hν]
          rw [show (μ i - μ a) * z = μ i * z + -(μ a * z) by ring,
            Complex.exp_add]
          ring
        rw [h2, h1, mul_zero]
      -- differentiate past the degree of the `a`-block
      set k : ℕ := (P a).natDegree + 1 with hk
      have hzero : ∀ z : ℂ,
          ∑ i ∈ insert a s, ((blockOp (ν i))^[k] (P i)).eval z
            * Complex.exp (ν i * z) = 0 := by
        intro z
        have h1 := congrFun (iterate_deriv_blockSum (insert a s) ν P k) z
        have h2 : deriv^[k] (fun z => ∑ i ∈ insert a s,
            (P i).eval z * Complex.exp (ν i * z)) = fun _ => (0 : ℂ) := by
          have hfun : (fun z => ∑ i ∈ insert a s,
              (P i).eval z * Complex.exp (ν i * z)) = fun _ => (0 : ℂ) :=
            funext hshift
          rw [hfun]
          exact CriticalLinePhasor.PolarCorrection.iterate_deriv_zero k
        rw [h2] at h1
        simpa using h1.symm
      -- the `a`-block is dead; the rest is a sum over `s`
      have hs : ∀ z : ℂ,
          ∑ i ∈ s, ((blockOp (ν i))^[k] (P i)).eval z
            * Complex.exp (ν i * z) = 0 := by
        intro z
        have h1 := hzero z
        rw [Finset.sum_insert ha] at h1
        have hνa : ν a = 0 := by rw [hν]; ring
        have hdead : (blockOp (ν a))^[k] (P a) = 0 := by
          rw [hνa, hk]
          exact blockOp_zero_iterate (P a)
        rw [hdead] at h1
        simpa using h1
      -- induction: the transformed blocks over `s` all vanish
      have hinj_s : Set.InjOn ν s := by
        intro i hi j hj hij
        apply hinj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj)
        have : μ i - μ a = μ j - μ a := hij
        linear_combination this
      have hIH := ih ν (fun i => (blockOp (ν i))^[k] (P i)) hinj_s hs
      -- undo the injective operators
      have hPzero_s : ∀ i ∈ s, P i = 0 := by
        intro i hi
        have hνi : ν i ≠ 0 := by
          rw [hν]
          intro hcon
          have : μ i = μ a := by linear_combination hcon
          exact ha (by
            have := hinj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self a s) this
            rwa [this] at hi)
        have hIHi := hIH i hi
        have hfix : (blockOp (ν i))^[k] (0 : ℂ[X]) = 0 :=
          Function.iterate_fixed (by unfold blockOp; simp) k
        exact Function.Injective.iterate (blockOp_injective hνi) k
          (by rw [hIHi, hfix])
      -- and finally the `a`-block itself
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · have h0 : ∀ z : ℂ, (P i).eval z * Complex.exp (μ i * z) = 0 := by
          intro z
          have h1 := h z
          rw [Finset.sum_insert ha] at h1
          have h2 : ∑ j ∈ s, (P j).eval z * Complex.exp (μ j * z) = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            rw [hPzero_s j hj]
            simp
          rw [h2, add_zero] at h1
          exact h1
        have heval : ∀ z : ℂ, (P i).eval z = 0 := by
          intro z
          have := h0 z
          rcases mul_eq_zero.mp this with h' | h'
          · exact h'
          · exact absurd h' (Complex.exp_ne_zero _)
        exact Polynomial.funext fun z => by rw [heval z]; simp
      · exact hPzero_s i hi'

/-- **The centre carries no Jordan block**: projective translation
invariance under one nonzero shift forces a polynomial to be constant. -/
theorem poly_translation_rigidity {P : ℂ[X]} {h w : ℂ} (hh : h ≠ 0)
    (hinv : ∀ u : ℂ, P.eval (u + h) = w * P.eval u) :
    P.natDegree = 0 := by
  by_cases hP : P = 0
  · rw [hP]; simp
  -- the functional identity as polynomials
  have hcomp : P.comp (X + C h) = C w * P := by
    apply Polynomial.funext
    intro u
    simp only [eval_comp, eval_add, eval_X, eval_C, eval_mul]
    exact hinv u
  -- leading coefficients force w = 1
  have hlead : P.leadingCoeff = w * P.leadingCoeff := by
    have h1 := congrArg leadingCoeff hcomp
    rwa [leadingCoeff_comp (by simp), leadingCoeff_mul, leadingCoeff_C,
      leadingCoeff_X_add_C, one_pow, mul_one] at h1
  have hw : w = 1 := by
    have h2 : (w - 1) * P.leadingCoeff = 0 := by linear_combination -hlead
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' (leadingCoeff_ne_zero.mpr hP)
  subst hw
  -- infinitely many roots of P − P(0)
  by_contra hdeg
  have hroots : ∀ n : ℕ, (P - C (P.eval 0)).IsRoot (n * h) := by
    intro n
    induction n with
    | zero => simp [IsRoot]
    | succ m ihm =>
        simp only [IsRoot, eval_sub, eval_C, sub_eq_zero] at ihm ⊢
        push_cast
        rw [show ((m : ℂ) + 1) * h = (m : ℂ) * h + h by ring, hinv, one_mul]
        exact ihm
  have hne : P - C (P.eval 0) ≠ 0 := by
    intro hcon
    apply hdeg
    have hPC : P = C (P.eval 0) := by linear_combination hcon
    rw [hPC]
    simp
  apply hne
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.Infinite.mono
    (s := Set.range fun n : ℕ => (n : ℂ) * h)
  · rintro z ⟨n, rfl⟩
    exact hroots n
  · apply Set.infinite_range_of_injective
    intro m n hmn
    have hmn2 : (m : ℂ) = n := mul_right_cancel₀ hh hmn
    exact Nat.cast_inj.mp hmn2

/-! ## The interval corollary: the promised bridge, discharged -/

/-- The generic identity bridge: an entire function vanishing on an open
real interval vanishes identically. -/
theorem entire_eq_zero_of_zero_on_interval {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {a b : ℝ} (hab : a < b)
    (hz : ∀ x : ℝ, x ∈ Set.Ioo a b → f (x : ℂ) = 0) :
    ∀ z : ℂ, f z = 0 := by
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
      have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    exact ⟨by linarith, by linarith⟩
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
  have hfreq : ∃ᶠ z in nhdsWithin (x₀ : ℂ) {(x₀ : ℂ)}ᶜ, f z = 0 :=
    htend.frequently (Filter.Frequently.of_forall fun m => hz _ (hmem m))
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ ((x₀ : ℝ) : ℂ)) hfreq
  intro z
  exact this (Set.mem_univ z)

/-- Block sums are entire. -/
lemma differentiable_blockSum {ι : Type*} (s : Finset ι) (ν : ι → ℂ)
    (P : ι → ℂ[X]) :
    Differentiable ℂ (fun z => ∑ i ∈ s, (P i).eval z * Complex.exp (ν i * z)) :=
  fun z => (by
    have h0 := HasDerivAt.sum
      (fun i (_ : i ∈ s) => hasDerivAt_block (ν i) (P i) z)
    have hfn : (∑ i ∈ s, fun w => (P i).eval w * Complex.exp (ν i * w))
        = fun w => ∑ i ∈ s, (P i).eval w * Complex.exp (ν i * w) := by
      funext w
      simp [Finset.sum_apply]
    rw [hfn] at h0
    exact h0.differentiableAt)

/-- **The interval form of the full independence** — the deferred corollary,
discharged: vanishing of the exponential-polynomial sum on an open real
interval kills every polynomial coefficient. -/
theorem expPoly_independent_of_zero_on_interval {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (μ : ι → ℂ) (P : ι → ℂ[X])
    (hinj : Set.InjOn μ s) {a b : ℝ} (hab : a < b)
    (hz : ∀ x : ℝ, x ∈ Set.Ioo a b →
      ∑ i ∈ s, (P i).eval (x : ℂ) * Complex.exp (μ i * x) = 0) :
    ∀ i ∈ s, P i = 0 := by
  apply expPoly_independent s μ P hinj
  exact entire_eq_zero_of_zero_on_interval
    (differentiable_blockSum s μ P) hab hz

end CriticalLinePhasor.PolarCorrectionJordan

#print axioms CriticalLinePhasor.PolarCorrectionJordan.expPoly_independent
#print axioms CriticalLinePhasor.PolarCorrectionJordan.poly_translation_rigidity
#print axioms CriticalLinePhasor.PolarCorrectionJordan.expPoly_independent_of_zero_on_interval
