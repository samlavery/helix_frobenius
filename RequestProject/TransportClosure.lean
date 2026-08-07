import RequestProject.Sym2RankinBank
import RequestProject.GlobalHelixCPSFullCompletion
import RequestProject.SymrBankAllRanks
import RequestProject.CarrierFunctoriality

/-!
# Transport closure: direct sums of weight systems compose exactly

Rung 8 of the benchmark ladder — the systems-level property.  A carrier transport acts on
a weight system; this file proves that the arithmetic passport **composes**: the direct
sum of two weight systems carries

* the **Cauchy product** of the local Euler coefficients (`radialLocalEulerCoeff_sumElim`
  — the master law `h_j(u ⊕ v) = Σ_{a+b=j} h_a(u)·h_b(v)`),
* the **Dirichlet convolution** of the global banks (`bankArithmetic_sumElim`, through
  the generic multiplicativity `isMultiplicative_bankArithmetic` and the prime-power
  values `bankArithmetic_prime_pow`),
* the **product** of the prescribed completions at the product conductor and the
  concatenated shift list (`completedReadout_sumPair`),
* the **product** of self-dual functional equations (`FE_mul`),

together with index-relabeling invariance (`radialLocalEulerCoeff_equiv`,
`radialGlobalSatakeCoeff_equiv`) and the sum of polynomial Satake pairs (`sumPair`,
with `sumPair_primalCoeff` the coefficient closure).  The abstract composition laws —
associativity, two-sided identity, faithfulness closed under composition, base-change
degrees multiplying — are the compiled `CarrierFunctoriality`.

Two arithmetic instances close the loop with the landed r = 2 chain:

* `tensorSquare_bank` — **`std ⊗ std = Sym² ⊕ 1`**: the direct sum of the `Sym²` clock
  system and the unit system carries the rank-4 Rankin bank `ζ ⋆ sym2Bank` — the
  tensor-square decomposition realized as a closure instance;
* `plethysm_bank` — **`Sym² ∘ Sym² = Sym⁴ ⊕ 1`**: the six pairwise products of the
  `Sym²` clock (`sym2CompWeight`, `sym2CompWeight_products`) split as the `Sym⁴` clock
  plus one trivial channel (`sym2CompWeight_decomposition` via `sixSplit`), so the
  composite bank is `ζ ⋆ symrBank H 4` — the plethysm at the bank level, from one seed.

No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups ArithmeticFunction.zeta LSeries.notation

namespace CriticalLinePhasor.TransportClosure

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.Sym2Rankin CriticalLinePhasor.SymrBank

variable {k : ℤ} {f : CuspForm 𝒮ℒ k}


/-- Index re-labeling invariance of the local Euler coefficient. -/
theorem radialLocalEulerCoeff_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : κ → ℂ) (j : ℕ) :
    radialLocalEulerCoeff (w ∘ e) j = radialLocalEulerCoeff w j := by
  classical
  unfold radialLocalEulerCoeff
  refine Finset.sum_nbij' (fun l => Finsupp.equivMapDomain e l)
    (fun l => Finsupp.equivMapDomain e.symm l) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_finsuppAntidiag] at hl ⊢
    refine ⟨?_, Finset.subset_univ _⟩
    rw [← hl.1]
    calc ∑ c, (Finsupp.equivMapDomain e l) c
        = ∑ c, l (e.symm c) := Finset.sum_congr rfl fun c _ => rfl
      _ = ∑ i, l i := Equiv.sum_comp e.symm _
  · intro l hl
    simp only [Finset.mem_finsuppAntidiag] at hl ⊢
    refine ⟨?_, Finset.subset_univ _⟩
    rw [← hl.1]
    calc ∑ i, (Finsupp.equivMapDomain e.symm l) i
        = ∑ i, l (e i) := Finset.sum_congr rfl fun i _ => by simp
      _ = ∑ c, l c := Equiv.sum_comp e _
  · intro l _
    ext i
    simp
  · intro l _
    ext i
    simp
  · intro l _
    rw [← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Finsupp.equivMapDomain]

/-- The unit weight system: one channel of weight `1` has all local coefficients `1`. -/
theorem radialLocalEulerCoeff_unit (j : ℕ) :
    radialLocalEulerCoeff (fun _ : Fin 1 => (1 : ℂ)) j = 1 := by
  classical
  unfold radialLocalEulerCoeff
  refine Eq.trans (Finset.sum_congr rfl (g := fun _ => (1 : ℂ))
    (fun l _ => Finset.prod_eq_one fun i _ => one_pow _)) ?_
  simp [Finset.card_finsuppAntidiag_nat_eq_multichoose, Nat.multichoose_eq]


/-- Restriction of a finitely-supported function on a sum type to the left summand. -/
noncomputable def restrictL {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l : (ι ⊕ κ) →₀ ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => l (Sum.inl i))

/-- Restriction to the right summand. -/
noncomputable def restrictR {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l : (ι ⊕ κ) →₀ ℕ) : κ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => l (Sum.inr i))

@[simp] theorem restrictL_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l : (ι ⊕ κ) →₀ ℕ) (i : ι) : restrictL l i = l (Sum.inl i) := rfl

@[simp] theorem restrictR_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l : (ι ⊕ κ) →₀ ℕ) (i : κ) : restrictR l i = l (Sum.inr i) := rfl

/-- Glue two finitely-supported functions along a sum type. -/
noncomputable def glue {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l₁ : ι →₀ ℕ) (l₂ : κ →₀ ℕ) : (ι ⊕ κ) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim l₁ l₂)

@[simp] theorem glue_inl {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l₁ : ι →₀ ℕ) (l₂ : κ →₀ ℕ) (i : ι) : glue l₁ l₂ (Sum.inl i) = l₁ i := rfl

@[simp] theorem glue_inr {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l₁ : ι →₀ ℕ) (l₂ : κ →₀ ℕ) (i : κ) : glue l₁ l₂ (Sum.inr i) = l₂ i := rfl

/-- **The direct-sum Cauchy law**: the local Euler coefficient of a disjoint union of
weight systems is the Cauchy product of the two coefficients. -/
theorem radialLocalEulerCoeff_sumElim {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → ℂ) (v : κ → ℂ) (j : ℕ) :
    radialLocalEulerCoeff (Sum.elim u v) j
      = ∑ a ∈ Finset.range (j + 1),
          radialLocalEulerCoeff u a * radialLocalEulerCoeff v (j - a) := by
  classical
  unfold radialLocalEulerCoeff
  have hsplit : ∀ a : ℕ,
      (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) a, ∏ i, u i ^ l i) *
        (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset κ) (j - a), ∏ i, v i ^ l i)
      = ∑ p ∈ (Finset.finsuppAntidiag (Finset.univ : Finset ι) a) ×ˢ
            (Finset.finsuppAntidiag (Finset.univ : Finset κ) (j - a)),
          (∏ i, u i ^ p.1 i) * (∏ i, v i ^ p.2 i) := by
    intro a
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
  rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_sigma']
  refine Finset.sum_nbij' (fun l => (⟨∑ i : ι, l (Sum.inl i),
      (restrictL l, restrictR l)⟩ : Σ _ : ℕ, (ι →₀ ℕ) × (κ →₀ ℕ)))
    (fun q => glue q.2.1 q.2.2) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_finsuppAntidiag] at hl
    have hsum : ∑ i : ι ⊕ κ, l i = j := hl.1
    rw [Fintype.sum_sum_type] at hsum
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_product,
      Finset.mem_finsuppAntidiag]
    have eL : ∑ i : ι, restrictL l i = ∑ i : ι, l (Sum.inl i) :=
      Finset.sum_congr rfl fun i _ => rfl
    have eR : ∑ i : κ, restrictR l i = ∑ i : κ, l (Sum.inr i) :=
      Finset.sum_congr rfl fun i _ => rfl
    refine ⟨by omega, ⟨by rw [eL], Finset.subset_univ _⟩,
      ⟨by rw [eR]; omega, Finset.subset_univ _⟩⟩
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_product,
      Finset.mem_finsuppAntidiag] at hq
    obtain ⟨ha, ⟨h1, -⟩, ⟨h2, -⟩⟩ := hq
    simp only [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    rw [Fintype.sum_sum_type]
    have e1 : ∑ i : ι, glue q.2.1 q.2.2 (Sum.inl i) = ∑ i : ι, q.2.1 i :=
      Finset.sum_congr rfl fun i _ => rfl
    have e2 : ∑ i : κ, glue q.2.1 q.2.2 (Sum.inr i) = ∑ i : κ, q.2.2 i :=
      Finset.sum_congr rfl fun i _ => rfl
    rw [e1, e2, h1, h2]
    omega
  · intro l _
    ext i
    cases i with
    | inl i => simp
    | inr i => simp
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_product,
      Finset.mem_finsuppAntidiag] at hq
    obtain ⟨-, ⟨h1, -⟩, -⟩ := hq
    obtain ⟨a, l₁, l₂⟩ := q
    have hfst : ∑ i : ι, glue l₁ l₂ (Sum.inl i) = a := by
      rw [show ∑ i : ι, glue l₁ l₂ (Sum.inl i) = ∑ i : ι, l₁ i from
        Finset.sum_congr rfl fun i _ => rfl]
      exact h1
    refine Sigma.ext hfst (heq_of_eq ?_)
    refine Prod.ext ?_ ?_
    · ext i; simp
    · ext i; simp
  · intro l _
    rw [Fintype.prod_sum_type]
    rfl


/-- The Dirichlet convolution at a prime power is the Cauchy product of prime-power values. -/
theorem mul_apply_prime_pow (A B : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (A * B) (p ^ j) = ∑ a ∈ range (j + 1), A (p ^ a) * B (p ^ (j - a)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun d e => A d * B e),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos]

/-- The all-place bank as a plain product over prime factors. -/
theorem radialGlobalSatakeCoeff_eq_prod_dite {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (n : ℕ) :
    radialGlobalSatakeCoeff w n
      = ∏ p ∈ (n + 1).primeFactors,
          (if hp : p.Prime then
            radialLocalEulerCoeff (w ⟨p, hp⟩) ((n + 1).factorization p) else 1) := by
  unfold radialGlobalSatakeCoeff
  rw [← Finset.prod_coe_sort ((n + 1).primeFactors)
    (fun p => if hp : p.Prime then
      radialLocalEulerCoeff (w ⟨p, hp⟩) ((n + 1).factorization p) else 1)]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [dif_pos (Nat.prime_of_mem_primeFactors p.2)]

/-- The shifted all-place bank of any weight family is a multiplicative arithmetic
function. -/
theorem isMultiplicative_bankArithmetic {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) :
    (coefficientArithmetic (radialGlobalSatakeCoeff w)).IsMultiplicative := by
  constructor
  · show (if (1 : ℕ) = 0 then 0 else radialGlobalSatakeCoeff w (1 - 1)) = 1
    rw [if_neg one_ne_zero]
    exact radialGlobalSatakeCoeff_zero w
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · have : n = 1 := by rwa [Nat.coprime_zero_left] at hmn
      subst this
      simp [coefficientArithmetic]
    rcases eq_or_ne n 0 with rfl | hn
    · have : m = 1 := by rwa [Nat.coprime_zero_right] at hmn
      subst this
      simp [coefficientArithmetic]
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
    show (if m * n = 0 then 0 else radialGlobalSatakeCoeff w (m * n - 1))
        = (if m = 0 then 0 else radialGlobalSatakeCoeff w (m - 1)) *
          (if n = 0 then 0 else radialGlobalSatakeCoeff w (n - 1))
    rw [if_neg hmn0, if_neg hm, if_neg hn,
      radialGlobalSatakeCoeff_eq_prod_dite, radialGlobalSatakeCoeff_eq_prod_dite,
      radialGlobalSatakeCoeff_eq_prod_dite,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hmn0),
      Nat.sub_add_cancel hm1, Nat.sub_add_cancel hn1,
      Nat.primeFactors_mul hm hn]
    have hdisj : Disjoint m.primeFactors n.primeFactors :=
      Nat.Coprime.disjoint_primeFactors hmn
    rw [Finset.prod_union hdisj]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine Finset.prod_congr rfl fun p hpm => ?_
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpm
      rw [dif_pos hp, dif_pos hp]
      congr 1
      rw [Nat.factorization_mul hm hn]
      have hnp : n.factorization p = 0 := by
        have hpn : p ∉ n.primeFactors := Finset.disjoint_left.mp hdisj hpm
        rw [← Nat.support_factorization] at hpn
        exact Finsupp.notMem_support_iff.mp hpn
      simp [hnp]
    · refine Finset.prod_congr rfl fun p hpn => ?_
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpn
      rw [dif_pos hp, dif_pos hp]
      congr 1
      rw [Nat.factorization_mul hm hn]
      have hmp : m.factorization p = 0 := by
        have hpm : p ∉ m.primeFactors := Finset.disjoint_right.mp hdisj hpn
        rw [← Nat.support_factorization] at hpm
        exact Finsupp.notMem_support_iff.mp hpm
      simp [hmp]

/-- The shifted bank at prime powers is the local Euler coefficient. -/
theorem bankArithmetic_prime_pow {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (coefficientArithmetic (radialGlobalSatakeCoeff w)) (p ^ j)
      = radialLocalEulerCoeff (w ⟨p, hp⟩) j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · show (if (1 : ℕ) = 0 then 0 else radialGlobalSatakeCoeff w (1 - 1)) = _
    rw [if_neg one_ne_zero]
    show radialGlobalSatakeCoeff w 0 = _
    rw [radialGlobalSatakeCoeff_zero]
    classical
    unfold radialLocalEulerCoeff
    simp
  · have hpj : p ^ j ≠ 0 := pow_ne_zero _ hp.pos.ne'
    show (if p ^ j = 0 then 0 else radialGlobalSatakeCoeff w (p ^ j - 1)) = _
    rw [if_neg hpj, radialGlobalSatakeCoeff_eq_prod_dite,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpj),
      Nat.primeFactors_prime_pow hj.ne' hp, Finset.prod_singleton, dif_pos hp,
      Nat.Prime.factorization_pow hp]
    simp


/-- **The bank closure law**: the shifted all-place bank of a direct sum of weight families
is the Dirichlet convolution of the two banks. -/
theorem bankArithmetic_sumElim {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : Nat.Primes → ι → ℂ) (v : Nat.Primes → κ → ℂ) :
    coefficientArithmetic (radialGlobalSatakeCoeff (fun p => Sum.elim (u p) (v p)))
      = coefficientArithmetic (radialGlobalSatakeCoeff u) *
          coefficientArithmetic (radialGlobalSatakeCoeff v) := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_bankArithmetic _) _
    ((isMultiplicative_bankArithmetic u).mul (isMultiplicative_bankArithmetic v))]
  intro p j hp
  rw [bankArithmetic_prime_pow _ hp, mul_apply_prime_pow _ _ hp,
    radialLocalEulerCoeff_sumElim]
  exact Finset.sum_congr rfl fun a _ => by
    rw [bankArithmetic_prime_pow u hp, bankArithmetic_prime_pow v hp]

/-- The direct sum of two polynomial Satake dual pairs. -/
noncomputable def sumPair {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W₁ : PolynomialSatakeDualPair ι) (W₂ : PolynomialSatakeDualPair κ) :
    PolynomialSatakeDualPair (ι ⊕ κ) where
  primal := fun p => Sum.elim (W₁.primal p) (W₂.primal p)
  dual := fun p => Sum.elim (W₁.dual p) (W₂.dual p)
  primalExponent := max W₁.primalExponent W₂.primalExponent
  dualExponent := max W₁.dualExponent W₂.dualExponent
  primal_ne_zero := by
    intro p i
    cases i with
    | inl i => exact W₁.primal_ne_zero p i
    | inr i => exact W₂.primal_ne_zero p i
  dual_eq_inv := by
    intro p i
    cases i with
    | inl i => exact W₁.dual_eq_inv p i
    | inr i => exact W₂.dual_eq_inv p i
  primal_bound := by
    intro p i
    have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
    cases i with
    | inl i =>
        exact le_trans (W₁.primal_bound p i) (pow_le_pow_right₀ hp1 (le_max_left _ _))
    | inr i =>
        exact le_trans (W₂.primal_bound p i) (pow_le_pow_right₀ hp1 (le_max_right _ _))
  dual_bound := by
    intro p i
    have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
    cases i with
    | inl i =>
        exact le_trans (W₁.dual_bound p i) (pow_le_pow_right₀ hp1 (le_max_left _ _))
    | inr i =>
        exact le_trans (W₂.dual_bound p i) (pow_le_pow_right₀ hp1 (le_max_right _ _))

/-- **Coefficient closure**: the primal coefficients of the sum pair are the Dirichlet
convolution of the two coefficient banks, index for index. -/
theorem sumPair_primalCoeff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W₁ : PolynomialSatakeDualPair ι) (W₂ : PolynomialSatakeDualPair κ) (n : ℕ) :
    cpsPolynomialPrimalCoeff (sumPair W₁ W₂) n
      = (coefficientArithmetic (cpsPolynomialPrimalCoeff W₁) *
          coefficientArithmetic (cpsPolynomialPrimalCoeff W₂)) (n + 1) := by
  have h := congrArg (fun A : ArithmeticFunction ℂ => A (n + 1))
    (bankArithmetic_sumElim W₁.primal W₂.primal)
  rw [show coefficientArithmetic
      (radialGlobalSatakeCoeff (fun p => Sum.elim (W₁.primal p) (W₂.primal p))) (n + 1)
      = radialGlobalSatakeCoeff
          (fun p => Sum.elim (W₁.primal p) (W₂.primal p)) n from by
    simp [coefficientArithmetic]] at h
  exact h



/-- The generic shifted-Dirichlet ↔ L-series bridge. -/
theorem dirichlet_shift_eq_LSeries (A : ArithmeticFunction ℂ) {s : ℂ}
    (hsum : LSeriesSummable (⇑A) s) :
    CriticalLinePhasor.CarrierTheta.dirichlet (fun n => A (n + 1)) s
      = LSeries (⇑A) s := by
  have hsum' : Summable (LSeries.term (⇑A) s) := hsum
  rw [LSeries, hsum'.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  unfold CriticalLinePhasor.CarrierTheta.dirichlet
  refine tsum_congr fun n => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n),
    show ((n + 1 : ℕ) : ℂ) ^ (-s) = (((n + 1 : ℕ) : ℂ) ^ s)⁻¹ from cpow_neg _ s,
    div_eq_mul_inv]

/-- Global index-relabeling invariance of the all-place bank. -/
theorem radialGlobalSatakeCoeff_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : Nat.Primes → κ → ℂ) :
    radialGlobalSatakeCoeff (fun p => w p ∘ e) = radialGlobalSatakeCoeff w := by
  funext n
  unfold radialGlobalSatakeCoeff
  exact Finset.prod_congr rfl fun p _ => radialLocalEulerCoeff_equiv e _ _

/-- The Sym² clock bank, shifted, is the `Sym²` convolution bank. -/
theorem bankArithmetic_symClock_eq_sym2Bank (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => fun i : Fin 3 => symClockWeight 2 (H.satake p.2) (i : ℕ)))
      = sym2Bank f := by
  ext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [coefficientArithmetic]
  · show (if m = 0 then 0 else _) = _
    rw [if_neg hm.ne']
    rw [CriticalLinePhasor.Sym2Join.radialGlobal_eq_sym2Bank H (m - 1),
      Nat.sub_add_cancel hm]

/-- The unit weight system's bank is `ζ`. -/
theorem bankArithmetic_unit_eq_zeta :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun _ : Nat.Primes => fun _ : Fin 1 => (1 : ℂ)))
      = ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_bankArithmetic _) _ isMultiplicative_zeta.natCast]
  intro p j hp
  rw [bankArithmetic_prime_pow _ hp, radialLocalEulerCoeff_unit,
    ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    if_neg (pow_ne_zero _ hp.pos.ne'), Nat.cast_one]

/-- **The tensor-square decomposition at the bank level**: the direct sum of the `Sym²`
clock system and the unit system carries the rank-4 Rankin bank —
`std ⊗ std = Sym² ⊕ 1` as a closure instance. -/
theorem tensorSquare_bank (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => Sum.elim (fun i : Fin 3 => symClockWeight 2 (H.satake p.2) (i : ℕ))
        (fun _ : Fin 1 => (1 : ℂ))))
      = rankinBank f := by
  rw [bankArithmetic_sumElim, bankArithmetic_symClock_eq_sym2Bank H,
    bankArithmetic_unit_eq_zeta, mul_comm]
  rfl



/-- The `Sym²∘Sym²` weight system: the pairwise products of the `Sym²` clock. -/
noncomputable def sym2CompWeight (α : ℂ) : Fin 6 → ℂ :=
  ![α ^ (4 : ℤ), α ^ (2 : ℤ), 1, 1, α ^ (-2 : ℤ), α ^ (-4 : ℤ)]

/-- The six entries are the pairwise products `w_i·w_j`, `i ≤ j`, of the `Sym²` clock
`(α², 1, α⁻²)` — in the order `(0,0),(0,1),(1,1),(0,2),(1,2),(2,2)`. -/
theorem sym2CompWeight_products (α : ℂ) (hα : α ≠ 0) :
    sym2CompWeight α 0 = symClockWeight 2 α 0 * symClockWeight 2 α 0 ∧
    sym2CompWeight α 1 = symClockWeight 2 α 0 * symClockWeight 2 α 1 ∧
    sym2CompWeight α 2 = symClockWeight 2 α 1 * symClockWeight 2 α 1 ∧
    sym2CompWeight α 3 = symClockWeight 2 α 0 * symClockWeight 2 α 2 ∧
    sym2CompWeight α 4 = symClockWeight 2 α 1 * symClockWeight 2 α 2 ∧
    sym2CompWeight α 5 = symClockWeight 2 α 2 * symClockWeight 2 α 2 := by
  have h0 : symClockWeight 2 α 0 = α ^ (2 : ℤ) := by unfold symClockWeight; norm_num
  have h1 : symClockWeight 2 α 1 = 1 := by unfold symClockWeight; norm_num
  have h2 : symClockWeight 2 α 2 = α ^ (-2 : ℤ) := by unfold symClockWeight; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [sym2CompWeight, h0, h1, h2, ← zpow_add₀ hα] <;>
    field_simp

/-- The relabeling `Fin 6 ≃ Fin 5 ⊕ Fin 1` that splits off the trivial channel. -/
def sixSplit : Fin 6 ≃ Fin 5 ⊕ Fin 1 where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inl 3, Sum.inl 4]
  invFun := Sum.elim ![0, 1, 2, 4, 5] (fun _ => 3)
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    rcases i with i | i
    · fin_cases i <;> rfl
    · fin_cases i
      rfl

/-- **The plethysm decomposition of the weight system**: `Sym²∘Sym² = Sym⁴ ⊕ 1` — the
six pairwise products are the `Sym⁴` clock together with one trivial channel. -/
theorem sym2CompWeight_decomposition (α : ℂ) :
    sym2CompWeight α
      = (Sum.elim (fun i : Fin 5 => symClockWeight 4 α (i : ℕ))
          (fun _ : Fin 1 => (1 : ℂ))) ∘ sixSplit := by
  funext i
  fin_cases i <;>
    simp only [sym2CompWeight, sixSplit, Function.comp_apply, Equiv.coe_fn_mk] <;>
    norm_num [symClockWeight]

/-- **The plethysm bank law**: the `Sym²∘Sym²` bank is `ζ ⋆ Sym⁴`-bank — the closure
law's Cauchy product realized as the Dirichlet dressing of the `Sym⁴` bank. -/
theorem plethysm_bank (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => sym2CompWeight (H.satake p.2)))
      = ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) * symrBank H 4 := by
  have hdec : (fun p : Nat.Primes => sym2CompWeight (H.satake p.2))
      = fun p : Nat.Primes =>
          (Sum.elim (fun i : Fin 5 => symClockWeight 4 (H.satake p.2) (i : ℕ))
            (fun _ : Fin 1 => (1 : ℂ))) ∘ sixSplit := by
    funext p
    exact sym2CompWeight_decomposition (H.satake p.2)
  rw [hdec, radialGlobalSatakeCoeff_equiv sixSplit, bankArithmetic_sumElim,
    bankArithmetic_unit_eq_zeta]
  have h4 : coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p : Nat.Primes => fun i : Fin 5 => symClockWeight 4 (H.satake p.2) (i : ℕ)))
      = symrBank H 4 := by
    ext m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [coefficientArithmetic]
    · show (if m = 0 then 0 else _) = _
      rw [if_neg hm.ne']
      rw [show radialGlobalSatakeCoeff
          (fun p : Nat.Primes => fun i : Fin 5 => symClockWeight 4 (H.satake p.2) (i : ℕ))
            (m - 1)
          = symrBank H 4 (m - 1 + 1) from
        CriticalLinePhasor.Sym2Join.radialGlobal_eq_symrBank H 4 (m - 1),
        Nat.sub_add_cancel hm]
  rw [h4, mul_comm]


/-- **Completed-readout closure**: the prescribed completion of a sum pair, at the product
conductor and concatenated shift list, is the product of the two prescribed completions —
on any common point of absolute convergence. -/
theorem completedReadout_sumPair {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W₁ : PolynomialSatakeDualPair ι) (W₂ : PolynomialSatakeDualPair κ)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (μs₁ μs₂ : List ℂ) (s : ℂ)
    (h₁ : LSeriesSummable (⇑(coefficientArithmetic (cpsPolynomialPrimalCoeff W₁))) s)
    (h₂ : LSeriesSummable (⇑(coefficientArithmetic (cpsPolynomialPrimalCoeff W₂))) s) :
    cpsPolynomialFullPrimalCompletedReadout (sumPair W₁ W₂) (C₁ * C₂) (μs₁ ++ μs₂) s
      = cpsPolynomialFullPrimalCompletedReadout W₁ C₁ μs₁ s *
          cpsPolynomialFullPrimalCompletedReadout W₂ C₂ μs₂ s := by
  unfold cpsPolynomialFullPrimalCompletedReadout
  have hcond : ((C₁ * C₂ : ℝ) : ℂ) ^ s = ((C₁ : ℝ) : ℂ) ^ s * ((C₂ : ℝ) : ℂ) ^ s := by
    rw [Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg hC₁ hC₂ s
  have hgamma : ((μs₁ ++ μs₂).map fun μ => Complex.Gammaℂ (s + μ)).prod
      = (μs₁.map fun μ => Complex.Gammaℂ (s + μ)).prod *
        (μs₂.map fun μ => Complex.Gammaℂ (s + μ)).prod := by
    rw [List.map_append, List.prod_append]
  have hmul : ∀ (A B : ArithmeticFunction ℂ),
      LSeriesSummable (⇑A) s → LSeriesSummable (⇑B) s →
      CriticalLinePhasor.CarrierTheta.dirichlet (fun n => (A * B) (n + 1)) s
        = CriticalLinePhasor.CarrierTheta.dirichlet (fun n => A (n + 1)) s *
          CriticalLinePhasor.CarrierTheta.dirichlet (fun n => B (n + 1)) s := by
    intro A B hA hB
    rw [dirichlet_shift_eq_LSeries _
        (ArithmeticFunction.LSeriesSummable_mul hA hB),
      dirichlet_shift_eq_LSeries _ hA,
      dirichlet_shift_eq_LSeries _ hB]
    exact ArithmeticFunction.LSeries_mul' hA hB
  have hdir : CriticalLinePhasor.CarrierTheta.dirichlet
      (cpsPolynomialPrimalCoeff (sumPair W₁ W₂)) s
      = CriticalLinePhasor.CarrierTheta.dirichlet (cpsPolynomialPrimalCoeff W₁) s *
        CriticalLinePhasor.CarrierTheta.dirichlet (cpsPolynomialPrimalCoeff W₂) s := by
    have hshape : cpsPolynomialPrimalCoeff (sumPair W₁ W₂)
        = fun n => ((coefficientArithmetic (cpsPolynomialPrimalCoeff W₁) *
            coefficientArithmetic (cpsPolynomialPrimalCoeff W₂))) (n + 1) :=
      funext (sumPair_primalCoeff W₁ W₂)
    have hshape₁ : (fun n => (coefficientArithmetic (cpsPolynomialPrimalCoeff W₁)) (n + 1))
        = cpsPolynomialPrimalCoeff W₁ := by
      funext n
      simp [coefficientArithmetic]
    have hshape₂ : (fun n => (coefficientArithmetic (cpsPolynomialPrimalCoeff W₂)) (n + 1))
        = cpsPolynomialPrimalCoeff W₂ := by
      funext n
      simp [coefficientArithmetic]
    rw [hshape, hmul _ _ h₁ h₂, hshape₁, hshape₂]
  rw [hcond, hgamma, hdir]
  ring

/-- **Functional-equation closure**: self-dual reflections multiply. -/
theorem FE_mul {F G : ℂ → ℂ} (hF : ∀ s : ℂ, F (1 - s) = F s)
    (hG : ∀ s : ℂ, G (1 - s) = G s) (s : ℂ) :
    F (1 - s) * G (1 - s) = F s * G s := by
  rw [hF, hG]

end CriticalLinePhasor.TransportClosure

#print axioms CriticalLinePhasor.TransportClosure.radialLocalEulerCoeff_equiv
#print axioms CriticalLinePhasor.TransportClosure.radialLocalEulerCoeff_unit
#print axioms CriticalLinePhasor.TransportClosure.radialLocalEulerCoeff_sumElim
#print axioms CriticalLinePhasor.TransportClosure.mul_apply_prime_pow
#print axioms CriticalLinePhasor.TransportClosure.isMultiplicative_bankArithmetic
#print axioms CriticalLinePhasor.TransportClosure.bankArithmetic_prime_pow
#print axioms CriticalLinePhasor.TransportClosure.bankArithmetic_sumElim
#print axioms CriticalLinePhasor.TransportClosure.sumPair
#print axioms CriticalLinePhasor.TransportClosure.sumPair_primalCoeff
#print axioms CriticalLinePhasor.TransportClosure.dirichlet_shift_eq_LSeries
#print axioms CriticalLinePhasor.TransportClosure.radialGlobalSatakeCoeff_equiv
#print axioms CriticalLinePhasor.TransportClosure.bankArithmetic_symClock_eq_sym2Bank
#print axioms CriticalLinePhasor.TransportClosure.bankArithmetic_unit_eq_zeta
#print axioms CriticalLinePhasor.TransportClosure.tensorSquare_bank
#print axioms CriticalLinePhasor.TransportClosure.sym2CompWeight_products
#print axioms CriticalLinePhasor.TransportClosure.sym2CompWeight_decomposition
#print axioms CriticalLinePhasor.TransportClosure.plethysm_bank
#print axioms CriticalLinePhasor.TransportClosure.completedReadout_sumPair
#print axioms CriticalLinePhasor.TransportClosure.FE_mul
