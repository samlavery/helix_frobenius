import RequestProject.Sym2CoefficientIdentification
import RequestProject.Sym2RegistrationLanding

/-!
# The Hecke-multiplicativity wire (M1): the Sym² Euler identification

The named arithmetic input of the r = 2 rung, typed and consumed.  Input
(`HeckeEigenData`): the classical level-one Hecke eigenform package for `f` —
normalized first coefficient, coprime multiplicativity, the prime-power recursion
`a_{p^{j+2}} = a_p·a_{p^{j+1}} − p^{k−1}·a_{p^j}`, and reality of the coefficients.
This package is classical Hecke theory; it is not available in Mathlib (no Hecke
operators are formalized there), so it enters as the structure's fields.

From it, this file derives the whole wire:

* `HeckeEigenData.satake` — **the Satake lift**: at every prime a nonzero `α_p` with
  `a_{p^j} = p^{j(k−1)/2}·U_j(α_p)` for all `j` (`coeff_prime_pow`), where `U_j` is the
  compiled seed clock `Sym2Identification.seedCoeff`.  Existence of `α_p` is the
  quadratic `α + α⁻¹ = a_p/p^{(k−1)/2}`, solved in `ℂ`.
* `rankinSquareNorm_prime_pow` — the Deligne-normalized Rankin square at prime powers
  is the squared seed clock: `b_{p^j} = U_j(α_p)²`.
* `muRankin_prime_pow` — the Möbius peel of the Rankin square at prime powers is the
  compiled local peel: `(μ ⋆ b)_{p^j} = peeled α_p j`.
* `sym2Bank` — the global Sym² bank, defined as the square-dilation convolution
  `sqIndicator ⋆ (μ ⋆ b)`; `sym2Bank_prime_pow` identifies its local factors with the
  compiled Sym²-Satake traces: `sym2Bank_{p^j} = h_j(α_p², 1, α_p⁻²)`
  (`Sym2Identification.sym2Coeff`, the trace of `Sym^j` of the Sym²-Satake class) —
  Brick 1's local layer (`sym2Coeff_eq_sum_peeled`) assembled globally.
* `LSeries_sqIndicator` — the square-dilation factor reads out as `ζ(2s)`.
* `sym2_euler_identity` — **M1's display**: on `2 < Re s`,
  `ζ(2s) · L(μ ⋆ b, s) = L(sym2Bank, s)` — unconditional convolution algebra; the
  arithmetic content of the wire is exactly `sym2Bank_prime_pow` above.
* `sym2_readout` — **the landing**: composed with the compiled Γℝ-chart display,
  `mellin (θ_μ(θ̄_f − ‖f‖²)) s = 2^{−k} · Γℝ(s)Γℝ(s+1)Γℝ(s+k−1)Γℝ(s+k) · L(sym2Bank, s)`
  — the peeled Rankin readout of the carrier profile IS the chart-completed L-series
  of the bank whose local factors are the literal Sym²-Satake traces.

Everything derived here is unconditional given the structure; the structure's fields
are the entire arithmetic input.
-/

open ArithmeticFunction LSeries UpperHalfPlane Complex Finset
open scoped LSeries.notation MatrixGroups Real ArithmeticFunction.Moebius
  ArithmeticFunction.zeta

namespace CriticalLinePhasor.Sym2Wire

open CriticalLinePhasor.Sym2Identification
open CriticalLinePhasor.HeckeSupBound
open CriticalLinePhasor.Unfolding
open CriticalLinePhasor.Sym2Registration

variable {k : ℤ}

/-! ## The typed input: the classical Hecke eigenform package -/

/-- **M1's classical input, typed.**  The level-one Hecke eigenform package for `f`:
normalized first coefficient, coprime multiplicativity, the prime-power recursion with
the weight-`k` scale, and reality of the coefficients.  Classical Hecke theory; not in
Mathlib (no Hecke operators are formalized there), hence a structure, not a theorem. -/
structure HeckeEigenData (f : CuspForm 𝒮ℒ k) : Type where
  one : (qExpansion 1 f).coeff 1 = 1
  coprime_mul : ∀ m n : ℕ, Nat.Coprime m n →
    (qExpansion 1 f).coeff (m * n) =
      (qExpansion 1 f).coeff m * (qExpansion 1 f).coeff n
  prime_rec : ∀ p : ℕ, p.Prime → ∀ j : ℕ,
    (qExpansion 1 f).coeff (p ^ (j + 2)) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff (p ^ (j + 1)) -
        (p : ℂ) ^ ((k : ℂ) - 1) * (qExpansion 1 f).coeff (p ^ j)
  conj_eq : ∀ n : ℕ,
    (starRingEnd ℂ) ((qExpansion 1 f).coeff n) = (qExpansion 1 f).coeff n

variable {f : CuspForm 𝒮ℒ k}

/-! ## The prime scale and the Satake lift -/

/-- The prime normalization scale `ν_p = p^{(k−1)/2}`, as a (real, positive) complex
number. -/
noncomputable def primeScale (k : ℤ) (p : ℕ) : ℂ :=
  (((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ)

theorem primeScale_ne_zero {p : ℕ} (hp : p.Prime) : primeScale k p ≠ 0 := by
  unfold primeScale
  exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _).ne'

theorem primeScale_conj (p : ℕ) :
    (starRingEnd ℂ) (primeScale k p) = primeScale k p :=
  Complex.conj_ofReal _

/-- The square of the prime scale is the recursion weight: `ν_p² = p^{k−1}`. -/
theorem primeScale_sq {p : ℕ} (hp : p.Prime) :
    primeScale k p ^ 2 = (p : ℂ) ^ ((k : ℂ) - 1) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  unfold primeScale
  rw [← Complex.ofReal_pow]
  rw [show ((p : ℝ) ^ (((k : ℝ) - 1) / 2)) ^ 2
      = (p : ℝ) ^ ((k : ℝ) - 1) from by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (((k : ℝ) - 1) / 2)) 2,
      ← Real.rpow_mul hppos.le]
    norm_num]
  rw [Complex.ofReal_cpow hppos.le]
  push_cast
  rfl

/-- The seed clock at level one: `U_1 = α + α⁻¹`. -/
theorem seedCoeff_one (α : ℂ) : seedCoeff α 1 = α + α⁻¹ := by
  unfold seedCoeff
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [zpow_neg]

/-- Every complex number is `α + α⁻¹` for some nonzero `α` — the Satake quadratic,
solved in `ℂ`. -/
theorem exists_satake (c : ℂ) : ∃ α : ℂ, α ≠ 0 ∧ α + α⁻¹ = c := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (c ^ 2 - 4) (n := 2) (by norm_num)
  have hprod : (c + w) / 2 * ((c - w) / 2) = 1 := by
    field_simp
    linear_combination -hw
  have hne : (c + w) / 2 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact zero_ne_one hprod
  refine ⟨(c + w) / 2, hne, ?_⟩
  rw [inv_eq_of_mul_eq_one_right hprod]
  ring

/-- **The Satake lift at a prime**: a nonzero `α` with
`a_{p^j} = ν_p^j · U_j(α)` for every `j` — the two-term Hecke recursion and the
Chebyshev recursion agree from matching seeds. -/
theorem HeckeEigenData.exists_prime_satake (H : HeckeEigenData f) {p : ℕ}
    (hp : p.Prime) :
    ∃ α : ℂ, α ≠ 0 ∧ ∀ j : ℕ,
      (qExpansion 1 f).coeff (p ^ j) = primeScale k p ^ j * seedCoeff α j := by
  obtain ⟨α, hα0, hαc⟩ :=
    exists_satake ((qExpansion 1 f).coeff p / primeScale k p)
  have hν := primeScale_ne_zero (k := k) hp
  refine ⟨α, hα0, ?_⟩
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => simp [H.one]
    | 1 =>
      rw [seedCoeff_one, hαc, pow_one]
      field_simp
    | (j + 2) =>
      have ih1 := ih (j + 1) (by omega)
      have ih0 := ih j (by omega)
      have hp1 : (qExpansion 1 f).coeff p = primeScale k p * (α + α⁻¹) := by
        have := ih 1 (by omega)
        rw [pow_one] at this
        rw [this, seedCoeff_one, pow_one]
      rw [H.prime_rec p hp j, ih1, ih0, hp1, ← primeScale_sq (k := k) hp,
        seedCoeff_rec α hα0 j]
      ring

/-- A chosen Satake parameter at each prime. -/
noncomputable def HeckeEigenData.satake (H : HeckeEigenData f) {p : ℕ}
    (hp : p.Prime) : ℂ :=
  (H.exists_prime_satake hp).choose

theorem HeckeEigenData.satake_ne_zero (H : HeckeEigenData f) {p : ℕ}
    (hp : p.Prime) : H.satake hp ≠ 0 :=
  (H.exists_prime_satake hp).choose_spec.1

/-- The coefficients at prime powers through the lift. -/
theorem HeckeEigenData.coeff_prime_pow (H : HeckeEigenData f) {p : ℕ}
    (hp : p.Prime) (j : ℕ) :
    (qExpansion 1 f).coeff (p ^ j) =
      primeScale k p ^ j * seedCoeff (H.satake hp) j :=
  (H.exists_prime_satake hp).choose_spec.2 j

/-- The lifted seed clock is real: `conj U_j(α_p) = U_j(α_p)`. -/
theorem HeckeEigenData.seedCoeff_conj (H : HeckeEigenData f) {p : ℕ}
    (hp : p.Prime) (j : ℕ) :
    (starRingEnd ℂ) (seedCoeff (H.satake hp) j) = seedCoeff (H.satake hp) j := by
  have hν : primeScale k p ^ j ≠ 0 := pow_ne_zero _ (primeScale_ne_zero hp)
  have hU : seedCoeff (H.satake hp) j =
      (qExpansion 1 f).coeff (p ^ j) / primeScale k p ^ j := by
    rw [H.coeff_prime_pow hp j]
    field_simp
  rw [hU, map_div₀, H.conj_eq, map_pow, primeScale_conj]

/-! ## The Rankin square and its Möbius peel at prime powers -/

/-- The normalized Rankin square at prime powers is the squared seed clock:
`b_{p^j} = U_j(α_p)²`. -/
theorem rankinSquareNorm_prime_pow (H : HeckeEigenData f) {p : ℕ}
    (hp : p.Prime) (j : ℕ) :
    rankinSquareNorm f (p ^ j) = seedCoeff (H.satake hp) j ^ 2 := by
  have hpj : (p : ℕ) ^ j ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hcoe : rankinSquareNorm f (p ^ j) =
      ((‖(qExpansion 1 f).coeff (p ^ j)‖ ^ 2 /
        ((p ^ j : ℕ) : ℝ) ^ ((k : ℝ) - 1) : ℝ) : ℂ) := by
    rw [rankinSquareNorm, toArithmeticFunction]
    simp only [ArithmeticFunction.coe_mk, if_neg hpj]
  -- numerator: ‖a‖² = a·conj a = ν^{2j}·U²
  have hnum : ((‖(qExpansion 1 f).coeff (p ^ j)‖ ^ 2 : ℝ) : ℂ) =
      primeScale k p ^ (2 * j) * seedCoeff (H.satake hp) j ^ 2 := by
    have h1 : ((‖(qExpansion 1 f).coeff (p ^ j)‖ ^ 2 : ℝ) : ℂ) =
        (qExpansion 1 f).coeff (p ^ j) *
          (starRingEnd ℂ) ((qExpansion 1 f).coeff (p ^ j)) := by
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq]
    rw [h1, H.coeff_prime_pow hp j, map_mul, map_pow, primeScale_conj,
      H.seedCoeff_conj hp j]
    ring
  -- denominator: (p^j)^{k−1} = ν^{2j}
  have hden : ((((p ^ j : ℕ) : ℝ) ^ ((k : ℝ) - 1) : ℝ) : ℂ) =
      primeScale k p ^ (2 * j) := by
    unfold primeScale
    rw [← Complex.ofReal_pow]
    congr 1
    rw [show (((p ^ j : ℕ) : ℝ)) = (p : ℝ) ^ (j : ℕ) from by push_cast; rfl,
      ← Real.rpow_natCast ((p : ℝ)) j, ← Real.rpow_mul hppos.le,
      ← Real.rpow_natCast ((p : ℝ) ^ (((k : ℝ) - 1) / 2)) (2 * j),
      ← Real.rpow_mul hppos.le]
    congr 1
    push_cast
    ring
  have hν2j : primeScale k p ^ (2 * j) ≠ 0 :=
    pow_ne_zero _ (primeScale_ne_zero hp)
  rw [hcoe, Complex.ofReal_div, hnum, hden]
  exact mul_div_cancel_left₀ _ hν2j

/-- `b_1 = 1`. -/
theorem rankinSquareNorm_one (H : HeckeEigenData f) :
    rankinSquareNorm f 1 = 1 := by
  have h1 : (1 : ℕ) ≠ 0 := one_ne_zero
  rw [rankinSquareNorm, toArithmeticFunction]
  simp only [ArithmeticFunction.coe_mk, if_neg h1]
  rw [H.one]
  norm_num

/-- **The Möbius peel at prime powers is the compiled local peel**:
`(μ ⋆ b)_{p^j} = peeled α_p j`. -/
theorem muRankin_prime_pow (H : HeckeEigenData f) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((μ : ArithmeticFunction ℂ) * rankinSquareNorm f) (p ^ j) =
      peeled (H.satake hp) j := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (f := fun d e => (μ : ArithmeticFunction ℂ) d * rankinSquareNorm f e),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hdiv : ∀ i ∈ Finset.range (j + 1), (p : ℕ) ^ j / p ^ i = p ^ (j - i) := by
    intro i hi
    have hij : i ≤ j := by
      have := Finset.mem_range.mp hi
      omega
    rw [Nat.pow_div hij hp.pos]
  rw [Finset.sum_congr rfl fun i hi => by rw [hdiv i hi]]
  match j with
  | 0 =>
    rw [Finset.sum_range_one]
    simp only [pow_zero, Nat.sub_zero]
    rw [show ((μ : ArithmeticFunction ℂ) 1) = 1 from by simp,
      rankinSquareNorm_one H, peeled_zero, one_mul]
  | (j + 1) =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hzero : ∀ i ∈ Finset.range j,
        ((μ : ArithmeticFunction ℂ) (p ^ (i + 1 + 1))) *
          rankinSquareNorm f (p ^ (j + 1 - (i + 1 + 1))) = 0 := by
      intro i _
      have hμ0 : ((μ : ArithmeticFunction ℂ) (p ^ (i + 2))) = 0 := by
        rw [show ((μ : ArithmeticFunction ℂ) (p ^ (i + 2)))
            = ((moebius (p ^ (i + 2)) : ℤ) : ℂ) from by simp,
          ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
        simp [show i + 2 ≠ 1 from by omega]
      rw [show i + 1 + 1 = i + 2 from rfl, hμ0, zero_mul]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, zero_add]
    have hμp : ((μ : ArithmeticFunction ℂ) (p ^ (0 + 1))) = -1 := by
      rw [pow_one,
        show ((μ : ArithmeticFunction ℂ) p) = ((moebius p : ℤ) : ℂ) from by simp,
        ArithmeticFunction.moebius_apply_prime hp]
      norm_num
    have hμ0 : ((μ : ArithmeticFunction ℂ) (p ^ 0)) = 1 := by
      norm_num
    rw [show j + 1 - 0 = j + 1 from by omega,
      show j + 1 - (0 + 1) = j from by omega,
      hμp, hμ0, one_mul,
      rankinSquareNorm_prime_pow H hp (j + 1),
      rankinSquareNorm_prime_pow H hp j, peeled_succ]
    ring

/-! ## The square-dilation factor and its `ζ(2s)` readout -/

/-- The square indicator: the arithmetic function of the square-dilation, whose
L-series is `ζ(2s)`. -/
noncomputable def sqIndicator : ArithmeticFunction ℂ :=
  toArithmeticFunction fun n => if IsSquare n then 1 else 0

theorem sqIndicator_apply {n : ℕ} (hn : n ≠ 0) :
    sqIndicator n = if IsSquare n then 1 else 0 := by
  rw [sqIndicator, toArithmeticFunction]
  simp only [ArithmeticFunction.coe_mk, if_neg hn]

/-- At prime powers the square indicator reads the parity of the exponent. -/
theorem sqIndicator_prime_pow {p : ℕ} (hp : p.Prime) (i : ℕ) :
    sqIndicator (p ^ i) = if Even i then 1 else 0 := by
  rw [sqIndicator_apply (pow_ne_zero _ hp.pos.ne')]
  congr 1
  rw [eq_iff_iff]
  constructor
  · rintro ⟨r, hr⟩
    have hrd : r ∣ p ^ i := Dvd.intro_left r hr.symm
    obtain ⟨m, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hrd
    rw [← pow_add] at hr
    exact ⟨m, Nat.pow_right_injective hp.two_le hr⟩
  · rintro ⟨m, rfl⟩
    exact ⟨p ^ m, by rw [← pow_add]⟩

/-- The support of the square-indicator L-series terms lies over the squares. -/
theorem term_sqIndicator_support (s : ℂ) :
    Function.support (fun n => LSeries.term (⇑sqIndicator) s n) ⊆
      Set.range (fun m : ℕ => m ^ 2) := by
  intro n hn
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [LSeries.term_zero] at hn
  · have hsq : IsSquare n := by
      by_contra hcon
      apply hn
      show LSeries.term (⇑sqIndicator) s n = 0
      rw [LSeries.term_of_ne_zero hn0, sqIndicator_apply hn0, if_neg hcon]
      simp
    obtain ⟨r, hr⟩ := hsq
    exact ⟨r, by rw [hr]; ring⟩

/-- The square-indicator term at a square is the zeta term at doubled argument. -/
theorem term_sqIndicator_sq (s : ℂ) (m : ℕ) :
    LSeries.term (⇑sqIndicator) s (m ^ 2) = LSeries.term (↗ζ) (2 * s) m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [LSeries.term_zero]
  · have hm2 : (m : ℕ) ^ 2 ≠ 0 := pow_ne_zero _ hm
    have hmc : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    rw [LSeries.term_of_ne_zero hm2, LSeries.term_of_ne_zero hm,
      sqIndicator_apply hm2, if_pos ⟨m, (sq m).symm ▸ rfl⟩]
    have hζ : ((ζ m : ℕ) : ℂ) = 1 := by
      simp [ArithmeticFunction.zeta_apply, hm]
    rw [hζ]
    congr 1
    -- (m²)^s = m^(2s), positive natural base
    have h2 : ((2 : ℂ)) * s = ((2 : ℕ) : ℂ) * s := by norm_num
    rw [h2, Complex.cpow_nat_mul]
    have hm2' : ((m ^ 2 : ℕ) : ℂ) = ((m : ℝ) : ℂ) * ((m : ℝ) : ℂ) := by push_cast; ring
    rw [hm2', Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg m)]
    push_cast
    ring

/-- **The square-dilation readout**: `L(sqIndicator, s) = ζ(2s)` on `1 < Re(2s)`. -/
theorem LSeries_sqIndicator {s : ℂ} (hs : 1 < (2 * s).re) :
    LSeries (⇑sqIndicator) s = riemannZeta (2 * s) := by
  have hinj : Function.Injective (fun m : ℕ => m ^ 2) :=
    Nat.pow_left_injective (by norm_num)
  rw [← LSeries_zeta_eq_riemannZeta hs]
  unfold LSeries
  rw [← Function.Injective.tsum_eq hinj (term_sqIndicator_support s)]
  exact tsum_congr fun m => term_sqIndicator_sq s m

/-- The square-indicator L-series is summable on `1 < Re(2s)`. -/
theorem sqIndicator_LSeriesSummable {s : ℂ} (hs : 1 < (2 * s).re) :
    LSeriesSummable (⇑sqIndicator) s := by
  have hinj : Function.Injective (fun m : ℕ => m ^ 2) :=
    Nat.pow_left_injective (by norm_num)
  have hzero : ∀ n ∉ Set.range (fun m : ℕ => m ^ 2),
      LSeries.term (⇑sqIndicator) s n = 0 := by
    intro n hn
    by_contra hcon
    exact hn (term_sqIndicator_support s hcon)
  rw [LSeriesSummable, ← Function.Injective.summable_iff hinj hzero]
  have : (fun m : ℕ => LSeries.term (⇑sqIndicator) s (m ^ 2)) =
      fun m : ℕ => LSeries.term (↗ζ) (2 * s) m := by
    funext m
    exact term_sqIndicator_sq s m
  rw [show ((fun n => LSeries.term (⇑sqIndicator) s n) ∘ fun m : ℕ => m ^ 2)
      = fun m : ℕ => LSeries.term (⇑sqIndicator) s (m ^ 2) from rfl, this]
  exact LSeriesSummable_zeta_iff.mpr hs

/-! ## The global Sym² bank and M1's display -/

/-- **The global Sym² bank**: the square-dilation convolution of the Möbius-peeled
Rankin square.  Its local factors are the literal Sym²-Satake traces
(`sym2Bank_prime_pow`), and its L-series is `ζ(2s)·L(μ ⋆ b, s)`
(`sym2_euler_identity`). -/
noncomputable def sym2Bank (f : CuspForm 𝒮ℒ k) : ArithmeticFunction ℂ :=
  sqIndicator * ((μ : ArithmeticFunction ℂ) * rankinSquareNorm f)

/-- **The local factors of the Sym² bank are the Sym²-Satake traces**: at every prime
power, `sym2Bank_{p^j} = h_j(α_p², 1, α_p⁻²)` — Brick 1's local peel-and-redilate
identity (`sym2Coeff_eq_sum_peeled`) assembled through the convolution. -/
theorem sym2Bank_prime_pow (H : HeckeEigenData f) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    sym2Bank f (p ^ j) = Sym2Identification.sym2Coeff (H.satake hp) j := by
  unfold sym2Bank
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (f := fun d e => sqIndicator d *
        ((μ : ArithmeticFunction ℂ) * rankinSquareNorm f) e),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hdiv : ∀ i ∈ Finset.range (j + 1), (p : ℕ) ^ j / p ^ i = p ^ (j - i) := by
    intro i hi
    have hij : i ≤ j := by
      have := Finset.mem_range.mp hi
      omega
    rw [Nat.pow_div hij hp.pos]
  rw [Finset.sum_congr rfl fun i hi => by
    rw [hdiv i hi, sqIndicator_prime_pow hp i, muRankin_prime_pow H hp (j - i)]]
  -- extract the even indices and reindex by halves
  rw [Finset.sum_congr rfl fun i _ => (ite_mul _ _ _ _).trans (by rw [one_mul, zero_mul]),
    ← Finset.sum_filter]
  rw [sym2Coeff_eq_sum_peeled (H.satake hp) (H.satake_ne_zero hp) j]
  refine Finset.sum_nbij' (fun i => i / 2) (fun m => 2 * m) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_range]
    omega
  · intro m hm
    simp only [Finset.mem_range] at hm
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · exact ⟨m, by omega⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨-, m, hm⟩ := hi
    omega
  · intro m _
    omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨-, m, hm⟩ := hi
    congr 1
    omega

/-- **M1's display — the Sym² Euler identity**: on `2 < Re s`,
`ζ(2s) · L(μ ⋆ b, s) = L(sym2Bank, s)`.  This convolution identity is unconditional —
no Hecke input; the arithmetic content of the wire lives entirely in
`sym2Bank_prime_pow`, which identifies the bank's local factors with the literal
Sym²-Satake traces under `HeckeEigenData`. -/
theorem sym2_euler_identity (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    riemannZeta (2 * s) *
        LSeries (⇑((μ : ArithmeticFunction ℂ) * rankinSquareNorm f)) s =
      LSeries (⇑(sym2Bank f)) s := by
  have hs2 : 1 < (2 * s).re := by
    have h2 : (2 * s).re = 2 * s.re := by
      simp [Complex.mul_re]
    rw [h2]
    linarith
  have hμs : LSeriesSummable (⇑(μ : ArithmeticFunction ℂ)) s := by
    have : (⇑(μ : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗μ := by
      funext n
      simp
    rw [this]
    exact LSeriesSummable_moebius_iff.mpr (by linarith)
  have hb : LSeriesSummable (⇑(rankinSquareNorm f)) s :=
    rankinSquareNorm_LSeriesSummable f hk hs
  have hμb : LSeriesSummable (⇑((μ : ArithmeticFunction ℂ) * rankinSquareNorm f)) s := by
    rw [← ArithmeticFunction.coe_mul]
    exact hμs.convolution hb
  have hsq : LSeriesSummable (⇑sqIndicator) s := sqIndicator_LSeriesSummable hs2
  calc riemannZeta (2 * s) *
        LSeries (⇑((μ : ArithmeticFunction ℂ) * rankinSquareNorm f)) s
      = LSeries (⇑sqIndicator) s *
          LSeries (⇑((μ : ArithmeticFunction ℂ) * rankinSquareNorm f)) s := by
        rw [LSeries_sqIndicator hs2]
    _ = LSeries ((⇑sqIndicator) ⍟
          ⇑((μ : ArithmeticFunction ℂ) * rankinSquareNorm f)) s :=
        (LSeries_convolution' hsq hμb).symm
    _ = LSeries (⇑(sym2Bank f)) s := by
        rw [sym2Bank, ArithmeticFunction.coe_mul]

/-- **The landing**: composed with the compiled Γℝ-chart display, the peeled Rankin
readout of the carrier profile IS the chart-completed L-series of the bank —
`mellin (θ_μ(θ̄_f − ‖f‖²)) s = 2^{−k}·Γℝ(s)Γℝ(s+1)Γℝ(s+k−1)Γℝ(s+k)·L(sym2Bank, s)`
on `2 < Re s`.  Unconditional; reading `L(sym2Bank)` as the Sym²-Satake Euler data is
`sym2Bank_prime_pow` under `HeckeEigenData`. -/
theorem sym2_readout (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    mellin (peeledProfile k f) s =
      (2 : ℂ) ^ (-(k : ℂ)) *
        (Gammaℝ s * Gammaℝ (s + 1) * Gammaℝ (s + (k : ℂ) - 1) * Gammaℝ (s + (k : ℂ))) *
        LSeries (⇑(sym2Bank f)) s := by
  rw [peeled_readout_gammaChart f hk hs, ← sym2_euler_identity hk hs]
  ring

end CriticalLinePhasor.Sym2Wire

#print axioms CriticalLinePhasor.Sym2Wire.exists_satake
#print axioms CriticalLinePhasor.Sym2Wire.HeckeEigenData.exists_prime_satake
#print axioms CriticalLinePhasor.Sym2Wire.rankinSquareNorm_prime_pow
#print axioms CriticalLinePhasor.Sym2Wire.muRankin_prime_pow
#print axioms CriticalLinePhasor.Sym2Wire.sqIndicator_prime_pow
#print axioms CriticalLinePhasor.Sym2Wire.LSeries_sqIndicator
#print axioms CriticalLinePhasor.Sym2Wire.sym2Bank_prime_pow
#print axioms CriticalLinePhasor.Sym2Wire.sym2_euler_identity
#print axioms CriticalLinePhasor.Sym2Wire.sym2_readout
