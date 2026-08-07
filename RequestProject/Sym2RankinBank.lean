import RequestProject.Sym2GlobalJoin
import RequestProject.GlobalHelixCPSPolynomialDualPair

/-!
# The rank-4 Rankin bank and its arithmetic Satake pair

The `Sym²` coupling consumes the *unpeeled* Rankin object: the degree-4 Euler datum of
`L(f×f)` in Deligne normalization, whose local roots are `(α_p², 1, α_p⁻², 1)` and whose
coefficients are `c = ζ ⋆ sym2Bank` — the divisor-sum dressing of the `Sym²` bank.  This
file constructs that object on both sides and proves they are the same:

* `rankinWeight` — the rank-4 clock family `(α², 1, α⁻², 1)`;
* `radialLocalEulerCoeff_rankinWeight` — **the partial-sum law**: the fourth weight is `1`,
  so `h_j(α²,1,α⁻²,1) = Σ_{u≤j} h_u(α²,1,α⁻²)`;
* `sym2Coeff_inv` — the `Sym²` trace is inversion-invariant (swap the triangle);
* `rankinBank` / `isMultiplicative_rankinBank` / `rankinBank_prime_pow` — the global bank
  `ζ ⋆ sym2Bank`, multiplicative, with prime-power values the partial sums of the `Sym²`
  traces;
* `norm_le_of_add_inv` / `satake_uniform_bound` — Hecke's coefficient bound pushed through
  the seed relation `α_p + α_p⁻¹ = a_p/p^{(k−1)/2}`: one natural exponent bounds `‖α_p‖²`
  and `‖α_p⁻¹‖²` by `p^E` at every prime;
* `rankinSatakePair` — the `PolynomialSatakeDualPair (Fin 4)` of the Rankin square;
* `rankinPrimalCoeff_eq` / `rankinDualCoeff_eq` — **the coefficient identification**: both
  all-place coefficient banks of the pair are literally `rankinBank ∘ (·+1)`.

With these, the prescribed CPS completion machinery reads the genuine `L(f×f)` Euler
datum — the coefficient half of the r = 2 coupling's identification layer.

No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups Real

namespace CriticalLinePhasor.Sym2Rankin

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.Sym2Wire
open CriticalLinePhasor.Sym2Join
open CriticalLinePhasor.HeckeSupBound
open CriticalLinePhasor.Sym2Identification (sym2Coeff)

variable {k : ℤ} {f : CuspForm 𝒮ℒ k}


/-- The rank-4 Rankin weight family `(α², 1, α⁻², 1)`. -/
noncomputable def rankinWeight (α : ℂ) : Fin 4 → ℂ :=
  ![α ^ (2 : ℤ), 1, α ^ (-2 : ℤ), 1]

theorem rankinWeight_eq_clock (α : ℂ) (i : Fin 3) :
    rankinWeight α i.castSucc = symClockWeight 2 α (i : ℕ) := by
  fin_cases i <;> simp [rankinWeight, symClockWeight]

theorem rankinWeight_last (α : ℂ) : rankinWeight α (Fin.last 3) = 1 := rfl

noncomputable def mk4 (a b c d : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, b, c, d]

@[simp] theorem mk4_0 (a b c d : ℕ) : mk4 a b c d 0 = a := rfl
@[simp] theorem mk4_1 (a b c d : ℕ) : mk4 a b c d 1 = b := rfl
@[simp] theorem mk4_2 (a b c d : ℕ) : mk4 a b c d 2 = c := rfl
@[simp] theorem mk4_3 (a b c d : ℕ) : mk4 a b c d 3 = d := rfl

/-- **The rank-4 local coefficient is the partial sum of the rank-3 ones**: the fourth
weight is `1`, so `h_j(α²,1,α⁻²,1) = Σ_{u ≤ j} h_u(α²,1,α⁻²)`. -/
theorem radialLocalEulerCoeff_rankinWeight (α : ℂ) (j : ℕ) :
    radialLocalEulerCoeff (rankinWeight α) j
      = ∑ u ∈ range (j + 1),
          radialLocalEulerCoeff (fun i : Fin 3 => symClockWeight 2 α (i : ℕ)) u := by
  unfold radialLocalEulerCoeff
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun l => (⟨l 0 + l 1 + l 2,
      mk3 (l 0) (l 1) (l 2)⟩ : Σ _ : ℕ, Fin 3 →₀ ℕ))
    (fun q => mk4 (q.2 0) (q.2 1) (q.2 2) (j - q.1)) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_finsuppAntidiag] at hl
    have h : l 0 + l 1 + l 2 + l 3 = j := by
      simpa [Fin.sum_univ_four] using hl.1
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_finsuppAntidiag]
    refine ⟨by omega, ?_, by simp⟩
    simp [Fin.sum_univ_three, mk3]
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_finsuppAntidiag] at hq
    have h : q.2 0 + q.2 1 + q.2 2 = q.1 := by
      have := hq.2.1
      simpa [Fin.sum_univ_three] using this
    simp only [Finset.mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    simp only [Fin.sum_univ_four, mk4_0, mk4_1, mk4_2, mk4_3]
    omega
  · intro l hl
    simp only [Finset.mem_finsuppAntidiag] at hl
    have h : l 0 + l 1 + l 2 + l 3 = j := by
      simpa [Fin.sum_univ_four] using hl.1
    ext i
    fin_cases i
    · simp
    · simp
    · simp
    · simp; omega
  · intro q hq
    obtain ⟨u, l'⟩ := q
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_finsuppAntidiag] at hq
    have h : l' 0 + l' 1 + l' 2 = u := by
      have := hq.2.1
      simpa [Fin.sum_univ_three] using this
    refine Sigma.ext (by simpa using h) (heq_of_eq ?_)
    ext i
    fin_cases i <;> simp
  · intro l _
    rw [Fin.prod_univ_four, Fin.prod_univ_three]
    show rankinWeight α 0 ^ l 0 * rankinWeight α 1 ^ l 1 * rankinWeight α 2 ^ l 2 *
        rankinWeight α 3 ^ l 3 = _
    have h0 : rankinWeight α 0 = symClockWeight 2 α 0 := rankinWeight_eq_clock α 0
    have h1 : rankinWeight α 1 = symClockWeight 2 α 1 := rankinWeight_eq_clock α 1
    have h2 : rankinWeight α 2 = symClockWeight 2 α 2 := rankinWeight_eq_clock α 2
    have h3 : rankinWeight α 3 = 1 := rfl
    rw [h0, h1, h2, h3, one_pow, mul_one]
    simp [mk3]



/-- The Sym² local trace is inversion-invariant: `sym2Coeff α⁻¹ = sym2Coeff α`. -/
theorem sym2Coeff_inv (α : ℂ) (j : ℕ) : sym2Coeff α⁻¹ j = sym2Coeff α j := by
  unfold sym2Coeff
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun q => (⟨q.2, q.1⟩ : Σ _ : ℕ, ℕ))
    (fun q => (⟨q.2, q.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_range] at hq ⊢
    omega
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_range] at hq ⊢
    omega
  · intro q _
    rfl
  · intro q _
    rfl
  · intro q _
    rw [inv_zpow, ← zpow_neg]
    congr 1
    ring

/-- **The rank-4 Rankin bank**: the divisor-sum dressing of the Sym² bank,
`c = ζ ⋆ sym2Bank` — the coefficients of `L(f×f)` in Deligne normalization. -/
noncomputable def rankinBank (f : CuspForm 𝒮ℒ k) : ArithmeticFunction ℂ :=
  ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) * sym2Bank f

theorem isMultiplicative_rankinBank (H : HeckeEigenData f) :
    (rankinBank f).IsMultiplicative :=
  by
  unfold rankinBank
  exact isMultiplicative_zeta.natCast.mul (isMultiplicative_sym2Bank H)

/-- The Rankin bank at prime powers is the partial sum of the Sym² traces. -/
theorem rankinBank_prime_pow (H : HeckeEigenData f) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    rankinBank f (p ^ j) = ∑ u ∈ range (j + 1), sym2Coeff (H.satake hp) u := by
  unfold rankinBank
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun d e => ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) d * sym2Bank f e),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hdiv : ∀ i ∈ Finset.range (j + 1), (p : ℕ) ^ j / p ^ i = p ^ (j - i) := by
    intro i hi
    exact Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos
  rw [Finset.sum_congr rfl fun i hi => by
    rw [hdiv i hi, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
      if_neg (pow_ne_zero _ hp.pos.ne'), Nat.cast_one, one_mul,
      sym2Bank_prime_pow H hp (j - i)]]
  refine Finset.sum_nbij' (fun i => j - i) (fun u => j - u) ?_ ?_ ?_ ?_ ?_ <;>
    intro i hi <;> simp only [Finset.mem_range] at hi ⊢ <;> omega



/-- From `α + α⁻¹ = t`, both `‖α‖` and `‖α⁻¹‖` are at most `‖t‖ + 1`. -/
theorem norm_le_of_add_inv (α t : ℂ) (h : α + α⁻¹ = t) :
    ‖α‖ ≤ ‖t‖ + 1 ∧ ‖α⁻¹‖ ≤ ‖t‖ + 1 := by
  constructor
  · rcases le_total ‖α‖ 1 with h1 | h1
    · linarith [norm_nonneg t]
    · have hinv : ‖α⁻¹‖ ≤ 1 := by
        rw [norm_inv]
        exact inv_le_one_of_one_le₀ h1
      have heq : α = t - α⁻¹ := by rw [← h]; ring
      calc ‖α‖ = ‖t - α⁻¹‖ := by rw [← heq]
        _ ≤ ‖t‖ + ‖α⁻¹‖ := norm_sub_le _ _
        _ ≤ ‖t‖ + 1 := by linarith
  · rcases le_total ‖α⁻¹‖ 1 with h1 | h1
    · linarith [norm_nonneg t]
    · have hinv : ‖α‖ ≤ 1 := by
        rw [show α = (α⁻¹)⁻¹ from (inv_inv α).symm, norm_inv]
        exact inv_le_one_of_one_le₀ h1
      have heq : α⁻¹ = t - α := by rw [← h]; ring
      calc ‖α⁻¹‖ = ‖t - α‖ := by rw [← heq]
        _ ≤ ‖t‖ + ‖α‖ := norm_sub_le _ _
        _ ≤ ‖t‖ + 1 := by linarith

/-- **The Satake parameter is polynomially bounded, uniformly in the prime**: one natural
exponent `E` bounds `‖α_p‖²` and `‖α_p⁻¹‖²` by `p^E` at every prime — Hecke's coefficient
bound pushed through the seed relation `α_p + α_p⁻¹ = a_p/p^{(k−1)/2}`. -/
theorem satake_uniform_bound (H : HeckeEigenData f) :
    ∃ E : ℕ, ∀ (p : Nat.Primes),
      ‖H.satake p.2‖ ^ 2 ≤ (p.1 : ℝ) ^ E ∧ ‖(H.satake p.2)⁻¹‖ ^ 2 ≤ (p.1 : ℝ) ^ E := by
  obtain ⟨M, hM0, hM⟩ := hecke_coeff_sq_bound f
  set B : ℝ := (Real.sqrt M + 2) ^ 2 with hB
  obtain ⟨E0, hE0⟩ := pow_unbounded_of_one_lt B one_lt_two
  refine ⟨E0 + 1, fun p => ?_⟩
  have hp : p.1.Prime := p.2
  have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p.1 : ℝ) := by linarith
  have hν : primeScale k p.1 ≠ 0 := primeScale_ne_zero hp
  have hseed := H.coeff_prime_pow hp 1
  rw [pow_one, pow_one, seedCoeff_one] at hseed
  have htval : H.satake p.2 + (H.satake p.2)⁻¹ =
      (qExpansion 1 f).coeff p.1 / primeScale k p.1 := by
    rw [hseed, mul_div_cancel_left₀ _ hν]
  have hcoeff : ‖(qExpansion 1 f).coeff p.1‖ ^ 2 ≤ M * (p.1 : ℝ) ^ k :=
    hM p.1 hp.one_lt.le
  have hscale : ‖primeScale k p.1‖ = (p.1 : ℝ) ^ (((k : ℝ) - 1) / 2) := by
    unfold primeScale
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hppos.le _)]
  have hden : ((p.1 : ℝ) ^ (((k : ℝ) - 1) / 2)) ^ (2 : ℕ) = (p.1 : ℝ) ^ ((k : ℝ) - 1) := by
    rw [← Real.rpow_natCast ((p.1 : ℝ) ^ (((k : ℝ) - 1) / 2)) 2,
      ← Real.rpow_mul hppos.le]
    norm_num
  have hzk : (p.1 : ℝ) ^ (k : ℤ) = (p.1 : ℝ) * (p.1 : ℝ) ^ ((k : ℝ) - 1) := by
    rw [show (p.1 : ℝ) * (p.1 : ℝ) ^ ((k : ℝ) - 1)
        = (p.1 : ℝ) ^ (1 : ℝ) * (p.1 : ℝ) ^ ((k : ℝ) - 1) by rw [Real.rpow_one],
      ← Real.rpow_add hppos, ← Real.rpow_intCast (p.1 : ℝ) k]
    congr 1
    ring
  have htnorm : ‖(qExpansion 1 f).coeff p.1 / primeScale k p.1‖ ^ 2 ≤ M * (p.1 : ℝ) := by
    rw [norm_div, div_pow, hscale, hden, div_le_iff₀ (Real.rpow_pos_of_pos hppos _)]
    calc ‖(qExpansion 1 f).coeff p.1‖ ^ 2 ≤ M * (p.1 : ℝ) ^ (k : ℤ) := hcoeff
      _ = M * (p.1 : ℝ) * (p.1 : ℝ) ^ ((k : ℝ) - 1) := by rw [hzk]; ring
  have httrace : ‖(qExpansion 1 f).coeff p.1 / primeScale k p.1‖ ≤
      Real.sqrt M * Real.sqrt (p.1 : ℝ) + 1 := by
    have h1 : ‖(qExpansion 1 f).coeff p.1 / primeScale k p.1‖ =
        Real.sqrt (‖(qExpansion 1 f).coeff p.1 / primeScale k p.1‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h1]
    calc Real.sqrt (‖(qExpansion 1 f).coeff p.1 / primeScale k p.1‖ ^ 2)
        ≤ Real.sqrt (M * (p.1 : ℝ)) := Real.sqrt_le_sqrt htnorm
      _ = Real.sqrt M * Real.sqrt (p.1 : ℝ) := Real.sqrt_mul hM0 _
      _ ≤ Real.sqrt M * Real.sqrt (p.1 : ℝ) + 1 := by linarith
  have hsqp1 : (1 : ℝ) ≤ Real.sqrt (p.1 : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  obtain ⟨hα, hαinv⟩ := norm_le_of_add_inv (H.satake p.2) _ htval
  have habs : ∀ y : ℝ, 0 ≤ y → y ≤ Real.sqrt M * Real.sqrt (p.1 : ℝ) + 1 + 1 →
      y ^ 2 ≤ B * (p.1 : ℝ) := by
    intro y hy0 hy
    have hy' : y ≤ (Real.sqrt M + 2) * Real.sqrt (p.1 : ℝ) := by
      calc y ≤ Real.sqrt M * Real.sqrt (p.1 : ℝ) + 2 := by linarith
        _ ≤ (Real.sqrt M + 2) * Real.sqrt (p.1 : ℝ) := by
            nlinarith [Real.sqrt_nonneg M]
    calc y ^ 2 ≤ ((Real.sqrt M + 2) * Real.sqrt (p.1 : ℝ)) ^ 2 := by
          nlinarith [Real.sqrt_nonneg M, Real.sqrt_nonneg (p.1 : ℝ)]
      _ = B * (p.1 : ℝ) := by
          rw [hB, mul_pow, Real.sq_sqrt hppos.le]
  have hBp : B * (p.1 : ℝ) ≤ (p.1 : ℝ) ^ (E0 + 1) := by
    calc B * (p.1 : ℝ) ≤ (2 : ℝ) ^ E0 * (p.1 : ℝ) :=
          mul_le_mul_of_nonneg_right hE0.le hppos.le
      _ ≤ (p.1 : ℝ) ^ E0 * (p.1 : ℝ) := by
          gcongr
      _ = (p.1 : ℝ) ^ (E0 + 1) := by ring
  refine ⟨le_trans (habs _ (norm_nonneg _) (by linarith)) hBp,
    le_trans (habs _ (norm_nonneg _) (by linarith)) hBp⟩




/-- The exponent of the rank-4 pair, chosen once from the uniform Satake bound. -/
noncomputable def rankinExponent (H : HeckeEigenData f) : ℕ :=
  (satake_uniform_bound H).choose

theorem rankinExponent_spec (H : HeckeEigenData f) (p : Nat.Primes) :
    ‖H.satake p.2‖ ^ 2 ≤ (p.1 : ℝ) ^ rankinExponent H ∧
      ‖(H.satake p.2)⁻¹‖ ^ 2 ≤ (p.1 : ℝ) ^ rankinExponent H :=
  (satake_uniform_bound H).choose_spec p

/-- **The rank-4 arithmetic Satake pair of the Rankin square**: weights `(α², 1, α⁻², 1)`
per prime, dual the pointwise inverse, polynomial bounds from Hecke's coefficient bound. -/
noncomputable def rankinSatakePair (H : HeckeEigenData f) :
    PolynomialSatakeDualPair (Fin 4) where
  primal := fun p => rankinWeight (H.satake p.2)
  dual := fun p i => (rankinWeight (H.satake p.2) i)⁻¹
  primalExponent := rankinExponent H
  dualExponent := rankinExponent H
  primal_ne_zero := by
    intro p i
    fin_cases i
    · exact zpow_ne_zero _ (H.satake_ne_zero p.2)
    · exact one_ne_zero
    · exact zpow_ne_zero _ (H.satake_ne_zero p.2)
    · exact one_ne_zero
  dual_eq_inv := fun p i => rfl
  primal_bound := by
    intro p i
    have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by
      exact_mod_cast p.2.one_lt.le
    have h1E : (1 : ℝ) ≤ (p.1 : ℝ) ^ rankinExponent H := one_le_pow₀ hp1
    fin_cases i
    · show ‖H.satake p.2 ^ (2 : ℤ)‖ ≤ _
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, norm_pow]
      exact (rankinExponent_spec H p).1
    · simpa [rankinWeight] using h1E
    · show ‖H.satake p.2 ^ (-2 : ℤ)‖ ≤ _
      rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, ← inv_pow,
        norm_pow]
      exact (rankinExponent_spec H p).2
    · simpa [rankinWeight] using h1E
  dual_bound := by
    intro p i
    have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by
      exact_mod_cast p.2.one_lt.le
    have h1E : (1 : ℝ) ≤ (p.1 : ℝ) ^ rankinExponent H := one_le_pow₀ hp1
    fin_cases i
    · show ‖(H.satake p.2 ^ (2 : ℤ))⁻¹‖ ≤ _
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ← inv_pow, norm_pow]
      exact (rankinExponent_spec H p).2
    · simpa [rankinWeight] using h1E
    · show ‖(H.satake p.2 ^ (-2 : ℤ))⁻¹‖ ≤ _
      rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) from rfl, zpow_neg, inv_inv, zpow_natCast,
        norm_pow]
      exact (rankinExponent_spec H p).1
    · simpa [rankinWeight] using h1E

/-- The inverse of the rank-4 weight family is the family at the inverse parameter. -/
theorem rankinWeight_inv (α : ℂ) (i : Fin 4) :
    (rankinWeight α i)⁻¹ = rankinWeight α⁻¹ i := by
  fin_cases i
  · show (α ^ (2 : ℤ))⁻¹ = (α⁻¹) ^ (2 : ℤ)
    rw [inv_zpow]
  · simp [rankinWeight]
  · show (α ^ (-2 : ℤ))⁻¹ = (α⁻¹) ^ (-2 : ℤ)
    rw [inv_zpow]
  · simp [rankinWeight]

/-- **The primal coefficients of the rank-4 pair are the Rankin bank**, up to the
`n ↔ n+1` index convention. -/
theorem rankinPrimalCoeff_eq (H : HeckeEigenData f) (n : ℕ) :
    cpsPolynomialPrimalCoeff (rankinSatakePair H) n = rankinBank f (n + 1) := by
  show radialGlobalSatakeCoeff (rankinSatakePair H).primal n = _
  rw [(isMultiplicative_rankinBank H).multiplicative_factorization _ (Nat.succ_ne_zero n),
    Finsupp.prod, Nat.support_factorization]
  unfold radialGlobalSatakeCoeff
  rw [← Finset.prod_coe_sort ((n + 1).primeFactors)
    (fun p => rankinBank f (p ^ ((n + 1).factorization p)))]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  show radialLocalEulerCoeff (rankinWeight (H.satake hp)) _ = _
  rw [radialLocalEulerCoeff_rankinWeight, rankinBank_prime_pow H hp]
  exact Finset.sum_congr rfl fun u _ =>
    radialLocalEulerCoeff_symClock_eq_sym2Coeff _ (H.satake_ne_zero hp) u

/-- **The dual coefficients coincide with the primal ones**: the inverse weight multiset
is the multiset at the inverse parameter, and the Sym² trace is inversion-invariant. -/
theorem rankinDualCoeff_eq (H : HeckeEigenData f) (n : ℕ) :
    cpsPolynomialDualCoeff (rankinSatakePair H) n = rankinBank f (n + 1) := by
  show radialGlobalSatakeCoeff (rankinSatakePair H).dual n = _
  rw [(isMultiplicative_rankinBank H).multiplicative_factorization _ (Nat.succ_ne_zero n),
    Finsupp.prod, Nat.support_factorization]
  unfold radialGlobalSatakeCoeff
  rw [← Finset.prod_coe_sort ((n + 1).primeFactors)
    (fun p => rankinBank f (p ^ ((n + 1).factorization p)))]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hα : H.satake hp ≠ 0 := H.satake_ne_zero hp
  show radialLocalEulerCoeff (fun i => (rankinWeight (H.satake hp) i)⁻¹) _ = _
  rw [show (fun i => (rankinWeight (H.satake hp) i)⁻¹)
      = rankinWeight (H.satake hp)⁻¹ from funext (rankinWeight_inv _),
    radialLocalEulerCoeff_rankinWeight, rankinBank_prime_pow H hp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [radialLocalEulerCoeff_symClock_eq_sym2Coeff _ (inv_ne_zero hα) u, sym2Coeff_inv]

end CriticalLinePhasor.Sym2Rankin

#print axioms CriticalLinePhasor.Sym2Rankin.radialLocalEulerCoeff_rankinWeight
#print axioms CriticalLinePhasor.Sym2Rankin.sym2Coeff_inv
#print axioms CriticalLinePhasor.Sym2Rankin.rankinBank_prime_pow
#print axioms CriticalLinePhasor.Sym2Rankin.satake_uniform_bound
#print axioms CriticalLinePhasor.Sym2Rankin.rankinSatakePair
#print axioms CriticalLinePhasor.Sym2Rankin.rankinPrimalCoeff_eq
#print axioms CriticalLinePhasor.Sym2Rankin.rankinDualCoeff_eq
