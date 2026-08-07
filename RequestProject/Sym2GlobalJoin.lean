import RequestProject.SymrBankAllRanks
import RequestProject.Sym2LocalJoin

/-!
# The global join: the CPS coefficient bank is the `Sym^r` bank

`Sym2LocalJoin` matched the two halves of the corpus one prime at a time.  This file
matches them globally, and the first theorem does it at **every rank at once**.

* `radialGlobal_eq_symrBank` — **rank-uniform.**  The CPS all-place coefficient
  `radialGlobalSatakeCoeff` evaluated on the rank-`r` clock weights of the lifted seed is
  the `Sym^r` bank, shifted by the index convention:
  `radialGlobalSatakeCoeff (p ↦ symClockWeight r α_p) n = symrBank H r (n+1)`.
  Both sides are the same product over `(n+1).primeFactors`; the proof is the
  `Finset` coercion and proof irrelevance on the primality certificate.  No arithmetic
  input — this is a statement about how the two files index the same object.

The rank-2 layer, where the corpus's independently-built `Sym²` bank lives:

* `isSquare_mul_iff_of_coprime` — coprime factors of a square are squares;
* `isMultiplicative_sqIndicator`, `isMultiplicative_rankinSquareNorm`,
  `isMultiplicative_sym2Bank` — the three convolution factors of
  `sym2Bank = sqIndicator ⋆ μ ⋆ b` and their product;
* `symrBank_two_eq_sym2Bank` — **the rank-2 bank identification**,
  `symrBank H 2 = sym2Bank f`.  Two multiplicative functions agreeing on prime powers
  agree; the prime-power agreement is `Sym2LocalJoin`;
* `radialGlobal_eq_sym2Bank` — the composite: the CPS coefficient sequence read at the
  `Sym²` clock weights is exactly the bank whose completed readout
  `Sym2GammaChart.sym2_readout_gammaC` computes.

This is the identification `SymrBankAllRanks`'s module docstring names as its one
deferred item.  With it, the Rankin readout of the carrier profile and the prescribed
CPS completion are readouts of the *same* coefficient sequence, which is what the
coupling machinery consumes.

No `axiom`, no `sorry`.
-/

open ArithmeticFunction Finset Complex UpperHalfPlane
open scoped MatrixGroups

namespace CriticalLinePhasor.Sym2Join

open CriticalLinePhasor.SymrBank CriticalLinePhasor.Sym2Wire
open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.Unfolding

variable {k : ℤ} {f : CuspForm 𝒮ℒ k}

/-! ## The rank-uniform layer -/

/-- **The CPS coefficient bank is the `Sym^r` bank, at every rank.**  The all-place
coefficient `radialGlobalSatakeCoeff` on the rank-`r` clock weights of the lifted seed is
`symrBank H r`, up to the `n ↔ n+1` index convention of the coefficient arithmetic.

Both sides are `∏_{p ∣ n+1} h_{v_p(n+1)}(α_p^{r}, …, α_p^{-r})`; the only content is the
`Finset`-coercion of the prime-factor product and proof irrelevance on the primality
certificate carried by `Nat.Primes`.  No arithmetic hypothesis beyond the seed structure
that produces the Satake parameters. -/
theorem radialGlobal_eq_symrBank (H : HeckeEigenData f) (r n : ℕ) :
    radialGlobalSatakeCoeff
      (fun p : Nat.Primes => fun i : Fin (r + 1) =>
        symClockWeight r (H.satake p.2) (i : ℕ)) n
      = symrBank H r (n + 1) := by
  rw [symrBank_apply H r (Nat.succ_ne_zero n)]
  unfold radialGlobalSatakeCoeff
  rw [← Finset.prod_coe_sort (n + 1).primeFactors
    (fun p => if hp : p.Prime then
      symrCoeff r (H.satake hp) ((n + 1).factorization p) else 1)]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [dif_pos (Nat.prime_of_mem_primeFactors p.2)]
  rfl

/-! ## Multiplicativity of the corpus's independently-built `Sym²` bank -/

/-- A product of coprime naturals is a square exactly when both factors are. -/
theorem isSquare_mul_iff_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    IsSquare (m * n) ↔ (IsSquare m ∧ IsSquare n) := by
  constructor
  · rintro ⟨c, hc⟩
    have hc2 : m * n = c ^ 2 := by rw [hc]; ring
    have hu : IsUnit (gcd m n) := Nat.isUnit_iff.mpr h
    have hu' : IsUnit (gcd n m) := by rwa [gcd_comm]
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hu hc2
    obtain ⟨e, he⟩ := exists_eq_pow_of_mul_eq_pow hu' (by rw [mul_comm]; exact hc2)
    exact ⟨⟨d, by rw [hd]; ring⟩, ⟨e, by rw [he]; ring⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a * b, by rw [ha, hb]; ring⟩

/-- The square indicator is multiplicative. -/
theorem isMultiplicative_sqIndicator : (sqIndicator).IsMultiplicative := by
  constructor
  · rw [sqIndicator_apply one_ne_zero]; simp
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · have : n = 1 := by rwa [Nat.coprime_zero_left] at hmn
      subst this; simp
    rcases eq_or_ne n 0 with rfl | hn
    · have : m = 1 := by rwa [Nat.coprime_zero_right] at hmn
      subst this; simp
    rw [sqIndicator_apply (mul_ne_zero hm hn), sqIndicator_apply hm,
      sqIndicator_apply hn]
    by_cases h1 : IsSquare m <;> by_cases h2 : IsSquare n <;>
      simp [isSquare_mul_iff_of_coprime hmn, h1, h2]

theorem rankinSquareNorm_apply' {n : ℕ} (hn : n ≠ 0) :
    rankinSquareNorm f n =
      ((‖(qExpansion 1 f).coeff n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) - 1) : ℝ) : ℂ) := by
  rw [rankinSquareNorm, toArithmeticFunction]
  simp only [ArithmeticFunction.coe_mk, if_neg hn]

/-- The Deligne-normalized Rankin square `b_n = ‖a_n‖²/n^{k−1}` is multiplicative —
coprime Hecke multiplicativity through the norm and the normalization. -/
theorem isMultiplicative_rankinSquareNorm (H : HeckeEigenData f) :
    (rankinSquareNorm f).IsMultiplicative := by
  constructor
  · rw [rankinSquareNorm_apply' one_ne_zero, H.one]; norm_num
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · have : n = 1 := by rwa [Nat.coprime_zero_left] at hmn
      subst this; simp
    rcases eq_or_ne n 0 with rfl | hn
    · have : m = 1 := by rwa [Nat.coprime_zero_right] at hmn
      subst this; simp
    have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [rankinSquareNorm_apply' (mul_ne_zero hm hn), rankinSquareNorm_apply' hm,
      rankinSquareNorm_apply' hn, H.coprime_mul m n hmn]
    have hsplit : (((m * n : ℕ) : ℝ) ^ ((k : ℝ) - 1) : ℝ) =
        ((m : ℝ) ^ ((k : ℝ) - 1)) * ((n : ℝ) ^ ((k : ℝ) - 1)) := by
      rw [show (((m * n : ℕ) : ℝ)) = (m : ℝ) * (n : ℝ) from by push_cast; rfl]
      exact Real.mul_rpow hmr.le hnr.le
    rw [hsplit, norm_mul, mul_pow]
    push_cast
    ring

/-- The `Sym²` bank is multiplicative: a Dirichlet product of three multiplicative
factors, `sqIndicator ⋆ μ ⋆ b`. -/
theorem isMultiplicative_sym2Bank (H : HeckeEigenData f) :
    (sym2Bank f).IsMultiplicative := by
  unfold sym2Bank
  exact isMultiplicative_sqIndicator.mul
    (isMultiplicative_moebius.intCast.mul (isMultiplicative_rankinSquareNorm H))

/-! ## The rank-2 identification -/

/-- **The rank-2 bank identification**: the rank-2 slice of the rank-uniform bank family
is the corpus's independently-constructed `Sym²` bank, `symrBank H 2 = sym2Bank f`.

Two multiplicative functions agreeing on prime powers agree; the prime-power agreement is
`Sym2LocalJoin.radialLocalEulerCoeff_symClock_eq_sym2Coeff` against
`Sym2Wire.sym2Bank_prime_pow`.  The two banks were built from opposite ends — one as the
complete homogeneous symmetric function of the clock weights, one as a square-dilation
convolution of the Möbius-peeled Rankin square — and they coincide. -/
theorem symrBank_two_eq_sym2Bank (H : HeckeEigenData f) :
    symrBank H 2 = sym2Bank f := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ (symrBank_isMultiplicative H 2)
    _ (isMultiplicative_sym2Bank H)]
  intro p j hp
  rw [symrBank_prime_pow H 2 hp j, sym2Bank_prime_pow H hp j]
  unfold symrCoeff
  exact radialLocalEulerCoeff_symClock_eq_sym2Coeff
    (H.satake hp) (H.satake_ne_zero hp) j

/-- **The composite join**: the CPS all-place coefficient sequence read at the `Sym²`
clock weights is the bank whose completed Rankin readout is computed by
`Sym2GammaChart.sym2_readout_gammaC`. -/
theorem radialGlobal_eq_sym2Bank (H : HeckeEigenData f) (n : ℕ) :
    radialGlobalSatakeCoeff
      (fun p : Nat.Primes => fun i : Fin 3 =>
        symClockWeight 2 (H.satake p.2) (i : ℕ)) n
      = sym2Bank f (n + 1) := by
  rw [radialGlobal_eq_symrBank H 2 n, symrBank_two_eq_sym2Bank H]

end CriticalLinePhasor.Sym2Join

#print axioms CriticalLinePhasor.Sym2Join.radialGlobal_eq_symrBank
#print axioms CriticalLinePhasor.Sym2Join.isMultiplicative_sqIndicator
#print axioms CriticalLinePhasor.Sym2Join.isMultiplicative_rankinSquareNorm
#print axioms CriticalLinePhasor.Sym2Join.isMultiplicative_sym2Bank
#print axioms CriticalLinePhasor.Sym2Join.symrBank_two_eq_sym2Bank
#print axioms CriticalLinePhasor.Sym2Join.radialGlobal_eq_sym2Bank
