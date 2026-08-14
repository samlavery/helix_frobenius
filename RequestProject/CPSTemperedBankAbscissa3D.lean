import RequestProject.CPSLocalEulerLogDerivative3D
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The tempered bank converges absolutely on `Re s > 1`

Every abscissa in the arithmetic CPS stack is currently read off the *radial* polynomial bound
`‖h_k(w)‖ ≤ (k+1)^(card ι)`, which only gives `abscissaOfAbsConv ≤ card ι + 1`.  That is the right
answer for a bank of unknown radius, and it is far too weak for the identification seam: the Euler
readout, the edge argument, and the logarithmic derivative all live on `Re s > 1`.

Once the bank is **tempered** the true majorant is available, and it is exact rather than
polynomial.  With `‖w p i‖ = 1` the local coefficient is a sum of unit monomials over the
`k`-antidiagonal of `ι`, so

  `‖h_k(w p)‖ ≤ #(finsuppAntidiag univ k) = h_k(1) = ((ζ ^ card ι) (p ^ k))`,

the `card ι`-fold divisor function at `p ^ k`; multiplicativity propagates it to every `n`.  The
`d`-fold divisor function is `d` Dirichlet convolutions of `ζ`, hence `LSeriesSummable` exactly on
`Re s > 1`, and comparison transfers that to the bank.

The identification of the divisor power with the all-ones bank is done through the compiled
prime-power generating series of `CPSLocalEulerLogDerivative3D`: `primePowerSeries` turns
Dirichlet convolution into the Cauchy product, so `ζ ^ d` at `p` is `(mk 1) ^ d`, which is the
local Euler series of the constant bank `1`.  No estimate is made anywhere; the majorant is
computed.
-/

open Finset ArithmeticFunction Complex
open scoped ArithmeticFunction.zeta LSeries.notation

namespace CriticalLinePhasor.GlobalHelix

open CriticalLinePhasor.CarrierTheta CriticalLinePhasor.TransportClosure

/-! ## The `d`-fold divisor function through its prime-power generating series -/

/-- The `d`-fold divisor arithmetic function, complex valued: `d` Dirichlet convolutions of the
constant function one. -/
noncomputable def divisorPowerC (d : ℕ) : ArithmeticFunction ℂ :=
  ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) ^ d

/-- At any prime, the generating series of `ζ` is the all-ones series. -/
theorem primePowerSeries_zetaC {p : ℕ} (hp : p.Prime) :
    primePowerSeries ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) p =
      PowerSeries.mk 1 := by
  ext n
  rw [coeff_primePowerSeries, PowerSeries.coeff_mk]
  simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]
  rw [if_neg (pow_ne_zero _ hp.ne_zero)]
  simp

/-- Dirichlet powers become Cauchy powers of the prime-power generating series. -/
theorem primePowerSeries_pow (F : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) (d : ℕ) :
    primePowerSeries (F ^ d) p = (primePowerSeries F p) ^ d := by
  induction d with
  | zero => simpa using primePowerSeries_one hp
  | succ d ih =>
      rw [pow_succ, ← primePowerSeries_mul _ _ hp, ih, pow_succ]

/-- The geometric Euler series of the weight one is the all-ones series. -/
theorem geometricEulerSeries_one : geometricEulerSeries (1 : ℂ) = PowerSeries.mk 1 := by
  ext n
  rw [coeff_geometricEulerSeries]
  simp

/-- The local Euler series of the constant bank `1` is the `card ι`-th Cauchy power of the
all-ones series. -/
theorem localEulerPowerSeries_one {ι : Type*} [Fintype ι] :
    localEulerPowerSeries (fun _ : ι => (1 : ℂ)) =
      (PowerSeries.mk 1) ^ (Fintype.card ι) := by
  rw [localEulerPowerSeries]
  simp [geometricEulerSeries_one, Finset.prod_const, Finset.card_univ]

/-- The `card ι`-fold divisor function at a prime power is exactly the all-ones local Euler
coefficient — the count of the antidiagonal. -/
theorem divisorPowerC_prime_pow {ι : Type*} [Fintype ι] {p : ℕ} (hp : p.Prime) (k : ℕ) :
    divisorPowerC (Fintype.card ι) (p ^ k) =
      radialLocalEulerCoeff (fun _ : ι => (1 : ℂ)) k := by
  have h := primePowerSeries_pow
    ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) hp (Fintype.card ι)
  rw [primePowerSeries_zetaC hp] at h
  have hk := congrArg (PowerSeries.coeff k) h
  rw [coeff_primePowerSeries] at hk
  rw [divisorPowerC, hk, ← localEulerPowerSeries_one (ι := ι), coeff_localEulerPowerSeries]

/-- **The tempered local majorant.**  A unit-modulus bank is dominated coefficientwise by the
constant bank `1`; the bound is the triangle inequality on the antidiagonal sum, with no slack
beyond it. -/
theorem norm_radialLocalEulerCoeff_le_one_bank {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (hw : ∀ i, ‖w i‖ = 1) (n : ℕ) :
    ‖radialLocalEulerCoeff w n‖ ≤
      ‖radialLocalEulerCoeff (fun _ : ι => (1 : ℂ)) n‖ := by
  classical
  have hone : radialLocalEulerCoeff (fun _ : ι => (1 : ℂ)) n =
      ((Finset.finsuppAntidiag (Finset.univ : Finset ι) n).card : ℂ) := by
    unfold radialLocalEulerCoeff
    simp
  rw [hone, Complex.norm_natCast]
  unfold radialLocalEulerCoeff
  calc
    ‖∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n, ∏ i, w i ^ l i‖ ≤
        ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n, ‖∏ i, w i ^ l i‖ :=
      norm_sum_le _ _
    _ = ∑ _l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [norm_prod]
      apply Finset.prod_eq_one
      intro i _
      rw [norm_pow, hw i, one_pow]
    _ = ((Finset.finsuppAntidiag (Finset.univ : Finset ι) n).card : ℝ) := by simp

/-- The divisor power is multiplicative. -/
theorem isMultiplicative_divisorPowerC (d : ℕ) :
    (divisorPowerC d).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.pow
    (ArithmeticFunction.isMultiplicative_zeta.natCast)

/-- **The tempered global majorant.**  Every value of a unit-modulus bank is dominated by the
`card ι`-fold divisor function. -/
theorem norm_bankArithmetic_le_divisorPowerC {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (hw : ∀ p i, ‖w p i‖ = 1) (n : ℕ) :
    ‖coefficientArithmetic (radialGlobalSatakeCoeff w) n‖ ≤
      ‖divisorPowerC (Fintype.card ι) n‖ := by
  have hA := isMultiplicative_bankArithmetic w
  have hM := isMultiplicative_divisorPowerC (Fintype.card ι)
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
  · simp
  · intro p k hp
    rw [bankArithmetic_prime_pow w hp, divisorPowerC_prime_pow (ι := ι) hp]
    exact norm_radialLocalEulerCoeff_le_one_bank _ (hw ⟨p, hp⟩) k
  · intro a b _ha _hb hab iha ihb
    rw [hA.map_mul_of_coprime hab, hM.map_mul_of_coprime hab, norm_mul, norm_mul]
    exact mul_le_mul iha ihb (norm_nonneg _) (norm_nonneg _)

/-! ## Absolute convergence on the standard half-plane -/

/-- The `d`-fold divisor series converges absolutely on `Re s > 1`. -/
theorem LSeriesSummable_divisorPowerC (d : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (⇑(divisorPowerC d)) s := by
  induction d with
  | zero =>
      have h1 : divisorPowerC 0 = 1 := by rw [divisorPowerC, pow_zero]
      rw [h1]
      refine summable_of_ne_finset_zero (s := {1}) ?_
      intro n hn
      simp only [Finset.mem_singleton] at hn
      rcases eq_or_ne n 0 with rfl | h0
      · simp [LSeries.term]
      · rw [LSeries.term_of_ne_zero h0, ArithmeticFunction.one_apply, if_neg hn, zero_div]
  | succ d ih =>
      have hstep : divisorPowerC (d + 1) =
          divisorPowerC d * ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
        rw [divisorPowerC, divisorPowerC, pow_succ]
      rw [hstep]
      refine ArithmeticFunction.LSeriesSummable_mul ih ?_
      simpa [ArithmeticFunction.natCoe_apply] using
        (ArithmeticFunction.LSeriesSummable_zeta_iff (s := s)).mpr hs

/-- **The tempered bank is absolutely summable on `Re s > 1`.**  This is the abscissa the
identification seam needs; the radial polynomial bound only reaches `card ι + 1`. -/
theorem bankArithmetic_LSeriesSummable_of_tempered {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (hw : ∀ p i, ‖w p i‖ = 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (⇑(coefficientArithmetic (radialGlobalSatakeCoeff w))) s :=
  Summable.of_norm
    (((LSeriesSummable_divisorPowerC (Fintype.card ι) hs).norm).of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun n => LSeries.norm_term_le s (norm_bankArithmetic_le_divisorPowerC w hw n)))

/-- The abscissa of absolute convergence of a tempered bank is at most one. -/
theorem bankArithmetic_abscissaOfAbsConv_le_one {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (hw : ∀ p i, ‖w p i‖ = 1) :
    LSeries.abscissaOfAbsConv
        (⇑(coefficientArithmetic (radialGlobalSatakeCoeff w))) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    bankArithmetic_LSeriesSummable_of_tempered w hw (by simpa using hy)

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.divisorPowerC_prime_pow
#print axioms CriticalLinePhasor.GlobalHelix.norm_bankArithmetic_le_divisorPowerC
#print axioms CriticalLinePhasor.GlobalHelix.LSeriesSummable_divisorPowerC
#print axioms CriticalLinePhasor.GlobalHelix.bankArithmetic_LSeriesSummable_of_tempered
#print axioms CriticalLinePhasor.GlobalHelix.bankArithmetic_abscissaOfAbsConv_le_one
