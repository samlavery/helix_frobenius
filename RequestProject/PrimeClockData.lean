import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.IsPrimePow

/-!
# Canonical prime-power clock data

The lightweight data layer shared by the Carlson mean theorem and the D8 bank.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.PrimeClockOrdering

abbrev PrimeTooth := ℕ × ℕ

def toothPrime (r : ℕ) : Nat.Primes :=
  ⟨Nat.nth Nat.Prime r, Nat.prime_nth_prime r⟩

def toothExponent (i : PrimeTooth) : ℕ := i.2 + 1

def toothNat (i : PrimeTooth) : ℕ := (toothPrime i.1 : ℕ) ^ toothExponent i

def primeToothLength (i : PrimeTooth) : ℝ :=
  (toothExponent i : ℝ) * Real.log (toothPrime i.1 : ℕ)

def primeToothFace (α : Nat.Primes → ℂ) (i : PrimeTooth) : ℂ :=
  α (toothPrime i.1) ^ toothExponent i

def primeToothExhaustion (N : ℕ) : Finset PrimeTooth :=
  Finset.range N ×ˢ Finset.range N

def primeToothEtaIndex (i : PrimeTooth) : ℕ := toothNat i - 1

def etaPrimePowerSupport (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n => IsPrimePow (n + 1)

theorem toothExponent_pos (i : PrimeTooth) : 0 < toothExponent i := by
  simp [toothExponent]

theorem primeToothLength_pos (i : PrimeTooth) : 0 < primeToothLength i := by
  unfold primeToothLength
  exact mul_pos (by exact_mod_cast toothExponent_pos i) (toothPrime i.1).2.log_pos

theorem primeToothFace_norm (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    (i : PrimeTooth) : ‖primeToothFace α i‖ = 1 := by
  rw [primeToothFace, norm_pow, hα, one_pow]

theorem primeToothExhaustion_mono : Monotone primeToothExhaustion := by
  intro M N hMN
  exact Finset.product_subset_product (Finset.range_mono hMN) (Finset.range_mono hMN)

theorem mem_primeToothExhaustion (i : PrimeTooth) :
    i ∈ primeToothExhaustion (max i.1 i.2 + 1) := by
  simp [primeToothExhaustion]

theorem primeToothExhaustion_eventually_mem (i : PrimeTooth) :
    ∀ᶠ N in atTop, i ∈ primeToothExhaustion N := by
  filter_upwards [eventually_ge_atTop (max i.1 i.2 + 1)] with N hN
  exact primeToothExhaustion_mono hN (mem_primeToothExhaustion i)

theorem toothNat_two_le (i : PrimeTooth) : 2 ≤ toothNat i := by
  unfold toothNat
  exact le_trans (toothPrime i.1).2.two_le (Nat.le_pow (toothExponent_pos i))

theorem primeToothEtaIndex_succ (i : PrimeTooth) :
    primeToothEtaIndex i + 1 = toothNat i := by
  unfold primeToothEtaIndex
  exact Nat.sub_add_cancel (le_trans (by decide : 1 ≤ 2) (toothNat_two_le i))

theorem primeToothLength_eq_log_toothNat (i : PrimeTooth) :
    primeToothLength i = Real.log (toothNat i) := by
  rw [primeToothLength, toothNat, Nat.cast_pow, Real.log_pow]

theorem primeToothEtaIndex_injective : Function.Injective primeToothEtaIndex := by
  intro i j hij
  have hnat : toothNat i = toothNat j := by
    rw [← primeToothEtaIndex_succ i, ← primeToothEtaIndex_succ j, hij]
  have hp := (toothPrime i.1).2.pow_inj (toothPrime j.1).2 hnat
  have hprime : i.1 = j.1 := by
    have hcount := congrArg (Nat.count Nat.Prime) hp.1
    simpa [toothPrime, Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] using hcount
  exact Prod.ext hprime hp.2

theorem primeToothLength_injective : Function.Injective primeToothLength := by
  intro i j hij
  apply primeToothEtaIndex_injective
  have hi : 0 < (toothNat i : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_two (toothNat_two_le i)
  have hj : 0 < (toothNat j : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_two (toothNat_two_le j)
  have hnatCast : (toothNat i : ℝ) = toothNat j :=
    Real.strictMonoOn_log.injOn hi hj <| by
      rw [← primeToothLength_eq_log_toothNat, ← primeToothLength_eq_log_toothNat, hij]
  have hnat : toothNat i = toothNat j := by exact_mod_cast hnatCast
  unfold primeToothEtaIndex
  rw [hnat]

theorem mem_etaPrimePowerSupport_iff {N n : ℕ} :
    n ∈ etaPrimePowerSupport N ↔ n < N ∧ IsPrimePow (n + 1) := by
  simp [etaPrimePowerSupport]

theorem primeToothEtaIndex_mem_support (i : PrimeTooth)
    {N : ℕ} (hN : primeToothEtaIndex i < N) :
    primeToothEtaIndex i ∈ etaPrimePowerSupport N := by
  rw [mem_etaPrimePowerSupport_iff]
  refine ⟨hN, ?_⟩
  rw [primeToothEtaIndex_succ, toothNat]
  exact (toothPrime i.1).2.isPrimePow.pow (Nat.succ_ne_zero i.2)

end CriticalLinePhasor.PrimeClockOrdering

#print axioms CriticalLinePhasor.PrimeClockOrdering.primeToothLength_pos
#print axioms CriticalLinePhasor.PrimeClockOrdering.primeToothFace_norm
#print axioms CriticalLinePhasor.PrimeClockOrdering.primeToothExhaustion_eventually_mem
#print axioms CriticalLinePhasor.PrimeClockOrdering.primeToothEtaIndex_injective
#print axioms CriticalLinePhasor.PrimeClockOrdering.primeToothLength_injective
