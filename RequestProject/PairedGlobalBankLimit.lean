import RequestProject.GlobalBankLimit

/-!
# Paired global bank limits

Consecutive clock faces whose strand-exchange factors cancel give a constant exchange factor on
every even truncation.  Thus the exchange-constant convergence input for the global bank limit is
automatic on the paired subsequence.
-/

open Complex Set Filter Topology CriticalLinePhasor.ChiralityHB
open scoped BigOperators

namespace CriticalLinePhasor.StrandExchange

/-- Products over even ranges collapse when every consecutive pair has product one. -/
theorem prod_range_two_mul_eq_one_of_pairs (f : ℕ → ℂ)
    (hpair : ∀ k, f (2 * k) * f (2 * k + 1) = 1) :
    ∀ n, ∏ i ∈ Finset.range (2 * n), f i = 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, Finset.prod_range_succ, Finset.prod_range_succ, ih]
      simpa [mul_assoc] using hpair n

/-- The exchange constant is fixed along even truncations when consecutive face factors cancel. -/
theorem completedBankStageExchangeConstant_two_mul
    (α : ℕ → ℂ) (β : ℂ)
    (hpair : ∀ k,
      (-(starRingEnd ℂ) (α (2 * k))) * (-(starRingEnd ℂ) (α (2 * k + 1))) = 1)
    (n : ℕ) :
    completedBankStageExchangeConstant α β (2 * n) = ((starRingEnd ℂ) β) ^ 2 := by
  rw [completedBankStageExchangeConstant,
    prod_range_two_mul_eq_one_of_pairs
      (fun i => -(starRingEnd ℂ) (α i)) hpair]
  simp

/-- Even completed-bank stages inherit the finite strand exchange with a constant factor. -/
theorem completedBankStage_two_mul_exchange
    (α : ℕ → ℂ) (hα : ∀ i, ‖α i‖ = 1) (ℓ : ℕ → ℝ)
    (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ : ℝ)
    (hpair : ∀ k,
      (-(starRingEnd ℂ) (α (2 * k))) * (-(starRingEnd ℂ) (α (2 * k + 1))) = 1)
    (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ)
        (completedBankStage α ℓ β ℓ₀ (2 * n) ((starRingEnd ℂ) z)) =
      ((starRingEnd ℂ) β) ^ 2 * completedBankStage α ℓ β ℓ₀ (2 * n) z := by
  rw [completedBankStage_exchange α hα ℓ β hβ ℓ₀]
  rw [completedBankStageExchangeConstant_two_mul α β hpair]

/-- A locally uniform limit of the paired even stages is entire and obeys the fixed exchange law. -/
theorem pairedCompletedBankLimit_entire_exchange
    (α : ℕ → ℂ) (hα : ∀ i, ‖α i‖ = 1) (ℓ : ℕ → ℝ)
    (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ : ℝ) (f : ℂ → ℂ)
    (hpair : ∀ k,
      (-(starRingEnd ℂ) (α (2 * k))) * (-(starRingEnd ℂ) (α (2 * k + 1))) = 1)
    (hconv : TendstoLocallyUniformly
      (fun n => completedBankStage α ℓ β ℓ₀ (2 * n)) f atTop) :
    Differentiable ℂ f ∧
      ∀ z, (starRingEnd ℂ) (f ((starRingEnd ℂ) z)) =
        ((starRingEnd ℂ) β) ^ 2 * f z := by
  refine ⟨locallyUniformLimit_differentiable hconv ?_,
    locallyUniformLimit_exchange hconv tendsto_const_nhds ?_⟩
  · intro n
    exact completedBankStage_differentiable α ℓ β ℓ₀ (2 * n)
  · exact completedBankStage_two_mul_exchange α hα ℓ β hβ ℓ₀ hpair

end CriticalLinePhasor.StrandExchange

#print axioms CriticalLinePhasor.StrandExchange.prod_range_two_mul_eq_one_of_pairs
#print axioms CriticalLinePhasor.StrandExchange.completedBankStageExchangeConstant_two_mul
#print axioms CriticalLinePhasor.StrandExchange.completedBankStage_two_mul_exchange
#print axioms CriticalLinePhasor.StrandExchange.pairedCompletedBankLimit_entire_exchange
