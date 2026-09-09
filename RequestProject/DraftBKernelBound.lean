import RequestProject.DraftBDiscrepancy
import RequestProject.PrimeKernelUniformBound

/-!
Apply the degree-uniform scalar estimate to the actual arithmetic kernels.
The bound below is uniform in degree, with a right side depending on the cutoff N.
It does not assert a polynomial bound for the end-paired stages as N tends to infinity.
The phase is the original exp(20*i*log n), including all prime powers.

Unfolded step: |n^(-2) exp(20*i*log n) q_k(log n)| <= n^(-1/2), for n >= 2.
Then |sum_{n<N} Lambda(n) K_k(n)| <= sum_{n<N} Lambda(n) n^(-1/2).
Searches: `rg -n 'primeStageKernel.*norm|norm.*primeStageKernel|anchor_primeTerm_phase|
primeCoeffStage_succ_closed|vonMangoldt_(nonneg|apply_one)' RequestProject
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean`.
-/

open Complex Finset Filter Topology

namespace CriticalLinePhasor.SeatingLedger

theorem primeStageKernel_norm_le {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    ‖primeStageKernel k n‖ ≤ (n : ℝ) ^ (-1 / 2 : ℝ) := by
  have hphase : ‖ContourArgument.PrimeClock.phase (-20) (Real.log n)‖ = 1 := by
    simp only [ContourArgument.PrimeClock.phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, neg_zero, Real.exp_zero]
  have he : ‖primeStageKernel k n‖ =
      ‖(((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * primeCoeffSymbol (-3) k (Real.log n)‖ := by
    rw [primeStageKernel, norm_mul, norm_mul, hphase, mul_one, norm_mul]
  rw [he]
  exact primeCoeffSymbol_weighted_log_norm_le hn k

theorem primeStageKernel_vonMangoldt_norm_le (n k : ℕ) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) * primeStageKernel k n‖ ≤
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 / 2 : ℝ) := by
  by_cases hn : 2 ≤ n
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_mul_of_nonneg_left (primeStageKernel_norm_le hn k)
      ArithmeticFunction.vonMangoldt_nonneg
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> simp

theorem primeStageCoeff_uniform_degree_bound (N k : ℕ) :
    ‖toeplitzCoeff (-3) (primeJetStage anchor20 N) (k + 1)‖ ≤
      ∑ n ∈ range N, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 / 2 : ℝ) := by
  have ht (n : ℕ) : LSeries.term ContourArgument.vonMangoldtC (1 - anchor20) n *
      primeCoeffSymbol (-3) k (Real.log n) =
      (ArithmeticFunction.vonMangoldt n : ℂ) * primeStageKernel k n := by
    rw [anchor_primeTerm_phase]
    simp only [primeStageKernel, Complex.ofReal_mul]
    ring
  rw [primeCoeffStage_succ_closed]
  simp_rw [ht]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ =>
    primeStageKernel_vonMangoldt_norm_le n k)

#print axioms primeStageKernel_norm_le
#print axioms primeStageCoeff_uniform_degree_bound

end CriticalLinePhasor.SeatingLedger
