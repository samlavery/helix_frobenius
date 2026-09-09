import RequestProject.DraftBPrimeStages
import RequestProject.PairedSides
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Module

/-!
# Arithmetic discrepancy estimate for Draft B

The target remains a common polynomial envelope for `explicitCoeffStage N k`,
eventually in N for each k. This file proves finite arithmetic estimates used
to investigate that envelope; it does not assert the envelope.

Unfolded arithmetic: E(N) = sum_{n<N} (Lambda(n)-1),
K_k(n) = n^(-2+20i) primeCoeffSymbol(-3,k,log n), with K_k(0)=0.
The end-paired stage is its uniform-density contribution plus
K_k(N-1) E(N) - sum_{n<N-1} (K_k(n+1)-K_k(n)) E(n+1).
Cancellation within E is retained before taking norms.

Expectation-free step: evaluate the cumulative signed mass before estimating it.
Decomposition A begins `have h := Finset.sum_range_by_parts K ... N`.
Decomposition B begins `induction N with`: check the boundary identity by
telescoping. Both are implemented below, independently.

Searches:
`rg -n -i 'pairedPrime.*(bound|polynomial)|paired_prime.*(bound|polynomial)|
explicit.*stage.*bound|primeCoeffSymbol|laguerre|compensat.*(prime|mangoldt)|
mangoldt.*(subtract|sub_one|discrepancy)|chebyshev.*(sub|error)'
RequestProject .lake/packages/mathlib/Mathlib --glob '*.lean'`
`rg -n 'sum_range_by_parts|sumRangeByParts|summation_by_parts|partialSummation|
abel_summation|psi_le_const_mul_self|psi_eq_sum_Icc|vonMangoldt_le_log'
RequestProject .lake/packages/mathlib/Mathlib --glob '*.lean'`
LeanSearch: summation by parts with cumulative sums and weight differences.
Loogle: `Finset.sum_range_by_parts`.
-/

open Complex Finset Filter Topology

namespace CriticalLinePhasor.SeatingLedger

/-- The integer-cutoff discrepancy. The term at zero is -1; its kernel is zero. -/
noncomputable def primeMassError (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (ArithmeticFunction.vonMangoldt n - 1)

theorem primeMassError_succ (N : ℕ) :
    primeMassError (N + 1) = primeMassError N + ArithmeticFunction.vonMangoldt N - 1 := by
  rw [primeMassError, sum_range_succ]
  change primeMassError N + (ArithmeticFunction.vonMangoldt N - 1) = _
  ring

theorem primeMassError_eq_psi (N : ℕ) :
    primeMassError N = Chebyshev.psi (N - 1 : ℕ) - N := by
  cases N with
  | zero => simp [primeMassError]
  | succ N =>
    simp only [primeMassError, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
      mul_one, Nat.add_sub_cancel, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    rw [Nat.range_succ_eq_Icc_zero]

/-- Chebyshev gives a concrete unconditional bound on the actual signed mass. -/
theorem primeMassError_abs_le (N : ℕ) :
    |primeMassError N| ≤ (Real.log 4 + 5) * N := by
  rw [primeMassError_eq_psi]
  have hN : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hpsi := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (N - 1))
  have hpsin := Chebyshev.psi_nonneg ((N - 1 : ℕ) : ℝ)
  have hupper : Chebyshev.psi (N - 1 : ℕ) ≤ (Real.log 4 + 4) * N :=
    hpsi.trans (mul_le_mul_of_nonneg_left hN (by linarith))
  rw [abs_le]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Abel summation specialized to the actual signed arithmetic coefficients. -/
theorem primeMassError_abel (K : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range N, ((ArithmeticFunction.vonMangoldt n - 1 : ℝ) : ℂ) * K n) =
      K (N - 1) * (primeMassError N : ℂ) -
        ∑ n ∈ range (N - 1), (K (n + 1) - K n) * (primeMassError (n + 1) : ℂ) := by
  have h := Finset.sum_range_by_parts K
    (fun n => ((ArithmeticFunction.vonMangoldt n - 1 : ℝ) : ℂ)) N
  simpa only [smul_eq_mul, primeMassError, Complex.ofReal_sum, mul_comm] using h

/-- Independent telescoping proof, with the boundary at N rather than N-1. -/
theorem primeMassError_abel_succ (K : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range (N + 1), ((ArithmeticFunction.vonMangoldt n - 1 : ℝ) : ℂ) * K n) =
      K N * (primeMassError (N + 1) : ℂ) -
        ∑ n ∈ range N, (K (n + 1) - K n) * (primeMassError (n + 1) : ℂ) := by
  induction N with
  | zero => simp [primeMassError, mul_comm]
  | succ N ih =>
    rw [sum_range_succ _ (N + 1), ih, sum_range_succ _ N, primeMassError_succ (N + 1)]
    push_cast
    ring

/-- A finite estimate in cumulative signed masses, not separate prime norms. -/
theorem primeMassError_weighted_norm_le (K : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ range N, ((ArithmeticFunction.vonMangoldt n - 1 : ℝ) : ℂ) * K n‖ ≤
      ‖K (N - 1)‖ * |primeMassError N| +
        ∑ n ∈ range (N - 1), ‖K (n + 1) - K n‖ * |primeMassError (n + 1)| := by
  rw [primeMassError_abel]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, le_refl]
  · calc
      ‖∑ n ∈ range (N - 1), (K (n + 1) - K n) * (primeMassError (n + 1) : ℂ)‖ ≤
          ∑ n ∈ range (N - 1), ‖(K (n + 1) - K n) * (primeMassError (n + 1) : ℂ)‖ :=
        norm_sum_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Apply the proved Chebyshev bound after, rather than before, summation by parts. -/
theorem primeMassError_chebyshev_norm_le (K : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ range N, ((ArithmeticFunction.vonMangoldt n - 1 : ℝ) : ℂ) * K n‖ ≤
      (Real.log 4 + 5) * ((N : ℝ) * ‖K (N - 1)‖ +
        ∑ n ∈ range (N - 1), ((n + 1 : ℕ) : ℝ) * ‖K (n + 1) - K n‖) := by
  calc
    _ ≤ ‖K (N - 1)‖ * |primeMassError N| +
        ∑ n ∈ range (N - 1), ‖K (n + 1) - K n‖ * |primeMassError (n + 1)| :=
      primeMassError_weighted_norm_le K N
    _ ≤ ‖K (N - 1)‖ * ((Real.log 4 + 5) * N) +
        ∑ n ∈ range (N - 1), ‖K (n + 1) - K n‖ * ((Real.log 4 + 5) * (n + 1)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (primeMassError_abs_le N) (norm_nonneg _)
      · apply Finset.sum_le_sum
        intro n hn
        simpa only [Nat.cast_add, Nat.cast_one] using
          mul_le_mul_of_nonneg_left (primeMassError_abs_le (n + 1)) (norm_nonneg _)
    _ = _ := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro n hn
        push_cast
        ring

/-- Actual degree kernel, with the common anchor phase and zero convention explicit. -/
noncomputable def primeStageKernel (k n : ℕ) : ℂ :=
  (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) *
    ContourArgument.PrimeClock.phase (-20) (Real.log n) *
      primeCoeffSymbol (-3) k (Real.log n)

/-- The end atom remains paired with the uniform integer density before estimating. -/
noncomputable def pairedDensityStage (N k : ℕ) : ℂ :=
  anchor20⁻¹ ^ 2 * transport anchor20 0 ^ k + ∑ n ∈ range N, primeStageKernel k n

theorem pairedPrimeStageCoeff_eq_density_add_error (N k : ℕ) :
    pairedPrimeStageCoeff N (k + 1) = pairedDensityStage N k +
      ∑ n ∈ range N, ((ArithmeticFunction.vonMangoldt n - 1 : ℝ) : ℂ) *
        primeStageKernel k n := by
  rw [pairedPrimeStageCoeff_succ_closed, pairedDensityStage, add_assoc, ← sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [anchor_primeTerm_phase]
  simp only [primeStageKernel, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- The prime-stage remainder is controlled by the exact signed mass and kernel variation. -/
theorem pairedPrimeStageCoeff_discrepancy_bound (N k : ℕ) :
    ‖pairedPrimeStageCoeff N (k + 1)‖ ≤ ‖pairedDensityStage N k‖ +
      (‖primeStageKernel k (N - 1)‖ * |primeMassError N| +
        ∑ n ∈ range (N - 1), ‖primeStageKernel k (n + 1) - primeStageKernel k n‖ *
          |primeMassError (n + 1)|) := by
  rw [pairedPrimeStageCoeff_eq_density_add_error]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  exact primeMassError_weighted_norm_le (primeStageKernel k) N

theorem pairedPrimeStageCoeff_chebyshev_bound (N k : ℕ) :
    ‖pairedPrimeStageCoeff N (k + 1)‖ ≤ ‖pairedDensityStage N k‖ +
      (Real.log 4 + 5) * ((N : ℝ) * ‖primeStageKernel k (N - 1)‖ +
        ∑ n ∈ range (N - 1), ((n + 1 : ℕ) : ℝ) *
          ‖primeStageKernel k (n + 1) - primeStageKernel k n‖) := by
  rw [pairedPrimeStageCoeff_eq_density_add_error]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  exact primeMassError_chebyshev_norm_le (primeStageKernel k) N

/-- Each fixed degree's logarithmic polynomial is smaller than the integer cutoff. -/
theorem primeCoeffSymbol_div_nat_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => primeCoeffSymbol (-3) k (Real.log n) / (n : ℂ))
      atTop (𝓝 0) := by
  have hm (m : ℕ) : Tendsto (fun n : ℕ => (Real.log n : ℂ) ^ m / (n : ℂ))
      atTop (𝓝 0) := by
    have hr := (Real.isLittleO_pow_log_id_atTop (n := m)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
    have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hr
    change Tendsto (fun n : ℕ => ((Real.log (n : ℝ) ^ m / (n : ℝ) : ℝ) : ℂ))
      atTop (𝓝 (0 : ℂ)) at hc
    simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast] using hc
  have hsum := tendsto_finsetSum (range (k + 1)) (fun i _ =>
    (hm (k + 1 - i)).const_mul ((k.choose i : ℂ) * (-3) ^ (k - i) * (-1) ^ i *
      ((-1) ^ (k + 1 - i) / ((k + 1 - i).factorial : ℂ))))
  simp only [mul_zero, sum_const_zero] at hsum
  refine hsum.congr (fun n => ?_)
  rw [primeCoeffSymbol, sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem primeStageKernel_scaled_norm (k n : ℕ) (hn : 0 < n) :
    (n : ℝ) * ‖primeStageKernel k n‖ =
      ‖primeCoeffSymbol (-3) k (Real.log n) / (n : ℂ)‖ := by
  have hphase : ‖ContourArgument.PrimeClock.phase (-20) (Real.log n)‖ = 1 := by
    simp only [ContourArgument.PrimeClock.phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, neg_zero, Real.exp_zero]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [primeStageKernel, norm_mul, norm_mul, hphase, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    norm_div, Complex.norm_natCast, Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two]
  field_simp [hn0]

/-- The Abel boundary vanishes for the actual arithmetic discrepancy at every fixed degree. -/
theorem primeMassError_kernel_boundary_tendsto_zero (k : ℕ) :
    Tendsto (fun N : ℕ => primeStageKernel k N * (primeMassError (N + 1) : ℂ))
      atTop (𝓝 0) := by
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlim := (primeCoeffSymbol_div_nat_tendsto_zero k).norm.const_mul
    (2 * (Real.log 4 + 5))
  simp only [norm_zero, mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmass : |primeMassError (N + 1)| ≤ (Real.log 4 + 5) * (2 * N) := by
    refine (primeMassError_abs_le (N + 1)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    push_cast
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖primeStageKernel k N‖ * |primeMassError (N + 1)| ≤
        ‖primeStageKernel k N‖ * ((Real.log 4 + 5) * (2 * N)) :=
      mul_le_mul_of_nonneg_left hmass (norm_nonneg _)
    _ = 2 * (Real.log 4 + 5) * ((N : ℝ) * ‖primeStageKernel k N‖) := by ring
    _ = _ := by rw [primeStageKernel_scaled_norm k N (by omega)]

/-- Match the stage remainder to the bounded gamma contribution, including degree zero. -/
theorem archRemainderCoeff_eq_pairedArch (k : ℕ) :
    archRemainderCoeff k = toeplitzCoeff (-3) (jets pairedArch anchor20) k := by
  have hj (m : ℕ) (hm : 1 ≤ m) :
      (jets archSide anchor20 - anchorEndJet) m = jets pairedArch anchor20 m := by
    cases m with
    | zero => omega
    | succ m =>
      rw [archSide_split,
        jets_add_contDiffOn anchor20_mem oneDiv_contDiffOn pairedArch_contDiffOn]
      simp only [Pi.sub_apply, Pi.add_apply]
      have hs : anchor20 ≠ 0 := by
        intro h
        have hr := congrArg Complex.re h
        rw [anchor20_re] at hr
        norm_num at hr
      have hend : jets (fun s : ℂ => 1 / s) anchor20 (m + 1) = anchorEndJet (m + 1) := by
        simp only [jets, anchorEndJet]
        rw [show (fun s : ℂ => 1 / s) = (fun s : ℂ => 1 / (s - 0)) by
          funext s; rw [sub_zero], iteratedDeriv_one_div_sub 0 m hs, sub_zero]
        have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
        have hsign : (-1 : ℂ) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
        calc
          _ = ((-1 : ℂ) ^ m * (-1) ^ m) *
              ((m.factorial : ℂ) / (m.factorial : ℂ)) * (1 / anchor20 ^ (m + 1)) := by ring
          _ = _ := by rw [hsign, div_self hf, one_mul, one_mul]
      rw [hend]
      ring
  cases k with
  | zero => simp only [archRemainderCoeff, toeplitzCoeff, hj 1 le_rfl]
  | succ k =>
      simp only [archRemainderCoeff, toeplitzCoeff]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hj (k + 2 - i) (by have := Finset.mem_range.mp hi; omega)]

/-- The bounded gamma branch and the arithmetic discrepancy bound assembled for the full stage. -/
theorem explicitCoeffStage_discrepancy_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N k,
      ‖explicitCoeffStage N (k + 1)‖ ≤ A + ‖pairedDensityStage N k‖ +
        (‖primeStageKernel k (N - 1)‖ * |primeMassError N| +
          ∑ n ∈ range (N - 1), ‖primeStageKernel k (n + 1) - primeStageKernel k n‖ *
            |primeMassError (n + 1)|) := by
  obtain ⟨A, hA⟩ := pairedArchCoeff_bounded
  refine ⟨A, (norm_nonneg _).trans (hA 0), fun N k => ?_⟩
  rw [explicitCoeffStage_eq_paired, archRemainderCoeff_eq_pairedArch]
  calc
    _ ≤ ‖toeplitzCoeff (-3) (jets pairedArch anchor20) (k + 1)‖ +
        ‖pairedPrimeStageCoeff N (k + 1)‖ := norm_add_le _ _
    _ ≤ A + (‖pairedDensityStage N k‖ +
        (‖primeStageKernel k (N - 1)‖ * |primeMassError N| +
          ∑ n ∈ range (N - 1), ‖primeStageKernel k (n + 1) - primeStageKernel k n‖ *
            |primeMassError (n + 1)|)) :=
      add_le_add (hA (k + 1)) (pairedPrimeStageCoeff_discrepancy_bound N k)
    _ = _ := by ring

/-- The density and signed Abel variation remain inside one norm. -/
noncomputable def primeDiscrepancyStage (N k : ℕ) : ℂ :=
  pairedDensityStage (N + 1) k -
    ∑ n ∈ range N, (primeStageKernel k (n + 1) - primeStageKernel k n) *
      (primeMassError (n + 1) : ℂ)

theorem explicitCoeffStage_eq_discrepancy_add_boundary (N k : ℕ) :
    explicitCoeffStage (N + 1) (k + 1) =
      archRemainderCoeff (k + 1) + primeDiscrepancyStage N k +
        primeStageKernel k N * (primeMassError (N + 1) : ℂ) := by
  rw [explicitCoeffStage_eq_paired, pairedPrimeStageCoeff_eq_density_add_error,
    primeMassError_abel_succ, primeDiscrepancyStage]
  ring

/-- The bounded gamma contribution and the vanishing cutoff boundary cost one common constant. -/
theorem explicitCoeffStage_eventually_le_discrepancy :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k, ∀ᶠ N in atTop,
      ‖explicitCoeffStage (N + 1) (k + 1)‖ ≤ A + ‖primeDiscrepancyStage N k‖ := by
  obtain ⟨A, hA⟩ := pairedArchCoeff_bounded
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  refine ⟨A + 1, by linarith, fun k => ?_⟩
  have hb := (primeMassError_kernel_boundary_tendsto_zero k).norm.eventually_lt_const
    (show ‖(0 : ℂ)‖ < 1 by simp)
  filter_upwards [hb] with N hN
  rw [explicitCoeffStage_eq_discrepancy_add_boundary, archRemainderCoeff_eq_pairedArch]
  calc
    _ ≤ ‖toeplitzCoeff (-3) (jets pairedArch anchor20) (k + 1) + primeDiscrepancyStage N k‖ +
        ‖primeStageKernel k N * (primeMassError (N + 1) : ℂ)‖ := norm_add_le _ _
    _ ≤ (‖toeplitzCoeff (-3) (jets pairedArch anchor20) (k + 1)‖ +
        ‖primeDiscrepancyStage N k‖) + 1 := add_le_add (norm_add_le _ _) hN.le
    _ ≤ (A + ‖primeDiscrepancyStage N k‖) + 1 := by gcongr; exact hA (k + 1)
    _ = _ := by ring

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.primeMassError_abs_le
#print axioms CriticalLinePhasor.SeatingLedger.primeMassError_abel_succ
#print axioms CriticalLinePhasor.SeatingLedger.pairedPrimeStageCoeff_discrepancy_bound
#print axioms CriticalLinePhasor.SeatingLedger.pairedPrimeStageCoeff_chebyshev_bound
#print axioms CriticalLinePhasor.SeatingLedger.primeMassError_kernel_boundary_tendsto_zero
#print axioms CriticalLinePhasor.SeatingLedger.explicitCoeffStage_discrepancy_bound
#print axioms CriticalLinePhasor.SeatingLedger.explicitCoeffStage_eventually_le_discrepancy
