import Mathlib

/-!
# The carrier's ordered sum converges where the projection's unordered sum does not

The alternating (P/M) bank `Σ (−1)ⁿ (n+1)^{−s}` is the carrier's readout: the
fiber accumulates phasors IN ORDER as it grows in height.  Written as a `tsum`
this series stalls at `Re s = 1`, because a `tsum` in `ℂ` is an unordered sum
and so demands ABSOLUTE convergence.  Summed IN ORDER it converges on the
whole of `Re s > 0`.

This module proves the estimate that makes that work: consecutive terms differ
by at most `‖s‖·a^{−σ−1}`, so the PAIRED series converges absolutely exactly
when `σ > 0`.

SCOPE, stated precisely because the tempting general claim is false: it is NOT
true that unordered summation is what confines one to `Re s > 1`.  This repo
already reaches `Re s > 0` with unordered sums —
`DVPTruncatedZeta.truncated_zeta_pos_re` writes `ζ` there using `tsum`s of
Euler–Maclaurin fractional-part integrals.  The gate at `Re s = 1` is a fact
about THIS series in THAT summation mode, not a general law.

Nothing here is an estimate on `ζ`; it is a statement about the construction.
-/

open Complex intervalIntegral

noncomputable section

namespace CriticalLinePhasor.DVP

/-- Consecutive `cpow` values differ by the integral of the derivative. -/
theorem cpow_diff_eq_integral (s : ℂ) (a : ℝ) (ha : 0 < a) :
    ((a : ℂ)) ^ (-s) - (((a + 1 : ℝ)) : ℂ) ^ (-s)
      = -∫ x : ℝ in a..(a + 1), (-s) * ((x : ℝ) : ℂ) ^ (-s - 1) := by
  have hd : ∀ x ∈ Set.uIcc a (a + 1),
      HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (-s))
        ((-s) * ((x : ℝ) : ℂ) ^ (-s - 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0:ℝ) < x := by linarith [hx.1]
    by_cases hs0 : (-s : ℂ) = 0
    · rw [hs0]
      simpa using (hasDerivAt_const x (1:ℂ))
    · exact hasDerivAt_ofReal_cpow_const hxpos.ne' hs0
  have h0mem : (0:ℝ) ∉ Set.uIcc a (a + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h; exact absurd h.1 (by linarith)
  have hint : IntervalIntegrable (fun x : ℝ => (-s) * ((x : ℝ) : ℂ) ^ (-s - 1))
      MeasureTheory.volume a (a + 1) :=
    (intervalIntegral.intervalIntegrable_cpow (Or.inr h0mem)).const_mul _
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [hsub]
  ring

/-- **The bounded-variation estimate.**  Consecutive terms of the bank differ
by at most `‖s‖·a^{−σ−1}` — the bound whose summability threshold is exactly
`Re s > 0`. -/
theorem cpow_diff_norm_le (s : ℂ) (a : ℝ) (ha : 0 < a) (hs : -1 ≤ s.re) :
    ‖((a : ℂ)) ^ (-s) - (((a + 1 : ℝ)) : ℂ) ^ (-s)‖
      ≤ ‖s‖ * a ^ (-s.re - 1) := by
  rw [cpow_diff_eq_integral s a ha, norm_neg]
  have hbd : ∀ x ∈ Set.uIcc a (a + 1),
      ‖(-s) * ((x : ℝ) : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0:ℝ) < x := by linarith [hx.1]
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    have hmono : x ^ (-s.re - 1) ≤ a ^ (-s.re - 1) :=
      Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)
    exact mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => hbd x (Set.uIoc_subset_uIcc hx))
  simpa using this

/-- **The paired bank converges absolutely exactly on the carrier's region.**
The pairing `(2k+1)^{−s} − (2k+2)^{−s}` is summable for every `Re s > 0` —
where the unordered sum of the bank itself is not. -/
theorem paired_bank_summable {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k : ℕ =>
      (((2 * k + 1 : ℕ) : ℝ) : ℂ) ^ (-s)
        - (((2 * k + 2 : ℕ) : ℝ) : ℂ) ^ (-s)) := by
  have hmaj : Summable (fun k : ℕ => ‖s‖ * ((2 * k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s.re - 1)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact ((hbase.comp_injective (fun a b hab => by omega)).mul_left _)
  apply Summable.of_norm_bounded hmaj
  intro k
  have hk : (0:ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have hcast : (((2 * k + 2 : ℕ) : ℝ)) = ((2 * k + 1 : ℕ) : ℝ) + 1 := by
    push_cast; ring
  rw [hcast]
  exact cpow_diff_norm_le s _ hk (by linarith)

/-- A phasor of the bank, in the projection's own notation. -/
def etaTerm (s : ℂ) (n : ℕ) : ℂ := (-1) ^ n / ((n : ℂ) + 1) ^ s

/-- **The ordered readout.**  The fiber accumulates phasors in order of
height; this is that sum, truncated at `N`.  It is NOT a `tsum`. -/
def etaPartial (s : ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, etaTerm s n

/-- Consecutive phasors, paired as they enter. -/
def pairTerm (s : ℂ) (k : ℕ) : ℂ := etaTerm s (2 * k) + etaTerm s (2 * k + 1)

theorem pairTerm_eq (s : ℂ) (k : ℕ) :
    pairTerm s k
      = (((2 * k + 1 : ℕ) : ℝ) : ℂ) ^ (-s)
          - (((2 * k + 2 : ℕ) : ℝ) : ℂ) ^ (-s) := by
  simp only [pairTerm, etaTerm, Complex.cpow_neg, pow_mul, pow_succ]
  push_cast
  ring_nf

theorem pairTerm_summable {s : ℂ} (hs : 0 < s.re) : Summable (pairTerm s) := by
  refine (paired_bank_summable hs).congr (fun k => ?_)
  rw [pairTerm_eq]

/-- Pairing is exact on even truncations. -/
theorem etaPartial_two_mul (s : ℂ) (K : ℕ) :
    etaPartial s (2 * K) = ∑ k ∈ Finset.range K, pairTerm s k := by
  induction K with
  | zero => simp [etaPartial]
  | succ K ih =>
      have h2 : 2 * (K + 1) = (2 * K + 1) + 1 := by ring
      rw [h2, etaPartial, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      rw [← etaPartial] at *
      rw [ih, pairTerm]
      ring

/-- **The carrier's bank converges on `Re s > 0`.**  The ORDERED sum of the
alternating phasor bank has a limit for every `s` with `Re s > 0` — the whole
right half-plane, not the projection's `Re s > 1`.  The gate at `Re s = 1` is
the price of forgetting the order, and is not paid here. -/
theorem etaPartial_tendsto {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (etaPartial s) Filter.atTop
      (nhds (∑' k : ℕ, pairTerm s k)) := by
  set L : ℂ := ∑' k : ℕ, pairTerm s k with hL
  have hpair : Filter.Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, pairTerm s k)
      Filter.atTop (nhds L) := (pairTerm_summable hs).hasSum.tendsto_sum_nat
  have hdiv : Filter.Tendsto (fun N : ℕ => N / 2) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.2 (fun b => ⟨2 * b, fun a ha => by omega⟩)
  have hmain : Filter.Tendsto (fun N : ℕ => etaPartial s (2 * (N / 2)))
      Filter.atTop (nhds L) := by
    have := hpair.comp hdiv
    refine this.congr (fun N => ?_)
    rw [Function.comp_apply, etaPartial_two_mul]
  have hgap : ∀ N : ℕ,
      ‖etaPartial s N - etaPartial s (2 * (N / 2))‖ ≤ (N : ℝ) ^ (-s.re) := by
    intro N
    rcases Nat.even_or_odd N with he | ho
    · obtain ⟨m, hm⟩ := he
      have hN : 2 * (N / 2) = N := by omega
      rw [hN, sub_self, norm_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg N) _
    · obtain ⟨m, hm⟩ := ho
      have hm' : N = 2 * m + 1 := by omega
      have hdiv2 : N / 2 = m := by omega
      have hstep : etaPartial s N
          = etaPartial s (2 * m) + etaTerm s (2 * m) := by
        rw [hm', etaPartial, Finset.sum_range_succ, ← etaPartial]
      rw [hdiv2, hstep, add_sub_cancel_left]
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have : 0 < N := by omega
        exact_mod_cast this
      have hbase : ((2 * m : ℕ) : ℂ) + 1 = (((N : ℝ)) : ℂ) := by
        rw [hm']; push_cast; ring
      rw [etaTerm, hbase, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hNpos,
        norm_pow, norm_neg, norm_one, one_pow, Real.rpow_neg (le_of_lt hNpos),
        one_div]
  have hzero : Filter.Tendsto
      (fun N : ℕ => etaPartial s N - etaPartial s (2 * (N / 2)))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm hgap ?_
    have hr : Filter.Tendsto (fun x : ℝ => x ^ (-s.re)) Filter.atTop (nhds 0) :=
      tendsto_rpow_neg_atTop hs
    exact hr.comp tendsto_natCast_atTop_atTop
  have hsum := hzero.add hmain
  rw [zero_add] at hsum
  refine hsum.congr (fun N => ?_)
  ring

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.etaPartial_tendsto
#print axioms CriticalLinePhasor.DVP.cpow_diff_norm_le
#print axioms CriticalLinePhasor.DVP.paired_bank_summable
end AxiomAudit
