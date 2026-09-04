import RequestProject.XiJetsArithmetic

/-!
# The explicit arithmetic symbol of the prime-jet form

The target, unfolded: for `s = σ + iγ`, `σ > 1`, and a finite coefficient vector
`r_j = R.coeff j`, take the real part of `Σ conj(r_j) r_k jetValueP s d M j k`.
Its nonprime part consists of the pole and Gamma jets, including the paired
first-order value. Its prime part is a single absolutely convergent sum in `n`
with weight `Λ(n) n^(-σ)` and phase `exp(-iγ log n)` multiplying a finite
quadratic polynomial in `log n`. No positivity of that form is assumed here.

Search record (before construction):
* `rg -n 'rh_iff_prime_jets_nonneg|hermForm_eq_hankel|primeJetsForm|primeSymbol|def pf' RequestProject`
* `rg -n -i 'prime_?symbol|prime_?jets_?form|hockey.?stick|hankel|pascal|prime_?jet|herm_?form_?eq' --glob '*.lean' .`
* `rg -n -i 'pf_fst|pf_snd|pf.*closed|closed.*pf|partial.?fraction|prime.?symbol|prime.?jets.?form|dc.?form|hankel|choose_succ_succ|choose_pos|sum_range_add_choose' RequestProject .lake/packages/mathlib/Mathlib`
* `rg -n 'logMul|LSeriesSummable.*log|term_def|term_of_ne_zero|re_tsum|conj_tsum' .lake/packages/mathlib/Mathlib`
Semantic searches: LeanSearch finite/infinite sum interchange; Loogle `Nat.choose, _ + _`.

Construction protocol: absent a prior expectation, compute the coefficients and
then the degree-(1,2) restriction. Two coefficient decompositions are Pascal
induction (`induction j generalizing k a`) and cumulative hockey-stick summation
(`rw [Nat.sum_range_add_choose]`). Two arithmetic decompositions are linearity
of convergent series (`apply HasSum.add`) and finite-sum interchange
(`rw [Summable.tsum_finsetSum]`).
-/

open Complex Finset
open LSeries

noncomputable section

namespace CriticalLinePhasor.ContourArgument

theorem pf_fst_closed (d : ℂ) (j k a : ℕ) :
    (pf d (j + 1) (k + 1)).1 (a + 1) =
      if a ≤ j then
        ((j + k - a).choose k : ℂ) * d⁻¹ ^ (j + k + 1 - a)
      else 0 := by
  induction j generalizing k a with
  | zero =>
    induction k with
    | zero => simp [pf_succ, pf_zero_right, pf_zero_left]
    | succ k ih =>
      rw [pf_succ]
      dsimp only
      rw [ih, pf_zero_left]
      by_cases ha : a = 0
      · subst a
        simp [pow_succ, mul_comm]
      · simp [ha, show ¬ a ≤ 0 by omega]
  | succ j ih =>
    induction k with
    | zero =>
      rw [pf_succ]
      dsimp only
      rw [pf_zero_right, ih]
      by_cases ha : a ≤ j
      · have hne : a + 1 ≠ j + 1 + 1 := by omega
        simp only [hne, ↓reduceIte, ha, zero_add, Nat.choose_zero_right,
          Nat.cast_one, one_mul, show a ≤ j + 1 by omega]
        rw [show j + 1 + 1 - a = (j + 1 - a) + 1 by omega, pow_succ]
        simp [mul_comm]
      · by_cases he : a = j + 1
        · subst a
          simp
        · simp [ha, he, show ¬ a ≤ j + 1 by omega, show a + 1 ≠ j + 1 + 1 by omega]
    | succ k ihk =>
      rw [pf_succ]
      dsimp only
      rw [ihk, ih]
      by_cases ha : a ≤ j
      · simp only [ha, show a ≤ j + 1 by omega, ↓reduceIte]
        rw [show j + 1 + (k + 1) - a = (j + k + 1 - a) + 1 by omega,
          Nat.choose_succ_succ, Nat.cast_add]
        rw [show j + 1 + k - a = j + k + 1 - a by omega,
          show j + (k + 1) - a = j + k + 1 - a by omega]
        rw [show j + 1 + (k + 1) + 1 - a = (j + k + 2 - a) + 1 by omega,
          show j + 1 + k + 1 - a = j + k + 2 - a by omega,
          show j + (k + 1) + 1 - a = j + k + 2 - a by omega, pow_succ]
        simp only [one_div]
        ring
      · by_cases he : a = j + 1
        · subst a
          simp [pow_succ, mul_comm]
        · simp [ha, show ¬ a ≤ j + 1 by omega]

#print axioms pf_fst_closed

end CriticalLinePhasor.ContourArgument
