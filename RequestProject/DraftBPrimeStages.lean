import RequestProject.ExplicitAnchorDischarge
import RequestProject.PrimeSymbolClock
import RequestProject.PrimeCoefficientSymbol

/-!
# Draft B: collect the actual prime stages after end pairing

Target, unfolded: find real C and natural p, independent of k and N, such that
for every k there is N_k with |stage_N(k)| <= C*(1+k^p) for all N >= N_k.
At s = -1+20i the reflected prime terms are Lambda(n)*n^(-2+20i).
The zeroth coefficient is 2*Re J(1)/(-3). Positive degrees use the finite Pascal
combination of J(2), ..., J(k+2). The prime powers retain their actual log n.

Construction A starts with `obtain ⟨C, hC⟩ := explicit_growth_unconditional`.
Construction B starts with `rw [explicitCoeffStage_eq_paired]`: first pair the
end atom at zero with the arithmetic finite sum; then estimate the remainder.
The end mode is evaluated exactly below, before taking norms.

Search record: `rg -n -i 'explicit_?coeff_?stage|explicitCoeffStage|prime_?jet_?stage|
primeJetStage|stage_?bound|polynomial_?growth|coeff.*bounded|bounded.*coeff'
RequestProject --glob '*.lean'`; `rg -n -i 'primeCoeffSymbol|prime_coeff_symbol|
toeplitz.*symbol|symbol.*toeplitz|stage.*closed|closed.*stage' RequestProject`;
`rg -n 'logMul_iterate|logMul_apply|iterate_logMul|logMul.*pow|term_log'
RequestProject .lake/packages/mathlib/Mathlib/NumberTheory/LSeries`.
Mathlib variants: `isBounded_range_of_tendsto`, `isBounded_iff_forall_norm_le`,
`eventually_lt_const`, `Tendsto.eventually_lt`, `pow.*isLittleO.*pow`.
LeanSearch: a convergent sequence in a normed space is bounded in norm.
Loogle: `Filter.Tendsto, Bornology.IsBounded`.
-/

open Complex Finset Filter Topology LSeries
open CriticalLinePhasor.ContourArgument

namespace CriticalLinePhasor.SeatingLedger

theorem primeJetStage_succ_closed (s : ℂ) (N m : ℕ) :
    primeJetStage s N (m + 1) = ∑ n ∈ range N,
      LSeries.term vonMangoldtC (1 - s) n *
        ((-1) ^ m / (m.factorial : ℂ) * (Real.log n : ℂ) ^ m) := by
  rw [primeJetStage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have h := PrimeClock.logMul_iterate_term (1 - s) m n
  change LSeries.term (logMul^[m] vonMangoldtC) (1 - s) n =
    (Real.log n : ℂ) ^ m * LSeries.term vonMangoldtC (1 - s) n at h
  rw [h]
  ring

theorem primeCoeffStage_succ_closed (s d : ℂ) (N k : ℕ) :
    toeplitzCoeff d (primeJetStage s N) (k + 1) =
      ∑ n ∈ range N, LSeries.term vonMangoldtC (1 - s) n *
        primeCoeffSymbol d k (Real.log n) := by
  unfold toeplitzCoeff
  trans ∑ i ∈ range (k + 1), ∑ n ∈ range N,
    LSeries.term vonMangoldtC (1 - s) n *
      ((k.choose i : ℂ) * d ^ (k - i) * (-1) ^ i *
        ((-1) ^ (k + 1 - i) / ((k + 1 - i).factorial : ℂ) *
          (Real.log n : ℂ) ^ (k + 1 - i)))
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    rw [show k + 2 - i = (k + 1 - i) + 1 by omega,
      primeJetStage_succ_closed, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    rw [primeCoeffSymbol, Finset.mul_sum]

theorem primeCoeffSymbol_zero (ℓ : ℝ) : primeCoeffSymbol (-3) 0 ℓ = -(ℓ : ℂ) := by
  simp [primeCoeffSymbol]

theorem primeCoeffSymbol_one (ℓ : ℝ) :
    primeCoeffSymbol (-3) 1 ℓ = (ℓ : ℂ) - 3 / 2 * (ℓ : ℂ) ^ 2 := by
  norm_num [primeCoeffSymbol, Finset.sum_range_succ]
  ring

/-- The end jet at zero, kept explicit before the completed pairing. -/
noncomputable def anchorEndJet (m : ℕ) : ℂ := 1 / anchor20 ^ m

/-- End and prime contribution are paired before estimating their norm. -/
noncomputable def pairedPrimeStageCoeff (N k : ℕ) : ℂ :=
  toeplitzCoeff (-3) (anchorEndJet + primeJetStage anchor20 N) k

noncomputable def archRemainderCoeff (k : ℕ) : ℂ :=
  toeplitzCoeff (-3) (jets archSide anchor20 - anchorEndJet) k

theorem explicitCoeffStage_eq_paired (N k : ℕ) :
    explicitCoeffStage N k = archRemainderCoeff k + pairedPrimeStageCoeff N k := by
  rw [archRemainderCoeff, pairedPrimeStageCoeff, ← toeplitzCoeff_add]
  unfold explicitCoeffStage
  congr 1
  ext m
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem anchorEndCoeff_succ (k : ℕ) :
    toeplitzCoeff (-3) anchorEndJet (k + 1) =
      anchor20⁻¹ ^ 2 * transport anchor20 0 ^ k := by
  have hs : anchor20 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [anchor20_re] at this
    norm_num at this
  have hd : anchor20 - (1 - (starRingEnd ℂ) anchor20) = (-3 : ℂ) := by
    apply Complex.ext <;> norm_num [anchor20]
  have h := transport_pow_identity anchor20 0 (by simpa using hs) k
  rw [hd] at h
  simp only [sub_zero] at h
  simp only [toeplitzCoeff, anchorEndJet, one_div, ← inv_pow]
  rw [← h]
  rw [show k + 2 = 2 + k by omega, pow_add, mul_assoc, ← mul_pow]
  have ht : anchor20⁻¹ * (0 - (1 - (starRingEnd ℂ) anchor20)) =
      transport anchor20 0 := by
    simp only [transport, sub_zero, div_eq_mul_inv]
    ring
  rw [ht]

theorem pairedPrimeStageCoeff_succ_closed (N k : ℕ) :
    pairedPrimeStageCoeff N (k + 1) =
      anchor20⁻¹ ^ 2 * transport anchor20 0 ^ k +
        ∑ n ∈ range N, LSeries.term vonMangoldtC (1 - anchor20) n *
          primeCoeffSymbol (-3) k (Real.log n) := by
  rw [pairedPrimeStageCoeff, toeplitzCoeff_add, anchorEndCoeff_succ,
    primeCoeffStage_succ_closed]

theorem pairedPrimeStageCoeff_zero_closed (N : ℕ) :
    pairedPrimeStageCoeff N 0 =
      2 * (((1 / anchor20 + ∑ n ∈ range N,
        LSeries.term vonMangoldtC (1 - anchor20) n).re : ℝ) : ℂ) / (-3) := by
  simp [pairedPrimeStageCoeff, toeplitzCoeff, anchorEndJet, primeJetStage]

theorem anchor_primeTerm_phase (n : ℕ) :
    LSeries.term vonMangoldtC (1 - anchor20) n =
      ((ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) *
        PrimeClock.phase (-20) (Real.log n) := by
  have h := PrimeClock.term_eq_weight_phase 2 (-20) n
  change LSeries.term vonMangoldtC ((2 : ℂ) + ((-20 : ℝ) : ℂ) * I) n = _ at h
  rw [show 1 - anchor20 = (2 : ℂ) + ((-20 : ℝ) : ℂ) * I by
    unfold anchor20; push_cast; ring]
  exact h

/-- The existing all-degree bound transfers to stages with one fixed constant. -/
theorem explicitCoeffStage_eventually_exponential :
    ∃ C : ℝ, ∀ k, ∀ᶠ N in atTop,
      ‖explicitCoeffStage N k‖ ≤ C * growthBase ^ k + 1 := by
  obtain ⟨C, hC⟩ := explicit_growth_unconditional
  refine ⟨C, fun k => ?_⟩
  have hlt := lt_of_le_of_lt (hC k) (lt_add_one (C * growthBase ^ k))
  exact ((explicitCoeffStage_tendsto k).norm.eventually_lt_const hlt).mono
    (fun N hN => hN.le)

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.primeCoeffStage_succ_closed
#print axioms CriticalLinePhasor.SeatingLedger.anchorEndCoeff_succ
#print axioms CriticalLinePhasor.SeatingLedger.pairedPrimeStageCoeff_succ_closed
#print axioms CriticalLinePhasor.SeatingLedger.pairedPrimeStageCoeff_zero_closed
#print axioms CriticalLinePhasor.SeatingLedger.anchor_primeTerm_phase
#print axioms CriticalLinePhasor.SeatingLedger.explicitCoeffStage_eventually_exponential
