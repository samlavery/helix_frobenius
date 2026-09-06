import RequestProject.PrimeSymbol
import RequestProject.PrimeSymbolClock

/-!
# Reconciliation of the two prime-symbol conventions

Unfolded target: with `C(j,k) = conj(r_j) * r_k`, `a = (pf d j k).1`,
and `b = (pf d j k).2`, the clock symbol is
`-Σ(j,k) [C(j,k) A(j,k) + conj(C(j,k) B(j,k))]`.
The one-sided symbol is `Σ(j,k) C(j,k) A(j,k)`.
For `r_0 = 0`, all surviving pairs have positive indices, so the paired
first-order coefficient in `B` agrees with `b 1`. Reflection and conjugation
then give exactly a factor of `-2`. No positivity assertion is used.

Search commands (repository and Mathlib):
`rg -n -i 'primeSymbol.*(clock|reconcil|eq.*form)|leftSymbol.*primeSymbol|rightSymbol.*primeSymbol|pairFunctional.*dcValue|dcMoment.*poleGamma' RequestProject .lake/packages/mathlib/Mathlib --glob '*.lean'`
`rg -n 'theorem pf_first_symm|primeSymbolForm.*conj|pf_swap|pf_conj' RequestProject`

Expectation-free next step: compare the summands, retaining the first-order
term until `pf_first_symm` applies. Two decompositions are available:
`rw [primeSymbolForm'_eq_conj]` after collecting the finite mirror sum;
or `rw [Finset.sum_comm]` followed by `pf_swap` on each positive pair.
The first is used below; the second is already the audited proof of the
imported mirror-sum theorem.
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.ContourArgument.PrimeSymbolReconciliation

theorem leftSymbol_eq (d : ℂ) (M j k : ℕ) (ℓ : ℝ) :
    PrimeClock.leftSymbol d M j k ℓ = primeSymbol d M j k ℓ := rfl

theorem rightSymbol_eq (d : ℂ) (M : ℕ) {j k : ℕ}
    (hj : 1 ≤ j) (hk : 1 ≤ k) (ℓ : ℝ) :
    PrimeClock.rightSymbol d M j k ℓ = primeSymbol' d M j k ℓ := by
  unfold PrimeClock.rightSymbol primeSymbol' PrimeClock.logWeight
  rw [pf_first_symm d (j + k) j k rfl hj hk]

theorem clock_primeSymbol_eq (R : Polynomial ℂ) (hR : R.coeff 0 = 0)
    (d ℓ : ℝ) :
    PrimeClock.primeSymbol R d ℓ =
      -2 * primeSymbolForm R (d : ℂ) (2 * R.natDegree + 2) ℓ := by
  have hright :
      (∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
        ((starRingEnd ℂ) (R.coeff j) * R.coeff k) *
          PrimeClock.rightSymbol (d : ℂ) (2 * R.natDegree + 2) j k ℓ) =
      (starRingEnd ℂ) (primeSymbolForm R (d : ℂ) (2 * R.natDegree + 2) ℓ) := by
    rw [← primeSymbolForm'_eq_conj R hR (Complex.conj_ofReal d)]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hj0 : j = 0
    · subst j; simp [hR]
    by_cases hk0 : k = 0
    · subst k; simp [hR]
    rw [rightSymbol_eq _ _ (by omega) (by omega)]
  have hleft :
      (∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
        ((starRingEnd ℂ) (R.coeff j) * R.coeff k) *
          PrimeClock.leftSymbol (d : ℂ) (2 * R.natDegree + 2) j k ℓ) =
      primeSymbolForm R (d : ℂ) (2 * R.natDegree + 2) ℓ := rfl
  simp only [PrimeClock.primeSymbol, PrimeClock.pairSymbol,
    Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [hleft]
  simp only [← map_sum]
  rw [hright, Complex.conj_conj]
  ring

theorem clock_primeJetsForm_eq (R : Polynomial ℂ) (s d : ℂ) :
    PrimeClock.primeJetsForm R s d =
      (primeJetsForm R s d (2 * R.natDegree + 2)).re := rfl

theorem dcMoment_zero (s : ℂ) :
    PrimeClock.dcMoment s 0 = poleGammaLogDeriv s := rfl

theorem dcMoment_succ (s : ℂ) (m : ℕ) :
    PrimeClock.dcMoment s (m + 1) =
      poleGammaJet s (m + 1) / ((-1) ^ (m + 1) * ((m + 1).factorial : ℂ)) := by
  unfold PrimeClock.dcMoment poleGammaJet
  have hf : ((m + 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hp : (-1 : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast
  field_simp

theorem pairFunctional_dcMoment (s d : ℂ) (M j k : ℕ) :
    PrimeClock.pairFunctional d M j k (PrimeClock.dcMoment s) =
      dcValue s d M j k := by
  unfold PrimeClock.pairFunctional dcValue
  simp only [dcMoment_zero, dcMoment_succ, Complex.add_conj,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp only [map_div₀, map_mul, map_pow, map_neg, map_one, map_natCast]
  have hp : (-1 : ℂ) ^ (i + 1) * (-1 : ℂ) ^ (i + 1) = 1 := by
    rw [← mul_pow]
    simp
  have hf : ((i + 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hp0 : (-1 : ℂ) ^ (i + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  linear_combination -(starRingEnd ℂ) (poleGammaJet s (i + 1)) * hp

theorem clock_dcForm_eq (R : Polynomial ℂ) (s d : ℂ) :
    PrimeClock.dcForm R s d = (dcForm R s d (2 * R.natDegree + 2)).re := by
  simp only [PrimeClock.dcForm, PrimeClock.momentForm, pairFunctional_dcMoment, dcForm]

end CriticalLinePhasor.ContourArgument.PrimeSymbolReconciliation

#print axioms CriticalLinePhasor.ContourArgument.pf_first_symm
#print axioms CriticalLinePhasor.ContourArgument.primeSymbolForm'_eq_conj
#print axioms CriticalLinePhasor.ContourArgument.PrimeSymbolReconciliation.clock_primeSymbol_eq
#print axioms CriticalLinePhasor.ContourArgument.PrimeSymbolReconciliation.clock_primeJetsForm_eq
#print axioms CriticalLinePhasor.ContourArgument.PrimeSymbolReconciliation.clock_dcForm_eq
