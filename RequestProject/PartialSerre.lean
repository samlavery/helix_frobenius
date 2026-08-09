import RequestProject.MaassSatoTateClosure

/-!
# The partial Serre criterion: graded cancellation gives graded moment convergence

The compiled Sato--Tate interface is all-or-nothing: cancellation at **every**
rank is equivalent to full carrier equidistribution.  The classical record for
a Maass form supplies cancellation only through rank nine (Kim--Shahidi); this
file compiles the graded statement that makes the record speak the interface's
language:

* `polyObservableAverage` — the prime average of a polynomial observable of
  degree `≤ R` in the symmetric-power characters, `∑_{r ≤ R} c_r · (U_r`-average`)`;
* `partial_serre` — **graded cancellation ⟹ graded convergence**: if the
  per-rank cancellation holds for `1 ≤ r ≤ R`, then the degree-`≤ R` observable
  average converges to `c₀`;
* `polyObservable_angleMeasure_integral` — `c₀` **is** the Sato--Tate integral
  of the observable (all higher characters integrate to zero), so the limit is
  the correct equidistribution value;
* `partial_serre_maass` — the instantiation at the Maass seed family.

Register.  With the classical record (cancellation through `r = 9`,
Kim--Shahidi, cited) the hypothesis of `partial_serre_maass` holds at `R = 9`:
every polynomial statistic of degree at most nine of a Maass form's Satake
angles converges to its Sato--Tate value.  The compiled layer is the exact
graded interface; the analytic inputs remain the cited per-rank one-line
statements.  No `axiom`, no `sorry`.
-/

open Filter Topology

namespace CriticalLinePhasor.PartialSerre

open CriticalLinePhasor.SatoTateCarrier3D CriticalLinePhasor.GeneralSeed
open CriticalLinePhasor.MaassSatoTate

/-- The prime average of the degree-`≤ R` polynomial observable
`∑_{r ≤ R} c_r · U_r`. -/
noncomputable def polyObservableAverage (F : ArithmeticSatakePrimeFamily)
    (c : ℕ → ℝ) (R n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (R + 1), c r * arithmeticSymmetricPowerPrimeAverage F r n

/-- The trivial-character average is identically one. -/
theorem average_zero_eq_one (F : ArithmeticSatakePrimeFamily) (n : ℕ) :
    arithmeticSymmetricPowerPrimeAverage F 0 n = 1 := by
  rw [← F.primeTestAverage_eq_arithmetic 0 n]
  simpa using primeTestAverage_chebyshev_U_zero F.angle n

/-- **The partial Serre criterion**: cancellation for `1 ≤ r ≤ R` gives
convergence of every degree-`≤ R` observable average to its constant term. -/
theorem partial_serre (F : ArithmeticSatakePrimeFamily) (R : ℕ)
    (hcanc : ∀ r : ℕ, 1 ≤ r → r ≤ R →
      Tendsto (fun n => arithmeticSymmetricPowerPrimeAverage F r n) atTop (𝓝 0))
    (c : ℕ → ℝ) :
    Tendsto (fun n => polyObservableAverage F c R n) atTop (𝓝 (c 0)) := by
  have hsum : Tendsto (fun n => polyObservableAverage F c R n) atTop
      (𝓝 (∑ r ∈ Finset.range (R + 1), if r = 0 then c 0 else 0)) := by
    unfold polyObservableAverage
    apply tendsto_finsetSum
    intro r hr
    rcases Nat.eq_zero_or_pos r with rfl | hrpos
    · have hconst : (fun n => c 0 * arithmeticSymmetricPowerPrimeAverage F 0 n)
          = fun _ => c 0 := by
        funext n
        rw [average_zero_eq_one, mul_one]
      rw [hconst]
      exact tendsto_const_nhds
    · rw [if_neg hrpos.ne']
      have hR : r ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      simpa using (hcanc r hrpos hR).const_mul (c r)
  have hval : (∑ r ∈ Finset.range (R + 1), if r = 0 then c 0 else 0) = c 0 := by
    rw [Finset.sum_ite_eq' (Finset.range (R + 1)) 0 (fun _ => c 0)]
    simp
  rwa [hval] at hsum

/-- The constant term **is** the Sato--Tate integral of the observable: every
nontrivial character integrates to zero, the trivial one to one. -/
theorem polyObservable_angleMeasure_integral (c : ℕ → ℝ) (R : ℕ) :
    ∑ r ∈ Finset.range (R + 1),
        c r * ∫ theta,
          cosinePolynomialTest (Polynomial.Chebyshev.U ℝ r) theta ∂angleMeasure
      = c 0 := by
  rw [Finset.sum_range_succ']
  have hz : ∀ r ∈ Finset.range R,
      c (r + 1) * ∫ theta,
        cosinePolynomialTest (Polynomial.Chebyshev.U ℝ (((r + 1 : ℕ) : ℤ))) theta
          ∂angleMeasure = 0 := by
    intro r _
    rw [chebyshev_U_angleMeasure_integral_zero (r + 1)
      (Nat.succ_le_succ (Nat.zero_le r)), mul_zero]
  rw [Finset.sum_eq_zero hz, zero_add]
  have h0 : (∫ theta,
      cosinePolynomialTest (Polynomial.Chebyshev.U ℝ (0 : ℕ)) theta ∂angleMeasure) = 1 := by
    simp
  rw [h0, mul_one]

/-- **The partial Serre criterion at the Maass seed**: graded cancellation for
`1 ≤ r ≤ R` gives every degree-`≤ R` polynomial statistic of the Satake angles
its Sato--Tate value.  With the classical record this holds at `R = 9`. -/
theorem partial_serre_maass (M : MaassEigenData) (hC : MaassTowerCeiling M) (R : ℕ)
    (hcanc : ∀ r : ℕ, 1 ≤ r → r ≤ R →
      Tendsto (fun n =>
        arithmeticSymmetricPowerPrimeAverage (maassSatoTateFamily M hC) r n)
        atTop (𝓝 0))
    (c : ℕ → ℝ) :
    Tendsto (fun n => polyObservableAverage (maassSatoTateFamily M hC) c R n)
      atTop (𝓝 (c 0)) :=
  partial_serre (maassSatoTateFamily M hC) R hcanc c

end CriticalLinePhasor.PartialSerre

#print axioms CriticalLinePhasor.PartialSerre.average_zero_eq_one
#print axioms CriticalLinePhasor.PartialSerre.partial_serre
#print axioms CriticalLinePhasor.PartialSerre.polyObservable_angleMeasure_integral
#print axioms CriticalLinePhasor.PartialSerre.partial_serre_maass
