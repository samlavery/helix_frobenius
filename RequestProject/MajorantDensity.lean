import RequestProject.PartialSerre

/-!
# Graded cancellation gives density bounds, via nonnegative majorants

`partial_serre` converts cancellation at ranks `1 ≤ r ≤ R` into convergence of every degree-`≤ R`
polynomial observable to its Sato--Tate value.  That is the interface; this file draws the
classically meaningful consequence.

If `g` is **dominated** on the Satake angles by a degree-`≤ R` combination of symmetric-power
characters,

  **`g(θ_p) ≤ ∑_{r ≤ R} c_r · U_r(cos θ_p)`  for every prime,**

then the prime average of `g` is eventually below `c₀ + ε`.  Taking `g` to be (a minorant of) an
indicator, `c₀` is an upper bound for the density of primes whose Satake angle lands in the target
set — a Serre-style bound, unconditional given the graded record.

This is what finitely many automorphic symmetric powers actually buy: not equidistribution, but
one-sided density bounds whose sharpness is governed by how well a low-degree nonnegative
combination can majorise an indicator.

**Scope.**  The majorant is an input, not constructed here; no claim is made about which `R` the
classical record supplies for any particular form.
-/

open Filter Topology Polynomial.Chebyshev

namespace CriticalLinePhasor.PartialSerre

open CriticalLinePhasor.SatoTateCarrier3D CriticalLinePhasor.GeneralSeed
open CriticalLinePhasor.MaassSatoTate

/-- The prime average of the symmetric-power character is the prime average of the Chebyshev
character read on the Satake angle. -/
theorem arithmeticAverage_eq_chebyshev (F : ArithmeticSatakePrimeFamily) (r n : ℕ) :
    arithmeticSymmetricPowerPrimeAverage F r n
      = (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), (U ℝ (r : ℤ)).eval (Real.cos (F.angle (nthPrime i))) := by
  rw [arithmeticSymmetricPowerPrimeAverage]
  refine congrArg (fun t => (1 / ((n + 1 : ℕ) : ℝ)) * t) ?_
  exact Finset.sum_congr rfl fun i _ => (F.character_eq_satakeTrace (nthPrime i) r).symm

/-- The degree-`≤ R` observable average is the prime average of the observable. -/
theorem polyObservableAverage_eq (F : ArithmeticSatakePrimeFamily) (c : ℕ → ℝ) (R n : ℕ) :
    polyObservableAverage F c R n
      = (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), ∑ r ∈ Finset.range (R + 1),
          c r * (U ℝ (r : ℤ)).eval (Real.cos (F.angle (nthPrime i))) := by
  calc polyObservableAverage F c R n
      = ∑ r ∈ Finset.range (R + 1), ∑ i : Fin (n + 1),
          (1 / ((n + 1 : ℕ) : ℝ)) *
            (c r * (U ℝ (r : ℤ)).eval (Real.cos (F.angle (nthPrime i)))) := by
        rw [polyObservableAverage]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [arithmeticAverage_eq_chebyshev, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i : Fin (n + 1), ∑ r ∈ Finset.range (R + 1),
          (1 / ((n + 1 : ℕ) : ℝ)) *
            (c r * (U ℝ (r : ℤ)).eval (Real.cos (F.angle (nthPrime i)))) :=
        Finset.sum_comm
    _ = (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ i : Fin (n + 1), ∑ r ∈ Finset.range (R + 1),
          c r * (U ℝ (r : ℤ)).eval (Real.cos (F.angle (nthPrime i))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-- **The majorant bound.**  If a degree-`≤ R` character combination dominates `g` on the Satake
angles, the prime average of `g` is eventually below the combination's constant term. -/
theorem majorant_prime_average_le (F : ArithmeticSatakePrimeFamily) (R : ℕ)
    (hcanc : ∀ r : ℕ, 1 ≤ r → r ≤ R →
      Tendsto (fun n => arithmeticSymmetricPowerPrimeAverage F r n) atTop (𝓝 0))
    (c : ℕ → ℝ) (g : ℝ → ℝ)
    (hmaj : ∀ p : Nat.Primes, g (F.angle p)
      ≤ ∑ r ∈ Finset.range (R + 1), c r * (U ℝ (r : ℤ)).eval (Real.cos (F.angle p)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i : Fin (n + 1), g (F.angle (nthPrime i)) < c 0 + ε := by
  have hobs := partial_serre F R hcanc c
  have hev : ∀ᶠ n : ℕ in atTop, polyObservableAverage F c R n < c 0 + ε :=
    hobs.eventually_lt_const (by linarith)
  filter_upwards [hev] with n hn
  refine lt_of_le_of_lt ?_ hn
  rw [polyObservableAverage_eq]
  have hpos : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpos.le
  exact Finset.sum_le_sum fun i _ => hmaj (nthPrime i)

end CriticalLinePhasor.PartialSerre

#print axioms CriticalLinePhasor.PartialSerre.majorant_prime_average_le
