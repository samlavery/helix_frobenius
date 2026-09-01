import RequestProject.BankHerglotzReduction
import RequestProject.PrimeClockCentered

/-!
# The one-clock-per-prime Herglotz door

This file specializes the off-zero Herglotz door to the fixed prime-clock
data: the first `N` primes, unit faces, and lengths `log p`.

Search audit:

```
rg -n "primeClock|primeToothLength|toothPrime|Finset.range" RequestProject
rg -n "Prime.log_pos|log_pos" .lake/packages/mathlib/Mathlib --glob '*.lean'
```
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.BankLimit

open CriticalLinePhasor.PrimeClockOrdering

/-- The length of the clock indexed by the `r`-th prime. -/
def onePrimeClockLength (r : ℕ) : ℝ := Real.log (toothPrime r : ℕ)

theorem onePrimeClockLength_pos (r : ℕ) : 0 < onePrimeClockLength r := by
  exact (toothPrime r).2.log_pos

/-- The bank door with all candidate data made literal: unit faces, one
clock per prime, and the natural prime ordering. -/
theorem riemannHypothesis_of_onePrimeClock_convergence_off_zeros :
    ∃ A : ℝ, 0 < A ∧
      ((∀ s : ℂ, 1269 / 2 < |s.im| →
          A / (Real.log |s.im|) ^ 9 < s.re → s.re < 1 / 2 →
          ZD.riemannXi s ≠ 0 →
          Tendsto (fun N => -∑ r ∈ Finset.range N,
              (((onePrimeClockLength r) / 2 : ℝ) : ℂ) *
                ((1 + Complex.exp (Complex.I * onePrimeClockLength r
                    * CriticalLinePhasor.HilbertPolya.spectralCoord s))
                 / (1 - Complex.exp (Complex.I * onePrimeClockLength r
                    * CriticalLinePhasor.HilbertPolya.spectralCoord s))))
            atTop (nhds (logDeriv ZD.riemannXi s))) →
        RiemannHypothesis) := by
  simpa using
    (riemannHypothesis_of_herglotz_sum_convergence_off_zeros
      (fun N : ℕ => Finset.range N) (fun _ : ℕ => (1 : ℂ))
      onePrimeClockLength (fun _ => norm_one) onePrimeClockLength_pos)

end CriticalLinePhasor.BankLimit

#print axioms CriticalLinePhasor.BankLimit.onePrimeClockLength_pos
#print axioms
  CriticalLinePhasor.BankLimit.riemannHypothesis_of_onePrimeClock_convergence_off_zeros
