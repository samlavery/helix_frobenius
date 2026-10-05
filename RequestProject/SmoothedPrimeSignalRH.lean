import RequestProject.SmoothedPrimeSignal
import RequestProject.VonMangoldtEFStandalone

/-!
# The one-sided bound on the smoothed prime signal, read at Mathlib's `RiemannHypothesis`

`SmoothedPrimeSignal.re_eq_half_of_lowerBound` puts every zero of `ζ` in the open strip `0 < Re ρ < 1` on
`Re ρ = ½` under the one-sided bound `W(y) ≥ D e^{y/2} − C` for `y ≥ 0`, where
`W(y) = Σ Λ(n) n^{−½} e^{−(y − log n)²}` and `D = √π e^{1/16}`.
`VMEFStandalone.NontrivialZeros_implies_RiemannHypothesis` reads the strip statement at Mathlib's
`RiemannHypothesis`.
-/

namespace SmoothedPrimeSignal

/-- **One input, read at the target.** -/
theorem riemannHypothesis_of_lowerBound (C : ℝ)
    (hC : ∀ y, 0 ≤ y → D * Real.exp (y / 2) - C ≤ W y) : RiemannHypothesis :=
  VMEFStandalone.NontrivialZeros_implies_RiemannHypothesis fun ρ hρ =>
    re_eq_half_of_lowerBound C hC ρ hρ.2.2 hρ.1 hρ.2.1

end SmoothedPrimeSignal

#print axioms SmoothedPrimeSignal.no_zero_right_of_lowerBound
#print axioms SmoothedPrimeSignal.re_eq_half_of_lowerBound
#print axioms SmoothedPrimeSignal.riemannHypothesis_of_lowerBound
