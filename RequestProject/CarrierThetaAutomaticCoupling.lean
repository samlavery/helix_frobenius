import RequestProject.CarrierThetaDirichletInverseGrowth

/-!
# Automatic carrier coupling from coefficient growth

The recursive growth theorem removes the separate bound on inverse coefficients from the exact
carrier reconstruction.  Polynomial growth of each coefficient bank now supplies all convergence
data for its Dirichlet-inverse dilation kernel.
-/

open Complex Set Filter Asymptotics

namespace CriticalLinePhasor.CarrierTheta

open ArithmeticFunction CriticalLinePhasor.StrandExchange

/-- Exponential decay of the completed primal carrier and polynomial growth of the original bank
automatically make the inverse dilation series summable. -/
theorem completedLogTheta_inverseSeries_summable_of_polynomial
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (E : ℂ → ℂ) (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (A : ℕ) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (haBound : ∀ n : ℕ, ‖a n‖ ≤ Ca * (n : ℝ) ^ A)
    {x : ℝ} (hx : 0 < x) :
    Summable fun p : ℕ+ × ℕ+ =>
      a p.1 * (dirichletInverse a ha) p.2 *
        completedLogTheta E k (((p.1 : ℕ) * (p.2 : ℕ)) * x) := by
  obtain ⟨B, Cb, hCb, hbBound⟩ :=
    dirichletInverse_polynomial_bound a ha A Ca hCa haBound
  exact completedLogTheta_inverseSeries_summable a ha E k Acar hpoly A B Ca Cb hx hCa hCb
    (fun n => haBound n) hbBound

/-- The same automatic convergence result for the completed dual carrier. -/
theorem completedLogThetaDual_inverseSeries_summable_of_polynomial
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (E : ℂ → ℂ) (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (A : ℕ) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (haBound : ∀ n : ℕ, ‖a n‖ ≤ Ca * (n : ℝ) ^ A)
    {x : ℝ} (hx : 0 < x) :
    Summable fun p : ℕ+ × ℕ+ =>
      a p.1 * (dirichletInverse a ha) p.2 *
        completedLogThetaDual E k (((p.1 : ℕ) * (p.2 : ℕ)) * x) := by
  obtain ⟨B, Cb, hCb, hbBound⟩ :=
    dirichletInverse_polynomial_bound a ha A Ca hCa haBound
  exact completedLogThetaDual_inverseSeries_summable a ha E k Acar hpoly
    A B Ca Cb hx hCa hCb (fun n => haBound n) hbBound

/-- Exact primal reconstruction with inverse growth synthesized internally. -/
theorem theta_dirichletInverse_completedLogTheta_of_polynomial
    (a : ℕ → ℂ) (ha : Invertible ((coefficientArithmetic a) 1))
    (E : ℂ → ℂ) (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (A : ℕ) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (haBound : ∀ n : ℕ, ‖(coefficientArithmetic a) n‖ ≤ Ca * (n : ℝ) ^ A)
    {x : ℝ} (hx : 0 < x) :
    theta a
      (dilationKernel (dirichletInverse (coefficientArithmetic a) ha)
        (completedLogTheta E k)) x = completedLogTheta E k x := by
  apply theta_dirichletInverse_coupling
  exact completedLogTheta_inverseSeries_summable_of_polynomial
    (coefficientArithmetic a) ha E k Acar hpoly A Ca hCa haBound hx

/-- Exact dual reconstruction with inverse growth synthesized internally. -/
theorem theta_dirichletInverse_completedLogThetaDual_of_polynomial
    (a : ℕ → ℂ) (ha : Invertible ((coefficientArithmetic a) 1))
    (E : ℂ → ℂ) (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (A : ℕ) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (haBound : ∀ n : ℕ, ‖(coefficientArithmetic a) n‖ ≤ Ca * (n : ℝ) ^ A)
    {x : ℝ} (hx : 0 < x) :
    theta a
      (dilationKernel (dirichletInverse (coefficientArithmetic a) ha)
        (completedLogThetaDual E k)) x = completedLogThetaDual E k x := by
  apply theta_dirichletInverse_coupling
  exact completedLogThetaDual_inverseSeries_summable_of_polynomial
    (coefficientArithmetic a) ha E k Acar hpoly A Ca hCa haBound hx

/-- Polynomial primal and dual coefficient banks inherit the completed carrier reflection through
their automatically synthesized inverse-dilation kernels. -/
theorem coefficientTheta_reflection_of_polynomial_carrier
    (E : ℂ → ℂ) (ε : ℂ)
    (hE : ∀ z, (starRingEnd ℂ) (E ((starRingEnd ℂ) z)) = ε * E z)
    (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (a aDual : ℕ → ℂ)
    (ha : Invertible ((coefficientArithmetic a) 1))
    (haDual : Invertible ((coefficientArithmetic aDual) 1))
    (A ADual : ℕ) (Ca CaDual : ℝ) (hCa : 0 ≤ Ca) (hCaDual : 0 ≤ CaDual)
    (haBound : ∀ n : ℕ,
      ‖(coefficientArithmetic a) n‖ ≤ Ca * (n : ℝ) ^ A)
    (haDualBound : ∀ n : ℕ,
      ‖(coefficientArithmetic aDual) n‖ ≤ CaDual * (n : ℝ) ^ ADual) :
    ∀ x ∈ Ioi (0 : ℝ),
      theta a
          (dilationKernel (dirichletInverse (coefficientArithmetic a) ha)
            (completedLogTheta E k)) (1 / x) =
        ((starRingEnd ℂ) ε * (x ^ k : ℝ)) •
          theta aDual
            (dilationKernel (dirichletInverse (coefficientArithmetic aDual) haDual)
              (completedLogThetaDual E k)) x := by
  apply coefficientTheta_reflection_of_carrier_coupling E ε hE k
  · intro x hx
    exact theta_dirichletInverse_completedLogTheta_of_polynomial
      a ha E k Acar hpoly A Ca hCa haBound hx
  · intro x hx
    exact theta_dirichletInverse_completedLogThetaDual_of_polynomial
      aDual haDual E k Acar hpoly ADual CaDual hCaDual haDualBound hx

end CriticalLinePhasor.CarrierTheta

#print axioms CriticalLinePhasor.CarrierTheta.completedLogTheta_inverseSeries_summable_of_polynomial
#print axioms CriticalLinePhasor.CarrierTheta.completedLogThetaDual_inverseSeries_summable_of_polynomial
#print axioms CriticalLinePhasor.CarrierTheta.theta_dirichletInverse_completedLogTheta_of_polynomial
#print axioms CriticalLinePhasor.CarrierTheta.theta_dirichletInverse_completedLogThetaDual_of_polynomial
#print axioms CriticalLinePhasor.CarrierTheta.coefficientTheta_reflection_of_polynomial_carrier
