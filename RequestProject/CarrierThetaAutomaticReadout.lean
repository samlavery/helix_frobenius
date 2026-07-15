import RequestProject.CarrierThetaAutomaticNiceness

/-!
# Exact readout of the automatic inverse-kernel construction

The coefficient theta with its synthesized Dirichlet-inverse kernel is pointwise the completed
carrier on positive heights.  Consequently its Mellin readout is exactly the carrier Mellin
readout on the whole plane, and likewise on the dual side.
-/

open Complex Set Filter MeasureTheory Asymptotics

namespace CriticalLinePhasor.CarrierTheta

open ArithmeticFunction CriticalLinePhasor.StrandExchange

/-- The synthesized primal coefficient theta has exactly the completed carrier Mellin readout. -/
theorem mellin_theta_dirichletInverse_completedLogTheta_of_polynomial
    (a : ℕ → ℂ) (ha : Invertible ((coefficientArithmetic a) 1))
    (E : ℂ → ℂ) (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (A : ℕ) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (haBound : ∀ n : ℕ, ‖(coefficientArithmetic a) n‖ ≤ Ca * (n : ℝ) ^ A)
    (s : ℂ) :
    mellin
        (theta a (dilationKernel (dirichletInverse (coefficientArithmetic a) ha)
          (completedLogTheta E k))) s =
      mellin (completedLogTheta E k) s := by
  unfold mellin
  apply setIntegral_congr_ae measurableSet_Ioi
  filter_upwards with x hx
  rw [theta_dirichletInverse_completedLogTheta_of_polynomial
    a ha E k Acar hpoly A Ca hCa haBound hx]

/-- The synthesized dual coefficient theta has exactly the completed dual-carrier Mellin readout. -/
theorem mellin_theta_dirichletInverse_completedLogThetaDual_of_polynomial
    (a : ℕ → ℂ) (ha : Invertible ((coefficientArithmetic a) 1))
    (E : ℂ → ℂ) (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (A : ℕ) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (haBound : ∀ n : ℕ, ‖(coefficientArithmetic a) n‖ ≤ Ca * (n : ℝ) ^ A)
    (s : ℂ) :
    mellin
        (theta a (dilationKernel (dirichletInverse (coefficientArithmetic a) ha)
          (completedLogThetaDual E k))) s =
      mellin (completedLogThetaDual E k) s := by
  unfold mellin
  apply setIntegral_congr_ae measurableSet_Ioi
  filter_upwards with x hx
  rw [theta_dirichletInverse_completedLogThetaDual_of_polynomial
    a ha E k Acar hpoly A Ca hCa haBound hx]

/-- Audit of the automatic construction at its public `StrongFEPair` interface: its completed
readout is the Mellin transform of the supplied completed carrier.  The coefficient bank has
been paired with its own Dirichlet-inverse dilation kernel before this readout is taken. -/
theorem automaticCoefficientThetaStrongFEPair_Lambda_eq_carrierMellin
    (E : ℂ → ℂ) (hEcont : Continuous E) (ε : ℂ) (hε : ε ≠ 0)
    (hE : ∀ z, (starRingEnd ℂ) (E ((starRingEnd ℂ) z)) = ε * E z)
    (k : ℝ) (hk : 0 < k) (Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (a aDual : ℕ → ℂ)
    (ha : Invertible ((coefficientArithmetic a) 1))
    (haDual : Invertible ((coefficientArithmetic aDual) 1))
    (A ADual : ℕ) (Ca CaDual : ℝ) (hCa : 0 ≤ Ca) (hCaDual : 0 ≤ CaDual)
    (haBound : ∀ n : ℕ,
      ‖(coefficientArithmetic a) n‖ ≤ Ca * (n : ℝ) ^ A)
    (haDualBound : ∀ n : ℕ,
      ‖(coefficientArithmetic aDual) n‖ ≤ CaDual * (n : ℝ) ^ ADual)
    (s : ℂ) :
    let P := automaticCoefficientThetaStrongFEPair E hEcont ε hε hE k hk Acar hpoly
      a aDual ha haDual A ADual Ca CaDual hCa hCaDual haBound haDualBound
    P.Λ s = mellin (completedLogTheta E k) s := by
  dsimp only
  exact mellin_theta_dirichletInverse_completedLogTheta_of_polynomial
    a ha E k Acar hpoly A Ca hCa haBound s

/-- The corresponding anti-helix readout is likewise the supplied completed dual carrier. -/
theorem automaticCoefficientThetaStrongFEPair_dualLambda_eq_carrierMellin
    (E : ℂ → ℂ) (hEcont : Continuous E) (ε : ℂ) (hε : ε ≠ 0)
    (hE : ∀ z, (starRingEnd ℂ) (E ((starRingEnd ℂ) z)) = ε * E z)
    (k : ℝ) (hk : 0 < k) (Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (a aDual : ℕ → ℂ)
    (ha : Invertible ((coefficientArithmetic a) 1))
    (haDual : Invertible ((coefficientArithmetic aDual) 1))
    (A ADual : ℕ) (Ca CaDual : ℝ) (hCa : 0 ≤ Ca) (hCaDual : 0 ≤ CaDual)
    (haBound : ∀ n : ℕ,
      ‖(coefficientArithmetic a) n‖ ≤ Ca * (n : ℝ) ^ A)
    (haDualBound : ∀ n : ℕ,
      ‖(coefficientArithmetic aDual) n‖ ≤ CaDual * (n : ℝ) ^ ADual)
    (s : ℂ) :
    let P := automaticCoefficientThetaStrongFEPair E hEcont ε hε hE k hk Acar hpoly
      a aDual ha haDual A ADual Ca CaDual hCa hCaDual haBound haDualBound
    P.symm.Λ s = mellin (completedLogThetaDual E k) s := by
  dsimp only
  exact mellin_theta_dirichletInverse_completedLogThetaDual_of_polynomial
    aDual haDual E k Acar hpoly ADual CaDual hCaDual haDualBound s

end CriticalLinePhasor.CarrierTheta

#print axioms CriticalLinePhasor.CarrierTheta.mellin_theta_dirichletInverse_completedLogTheta_of_polynomial
#print axioms CriticalLinePhasor.CarrierTheta.mellin_theta_dirichletInverse_completedLogThetaDual_of_polynomial
#print axioms CriticalLinePhasor.CarrierTheta.automaticCoefficientThetaStrongFEPair_Lambda_eq_carrierMellin
#print axioms CriticalLinePhasor.CarrierTheta.automaticCoefficientThetaStrongFEPair_dualLambda_eq_carrierMellin
