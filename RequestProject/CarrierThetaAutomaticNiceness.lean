import RequestProject.CarrierThetaAutomaticCoupling

/-!
# Automatic twisted niceness from polynomial carrier coefficients

The synthesized inverse kernels are reindexed as ordinary zero-based theta coefficients.  Their
polynomial growth and the rapid completed carrier decay yield rapid kernel decay.  Exact carrier
reconstruction transfers continuity and local integrability, completing every analytic input of
the coefficient-theta strong functional equation.
-/

open Complex Set Filter Topology MeasureTheory Asymptotics

namespace CriticalLinePhasor.CarrierTheta

open ArithmeticFunction CriticalLinePhasor.StrandExchange

/-- Read a positive arithmetic function as a zero-indexed coefficient sequence. -/
def arithmeticSequence (b : ArithmeticFunction ℂ) (n : ℕ) : ℂ := b (n + 1)

/-- Shifting a positive arithmetic function down and then back up recovers it exactly. -/
theorem coefficientArithmetic_arithmeticSequence (b : ArithmeticFunction ℂ) :
    coefficientArithmetic (arithmeticSequence b) = b := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [coefficientArithmetic, arithmeticSequence]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    simp [coefficientArithmetic, arithmeticSequence, hn, Nat.sub_add_cancel hn1]

/-- The zero-indexed theta of the shifted coefficients is the positive dilation kernel. -/
theorem theta_arithmeticSequence (b : ArithmeticFunction ℂ) (h : ℝ → ℂ) (x : ℝ) :
    theta (arithmeticSequence b) h x = dilationKernel b h x := by
  rw [theta_eq_positiveTheta, coefficientArithmetic_arithmeticSequence]
  rfl

/-- Polynomial growth of an arithmetic function gives the standard shifted theta bound. -/
theorem arithmeticSequence_polynomial_bound
    (b : ArithmeticFunction ℂ) (B : ℕ) (Cb : ℝ)
    (hb : ∀ n : ℕ+, ‖b n‖ ≤ Cb * ((n : ℕ) : ℝ) ^ B) :
    ∀ n : ℕ, ‖arithmeticSequence b n‖ ≤
      Cb * (((n + 1 : ℕ) : ℝ) ^ (B : ℝ)) := by
  intro n
  simpa [arithmeticSequence, Real.rpow_natCast] using
    hb (⟨n + 1, Nat.succ_pos n⟩ : ℕ+)

/-- The automatically synthesized primal dilation kernel decays faster than every real power. -/
theorem dilationKernel_completedLogTheta_rapid_of_polynomial
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (E : ℂ → ℂ) (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (A : ℕ) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (haBound : ∀ n : ℕ, ‖a n‖ ≤ Ca * (n : ℝ) ^ A) :
    ∀ q : ℝ,
      dilationKernel (dirichletInverse a ha) (completedLogTheta E k) =O[atTop]
        (fun x : ℝ => x ^ q) := by
  obtain ⟨B, Cb, hCb, hbBound⟩ :=
    dirichletInverse_polynomial_bound a ha A Ca hCa haBound
  intro q
  have hkernel :
      dilationKernel (dirichletInverse a ha) (completedLogTheta E k) =
        theta (arithmeticSequence (dirichletInverse a ha)) (completedLogTheta E k) := by
    funext x
    exact (theta_arithmeticSequence (dirichletInverse a ha) (completedLogTheta E k) x).symm
  rw [hkernel]
  exact theta_rapid_of_polynomial_of_kernel_rapid
    (arithmeticSequence (dirichletInverse a ha)) (completedLogTheta E k)
      Cb (B : ℝ) hCb
      (arithmeticSequence_polynomial_bound (dirichletInverse a ha) B Cb hbBound)
      (completedLogTheta_rapid_of_polynomial E k Acar hpoly) q

/-- The automatically synthesized dual dilation kernel has the same rapid decay. -/
theorem dilationKernel_completedLogThetaDual_rapid_of_polynomial
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (E : ℂ → ℂ) (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (A : ℕ) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (haBound : ∀ n : ℕ, ‖a n‖ ≤ Ca * (n : ℝ) ^ A) :
    ∀ q : ℝ,
      dilationKernel (dirichletInverse a ha) (completedLogThetaDual E k) =O[atTop]
        (fun x : ℝ => x ^ q) := by
  obtain ⟨B, Cb, hCb, hbBound⟩ :=
    dirichletInverse_polynomial_bound a ha A Ca hCa haBound
  intro q
  have hkernel :
      dilationKernel (dirichletInverse a ha) (completedLogThetaDual E k) =
        theta (arithmeticSequence (dirichletInverse a ha)) (completedLogThetaDual E k) := by
    funext x
    exact (theta_arithmeticSequence (dirichletInverse a ha)
      (completedLogThetaDual E k) x).symm
  rw [hkernel]
  exact theta_rapid_of_polynomial_of_kernel_rapid
    (arithmeticSequence (dirichletInverse a ha)) (completedLogThetaDual E k)
      Cb (B : ℝ) hCb
      (arithmeticSequence_polynomial_bound (dirichletInverse a ha) B Cb hbBound)
      (completedLogThetaDual_rapid_of_polynomial E k Acar hpoly) q

/-- Exact primal reconstruction transfers local integrability from the completed carrier. -/
theorem theta_inverseKernel_locallyIntegrableOn
    (a : ℕ → ℂ) (ha : Invertible ((coefficientArithmetic a) 1))
    (E : ℂ → ℂ) (hEcont : Continuous E) (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (A : ℕ) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (haBound : ∀ n : ℕ, ‖(coefficientArithmetic a) n‖ ≤ Ca * (n : ℝ) ^ A) :
    LocallyIntegrableOn
      (theta a (dilationKernel (dirichletInverse (coefficientArithmetic a) ha)
        (completedLogTheta E k))) (Ioi 0) := by
  have hcarrier : LocallyIntegrableOn (completedLogTheta E k) (Ioi 0) :=
    (completedLogTheta_continuousOn E hEcont k).locallyIntegrableOn measurableSet_Ioi
  apply LocallyIntegrableOn.congr _ hcarrier
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (theta_dirichletInverse_completedLogTheta_of_polynomial
    a ha E k Acar hpoly A Ca hCa haBound hx).symm

/-- Exact dual reconstruction transfers local integrability from the completed dual carrier. -/
theorem theta_inverseKernelDual_locallyIntegrableOn
    (a : ℕ → ℂ) (ha : Invertible ((coefficientArithmetic a) 1))
    (E : ℂ → ℂ) (hEcont : Continuous E) (k Acar : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ Acar))
    (A : ℕ) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (haBound : ∀ n : ℕ, ‖(coefficientArithmetic a) n‖ ≤ Ca * (n : ℝ) ^ A) :
    LocallyIntegrableOn
      (theta a (dilationKernel (dirichletInverse (coefficientArithmetic a) ha)
        (completedLogThetaDual E k))) (Ioi 0) := by
  have hcarrier : LocallyIntegrableOn (completedLogThetaDual E k) (Ioi 0) :=
    (completedLogThetaDual_continuousOn E hEcont k).locallyIntegrableOn measurableSet_Ioi
  apply LocallyIntegrableOn.congr _ hcarrier
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (theta_dirichletInverse_completedLogThetaDual_of_polynomial
    a ha E k Acar hpoly A Ca hCa haBound hx).symm

/-- An arithmetic-function bound is exactly the shifted coefficient bound used by theta decay. -/
theorem coefficientSequence_polynomial_bound
    (a : ℕ → ℂ) (A : ℕ) (Ca : ℝ)
    (haBound : ∀ n : ℕ, ‖(coefficientArithmetic a) n‖ ≤ Ca * (n : ℝ) ^ A) :
    ∀ n : ℕ, ‖a n‖ ≤ Ca * (((n + 1 : ℕ) : ℝ) ^ (A : ℝ)) := by
  intro n
  simpa [coefficientArithmetic, Real.rpow_natCast] using haBound (n + 1)

/-- Conjugation preserves nonvanishing. -/
theorem star_ne_zero {z : ℂ} (hz : z ≠ 0) : (starRingEnd ℂ) z ≠ 0 := by
  intro hstar
  apply hz
  have h := congrArg (starRingEnd ℂ) hstar
  simpa using h

/-- The strong functional-equation pair synthesized from polynomial primal and dual coefficient
banks and a completed carrier exchange. -/
noncomputable def automaticCoefficientThetaStrongFEPair
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
      ‖(coefficientArithmetic aDual) n‖ ≤ CaDual * (n : ℝ) ^ ADual) :
    StrongFEPair ℂ :=
  coefficientThetaStrongFEPair a aDual
    (dilationKernel (dirichletInverse (coefficientArithmetic a) ha)
      (completedLogTheta E k))
    (dilationKernel (dirichletInverse (coefficientArithmetic aDual) haDual)
      (completedLogThetaDual E k))
    Ca (A : ℝ) CaDual (ADual : ℝ) hCa hCaDual
    (coefficientSequence_polynomial_bound a A Ca haBound)
    (coefficientSequence_polynomial_bound aDual ADual CaDual haDualBound)
    (dilationKernel_completedLogTheta_rapid_of_polynomial
      (coefficientArithmetic a) ha E k Acar hpoly A Ca hCa haBound)
    (dilationKernel_completedLogThetaDual_rapid_of_polynomial
      (coefficientArithmetic aDual) haDual E k Acar hpoly ADual CaDual hCaDual haDualBound)
    (theta_inverseKernel_locallyIntegrableOn
      a ha E hEcont k Acar hpoly A Ca hCa haBound)
    (theta_inverseKernelDual_locallyIntegrableOn
      aDual haDual E hEcont k Acar hpoly ADual CaDual hCaDual haDualBound)
    k hk ((starRingEnd ℂ) ε) (star_ne_zero hε)
    (coefficientTheta_reflection_of_polynomial_carrier E ε hE k Acar hpoly
      a aDual ha haDual A ADual Ca CaDual hCa hCaDual haBound haDualBound)

/-- The automatically synthesized pair has the full twisted-niceness payload. -/
theorem automaticCoefficientTheta_twistedNiceness
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
      ‖(coefficientArithmetic aDual) n‖ ≤ CaDual * (n : ℝ) ^ ADual) :
    let P := automaticCoefficientThetaStrongFEPair E hEcont ε hε hE k hk Acar hpoly
      a aDual ha haDual A ADual Ca CaDual hCa hCaDual haBound haDualBound
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  dsimp only
  exact coefficientTheta_twistedNiceness a aDual
    (dilationKernel (dirichletInverse (coefficientArithmetic a) ha)
      (completedLogTheta E k))
    (dilationKernel (dirichletInverse (coefficientArithmetic aDual) haDual)
      (completedLogThetaDual E k))
    Ca (A : ℝ) CaDual (ADual : ℝ) hCa hCaDual
    (coefficientSequence_polynomial_bound a A Ca haBound)
    (coefficientSequence_polynomial_bound aDual ADual CaDual haDualBound)
    (dilationKernel_completedLogTheta_rapid_of_polynomial
      (coefficientArithmetic a) ha E k Acar hpoly A Ca hCa haBound)
    (dilationKernel_completedLogThetaDual_rapid_of_polynomial
      (coefficientArithmetic aDual) haDual E k Acar hpoly ADual CaDual hCaDual haDualBound)
    (theta_inverseKernel_locallyIntegrableOn
      a ha E hEcont k Acar hpoly A Ca hCa haBound)
    (theta_inverseKernelDual_locallyIntegrableOn
      aDual haDual E hEcont k Acar hpoly ADual CaDual hCaDual haDualBound)
    k hk ((starRingEnd ℂ) ε) (star_ne_zero hε)
    (coefficientTheta_reflection_of_polynomial_carrier E ε hE k Acar hpoly
      a aDual ha haDual A ADual Ca CaDual hCa hCaDual haBound haDualBound)

end CriticalLinePhasor.CarrierTheta

#print axioms CriticalLinePhasor.CarrierTheta.coefficientArithmetic_arithmeticSequence
#print axioms CriticalLinePhasor.CarrierTheta.theta_arithmeticSequence
#print axioms CriticalLinePhasor.CarrierTheta.arithmeticSequence_polynomial_bound
#print axioms CriticalLinePhasor.CarrierTheta.dilationKernel_completedLogTheta_rapid_of_polynomial
#print axioms CriticalLinePhasor.CarrierTheta.dilationKernel_completedLogThetaDual_rapid_of_polynomial
#print axioms CriticalLinePhasor.CarrierTheta.theta_inverseKernel_locallyIntegrableOn
#print axioms CriticalLinePhasor.CarrierTheta.theta_inverseKernelDual_locallyIntegrableOn
#print axioms CriticalLinePhasor.CarrierTheta.coefficientSequence_polynomial_bound
#print axioms CriticalLinePhasor.CarrierTheta.star_ne_zero
#print axioms CriticalLinePhasor.CarrierTheta.automaticCoefficientThetaStrongFEPair
#print axioms CriticalLinePhasor.CarrierTheta.automaticCoefficientTheta_twistedNiceness
