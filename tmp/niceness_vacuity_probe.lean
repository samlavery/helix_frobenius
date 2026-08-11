import RequestProject.Sym2Benchmark

open CriticalLinePhasor CriticalLinePhasor.GlobalHelix CriticalLinePhasor.Sym2Benchmark

/-- ADVERSARIAL PROBE: the pair carrying `sym2_GL3ConverseAnalyticInput_radiusLive`
(the paper's Theorem "niceness") has a completed transform that does not depend on the
Satake data at all — different base pair, different twist, same function. -/
example (pi pi' : PolynomialSatakeDualPair (Fin 2))
    (tau tau' : PolynomialSatakeDualPair (Fin 1)) (s : ℂ) :
    (cpsPolynomialStrongFEPair (arithmeticCPSPolynomialTwist 2 1 pi tau)).Λ s
      = (cpsPolynomialStrongFEPair (arithmeticCPSPolynomialTwist 2 1 pi' tau')).Λ s := by
  rw [cpsPolynomialStrongFEPair_Lambda_eq_carrierMellin,
    cpsPolynomialStrongFEPair_Lambda_eq_carrierMellin]

/-- Same for the contragredient leg. -/
example (pi pi' : PolynomialSatakeDualPair (Fin 2))
    (tau tau' : PolynomialSatakeDualPair (Fin 1)) (s : ℂ) :
    (cpsPolynomialStrongFEPair (arithmeticCPSPolynomialTwist 2 1 pi tau)).symm.Λ s
      = (cpsPolynomialStrongFEPair (arithmeticCPSPolynomialTwist 2 1 pi' tau')).symm.Λ s := by
  rw [cpsPolynomialStrongFEPair_dualLambda_eq_carrierMellin,
    cpsPolynomialStrongFEPair_dualLambda_eq_carrierMellin]

-- CONTRAST (the r=2 rung's object): the prescribed readout consumed by
-- `sym2RankinCoupling` is built from `cpsPolynomialPrimalCoeff W` against a kernel that
-- mentions only `C` and `μs` — so it is genuinely W-dependent.
open ConeProjection

example {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (C : ℝ) (μs : List ℂ)
    (x : ℝ) :
    cpsPolynomialFullPrimal3DBankReadout W C μs x =
      ∑' n : ℕ,
        fiberPhasor (coefficientFiber (cpsPolynomialPrimalCoeff W) n x) *
          conductorScaledCompletionKernelLog C μs
            (multiplicativeHeight (coefficientFiber (cpsPolynomialPrimalCoeff W) n x)) :=
  rfl
