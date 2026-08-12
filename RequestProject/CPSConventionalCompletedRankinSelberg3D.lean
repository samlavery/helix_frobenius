import RequestProject.CPSArithmeticStrongSource3D
import RequestProject.CarrierThetaDirichletInverseGrowth
import RequestProject.TransportClosure
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Conventional completed Rankin--Selberg sources for arithmetic CPS twists

This file gives a rigid, type-valued name to the completed Rankin--Selberg source already
constructed by the arithmetic reflected theta bank.  The conductor, archimedean shifts,
continuations, root number, and weight are projections of that same source; none is replaceable by
independent metadata.
-/

open Complex Set MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

/-- A conventional completed Rankin--Selberg source is the literal arithmetic reflected theta
source.  Keeping the source as data makes every completion parameter and every analytic property a
derived projection. -/
structure ConventionalCompletedRankinSelbergSource3D
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m))
    (D : ArithmeticCPSCompletionData r m) where
  source : ArithmeticCPSReflectedThetaSource r m pi tau D

namespace ConventionalCompletedRankinSelbergSource3D

variable {r m : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
  {tau : PolynomialSatakeDualPair (Fin m)}
  {D : ArithmeticCPSCompletionData r m}

/-- The arithmetic conductor of the completed tensor product. -/
def conductor (_L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) : ℝ :=
  D.conductor

/-- The tensor-product archimedean shifts of the completed tensor product. -/
noncomputable def gammaShifts
    (_L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) : List ℂ :=
  D.tensorShifts

/-- The completed primal Rankin--Selberg continuation. -/
noncomputable def completed
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) : ℂ → ℂ :=
  L.source.pair.Λ

/-- The completed contragredient Rankin--Selberg continuation. -/
noncomputable def completedDual
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) : ℂ → ℂ :=
  L.source.pair.symm.Λ

/-- The root number in the source functional equation. -/
noncomputable def rootNumber
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) : ℂ :=
  L.source.pair.ε

/-- The reflection weight in the source functional equation. -/
noncomputable def weight
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) : ℝ :=
  L.source.pair.k

/-- Package a reflected arithmetic theta source without changing any of its data. -/
def ofReflectedThetaSource
    (S : ArithmeticCPSReflectedThetaSource r m pi tau D) :
    ConventionalCompletedRankinSelbergSource3D r m pi tau D :=
  ⟨S⟩

/-- On the initial half-plane, the continuation is the literal conductor/Gamma completed Euler
readout of the arithmetic tensor twist. -/
theorem completed_initialIdentification
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (hm : 0 < m)
    (point : CPSCompletionPoint (arithmeticCPSPolynomialTwist r m pi tau) (D.clock hm)) :
    L.completed point.s =
      cpsPolynomialFullPrimalCompletedReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        L.conductor L.gammaShifts point.s := by
  exact L.source.primal_initialIdentification hm point

/-- The dual continuation has the literal completed contragredient Euler readout on the same
initial half-plane. -/
theorem completedDual_initialIdentification
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (hm : 0 < m)
    (point : CPSCompletionPoint (arithmeticCPSPolynomialTwist r m pi tau) (D.clock hm)) :
    L.completedDual point.s =
      cpsPolynomialFullDualCompletedReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        L.conductor L.gammaShifts point.s := by
  exact L.source.dual_initialIdentification hm point

/-- The completed Rankin--Selberg continuation is entire. -/
theorem completed_entire
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) :
    Differentiable ℂ L.completed :=
  L.source.pair.differentiable_Λ

/-- The completed contragredient continuation is entire. -/
theorem completedDual_entire
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) :
    Differentiable ℂ L.completedDual :=
  L.source.pair.symm.differentiable_Λ

/-- Uniform boundedness of the primal completion on every closed vertical strip. -/
theorem completed_boundedOn_verticalStrip
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (u v : ℝ) : ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖L.completed s‖ ≤ B :=
  CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
    L.source.pair u v

/-- Uniform boundedness of the dual completion on every closed vertical strip. -/
theorem completedDual_boundedOn_verticalStrip
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (u v : ℝ) : ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖L.completedDual s‖ ≤ B :=
  CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
    L.source.pair.symm u v

/-- The conventional completed functional equation, with the root number and weight read from the
same arithmetic source. -/
theorem functionalEquation
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) (s : ℂ) :
    L.completed (L.weight - s) = L.rootNumber • L.completedDual s :=
  L.source.pair.functional_equation s

/-- The root number is nonzero. -/
theorem rootNumber_ne_zero
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) :
    L.rootNumber ≠ 0 :=
  L.source.pair.hε

/-- The reflection weight is positive. -/
theorem weight_pos
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) :
    0 < L.weight :=
  L.source.pair.hk

/-- The conventional source recovers the exact analytic candidate consumed by the arithmetic CPS
converse construction. -/
noncomputable def analyticCandidate
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) :
    ArithmeticCPSAnalyticCandidate3D r m pi tau D :=
  L.source.analyticCandidate

/-- The positive-indexed arithmetic coefficients of the uncompleted Rankin--Selberg Euler
product. -/
noncomputable def arithmeticCoefficient
    (_L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) : ArithmeticFunction ℂ :=
  CarrierTheta.coefficientArithmetic
    (cpsPolynomialPrimalCoeff (arithmeticCPSPolynomialTwist r m pi tau))

/-- A concrete right half-plane on which the uncompleted Euler readout and its derivative converge
absolutely. -/
noncomputable def eulerConvergenceThreshold
    (_L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) : ℝ :=
  ((Fintype.card (CPSTensorIndex r m) +
    (arithmeticCPSPolynomialTwist r m pi tau).primalExponent : ℕ) : ℝ) + 1

/-- The uncompleted Rankin--Selberg Euler/Dirichlet readout attached to the same Satake bank as the
completed source. -/
noncomputable def uncompletedEuler
    (_L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) : ℂ → ℂ :=
  CarrierTheta.dirichlet
    (cpsPolynomialPrimalCoeff (arithmeticCPSPolynomialTwist r m pi tau))

/-- Absolute summability of the arithmetic Rankin--Selberg coefficients on the concrete initial
half-plane. -/
theorem arithmeticCoefficient_summable
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) {s : ℂ}
    (hs : L.eulerConvergenceThreshold < s.re) :
    LSeriesSummable (⇑L.arithmeticCoefficient) s := by
  refine LSeriesSummable_of_le_const_mul_rpow
    (x := L.eulerConvergenceThreshold) hs ⟨1, fun n hn => ?_⟩
  calc
    ‖L.arithmeticCoefficient n‖ ≤
        1 * (n : ℝ) ^
          (Fintype.card (CPSTensorIndex r m) +
            (arithmeticCPSPolynomialTwist r m pi tau).primalExponent : ℕ) :=
      cpsPolynomialPrimalArithmetic_norm_le
        (arithmeticCPSPolynomialTwist r m pi tau) n
    _ = 1 * (n : ℝ) ^
        (((Fintype.card (CPSTensorIndex r m) +
          (arithmeticCPSPolynomialTwist r m pi tau).primalExponent : ℕ) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    _ = 1 * (n : ℝ) ^ (L.eulerConvergenceThreshold - 1) := by
      simp [eulerConvergenceThreshold]

/-- The abscissa of absolute convergence is bounded by the explicit polynomial-growth
threshold. -/
theorem arithmeticCoefficient_abscissa_le
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) :
    LSeries.abscissaOfAbsConv (⇑L.arithmeticCoefficient) ≤ L.eulerConvergenceThreshold := by
  exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    (fun y hy => L.arithmeticCoefficient_summable hy)

/-- On its absolute-convergence half-plane, the zero-indexed carrier readout is exactly the
standard positive-indexed `LSeries`. -/
theorem uncompletedEuler_eq_LSeries
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) {s : ℂ}
    (hs : L.eulerConvergenceThreshold < s.re) :
    L.uncompletedEuler s = LSeries (⇑L.arithmeticCoefficient) s := by
  have hcoeff :
      cpsPolynomialPrimalCoeff (arithmeticCPSPolynomialTwist r m pi tau) =
        fun j => L.arithmeticCoefficient (j + 1) := by
    funext j
    simp [arithmeticCoefficient, CarrierTheta.coefficientArithmetic]
  rw [uncompletedEuler, hcoeff]
  exact CriticalLinePhasor.TransportClosure.dirichlet_shift_eq_LSeries
    L.arithmeticCoefficient (L.arithmeticCoefficient_summable hs)

/-- The derivative of the uncompleted Euler readout is the Dirichlet series obtained by
multiplying every arithmetic coefficient by `-log n`. -/
theorem uncompletedEuler_hasDerivAt
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) {s : ℂ}
    (hs : L.eulerConvergenceThreshold < s.re) :
    HasDerivAt L.uncompletedEuler
      (-LSeries (LSeries.logMul (⇑L.arithmeticCoefficient)) s) s := by
  have habs : LSeries.abscissaOfAbsConv (⇑L.arithmeticCoefficient) < s.re :=
    L.arithmeticCoefficient_abscissa_le.trans_lt (EReal.coe_lt_coe_iff.mpr hs)
  have heq : L.uncompletedEuler =ᶠ[nhds s] LSeries (⇑L.arithmeticCoefficient) := by
    have hopen : IsOpen {z : ℂ | L.eulerConvergenceThreshold < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact L.uncompletedEuler_eq_LSeries hz
  exact (LSeries_hasDerivAt habs).congr_of_eventuallyEq heq

/-- Pointwise derivative identity for the uncompleted arithmetic Euler readout. -/
theorem uncompletedEuler_deriv
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) {s : ℂ}
    (hs : L.eulerConvergenceThreshold < s.re) :
    deriv L.uncompletedEuler s =
      -LSeries (LSeries.logMul (⇑L.arithmeticCoefficient)) s :=
  (L.uncompletedEuler_hasDerivAt hs).deriv

/-- Exact logarithmic-derivative coefficient identity on the initial half-plane.  No
nonvanishing premise is needed because `logDeriv` is definitionally `deriv / value`. -/
theorem neg_logDeriv_uncompletedEuler
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) {s : ℂ}
    (hs : L.eulerConvergenceThreshold < s.re) :
    -logDeriv L.uncompletedEuler s =
      LSeries (LSeries.logMul (⇑L.arithmeticCoefficient)) s / L.uncompletedEuler s := by
  rw [logDeriv_apply, L.uncompletedEuler_deriv hs]
  ring

/-- The canonical inverse of the positive-indexed arithmetic coefficient at `1`. -/
@[reducible] noncomputable def arithmeticCoefficientOneInvertible
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) :
    Invertible (L.arithmeticCoefficient 1) := by
  simpa [arithmeticCoefficient] using
    cpsPolynomialPrimalOneInvertible (arithmeticCPSPolynomialTwist r m pi tau)

/-- The coefficient function `n ↦ log(n) A(n)` occurring in the derivative of an Euler
`L`-series. -/
noncomputable def weightedArithmeticCoefficient
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) : ArithmeticFunction ℂ where
  toFun n := Complex.log n * L.arithmeticCoefficient n
  map_zero' := by simp

/-- Polynomial growth data for the canonically constructed Dirichlet inverse.  This is data
derived from the source coefficient bound, not an analytic hypothesis. -/
structure DirichletInverseGrowthData
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) where
  exponent : ℕ
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  bound : ∀ n : ℕ+,
    ‖(ArithmeticFunction.dirichletInverse L.arithmeticCoefficient
      L.arithmeticCoefficientOneInvertible) n‖ ≤ constant * ((n : ℕ) : ℝ) ^ exponent

/-- Construct the inverse growth data from the already proved polynomial Satake bound. -/
noncomputable def dirichletInverseGrowthData
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) :
    DirichletInverseGrowthData L := by
  let h :=
    CarrierTheta.dirichletInverse_polynomial_bound
      L.arithmeticCoefficient L.arithmeticCoefficientOneInvertible
      (Fintype.card (CPSTensorIndex r m) +
        (arithmeticCPSPolynomialTwist r m pi tau).primalExponent)
      1 zero_le_one (by
        intro n
        simpa [arithmeticCoefficient] using
          cpsPolynomialPrimalArithmetic_norm_le
            (arithmeticCPSPolynomialTwist r m pi tau) n)
  let B := Classical.choose h
  let hB := Classical.choose_spec h
  let C := Classical.choose hB
  let hC := Classical.choose_spec hB
  exact ⟨B, C, hC.1, hC.2⟩

/-- The arithmetic-function Dirichlet inverse of the Rankin--Selberg coefficients. -/
noncomputable def inverseArithmeticCoefficient
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) : ArithmeticFunction ℂ :=
  ArithmeticFunction.dirichletInverse
    L.arithmeticCoefficient L.arithmeticCoefficientOneInvertible

/-- The generalized von Mangoldt coefficients of the Rankin--Selberg Euler product. -/
noncomputable def logarithmicCoefficient
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) : ArithmeticFunction ℂ :=
  L.weightedArithmeticCoefficient * L.inverseArithmeticCoefficient

/-- A concrete common half-plane for the coefficient series, its logarithmic weighting, and its
Dirichlet inverse. -/
noncomputable def logDerivativeConvergenceThreshold
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) : ℝ :=
  max L.eulerConvergenceThreshold ((L.dirichletInverseGrowthData.exponent : ℝ) + 1)

/-- Absolute convergence of the logarithmically weighted coefficient series. -/
theorem weightedArithmeticCoefficient_summable
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) {s : ℂ}
    (hs : L.logDerivativeConvergenceThreshold < s.re) :
    LSeriesSummable (⇑L.weightedArithmeticCoefficient) s := by
  have heuler : L.eulerConvergenceThreshold < s.re :=
    (le_max_left _ _).trans_lt hs
  have habs : LSeries.abscissaOfAbsConv (⇑L.arithmeticCoefficient) < s.re :=
    L.arithmeticCoefficient_abscissa_le.trans_lt (EReal.coe_lt_coe_iff.mpr heuler)
  simpa [weightedArithmeticCoefficient, LSeries.logMul] using
    LSeriesSummable_logMul_of_lt_re habs

/-- Absolute convergence of the constructed Dirichlet inverse. -/
theorem inverseArithmeticCoefficient_summable
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) {s : ℂ}
    (hs : L.logDerivativeConvergenceThreshold < s.re) :
    LSeriesSummable (⇑L.inverseArithmeticCoefficient) s := by
  have hinv : (L.dirichletInverseGrowthData.exponent : ℝ) + 1 < s.re :=
    (le_max_right _ _).trans_lt hs
  refine LSeriesSummable_of_le_const_mul_rpow
    (x := (L.dirichletInverseGrowthData.exponent : ℝ) + 1) hinv
    ⟨L.dirichletInverseGrowthData.constant, fun n hn => ?_⟩
  have hbound := L.dirichletInverseGrowthData.bound
    (⟨n, Nat.pos_of_ne_zero hn⟩ : ℕ+)
  simpa [inverseArithmeticCoefficient, Real.rpow_natCast] using hbound

/-- The weighted arithmetic function is definitionally the coefficient sequence `logMul` used by
the derivative theorem. -/
theorem weightedArithmeticCoefficient_eq_logMul
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) (n : ℕ) :
    L.weightedArithmeticCoefficient n =
      LSeries.logMul (⇑L.arithmeticCoefficient) n :=
  rfl

/-- Absolute convergence of the generalized von Mangoldt coefficient series. -/
theorem logarithmicCoefficient_summable
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) {s : ℂ}
    (hs : L.logDerivativeConvergenceThreshold < s.re) :
    LSeriesSummable (⇑L.logarithmicCoefficient) s := by
  exact ArithmeticFunction.LSeriesSummable_mul
    (L.weightedArithmeticCoefficient_summable hs)
    (L.inverseArithmeticCoefficient_summable hs)

/-- The Dirichlet series of the generalized von Mangoldt coefficients is exactly the negative
logarithmic derivative of the source Euler product. -/
theorem LSeries_logarithmicCoefficient_eq_neg_logDeriv
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) {s : ℂ}
    (hs : L.logDerivativeConvergenceThreshold < s.re) :
    LSeries (⇑L.logarithmicCoefficient) s = -logDeriv L.uncompletedEuler s := by
  have heuler : L.eulerConvergenceThreshold < s.re :=
    (le_max_left _ _).trans_lt hs
  have hA := L.arithmeticCoefficient_summable heuler
  have hW := L.weightedArithmeticCoefficient_summable hs
  have hI := L.inverseArithmeticCoefficient_summable hs
  have hprod :
      LSeries (⇑L.inverseArithmeticCoefficient) s *
          LSeries (⇑L.arithmeticCoefficient) s = 1 := by
    rw [← ArithmeticFunction.LSeries_mul' hI hA]
    rw [inverseArithmeticCoefficient, ArithmeticFunction.dirichletInverse_mul_self]
    simp [ArithmeticFunction.one_eq_delta, LSeries_delta]
  have hAne : LSeries (⇑L.arithmeticCoefficient) s ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hprod
    exact zero_ne_one hprod
  have hquot :
      LSeries (⇑L.logarithmicCoefficient) s =
        LSeries (LSeries.logMul (⇑L.arithmeticCoefficient)) s /
          LSeries (⇑L.arithmeticCoefficient) s := by
    rw [logarithmicCoefficient, ArithmeticFunction.LSeries_mul' hW hI]
    apply (eq_div_iff hAne).2
    calc
      (LSeries (⇑L.weightedArithmeticCoefficient) s *
          LSeries (⇑L.inverseArithmeticCoefficient) s) *
            LSeries (⇑L.arithmeticCoefficient) s =
          LSeries (⇑L.weightedArithmeticCoefficient) s *
            (LSeries (⇑L.inverseArithmeticCoefficient) s *
              LSeries (⇑L.arithmeticCoefficient) s) := by ring
      _ = LSeries (⇑L.weightedArithmeticCoefficient) s := by rw [hprod, mul_one]
      _ = LSeries (LSeries.logMul (⇑L.arithmeticCoefficient)) s := by
        exact LSeries_congr (fun _ => L.weightedArithmeticCoefficient_eq_logMul _) s
  calc
    LSeries (⇑L.logarithmicCoefficient) s =
        LSeries (LSeries.logMul (⇑L.arithmeticCoefficient)) s /
          LSeries (⇑L.arithmeticCoefficient) s := hquot
    _ = LSeries (LSeries.logMul (⇑L.arithmeticCoefficient)) s /
          L.uncompletedEuler s := by rw [L.uncompletedEuler_eq_LSeries heuler]
    _ = -logDeriv L.uncompletedEuler s := (L.neg_logDeriv_uncompletedEuler heuler).symm

/-- Exact prime-power expansion of the generalized von Mangoldt coefficient.  Every term is a
local Euler coefficient convolved with the canonically constructed local inverse. -/
theorem logarithmicCoefficient_prime_pow_expansion
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    {p : ℕ} (hp : p.Prime) (j : ℕ) :
    L.logarithmicCoefficient (p ^ j) =
      ∑ a ∈ Finset.range (j + 1),
        (Complex.log (p ^ a) *
            radialLocalEulerCoeff
              ((arithmeticCPSPolynomialTwist r m pi tau).primal ⟨p, hp⟩) a) *
          L.inverseArithmeticCoefficient (p ^ (j - a)) := by
  rw [logarithmicCoefficient,
    CriticalLinePhasor.TransportClosure.mul_apply_prime_pow _ _ hp]
  refine Finset.sum_congr rfl fun a ha => ?_
  dsimp [weightedArithmeticCoefficient]
  rw [show L.arithmeticCoefficient (p ^ a) =
      radialLocalEulerCoeff
        ((arithmeticCPSPolynomialTwist r m pi tau).primal ⟨p, hp⟩) a by
    simpa [arithmeticCoefficient, cpsPolynomialPrimalCoeff] using
      CriticalLinePhasor.TransportClosure.bankArithmetic_prime_pow
        (arithmeticCPSPolynomialTwist r m pi tau).primal hp a]
  rw [Nat.cast_pow]

end ConventionalCompletedRankinSelbergSource3D

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.ofReflectedThetaSource
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.completed_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.completedDual_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.functionalEquation
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.analyticCandidate
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.arithmeticCoefficient_summable
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.uncompletedEuler_eq_LSeries
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.uncompletedEuler_hasDerivAt
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.neg_logDeriv_uncompletedEuler
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.dirichletInverseGrowthData
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.logarithmicCoefficient_summable
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.LSeries_logarithmicCoefficient_eq_neg_logDeriv
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.logarithmicCoefficient_prime_pow_expansion
