import RequestProject.CPSConventionalCompletedRankinSelberg3D
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Local Euler power series and their logarithmic derivatives

The local complete-homogeneous coefficient bank is realized as a finite product of geometric
formal power series.  Its reciprocal is the literal Satake Euler polynomial.  These identities
provide the algebraic input for the prime-power coefficients of the Rankin--Selberg logarithmic
derivative.
-/

open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

open ConventionalCompletedRankinSelbergSource3D

/-- The geometric Euler series `1 + zX + z²X² + ...`. -/
noncomputable def geometricEulerSeries (z : ℂ) : PowerSeries ℂ :=
  PowerSeries.rescale z (PowerSeries.mk 1)

/-- The linear reciprocal of `geometricEulerSeries z`. -/
noncomputable def linearEulerFactor (z : ℂ) : PowerSeries ℂ :=
  1 - PowerSeries.C z * PowerSeries.X

/-- Coefficients of the geometric Euler series. -/
theorem coeff_geometricEulerSeries (z : ℂ) (n : ℕ) :
    PowerSeries.coeff n (geometricEulerSeries z) = z ^ n := by
  simp [geometricEulerSeries]

/-- The geometric Euler series and its linear Euler factor multiply to one. -/
theorem geometricEulerSeries_mul_linearEulerFactor (z : ℂ) :
    geometricEulerSeries z * linearEulerFactor z = 1 := by
  have h := congrArg (PowerSeries.rescale z)
    (PowerSeries.mk_one_mul_one_sub_eq_one (S := ℂ))
  simpa [geometricEulerSeries, linearEulerFactor, PowerSeries.rescale_mk,
    PowerSeries.rescale_X] using h

/-- The finite local Euler power series of a Satake root packet. -/
noncomputable def localEulerPowerSeries
    {ι : Type*} [Fintype ι] (w : ι → ℂ) : PowerSeries ℂ :=
  ∏ i, geometricEulerSeries (w i)

/-- The reciprocal Satake polynomial, regarded as a formal power series. -/
noncomputable def localEulerReciprocalSeries
    {ι : Type*} [Fintype ι] (w : ι → ℂ) : PowerSeries ℂ :=
  ∏ i, linearEulerFactor (w i)

/-- The coefficient of the local Euler power series is exactly the repository's
complete-homogeneous local coefficient. -/
theorem coeff_localEulerPowerSeries
    {ι : Type*} [Fintype ι] (w : ι → ℂ) (n : ℕ) :
    PowerSeries.coeff n (localEulerPowerSeries w) = radialLocalEulerCoeff w n := by
  classical
  rw [localEulerPowerSeries, radialLocalEulerCoeff]
  rw [show (∏ i, geometricEulerSeries (w i)) =
      ∏ i ∈ (Finset.univ : Finset ι), geometricEulerSeries (w i) by simp]
  rw [PowerSeries.coeff_prod]
  apply Finset.sum_congr rfl
  intro l hl
  simp [coeff_geometricEulerSeries]

/-- The full local Euler series and the literal reciprocal Satake polynomial multiply to one. -/
theorem localEulerPowerSeries_mul_reciprocal
    {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    localEulerPowerSeries w * localEulerReciprocalSeries w = 1 := by
  classical
  rw [localEulerPowerSeries, localEulerReciprocalSeries, ← Finset.prod_mul_distrib]
  simp [geometricEulerSeries_mul_linearEulerFactor]

/-- The formal logarithmic derivative of one geometric local factor. -/
theorem derivative_geometricEulerSeries_mul_linearEulerFactor (z : ℂ) :
    PowerSeries.derivativeFun (geometricEulerSeries z) * linearEulerFactor z =
      PowerSeries.C z * geometricEulerSeries z := by
  have hprod := geometricEulerSeries_mul_linearEulerFactor z
  have hder := congrArg PowerSeries.derivativeFun hprod
  have hlinear : PowerSeries.derivativeFun (linearEulerFactor z) = -PowerSeries.C z := by
    ext n
    cases n <;>
    simp [PowerSeries.coeff_derivativeFun, linearEulerFactor]
  rw [PowerSeries.derivativeFun_mul, hlinear, PowerSeries.derivativeFun_one] at hder
  simp only [smul_eq_mul] at hder
  linear_combination hder

/-- Finite-product logarithmic derivative identity for a packet of local Satake roots. -/
theorem derivative_geometricEulerSeries_prod_mul_linearEulerFactor_prod
    {ι : Type*} (s : Finset ι) (w : ι → ℂ) :
    PowerSeries.derivativeFun (∏ i ∈ s, geometricEulerSeries (w i)) *
        (∏ i ∈ s, linearEulerFactor (w i)) =
      ∑ i ∈ s, PowerSeries.C (w i) * geometricEulerSeries (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PowerSeries.derivativeFun_one]
  | @insert a s ha ih =>
      have hrecip :
          (∏ i ∈ s, geometricEulerSeries (w i)) *
              (∏ i ∈ s, linearEulerFactor (w i)) = 1 := by
        rw [← Finset.prod_mul_distrib]
        simp [geometricEulerSeries_mul_linearEulerFactor]
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
        PowerSeries.derivativeFun_mul]
      simp only [smul_eq_mul]
      calc
        (geometricEulerSeries (w a) *
              PowerSeries.derivativeFun (∏ i ∈ s, geometricEulerSeries (w i)) +
            (∏ i ∈ s, geometricEulerSeries (w i)) *
              PowerSeries.derivativeFun (geometricEulerSeries (w a))) *
            (linearEulerFactor (w a) *
              ∏ i ∈ s, linearEulerFactor (w i)) =
            (PowerSeries.derivativeFun (geometricEulerSeries (w a)) *
                linearEulerFactor (w a)) *
                ((∏ i ∈ s, geometricEulerSeries (w i)) *
                  ∏ i ∈ s, linearEulerFactor (w i)) +
              (geometricEulerSeries (w a) * linearEulerFactor (w a)) *
                (PowerSeries.derivativeFun (∏ i ∈ s, geometricEulerSeries (w i)) *
                  ∏ i ∈ s, linearEulerFactor (w i)) := by ring
        _ = PowerSeries.C (w a) * geometricEulerSeries (w a) +
              ∑ i ∈ s, PowerSeries.C (w i) * geometricEulerSeries (w i) := by
          rw [derivative_geometricEulerSeries_mul_linearEulerFactor,
            hrecip, ih, geometricEulerSeries_mul_linearEulerFactor,
            one_mul, mul_one]

/-- The formal logarithmic derivative of the complete local Euler packet is the Satake power-sum
generating series. -/
theorem derivative_localEulerPowerSeries_mul_reciprocal
    {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    PowerSeries.derivativeFun (localEulerPowerSeries w) *
        localEulerReciprocalSeries w =
      ∑ i, PowerSeries.C (w i) * geometricEulerSeries (w i) := by
  simpa [localEulerPowerSeries, localEulerReciprocalSeries] using
    derivative_geometricEulerSeries_prod_mul_linearEulerFactor_prod
      (Finset.univ : Finset ι) w

/-- Coefficientwise local Newton identity: the logarithmic derivative coefficient is the next
Satake power sum. -/
theorem coeff_derivative_localEulerPowerSeries_mul_reciprocal
    {ι : Type*} [Fintype ι] (w : ι → ℂ) (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.derivativeFun (localEulerPowerSeries w) *
          localEulerReciprocalSeries w) =
      ∑ i, w i ^ (n + 1) := by
  rw [derivative_localEulerPowerSeries_mul_reciprocal]
  simp [coeff_geometricEulerSeries, pow_succ']

/-- The formal series of the values of an arithmetic function on powers of one prime. -/
noncomputable def primePowerSeries (A : ArithmeticFunction ℂ) (p : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => A (p ^ n)

@[simp] theorem coeff_primePowerSeries
    (A : ArithmeticFunction ℂ) (p n : ℕ) :
    PowerSeries.coeff n (primePowerSeries A p) = A (p ^ n) := by
  simp [primePowerSeries]

/-- Dirichlet convolution restricts at a prime to the Cauchy product of prime-power series. -/
theorem primePowerSeries_mul
    (A B : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) :
    primePowerSeries A p * primePowerSeries B p = primePowerSeries (A * B) p := by
  ext n
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_primePowerSeries]
  exact (CriticalLinePhasor.TransportClosure.mul_apply_prime_pow A B hp n).symm

/-- The prime-power series of the identity arithmetic function is the constant series one. -/
theorem primePowerSeries_one {p : ℕ} (hp : p.Prime) :
    primePowerSeries (1 : ArithmeticFunction ℂ) p = 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      simp [primePowerSeries, ArithmeticFunction.one_eq_delta,
        LSeries.delta, hp.ne_one]

/-- The Rankin--Selberg arithmetic coefficients at one prime form the local Satake Euler series. -/
theorem primePowerSeries_arithmeticCoefficient_eq_localEulerPowerSeries
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    {p : ℕ} (hp : p.Prime) :
    primePowerSeries L.arithmeticCoefficient p =
      localEulerPowerSeries
        ((arithmeticCPSPolynomialTwist r m pi tau).primal ⟨p, hp⟩) := by
  ext n
  rw [coeff_primePowerSeries, coeff_localEulerPowerSeries]
  simpa [arithmeticCoefficient, cpsPolynomialPrimalCoeff] using
    CriticalLinePhasor.TransportClosure.bankArithmetic_prime_pow
      (arithmeticCPSPolynomialTwist r m pi tau).primal hp n

/-- The canonical Dirichlet inverse at powers of a prime is exactly the reciprocal Satake
polynomial, not independent metadata. -/
theorem primePowerSeries_inverseArithmeticCoefficient_eq_localEulerReciprocalSeries
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    {p : ℕ} (hp : p.Prime) :
    primePowerSeries L.inverseArithmeticCoefficient p =
      localEulerReciprocalSeries
        ((arithmeticCPSPolynomialTwist r m pi tau).primal ⟨p, hp⟩) := by
  let w := (arithmeticCPSPolynomialTwist r m pi tau).primal ⟨p, hp⟩
  have hAI :
      primePowerSeries L.arithmeticCoefficient p *
          primePowerSeries L.inverseArithmeticCoefficient p = 1 := by
    rw [primePowerSeries_mul _ _ hp, inverseArithmeticCoefficient,
      ArithmeticFunction.self_mul_dirichletInverse, primePowerSeries_one hp]
  have hHJ :
      localEulerPowerSeries w *
          primePowerSeries L.inverseArithmeticCoefficient p = 1 := by
    rw [← primePowerSeries_arithmeticCoefficient_eq_localEulerPowerSeries L hp]
    exact hAI
  have hPH : localEulerReciprocalSeries w * localEulerPowerSeries w = 1 := by
    rw [mul_comm, localEulerPowerSeries_mul_reciprocal]
  calc
    primePowerSeries L.inverseArithmeticCoefficient p =
        1 * primePowerSeries L.inverseArithmeticCoefficient p := by rw [one_mul]
    _ = (localEulerReciprocalSeries w * localEulerPowerSeries w) *
          primePowerSeries L.inverseArithmeticCoefficient p := by rw [hPH]
    _ = localEulerReciprocalSeries w *
          (localEulerPowerSeries w *
            primePowerSeries L.inverseArithmeticCoefficient p) := by ring
    _ = localEulerReciprocalSeries w := by rw [hHJ, mul_one]

/-- On positive real integers the complex logarithm respects ordinary natural powers. -/
theorem complex_log_nat_pow (p n : ℕ) :
    Complex.log ((p ^ n : ℕ) : ℂ) =
      (n : ℂ) * Complex.log (p : ℂ) := by
  calc
    Complex.log ((p ^ n : ℕ) : ℂ) =
        (Real.log (p ^ n : ℕ) : ℂ) := Complex.natCast_log.symm
    _ = ((n : ℝ) * Real.log (p : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
    _ = (n : ℂ) * Complex.log (p : ℂ) := by
      rw [← Complex.natCast_log]
      norm_cast

/-- Multiplication by `X` shifts a coefficient up by one. -/
theorem coeff_X_mul_succ (F : PowerSeries ℂ) (k : ℕ) :
    PowerSeries.coeff (k + 1) (PowerSeries.X * F) = PowerSeries.coeff k F := by
  simpa [Nat.add_comm] using PowerSeries.coeff_X_pow_mul F 1 k

/-- The coefficient of `X F'` is the index times the corresponding coefficient of `F`. -/
theorem coeff_X_mul_derivativeFun (F : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivativeFun F) =
      (n : ℂ) * PowerSeries.coeff n F := by
  cases n with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ k =>
      rw [show k + 1 = Nat.succ k by omega, coeff_X_mul_succ,
        PowerSeries.coeff_derivativeFun]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

/-- The logarithmically weighted Rankin--Selberg coefficients at one prime are the formal
derivative of the local Euler series, shifted once and scaled by `log p`. -/
theorem primePowerSeries_weightedArithmeticCoefficient_eq_derivative
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    {p : ℕ} (hp : p.Prime) :
    primePowerSeries L.weightedArithmeticCoefficient p =
      PowerSeries.C (Complex.log (p : ℂ)) *
        (PowerSeries.X * PowerSeries.derivativeFun
          (localEulerPowerSeries
            ((arithmeticCPSPolynomialTwist r m pi tau).primal ⟨p, hp⟩))) := by
  let pp : Nat.Primes := ⟨p, hp⟩
  let w := (arithmeticCPSPolynomialTwist r m pi tau).primal pp
  have hA := primePowerSeries_arithmeticCoefficient_eq_localEulerPowerSeries L hp
  ext n
  cases n with
  | zero => simp [primePowerSeries, weightedArithmeticCoefficient]
  | succ k =>
      have hcoeffA : L.arithmeticCoefficient (p ^ (k + 1)) =
          PowerSeries.coeff (k + 1) (localEulerPowerSeries w) := by
        have := congrArg (PowerSeries.coeff (k + 1)) hA
        simpa [w] using this
      rw [coeff_primePowerSeries]
      dsimp [weightedArithmeticCoefficient]
      rw [complex_log_nat_pow, hcoeffA]
      rw [PowerSeries.coeff_C_mul, coeff_X_mul_derivativeFun]
      ring

/-- The prime-power generating series of the generalized von Mangoldt coefficients is the
shifted local logarithmic derivative. -/
theorem primePowerSeries_logarithmicCoefficient_eq_localLogDerivative
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    {p : ℕ} (hp : p.Prime) :
    primePowerSeries L.logarithmicCoefficient p =
      PowerSeries.C (Complex.log (p : ℂ)) *
        (PowerSeries.X * (PowerSeries.derivativeFun
            (localEulerPowerSeries
              ((arithmeticCPSPolynomialTwist r m pi tau).primal ⟨p, hp⟩)) *
          localEulerReciprocalSeries
            ((arithmeticCPSPolynomialTwist r m pi tau).primal ⟨p, hp⟩))) := by
  rw [show L.logarithmicCoefficient =
      L.weightedArithmeticCoefficient * L.inverseArithmeticCoefficient by
    rfl]
  rw [← primePowerSeries_mul _ _ hp,
    primePowerSeries_weightedArithmeticCoefficient_eq_derivative L hp,
    primePowerSeries_inverseArithmeticCoefficient_eq_localEulerReciprocalSeries L hp]
  ring

/-- Closed Satake formula for every positive prime-power generalized von Mangoldt coefficient. -/
theorem logarithmicCoefficient_prime_pow_eq_satakePowerSum
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    {p j : ℕ} (hp : p.Prime) (hj : 0 < j) :
    L.logarithmicCoefficient (p ^ j) =
      Complex.log (p : ℂ) *
        ∑ i : CPSTensorIndex r m,
          arithmeticCPSTensorRoot r m pi tau
            (show Nat.Primes from ⟨p, hp⟩) i ^ j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  let pp : Nat.Primes := ⟨p, hp⟩
  let w := (arithmeticCPSPolynomialTwist r m pi tau).primal pp
  have hseries :=
    primePowerSeries_logarithmicCoefficient_eq_localLogDerivative L hp
  have hcoeff := congrArg (PowerSeries.coeff (k + 1)) hseries
  have hnewton := coeff_derivative_localEulerPowerSeries_mul_reciprocal w k
  rw [coeff_primePowerSeries] at hcoeff
  calc
    L.logarithmicCoefficient (p ^ (k + 1)) =
        Complex.log (p : ℂ) *
          PowerSeries.coeff k
            (PowerSeries.derivativeFun (localEulerPowerSeries w) *
              localEulerReciprocalSeries w) := by
      rw [hcoeff]
      rw [PowerSeries.coeff_C_mul]
      rw [coeff_X_mul_succ]
    _ = Complex.log (p : ℂ) * ∑ i, w i ^ (k + 1) := by rw [hnewton]
    _ = Complex.log (p : ℂ) *
        ∑ i : CPSTensorIndex r m,
          arithmeticCPSTensorRoot r m pi tau pp i ^ (k + 1) := by
      rfl

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.coeff_geometricEulerSeries
#print axioms CriticalLinePhasor.GlobalHelix.geometricEulerSeries_mul_linearEulerFactor
#print axioms CriticalLinePhasor.GlobalHelix.coeff_localEulerPowerSeries
#print axioms CriticalLinePhasor.GlobalHelix.localEulerPowerSeries_mul_reciprocal
#print axioms CriticalLinePhasor.GlobalHelix.derivative_geometricEulerSeries_mul_linearEulerFactor
#print axioms CriticalLinePhasor.GlobalHelix.derivative_geometricEulerSeries_prod_mul_linearEulerFactor_prod
#print axioms CriticalLinePhasor.GlobalHelix.derivative_localEulerPowerSeries_mul_reciprocal
#print axioms CriticalLinePhasor.GlobalHelix.coeff_derivative_localEulerPowerSeries_mul_reciprocal
#print axioms CriticalLinePhasor.GlobalHelix.primePowerSeries_mul
#print axioms CriticalLinePhasor.GlobalHelix.primePowerSeries_one
#print axioms CriticalLinePhasor.GlobalHelix.primePowerSeries_arithmeticCoefficient_eq_localEulerPowerSeries
#print axioms CriticalLinePhasor.GlobalHelix.primePowerSeries_inverseArithmeticCoefficient_eq_localEulerReciprocalSeries
#print axioms CriticalLinePhasor.GlobalHelix.complex_log_nat_pow
#print axioms CriticalLinePhasor.GlobalHelix.coeff_X_mul_succ
#print axioms CriticalLinePhasor.GlobalHelix.coeff_X_mul_derivativeFun
#print axioms CriticalLinePhasor.GlobalHelix.primePowerSeries_weightedArithmeticCoefficient_eq_derivative
#print axioms CriticalLinePhasor.GlobalHelix.primePowerSeries_logarithmicCoefficient_eq_localLogDerivative
#print axioms CriticalLinePhasor.GlobalHelix.logarithmicCoefficient_prime_pow_eq_satakePowerSum
