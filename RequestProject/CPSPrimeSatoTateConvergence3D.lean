import RequestProject.CPSRadialSatoTateGeometry3D
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.UniformOn

/-!
# Empirical prime measures on the three-dimensional Sato--Tate carrier

For a Satake-angle assignment on primes, the `N`th empirical measure below is the uniform
probability measure on the first `N + 1` canonical primes, pushed first to the angle line and then
to the native three-dimensional carrier.  The main theorem is the continuous-mapping theorem in
this concrete setting: prime-angle equidistribution converges to the Sato--Tate angle law if and
only if its native carrier realization converges to the carrier law (the reverse implication uses
the global coordinate, which is a left inverse of the carrier parametrization).
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BoundedContinuousFunction ENNReal

namespace CriticalLinePhasor.SatoTateCarrier3D

/-- The `n`th prime as a member of the subtype of prime natural numbers. -/
noncomputable def nthPrime (n : ℕ) : Nat.Primes :=
  ⟨Nat.nth Nat.Prime n, Nat.prime_nth_prime n⟩

/-- The uniform probability measure on a nonempty initial finite index space. -/
noncomputable def finiteUniformProbability (n : ℕ) : ProbabilityMeasure (Fin (n + 1)) :=
  ⟨uniformOn Set.univ, inferInstance⟩

/-- The empirical measure of the Satake angles at the first `n + 1` primes. -/
noncomputable def empiricalPrimeAngleMeasure
    (angle : Nat.Primes → ℝ) (n : ℕ) : ProbabilityMeasure ℝ :=
  (finiteUniformProbability n).map
    (measurable_of_finite (fun i : Fin (n + 1) => angle (nthPrime i))).aemeasurable

/-- The empirical prime measure lifted to the native three-dimensional helix. -/
noncomputable def empiricalPrimeCarrierMeasure
    (angle : Nat.Primes → ℝ) (n : ℕ) : ProbabilityMeasure (ℝ × ℝ × ℝ) :=
  (empiricalPrimeAngleMeasure angle n).map continuous_point.measurable.aemeasurable

/-- The normalized Sato--Tate angle law as a probability measure. -/
noncomputable def angleProbability : ProbabilityMeasure ℝ :=
  ⟨angleMeasure, angleMeasure_isProbability⟩

/-- The native three-dimensional Sato--Tate law as a probability measure. -/
noncomputable def carrierProbability : ProbabilityMeasure (ℝ × ℝ × ℝ) :=
  ⟨carrierMeasure, carrierMeasure_isProbability⟩

/-- The literal average of a bounded continuous test function over the Satake angles at the first
`n + 1` canonical primes. -/
noncomputable def primeTestAverage
    (angle : Nat.Primes → ℝ) (n : ℕ) (f : ℝ →ᵇ ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n + 1), f (angle (nthPrime i))

/-- Integration against the empirical prime-angle probability measure is exactly the literal
finite average over the first `n + 1` primes. -/
theorem integral_empiricalPrimeAngleMeasure
    (angle : Nat.Primes → ℝ) (n : ℕ) (f : ℝ →ᵇ ℝ) :
    ∫ theta, f theta ∂(empiricalPrimeAngleMeasure angle n : Measure ℝ) =
      primeTestAverage angle n f := by
  have hcast : ((n : ℝ≥0∞) + 1).toReal = (n : ℝ) + 1 := by
    norm_cast
  rw [empiricalPrimeAngleMeasure, ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_of_finite
      (fun i : Fin (n + 1) => angle (nthPrime i))).aemeasurable
      f.continuous.aestronglyMeasurable]
  simp [finiteUniformProbability, uniformOn, ProbabilityTheory.cond,
    primeTestAverage, ENNReal.toReal_inv, hcast]

/-- Standard arithmetic boundary for prime equidistribution: every bounded continuous test
function has its canonical first-prime average converge to its Sato--Tate integral. -/
structure PrimeSatoTateTestAverageInput where
  angle : Nat.Primes → ℝ
  test_average_tendsto : ∀ f : ℝ →ᵇ ℝ,
    Tendsto (fun n => primeTestAverage angle n f) atTop
      (𝓝 (∫ theta, f theta ∂angleMeasure))

/-- Typed arithmetic input: the empirical measures of a prime-indexed Satake-angle assignment
converge weakly to the normalized Sato--Tate angle law. -/
structure EmpiricalPrimeSatoTate where
  angle : Nat.Primes → ℝ
  angle_tendsto :
    Tendsto (empiricalPrimeAngleMeasure angle) atTop (𝓝 angleProbability)

/-- The standard test-average prime-equidistribution boundary constructs the probability-measure
form of empirical Sato--Tate convergence. -/
noncomputable def empiricalPrimeSatoTate_of_testAverages
    (input : PrimeSatoTateTestAverageInput) : EmpiricalPrimeSatoTate where
  angle := input.angle
  angle_tendsto := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    rw [show (∫ theta, f theta ∂(angleProbability : Measure ℝ)) =
      ∫ theta, f theta ∂angleMeasure from rfl]
    simpa only [integral_empiricalPrimeAngleMeasure] using input.test_average_tendsto f

/-- The native carrier probability law is exactly the pushforward of the angle probability law. -/
theorem angleProbability_map_point :
    angleProbability.map continuous_point.measurable.aemeasurable = carrierProbability := by
  apply ProbabilityMeasure.toMeasure_injective
  rfl

/-- The global-coordinate pushforward of the native carrier probability law recovers the angle
probability law. -/
theorem carrierProbability_map_globalCoordinate :
    carrierProbability.map continuous_globalCoordinate.measurable.aemeasurable =
      angleProbability := by
  apply ProbabilityMeasure.toMeasure_injective
  exact map_globalCoordinate_carrierMeasure

/-- Empirical prime Sato--Tate convergence on angles produces weak convergence of the actual
prime empirical measures on the native three-dimensional helix. -/
theorem empiricalPrimeCarrierMeasure_tendsto (data : EmpiricalPrimeSatoTate) :
    Tendsto (empiricalPrimeCarrierMeasure data.angle) atTop (𝓝 carrierProbability) := by
  rw [← angleProbability_map_point]
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => empiricalPrimeAngleMeasure data.angle n) angleProbability
    data.angle_tendsto continuous_point

/-- Direct 3D form of the standard arithmetic boundary: convergence of all canonical prime test
averages produces weak convergence of the empirical prime measures on the native carrier. -/
theorem empiricalPrimeCarrierMeasure_tendsto_of_testAverages
    (input : PrimeSatoTateTestAverageInput) :
    Tendsto (empiricalPrimeCarrierMeasure input.angle) atTop (𝓝 carrierProbability) :=
  empiricalPrimeCarrierMeasure_tendsto (empiricalPrimeSatoTate_of_testAverages input)

/-- The global coordinate recovers every empirical angle measure exactly from its 3D lift. -/
theorem empiricalPrimeCarrierMeasure_map_globalCoordinate
    (angle : Nat.Primes → ℝ) (n : ℕ) :
    (empiricalPrimeCarrierMeasure angle n).map
        continuous_globalCoordinate.measurable.aemeasurable =
      empiricalPrimeAngleMeasure angle n := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [empiricalPrimeCarrierMeasure, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map,
    Measure.map_map continuous_globalCoordinate.measurable continuous_point.measurable]
  simpa only [Function.comp_def, globalCoordinate_point] using
    (Measure.map_id' (μ := (empiricalPrimeAngleMeasure angle n).toMeasure))

/-- The 3D empirical-prime convergence statement is equivalent to the angle statement because
the carrier has the global coordinate as a continuous left inverse. -/
theorem empiricalPrimeCarrierMeasure_tendsto_iff (angle : Nat.Primes → ℝ) :
    Tendsto (empiricalPrimeCarrierMeasure angle) atTop (𝓝 carrierProbability) ↔
      Tendsto (empiricalPrimeAngleMeasure angle) atTop (𝓝 angleProbability) := by
  constructor
  · intro hcarrier
    have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => empiricalPrimeCarrierMeasure angle n) carrierProbability
      hcarrier continuous_globalCoordinate
    simpa only [empiricalPrimeCarrierMeasure_map_globalCoordinate,
      carrierProbability_map_globalCoordinate] using hmap
  · intro hangle
    rw [← angleProbability_map_point]
    exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => empiricalPrimeAngleMeasure angle n) angleProbability hangle continuous_point

end CriticalLinePhasor.SatoTateCarrier3D

#print axioms CriticalLinePhasor.SatoTateCarrier3D.empiricalPrimeCarrierMeasure_tendsto
#print axioms CriticalLinePhasor.SatoTateCarrier3D.integral_empiricalPrimeAngleMeasure
#print axioms CriticalLinePhasor.SatoTateCarrier3D.empiricalPrimeSatoTate_of_testAverages
#print axioms CriticalLinePhasor.SatoTateCarrier3D.empiricalPrimeCarrierMeasure_tendsto_of_testAverages
#print axioms CriticalLinePhasor.SatoTateCarrier3D.empiricalPrimeCarrierMeasure_tendsto_iff
