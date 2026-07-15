import RequestProject.CPSPrimeSatoTateConvergence3D
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Sato--Tate convergence from symmetric-power character averages

This file replaces the all-continuous-test input by the standard symmetric-power character
boundary.  The rescaled second-kind Chebyshev polynomial is the `SU(2)` character, and these
characters span every polynomial in the trace coordinate.  Uniform polynomial approximation on
the compact trace interval then promotes character convergence to weak convergence.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology Polynomial
open scoped BoundedContinuousFunction

namespace CriticalLinePhasor.SatoTateCarrier3D

/-- A polynomial in the compact trace coordinate `cos theta`, bundled as a bounded continuous
test on the whole angle line. -/
noncomputable def cosinePolynomialTest (p : ℝ[X]) : ℝ →ᵇ ℝ where
  toFun := fun theta => p.eval (Real.cos theta)
  continuous_toFun := p.continuous.comp Real.continuous_cos
  map_bounded' := by
    apply Metric.isBounded_range_iff.mp
    apply (isCompact_Icc.image p.continuous).isBounded.subset
    rintro y ⟨theta, rfl⟩
    exact ⟨Real.cos theta, Real.cos_mem_Icc theta, rfl⟩

@[simp] theorem cosinePolynomialTest_apply (p : ℝ[X]) (theta : ℝ) :
    cosinePolynomialTest p theta = p.eval (Real.cos theta) := rfl

@[simp] theorem cosinePolynomialTest_zero : cosinePolynomialTest 0 = 0 := by
  ext theta
  simp

@[simp] theorem cosinePolynomialTest_add (p q : ℝ[X]) :
    cosinePolynomialTest (p + q) = cosinePolynomialTest p + cosinePolynomialTest q := by
  ext theta
  simp

@[simp] theorem cosinePolynomialTest_smul (c : ℝ) (p : ℝ[X]) :
    cosinePolynomialTest (c • p) = c • cosinePolynomialTest p := by
  ext theta
  simp

/-- Integration against the normalized angle law is the corresponding weighted interval
integral.  This exposes the density used below to compute the character targets rather than
storing those targets in the arithmetic input. -/
theorem angleMeasure_integral_eq (f : ℝ →ᵇ ℝ) :
    ∫ theta, f theta ∂angleMeasure =
      (2 / Real.pi) * ∫ theta in (0 : ℝ)..Real.pi, f theta * Real.sin theta ^ 2 := by
  rw [angleMeasure, integral_withDensity_eq_integral_toReal_smul]
  · have hdensity_nonneg : ∀ theta : ℝ,
        0 ≤ (2 / Real.pi) * Real.sin theta ^ 2 := fun theta =>
      mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) (sq_nonneg _)
    simp_rw [ENNReal.toReal_ofReal (hdensity_nonneg _), smul_eq_mul]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    calc
      ∫ theta in (0 : ℝ)..Real.pi,
          (2 / Real.pi * Real.sin theta ^ 2) * f theta =
          ∫ theta in (0 : ℝ)..Real.pi,
            (2 / Real.pi) * (f theta * Real.sin theta ^ 2) := by
              apply intervalIntegral.integral_congr
              intro theta _
              ring
      _ = (2 / Real.pi) * ∫ theta in (0 : ℝ)..Real.pi,
            f theta * Real.sin theta ^ 2 := by
              rw [intervalIntegral.integral_const_mul]
  · fun_prop
  · exact Filter.Eventually.of_forall fun theta => ENNReal.ofReal_lt_top

/-- Product-to-sum form of the second-kind Chebyshev character against the Sato--Tate
weight. -/
theorem chebyshev_U_mul_sin_sq (r : ℕ) (theta : ℝ) :
    (Polynomial.Chebyshev.U ℝ r).eval (Real.cos theta) * Real.sin theta ^ 2 =
      (1 / 2 : ℝ) *
        (Real.cos ((r : ℝ) * theta) - Real.cos (((r + 2 : ℕ) : ℝ) * theta)) := by
  have hU := Polynomial.Chebyshev.U_real_cos theta (r : ℤ)
  have hprod := Real.two_mul_sin_mul_sin (((r : ℝ) + 1) * theta) theta
  rw [show (((r : ℤ) : ℝ) + 1) * theta = ((r : ℝ) + 1) * theta by norm_num] at hU
  rw [← hU] at hprod
  rw [show ((r : ℝ) + 1) * theta - theta = (r : ℝ) * theta by ring,
      show ((r : ℝ) + 1) * theta + theta = ((r + 2 : ℕ) : ℝ) * theta by
        push_cast; ring] at hprod
  nlinarith

/-- Every nontrivial symmetric-power character has Sato--Tate integral exactly zero. -/
theorem chebyshev_U_angleMeasure_integral_zero (r : ℕ) (hr : 1 ≤ r) :
    ∫ theta, cosinePolynomialTest (Polynomial.Chebyshev.U ℝ r) theta ∂angleMeasure = 0 := by
  rw [angleMeasure_integral_eq]
  have hint : (∫ theta in (0 : ℝ)..Real.pi,
      cosinePolynomialTest (Polynomial.Chebyshev.U ℝ r) theta * Real.sin theta ^ 2) =
      (1 / 2 : ℝ) *
        ((∫ theta in (0 : ℝ)..Real.pi, Real.cos ((r : ℝ) * theta)) -
         ∫ theta in (0 : ℝ)..Real.pi, Real.cos (((r + 2 : ℕ) : ℝ) * theta)) := by
    simp only [cosinePolynomialTest_apply]
    rw [intervalIntegral.integral_congr (fun theta _ => chebyshev_U_mul_sin_sq r theta),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [hint]
  have hr0 : (r : ℤ) ≠ 0 := by omega
  have hr20 : ((r + 2 : ℕ) : ℤ) ≠ 0 := by omega
  rw [show (∫ theta in (0 : ℝ)..Real.pi, Real.cos ((r : ℝ) * theta)) =
          if (r : ℤ) = 0 then Real.pi else 0 by
        simpa using CatalanMoment.integral_cos_int_mul (r : ℤ),
      if_neg hr0,
      show (∫ theta in (0 : ℝ)..Real.pi, Real.cos (((r + 2 : ℕ) : ℝ) * theta)) =
          if ((r + 2 : ℕ) : ℤ) = 0 then Real.pi else 0 by
        simpa using CatalanMoment.integral_cos_int_mul ((r + 2 : ℕ) : ℤ),
      if_neg hr20]
  ring

/-- The trivial character has integral one under the normalized angle law. -/
theorem chebyshev_U_zero_angleMeasure_integral :
    ∫ theta, cosinePolynomialTest (Polynomial.Chebyshev.U ℝ (0 : ℤ)) theta ∂angleMeasure = 1 := by
  simp [cosinePolynomialTest]

/-- Every finite empirical prime average of the trivial character is one. -/
theorem primeTestAverage_chebyshev_U_zero (angle : Nat.Primes → ℝ) (n : ℕ) :
    primeTestAverage angle n
      (cosinePolynomialTest (Polynomial.Chebyshev.U ℝ (0 : ℤ))) = 1 := by
  simp only [primeTestAverage, cosinePolynomialTest, Polynomial.Chebyshev.U_zero,
    Polynomial.eval_one, BoundedContinuousFunction.coe_mk, Finset.sum_const,
    Finset.card_fin, nsmul_eq_mul]
  field_simp

/-- The second-kind Chebyshev family indexed by natural symmetric-power degree is a polynomial
sequence: its `r`th member has degree exactly `r`. -/
noncomputable def symmetricCharacterSequence : Polynomial.Sequence ℝ where
  elems' r := Polynomial.Chebyshev.U ℝ r
  degree_eq' r := Polynomial.Chebyshev.degree_U_natCast ℝ r

/-- The arithmetic boundary consists only of the canonical prime averages of every
symmetric-power character.  The angle support is recorded independently. -/
structure SymmetricPowerCharacterPrimeAverageInput where
  angle : Nat.Primes → ℝ
  angle_mem : ∀ p, angle p ∈ Icc (0 : ℝ) Real.pi
  character_average_tendsto : ∀ r : ℕ,
    Tendsto
      (fun n => primeTestAverage angle n
        (cosinePolynomialTest (Polynomial.Chebyshev.U ℝ r))) atTop
      (𝓝 (∫ theta, cosinePolynomialTest (Polynomial.Chebyshev.U ℝ r) theta ∂angleMeasure))

/-- Convergence of a polynomial trace test against the prime empirical measures. -/
def PolynomialPrimeTestConverges
    (angle : Nat.Primes → ℝ) (p : ℝ[X]) : Prop :=
  Tendsto
    (fun n => ∫ theta, cosinePolynomialTest p theta
      ∂(empiricalPrimeAngleMeasure angle n : Measure ℝ)) atTop
    (𝓝 (∫ theta, cosinePolynomialTest p theta ∂angleMeasure))

/-- A character-average input gives the integral form of convergence for each character. -/
theorem SymmetricPowerCharacterPrimeAverageInput.character_integral_tendsto
    (input : SymmetricPowerCharacterPrimeAverageInput) (r : ℕ) :
    PolynomialPrimeTestConverges input.angle (Polynomial.Chebyshev.U ℝ r) := by
  simpa only [PolynomialPrimeTestConverges, integral_empiricalPrimeAngleMeasure] using
    input.character_average_tendsto r

/-- The convergent polynomial tests form a real submodule. -/
theorem polynomialPrimeTestConverges_zero (angle : Nat.Primes → ℝ) :
    PolynomialPrimeTestConverges angle 0 := by
  simp [PolynomialPrimeTestConverges]

theorem polynomialPrimeTestConverges_add
    {angle : Nat.Primes → ℝ} {p q : ℝ[X]}
    (hp : PolynomialPrimeTestConverges angle p)
    (hq : PolynomialPrimeTestConverges angle q) :
    PolynomialPrimeTestConverges angle (p + q) := by
  unfold PolynomialPrimeTestConverges at hp hq ⊢
  convert hp.add hq using 1
  · funext n
    rw [cosinePolynomialTest_add]
    change (∫ theta, cosinePolynomialTest p theta + cosinePolynomialTest q theta
      ∂(empiricalPrimeAngleMeasure angle n : Measure ℝ)) = _
    rw [integral_add
      ((cosinePolynomialTest p).integrable _) ((cosinePolynomialTest q).integrable _)]
  · congr 1
    rw [cosinePolynomialTest_add]
    change (∫ theta, cosinePolynomialTest p theta + cosinePolynomialTest q theta
      ∂angleMeasure) = _
    rw [integral_add
      ((cosinePolynomialTest p).integrable _) ((cosinePolynomialTest q).integrable _)]

theorem polynomialPrimeTestConverges_smul
    {angle : Nat.Primes → ℝ} (c : ℝ) {p : ℝ[X]}
    (hp : PolynomialPrimeTestConverges angle p) :
    PolynomialPrimeTestConverges angle (c • p) := by
  unfold PolynomialPrimeTestConverges at hp ⊢
  convert hp.const_smul c using 1
  · funext n
    rw [cosinePolynomialTest_smul]
    change (∫ theta, c * cosinePolynomialTest p theta
      ∂(empiricalPrimeAngleMeasure angle n : Measure ℝ)) = _
    rw [integral_const_mul]
    rfl
  · congr 1
    rw [cosinePolynomialTest_smul]
    change (∫ theta, c * cosinePolynomialTest p theta ∂angleMeasure) = _
    rw [integral_const_mul]
    rfl

/-- Symmetric-power character convergence already gives convergence for every polynomial in the
trace coordinate, since the second-kind Chebyshev sequence spans every degree truncation. -/
theorem SymmetricPowerCharacterPrimeAverageInput.polynomial_tendsto
    (input : SymmetricPowerCharacterPrimeAverageInput) (p : ℝ[X]) :
    PolynomialPrimeTestConverges input.angle p := by
  let N := p.natDegree + 1
  have hpdeg : p ∈ Polynomial.degreeLT ℝ N := by
    rw [Polynomial.mem_degreeLT]
    by_cases hp0 : p = 0
    · simp [hp0]
    · rw [Polynomial.degree_eq_natDegree hp0]
      exact_mod_cast Nat.lt_succ_self p.natDegree
  have hspan : p ∈ Submodule.span ℝ
      (symmetricCharacterSequence '' Set.Iio N) := by
    rw [Polynomial.Sequence.span_degreeLT symmetricCharacterSequence (by
      intro i hi
      simp [symmetricCharacterSequence])]
    exact hpdeg
  refine Submodule.span_induction (p := fun q _ => PolynomialPrimeTestConverges input.angle q)
    ?_ (polynomialPrimeTestConverges_zero input.angle)
    (fun _ _ _ _ hq hr => polynomialPrimeTestConverges_add hq hr)
    (fun c _ _ hq => polynomialPrimeTestConverges_smul c hq) hspan
  rintro q ⟨i, hi, rfl⟩
  exact input.character_integral_tendsto i

/-- The normalized angle law is supported on its defining compact interval. -/
theorem angleMeasure_ae_mem_Icc :
    ∀ᵐ theta ∂angleMeasure, theta ∈ Icc (0 : ℝ) Real.pi := by
  unfold angleMeasure
  apply (withDensity_absolutelyContinuous
    (volume.restrict (Icc (0 : ℝ) Real.pi)) _).ae_le
  exact ae_restrict_mem measurableSet_Icc

/-- Every empirical prime-angle measure is supported on the same compact interval. -/
theorem empiricalPrimeAngleMeasure_ae_mem_Icc
    (input : SymmetricPowerCharacterPrimeAverageInput) (n : ℕ) :
    ∀ᵐ theta ∂(empiricalPrimeAngleMeasure input.angle n : Measure ℝ),
      theta ∈ Icc (0 : ℝ) Real.pi := by
  rw [empiricalPrimeAngleMeasure, ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (measurable_of_finite
    (fun i : Fin (n + 1) => input.angle (nthPrime i))).aemeasurable measurableSet_Icc).2
  exact Filter.Eventually.of_forall fun i => input.angle_mem (nthPrime i)

/-- A bounded continuous angle test can be uniformly approximated on `[0, pi]` by a polynomial in
`cos theta`, which is the trace coordinate used by the symmetric-power characters. -/
theorem exists_cosinePolynomialTest_near
    (f : ℝ →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ p : ℝ[X], ∀ theta ∈ Icc (0 : ℝ) Real.pi,
      |cosinePolynomialTest p theta - f theta| < epsilon := by
  have hcont : ContinuousOn (fun x : ℝ => f (Real.arccos x)) (Icc (-1 : ℝ) 1) :=
    (f.continuous.comp Real.continuous_arccos).continuousOn
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn
    (-1 : ℝ) 1 (fun x : ℝ => f (Real.arccos x)) hcont epsilon hepsilon
  refine ⟨p, fun theta htheta => ?_⟩
  have h := hp (Real.cos theta) (Real.cos_mem_Icc theta)
  simpa only [cosinePolynomialTest_apply,
    Real.arccos_cos htheta.1 htheta.2] using h

/-- Probability integrals of two tests differ by at most their almost-everywhere uniform error. -/
theorem abs_integral_sub_le_of_ae
    {mu : Measure ℝ} [IsProbabilityMeasure mu]
    (f g : ℝ →ᵇ ℝ) {delta : ℝ}
    (hdelta : ∀ᵐ theta ∂mu, |f theta - g theta| ≤ delta) :
    |(∫ theta, f theta ∂mu) - ∫ theta, g theta ∂mu| ≤ delta := by
  rw [← integral_sub (f.integrable mu) (g.integrable mu), ← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le_const (μ := mu)
    (f := fun theta => f theta - g theta) (C := delta) (by
      filter_upwards [hdelta] with theta htheta
      simpa only [Real.norm_eq_abs] using htheta)
  simpa using h

/-- The prime empirical integral and the limiting Sato--Tate integral of an approximating
cosine-polynomial are uniformly close to the corresponding integrals of the original test. -/
theorem cosinePolynomialTest_integral_approximation
    (input : SymmetricPowerCharacterPrimeAverageInput)
    (f : ℝ →ᵇ ℝ) (p : ℝ[X]) {delta : ℝ}
    (happrox : ∀ theta ∈ Icc (0 : ℝ) Real.pi,
      |cosinePolynomialTest p theta - f theta| < delta) :
    (∀ n,
      |(∫ theta, cosinePolynomialTest p theta
          ∂(empiricalPrimeAngleMeasure input.angle n : Measure ℝ)) -
        ∫ theta, f theta
          ∂(empiricalPrimeAngleMeasure input.angle n : Measure ℝ)| ≤ delta) ∧
      |(∫ theta, cosinePolynomialTest p theta ∂angleMeasure) -
        ∫ theta, f theta ∂angleMeasure| ≤ delta := by
  constructor
  · intro n
    apply abs_integral_sub_le_of_ae
    filter_upwards [empiricalPrimeAngleMeasure_ae_mem_Icc input n] with theta htheta
    exact (happrox theta htheta).le
  · apply abs_integral_sub_le_of_ae
    filter_upwards [angleMeasure_ae_mem_Icc] with theta htheta
    exact (happrox theta htheta).le

/-- Symmetric-power character averages imply convergence of every bounded continuous angle-test
integral.  The proof uses the character span for polynomial tests and uniform approximation on the
compact trace interval. -/
theorem SymmetricPowerCharacterPrimeAverageInput.integral_tendsto
    (input : SymmetricPowerCharacterPrimeAverageInput) (f : ℝ →ᵇ ℝ) :
    Tendsto
      (fun n => ∫ theta, f theta
        ∂(empiricalPrimeAngleMeasure input.angle n : Measure ℝ)) atTop
      (𝓝 (∫ theta, f theta ∂angleMeasure)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨p, hp⟩ := exists_cosinePolynomialTest_near f (by positivity : 0 < epsilon / 3)
  have hpoly := input.polynomial_tendsto p
  rw [PolynomialPrimeTestConverges, Metric.tendsto_atTop] at hpoly
  obtain ⟨N, hN⟩ := hpoly (epsilon / 3) (by positivity)
  have happrox := cosinePolynomialTest_integral_approximation input f p hp
  refine ⟨N, fun n hn => ?_⟩
  let Bn : ℝ := ∫ theta, f theta
    ∂(empiricalPrimeAngleMeasure input.angle n : Measure ℝ)
  let An : ℝ := ∫ theta, cosinePolynomialTest p theta
    ∂(empiricalPrimeAngleMeasure input.angle n : Measure ℝ)
  let A : ℝ := ∫ theta, cosinePolynomialTest p theta ∂angleMeasure
  let B : ℝ := ∫ theta, f theta ∂angleMeasure
  have hnmid : dist An A < epsilon / 3 := by
    simpa [An, A] using hN n hn
  have hnleft : dist Bn An ≤ epsilon / 3 := by
    simpa [Bn, An, Real.dist_eq, abs_sub_comm] using happrox.1 n
  have hnright : dist A B ≤ epsilon / 3 := by
    simpa [A, B, Real.dist_eq] using happrox.2
  calc
    dist Bn B ≤ dist Bn An + dist An A + dist A B := dist_triangle4 _ _ _ _
    _ < epsilon := by linarith

/-- The literal first-prime averages of every bounded continuous test converge, now derived from
the symmetric-power character averages rather than stored as an input field. -/
theorem SymmetricPowerCharacterPrimeAverageInput.test_average_tendsto
    (input : SymmetricPowerCharacterPrimeAverageInput) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => primeTestAverage input.angle n f) atTop
      (𝓝 (∫ theta, f theta ∂angleMeasure)) := by
  simpa only [integral_empiricalPrimeAngleMeasure] using input.integral_tendsto f

/-- Character averages construct the all-test interface consumed by the probability-measure
convergence theorem. -/
noncomputable def SymmetricPowerCharacterPrimeAverageInput.toTestAverageInput
    (input : SymmetricPowerCharacterPrimeAverageInput) : PrimeSatoTateTestAverageInput where
  angle := input.angle
  test_average_tendsto := input.test_average_tendsto

/-- **Empirical-prime Sato--Tate convergence from symmetric-power characters.**  The canonical
prime averages of the `SU(2)` characters alone force weak convergence of the native three-
dimensional carrier measures. -/
theorem empiricalPrimeCarrierMeasure_tendsto_of_symmetricPowerCharacters
    (input : SymmetricPowerCharacterPrimeAverageInput) :
    Tendsto (empiricalPrimeCarrierMeasure input.angle) atTop (𝓝 carrierProbability) :=
  empiricalPrimeCarrierMeasure_tendsto_of_testAverages input.toTestAverageInput

/-- Arithmetic boundary in its usual explicit form: each nontrivial symmetric-power character
average converges to zero.  The target law is not a field of this structure; it is computed above
from the carrier density. -/
structure SymmetricPowerCharacterPrimeZeroInput where
  angle : Nat.Primes → ℝ
  angle_mem : ∀ p, angle p ∈ Icc (0 : ℝ) Real.pi
  character_average_tendsto_zero : ∀ r : ℕ, 1 ≤ r →
    Tendsto
      (fun n => primeTestAverage angle n
        (cosinePolynomialTest (Polynomial.Chebyshev.U ℝ r))) atTop
      (𝓝 0)

/-- The explicit-zero arithmetic boundary supplies the character-integral interface, using the
computed zeroth and nontrivial character integrals. -/
noncomputable def SymmetricPowerCharacterPrimeZeroInput.toCharacterAverageInput
    (input : SymmetricPowerCharacterPrimeZeroInput) :
    SymmetricPowerCharacterPrimeAverageInput where
  angle := input.angle
  angle_mem := input.angle_mem
  character_average_tendsto := by
    intro r
    rcases r with _ | r
    · convert (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)) using 1
      · funext n
        simpa using primeTestAverage_chebyshev_U_zero input.angle n
      · simp
    · simpa only [chebyshev_U_angleMeasure_integral_zero (r + 1) (by omega)] using
        input.character_average_tendsto_zero (r + 1) (by omega)

/-- **Empirical-prime Sato--Tate from explicit character limits.**  Vanishing of every
nontrivial symmetric-power character average forces weak convergence of the native 3D carrier
measures. -/
theorem empiricalPrimeCarrierMeasure_tendsto_of_characterAveragesZero
    (input : SymmetricPowerCharacterPrimeZeroInput) :
    Tendsto (empiricalPrimeCarrierMeasure input.angle) atTop (𝓝 carrierProbability) :=
  empiricalPrimeCarrierMeasure_tendsto_of_symmetricPowerCharacters
    input.toCharacterAverageInput

end CriticalLinePhasor.SatoTateCarrier3D

#print axioms CriticalLinePhasor.SatoTateCarrier3D.SymmetricPowerCharacterPrimeAverageInput.polynomial_tendsto
#print axioms CriticalLinePhasor.SatoTateCarrier3D.SymmetricPowerCharacterPrimeAverageInput.integral_tendsto
#print axioms CriticalLinePhasor.SatoTateCarrier3D.empiricalPrimeCarrierMeasure_tendsto_of_symmetricPowerCharacters
#print axioms CriticalLinePhasor.SatoTateCarrier3D.chebyshev_U_angleMeasure_integral_zero
#print axioms CriticalLinePhasor.SatoTateCarrier3D.empiricalPrimeCarrierMeasure_tendsto_of_characterAveragesZero
