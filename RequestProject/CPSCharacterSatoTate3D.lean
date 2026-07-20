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

/-- **Equidistribution forces every nontrivial symmetric-power character average to vanish.**  The
converse of the method of moments: if the empirical prime-angle measures converge weakly to the
Sato--Tate law, then for every `r ≥ 1` the prime average of the `r`th symmetric-power character
`(N+1)^{-1}∑_{j≤N} U_r(cos θ_{p_j})` tends to `0`.  Weak convergence, applied to the
bounded-continuous test `cosinePolynomialTest (U r)`, gives convergence of the empirical integral to
the Sato--Tate integral, which vanishes for `r ≥ 1` (`chebyshev_U_angleMeasure_integral_zero`). -/
theorem equidistribution_forces_characterAverage_zero
    {angle : Nat.Primes → ℝ}
    (hequi : Tendsto (empiricalPrimeAngleMeasure angle) atTop (𝓝 angleProbability))
    (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun n => primeTestAverage angle n
        (cosinePolynomialTest (Polynomial.Chebyshev.U ℝ r))) atTop (𝓝 0) := by
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).mp hequi
    (cosinePolynomialTest (Polynomial.Chebyshev.U ℝ r))
  rw [show (∫ theta, cosinePolynomialTest (Polynomial.Chebyshev.U ℝ r) theta
        ∂(angleProbability : Measure ℝ)) =
      ∫ theta, cosinePolynomialTest (Polynomial.Chebyshev.U ℝ r) theta ∂angleMeasure from rfl,
    chebyshev_U_angleMeasure_integral_zero r hr] at h
  simpa only [integral_empiricalPrimeAngleMeasure] using h

/-- **The symmetric-power character prime-average cancellation IS equidistribution** (method of
moments, both directions).  For a Satake-angle assignment supported on `[0, π]`, the empirical
prime-angle measures converge weakly to the Sato--Tate law **iff** every nontrivial symmetric-power
character average vanishes.  This puts the arithmetic Tauberian input
(`SymmetricPowerCharacterPrimeZeroInput`) provably *on* the equidistribution critical path: it is not
only sufficient (`←`, the moment method) but necessary (`→`) --- equidistribution cannot hold without
it.  Unlike an off-path chart shadow, discharging this one input is exactly equivalent to the
Sato--Tate conclusion. -/
theorem characterAverageZero_iff_equidistribution
    (angle : Nat.Primes → ℝ) (angle_mem : ∀ p, angle p ∈ Icc (0 : ℝ) Real.pi) :
    (∀ r : ℕ, 1 ≤ r →
        Tendsto (fun n => primeTestAverage angle n
          (cosinePolynomialTest (Polynomial.Chebyshev.U ℝ r))) atTop (𝓝 0))
      ↔ Tendsto (empiricalPrimeAngleMeasure angle) atTop (𝓝 angleProbability) := by
  constructor
  · intro hzero
    exact (empiricalPrimeSatoTate_of_testAverages
      (SymmetricPowerCharacterPrimeZeroInput.toCharacterAverageInput
          ⟨angle, angle_mem, hzero⟩).toTestAverageInput).angle_tendsto
  · intro hequi r hr
    exact equidistribution_forces_characterAverage_zero hequi r hr

/-! ## Exact arithmetic Satake-to-carrier identification -/

/-- The trace of the literal local roots
`a^r, a^(r-1)a⁻¹, ..., (a⁻¹)^r` of the `r`th symmetric power. -/
noncomputable def symmetricPowerSatakeTrace (a : ℂ) (r : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (r + 1), a ^ (r - j) * (a⁻¹) ^ j

/-- The `j`th literal local root of the `r`th symmetric power. -/
noncomputable def symmetricPowerSatakeRoot
    (a : ℂ) (r : ℕ) (j : Fin (r + 1)) : ℂ :=
  a ^ (r - j.1) * (a⁻¹) ^ j.1

/-- The symmetric-power Satake trace is exactly the sum of its literal local roots. -/
theorem symmetricPowerSatakeTrace_eq_sum_roots (a : ℂ) (r : ℕ) :
    symmetricPowerSatakeTrace a r =
      ∑ j : Fin (r + 1), symmetricPowerSatakeRoot a r j := by
  exact (Fin.sum_univ_eq_sum_range
    (fun j => a ^ (r - j) * (a⁻¹) ^ j) (r + 1)).symm

theorem symmetricPowerSatakeTrace_succ (a : ℂ) (r : ℕ) :
    symmetricPowerSatakeTrace a (r + 1) =
      a * symmetricPowerSatakeTrace a r + (a⁻¹) ^ (r + 1) := by
  rw [symmetricPowerSatakeTrace, symmetricPowerSatakeTrace,
    show r + 1 + 1 = (r + 1) + 1 by omega,
    Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.sub_self, pow_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show r + 1 - j = (r - j) + 1 by omega, pow_succ]
  ring

@[simp] theorem symmetricPowerSatakeTrace_zero (a : ℂ) :
    symmetricPowerSatakeTrace a 0 = 1 := by
  simp [symmetricPowerSatakeTrace]

theorem symmetricPowerSatakeTrace_one (a : ℂ) :
    symmetricPowerSatakeTrace a 1 = a + a⁻¹ := by
  norm_num [symmetricPowerSatakeTrace, Finset.sum_range_succ, pow_succ]

/-- The literal symmetric-power root trace obeys the second-kind Chebyshev recurrence. -/
theorem symmetricPowerSatakeTrace_add_two (a : ℂ) (ha : a ≠ 0) (r : ℕ) :
    symmetricPowerSatakeTrace a (r + 2) =
      (a + a⁻¹) * symmetricPowerSatakeTrace a (r + 1) -
        symmetricPowerSatakeTrace a r := by
  rw [show r + 2 = (r + 1) + 1 by omega,
    symmetricPowerSatakeTrace_succ, symmetricPowerSatakeTrace_succ]
  simp only [pow_succ]
  have hprod : a * symmetricPowerSatakeTrace a r * a⁻¹ =
      symmetricPowerSatakeTrace a r := by
    calc
      a * symmetricPowerSatakeTrace a r * a⁻¹ =
          symmetricPowerSatakeTrace a r * (a * a⁻¹) := by ring
      _ = symmetricPowerSatakeTrace a r := by rw [mul_inv_cancel₀ ha, mul_one]
  ring_nf
  rw [hprod]
  ring

/-- Once the arithmetic tower has derived `‖a‖ = 1`, its literal symmetric-power Satake trace is
exactly the `SU(2)` character `U_r(re a)`.  No angle or compact support is assumed. -/
theorem chebyshev_U_re_eq_symmetricPowerSatakeTrace
    (a : ℂ) (ha : ‖a‖ = 1) (r : ℕ) :
    (((Polynomial.Chebyshev.U ℝ r).eval a.re : ℝ) : ℂ) =
      symmetricPowerSatakeTrace a r := by
  have ha0 : a ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hinv : a⁻¹ = starRingEnd ℂ a := Complex.inv_eq_conj ha
  have hadd : a + a⁻¹ = ((2 * a.re : ℝ) : ℂ) := by
    rw [hinv, Complex.add_conj]
  induction r using Nat.twoStepInduction with
  | zero => simp [symmetricPowerSatakeTrace_zero]
  | one =>
      norm_num [Polynomial.Chebyshev.U_one, symmetricPowerSatakeTrace_one, hadd]
  | more r h0 h1 =>
      have h0c : (Polynomial.Chebyshev.U ℂ (r : ℤ)).eval (a.re : ℂ) =
          symmetricPowerSatakeTrace a r := by simpa using h0
      have h1c : (Polynomial.Chebyshev.U ℂ ((r + 1 : ℕ) : ℤ)).eval (a.re : ℂ) =
          symmetricPowerSatakeTrace a (r + 1) := by simpa using h1
      rw [show ((r + 1 : ℕ) : ℤ) = (r : ℤ) + 1 by omega] at h1c
      rw [show ((r + 2 : ℕ) : ℤ) = (r : ℤ) + 2 by omega,
        Polynomial.Chebyshev.U_add_two,
        symmetricPowerSatakeTrace_add_two a ha0 r, hadd]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat, Polynomial.eval_X]
      push_cast
      rw [h0c, h1c]

/-- The canonical conjugacy-class angle is derived from the unit-radius arithmetic strand, and
its character is still the literal symmetric-power Satake trace. -/
theorem chebyshev_U_cos_abs_arg_eq_symmetricPowerSatakeTrace
    (a : ℂ) (ha : ‖a‖ = 1) (r : ℕ) :
    (((Polynomial.Chebyshev.U ℝ r).eval (Real.cos |Complex.arg a|) : ℝ) : ℂ) =
      symmetricPowerSatakeTrace a r := by
  rw [Real.cos_abs]
  have hre : Real.cos (Complex.arg a) = a.re := by
    have hpolar := Complex.norm_mul_cos_arg a
    rw [ha, one_mul] at hpolar
    exact hpolar
  rw [hre]
  exact chebyshev_U_re_eq_symmetricPowerSatakeTrace a ha r

/-- A prime-indexed arithmetic rank-two strand.  At every prime its unit radius is an output of
the identified all-rank tower ceiling. -/
structure ArithmeticSatakePrimeFamily where
  tower : Nat.Primes → GlobalHelix.ArithmeticSatakeTowerAtPrime

/-- The prime angle is the canonical compact conjugacy-class coordinate extracted from the
arithmetic strand after radial closure. -/
noncomputable def ArithmeticSatakePrimeFamily.angle
    (F : ArithmeticSatakePrimeFamily) (p : Nat.Primes) : ℝ :=
  |Complex.arg (F.tower p).value|

theorem ArithmeticSatakePrimeFamily.angle_mem
    (F : ArithmeticSatakePrimeFamily) (p : Nat.Primes) :
    F.angle p ∈ Set.Icc (0 : ℝ) Real.pi := by
  exact ⟨abs_nonneg _, Complex.abs_arg_le_pi _⟩

/-- Exact local identification: the character read on the native helix is the real part of the
literal arithmetic symmetric-power Satake trace. -/
theorem ArithmeticSatakePrimeFamily.character_eq_satakeTrace
    (F : ArithmeticSatakePrimeFamily) (p : Nat.Primes) (r : ℕ) :
    (Polynomial.Chebyshev.U ℝ r).eval (Real.cos (F.angle p)) =
      (symmetricPowerSatakeTrace (F.tower p).value r).re := by
  have h := chebyshev_U_cos_abs_arg_eq_symmetricPowerSatakeTrace
    (F.tower p).value (F.tower p).radius_one r
  exact congr_arg Complex.re h

/-- The literal first-prime average of the actual symmetric-power Satake traces. -/
noncomputable def arithmeticSymmetricPowerPrimeAverage
    (F : ArithmeticSatakePrimeFamily) (r n : ℕ) : ℝ :=
  (1 / ((n + 1 : ℕ) : ℝ)) *
    ∑ i : Fin (n + 1),
      (symmetricPowerSatakeTrace (F.tower (nthPrime i)).value r).re

/-- Exact global identification: the character average used by the Sato--Tate density theorem is
definitionally the average of the literal arithmetic symmetric-power prime traces. -/
theorem ArithmeticSatakePrimeFamily.primeTestAverage_eq_arithmetic
    (F : ArithmeticSatakePrimeFamily) (r n : ℕ) :
    primeTestAverage F.angle n
      (cosinePolynomialTest (Polynomial.Chebyshev.U ℝ r)) =
      arithmeticSymmetricPowerPrimeAverage F r n := by
  unfold primeTestAverage arithmeticSymmetricPowerPrimeAverage
  simp only [one_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact F.character_eq_satakeTrace (nthPrime i) r

/-- Prime cancellation stated on the literal arithmetic symmetric-power Satake bank. -/
structure ArithmeticSymmetricPowerPrimeCancellation
    (F : ArithmeticSatakePrimeFamily) : Prop where
  tendsto_zero : ∀ r : ℕ, 1 ≤ r →
    Tendsto (fun n => arithmeticSymmetricPowerPrimeAverage F r n)
      atTop (nhds 0)

noncomputable def ArithmeticSymmetricPowerPrimeCancellation.toCharacterPrimeZeroInput
    {F : ArithmeticSatakePrimeFamily}
    (h : ArithmeticSymmetricPowerPrimeCancellation F) :
    SymmetricPowerCharacterPrimeZeroInput where
  angle := F.angle
  angle_mem := F.angle_mem
  character_average_tendsto_zero := by
    intro r hr
    simpa only [F.primeTestAverage_eq_arithmetic] using h.tendsto_zero r hr

/-- Arithmetic symmetric-power prime cancellation lands directly in weak convergence of the
native 3D carrier measures. -/
theorem empiricalPrimeCarrierMeasure_tendsto_of_arithmeticSatakeCancellation
    (F : ArithmeticSatakePrimeFamily)
    (h : ArithmeticSymmetricPowerPrimeCancellation F) :
    Tendsto (empiricalPrimeCarrierMeasure F.angle) atTop
      (nhds carrierProbability) :=
  empiricalPrimeCarrierMeasure_tendsto_of_characterAveragesZero
    h.toCharacterPrimeZeroInput

/-- The exact arithmetic boundary for 3D Sato--Tate: cancellation of the literal
symmetric-power Satake prime traces is equivalent to convergence of the empirical carrier
measures. -/
theorem arithmeticSatakeCancellation_iff_carrierEquidistribution
    (F : ArithmeticSatakePrimeFamily) :
    (∀ r : ℕ, 1 ≤ r →
        Tendsto (fun n => arithmeticSymmetricPowerPrimeAverage F r n)
          atTop (nhds 0)) ↔
      Tendsto (empiricalPrimeCarrierMeasure F.angle) atTop
        (nhds carrierProbability) := by
  constructor
  · intro h
    exact empiricalPrimeCarrierMeasure_tendsto_of_arithmeticSatakeCancellation F ⟨h⟩
  · intro hcarrier r hr
    have hangle := (empiricalPrimeCarrierMeasure_tendsto_iff F.angle).mp hcarrier
    have hcharacters :=
      (characterAverageZero_iff_equidistribution F.angle F.angle_mem).mpr hangle
    simpa only [F.primeTestAverage_eq_arithmetic] using hcharacters r hr

end CriticalLinePhasor.SatoTateCarrier3D

#print axioms CriticalLinePhasor.SatoTateCarrier3D.SymmetricPowerCharacterPrimeAverageInput.polynomial_tendsto
#print axioms CriticalLinePhasor.SatoTateCarrier3D.SymmetricPowerCharacterPrimeAverageInput.integral_tendsto
#print axioms CriticalLinePhasor.SatoTateCarrier3D.empiricalPrimeCarrierMeasure_tendsto_of_symmetricPowerCharacters
#print axioms CriticalLinePhasor.SatoTateCarrier3D.chebyshev_U_angleMeasure_integral_zero
#print axioms CriticalLinePhasor.SatoTateCarrier3D.empiricalPrimeCarrierMeasure_tendsto_of_characterAveragesZero
#print axioms CriticalLinePhasor.SatoTateCarrier3D.equidistribution_forces_characterAverage_zero
#print axioms CriticalLinePhasor.SatoTateCarrier3D.characterAverageZero_iff_equidistribution
#print axioms CriticalLinePhasor.SatoTateCarrier3D.symmetricPowerSatakeTrace_eq_sum_roots
#print axioms CriticalLinePhasor.SatoTateCarrier3D.chebyshev_U_re_eq_symmetricPowerSatakeTrace
#print axioms CriticalLinePhasor.SatoTateCarrier3D.ArithmeticSatakePrimeFamily.character_eq_satakeTrace
#print axioms CriticalLinePhasor.SatoTateCarrier3D.ArithmeticSatakePrimeFamily.primeTestAverage_eq_arithmetic
#print axioms CriticalLinePhasor.SatoTateCarrier3D.arithmeticSatakeCancellation_iff_carrierEquidistribution
