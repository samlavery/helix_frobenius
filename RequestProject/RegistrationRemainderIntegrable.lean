import RequestProject.RegistrationBoundary

/-!
# The archimedean remainder is integrable over every gap (ledger 610)

Discharges the hypothesis `hrem` of `smoothed_gap_count` (608) and `gap_count_decomposition` (609).
The zero density `rieszZeroDensity L` is measurable in the height (a pointwise limit of measurable
partial sums over the zeros) and bounded on every compact height window (a summable majorant uniform
in the height), hence integrable on every gap. At good heights the remainder is the density minus the
clock rate plus the bank's real part (`rieszZeroDensity_eq`), and the non-good heights are a null set
(`goodHeight_ae`); so the remainder is interval integrable on every gap with positive base height.

With this, the station gap identities hold with no analytic hypothesis beyond the strain bound `hB`
and the level condition `hn`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real
open CriticalLinePhasor.CarrierScale (theta clockRate continuous_clockRate)

namespace CriticalLinePhasor.ContourArgument

/-- The complex zero sum converges at every height. -/
theorem summable_zero_kernel {L : ℝ} (hL : 0 < L) (t : ℝ) :
    Summable (fun ρ : Zero =>
      (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))) := by
  obtain ⟨C, R, hC, hR, hbound⟩ := rieszKernel_bound_uniform hL t t
  have hg : Summable (fun ρ : Zero => C * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :=
    (ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros).mul_left C
  apply Summable.of_norm_bounded_eventually hg
  filter_upwards [CriticalLinePhasor.StBridge.eventually_cofinite_norm_ge R] with ρ hρR
  rw [norm_mul, Complex.norm_natCast]
  have := hbound ρ.val ρ.2.1.le ρ.2.2.1.le hρR t ⟨le_rfl, le_rfl⟩
  calc (ZD.xiOrderNat ρ.val : ℝ) * ‖rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))‖
      ≤ (ZD.xiOrderNat ρ.val : ℝ) * (C / ‖ρ.val‖ ^ 2) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = C * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by ring

/-- The density is measurable in the height: a pointwise limit of measurable partial sums. -/
theorem rieszZeroDensity_measurable {L : ℝ} (hL : 0 < L) : Measurable (rieszZeroDensity L) := by
  have hpart : ∀ F : Finset Zero, Measurable (fun t : ℝ =>
      (∑ ρ ∈ F, (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re) := by
    intro F
    apply Complex.continuous_re.measurable.comp
    apply Finset.measurable_sum
    intro ρ _
    apply measurable_const.mul
    have hK : Measurable (fun w : ℂ => rieszKernel L w) := by
      unfold rieszKernel
      exact (expRatio_differentiable L).continuous.measurable.div measurable_id
    have hshift : Continuous (fun t : ℝ => ρ.val - (1 / 2 + (t : ℂ) * I)) := by fun_prop
    exact hK.comp hshift.measurable
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset Zero)) hpart ?_
  rw [tendsto_pi_nhds]
  intro t
  unfold rieszZeroDensity
  exact (Complex.continuous_re.tendsto _).comp (summable_zero_kernel hL t).hasSum

/-- The density is bounded on every compact height window. -/
theorem rieszZeroDensity_bound {L : ℝ} (hL : 0 < L) (a b : ℝ) :
    ∃ M : ℝ, ∀ t ∈ Icc a b, |rieszZeroDensity L t| ≤ M := by
  classical
  obtain ⟨C, R, hC, hR, hbound⟩ := rieszKernel_bound_uniform hL a b
  choose Mρ hMρ using fun ρ : Zero => rieszKernel_re_bound_fixed hL ρ.val ρ.2.2.1.le
  -- the majorant: the per-zero bound for the finitely many zeros below `R`, the uniform one above
  set g : Zero → ℝ := fun ρ => (ZD.xiOrderNat ρ.val : ℝ) * (if ‖ρ.val‖ < R then Mρ ρ else C / ‖ρ.val‖ ^ 2)
    with hg_def
  have hg_sum : Summable g := by
    have hg0 : Summable (fun ρ : Zero => C * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :=
      (ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros).mul_left C
    apply Summable.of_norm_bounded_eventually hg0
    filter_upwards [CriticalLinePhasor.StBridge.eventually_cofinite_norm_ge R] with ρ hρR
    rw [hg_def]
    simp only [not_lt.2 hρR, if_false]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply le_of_eq
    ring
  have hterm : ∀ t ∈ Icc a b, ∀ ρ : Zero,
      |(ZD.xiOrderNat ρ.val : ℝ) * (rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re| ≤ g ρ := by
    intro t ht ρ
    rw [hg_def, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ))]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    split_ifs with hlt
    · exact hMρ ρ t
    · rw [not_lt] at hlt
      exact (Complex.abs_re_le_norm _).trans (hbound ρ.val ρ.2.1.le ρ.2.2.1.le hlt t ht)
  refine ⟨∑' ρ, g ρ, fun t ht => ?_⟩
  rw [rieszZeroDensity_eq_tsum_re hL a b ht]
  have habs : Summable (fun ρ : Zero =>
      |(ZD.xiOrderNat ρ.val : ℝ) * (rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re|) :=
    Summable.of_nonneg_of_le (fun ρ => abs_nonneg _) (hterm t ht) hg_sum
  calc |∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℝ) * (rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re|
      ≤ ∑' ρ : Zero, |(ZD.xiOrderNat ρ.val : ℝ) * (rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re| := by
        have := norm_tsum_le_tsum_norm (f := fun ρ : Zero =>
          (ZD.xiOrderNat ρ.val : ℝ) * (rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re)
          (by simpa only [Real.norm_eq_abs] using habs)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' ρ, g ρ := Summable.tsum_le_tsum (hterm t ht) habs hg_sum

/-- The density is integrable over every height interval. -/
theorem rieszZeroDensity_intervalIntegrable {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (rieszZeroDensity L) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  obtain ⟨M, hM⟩ := rieszZeroDensity_bound hL a b
  apply Measure.integrableOn_of_bounded (M := M)
  · simp
  · exact (rieszZeroDensity_measurable hL).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall (fun t ht => by rw [Real.norm_eq_abs]; exact hM t ⟨ht.1.le, ht.2⟩)

/-- **The archimedean remainder is integrable over every gap with positive base height.** -/
theorem rieszRemainder_intervalIntegrable {L : ℝ} (hL : 0 < L) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (rieszRemainder L) volume a b := by
  have hd := rieszZeroDensity_intervalIntegrable hL hab
  have i1 : IntervalIntegrable clockRate volume a b := continuous_clockRate.intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t : ℝ => (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re) volume a b :=
    (rieszPrimeSum_re_continuous hL).intervalIntegrable _ _
  refine ((hd.sub i1).add i2).congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [goodHeight_ae (a := a) (b := b) ha (by linarith)] with t ht htI
  rw [rieszZeroDensity_eq hL (ht htI)]
  ring

/-- `smoothed_gap_count` with the integrability hypothesis discharged. -/
theorem smoothed_gap_count' {L : ℝ} (hL : 0 < L) {B : ℝ} (hB : ∀ t, |rieszStrain L t| ≤ B)
    {n : ℕ} (hn : regClock (rieszStrain L) 10 < stationLevel n) :
    (1 / Real.pi) * ∫ t in station (rieszStrain L) n..station (rieszStrain L) (n + 1),
        rieszZeroDensity L t
      = 1 + (1 / Real.pi) * ∫ t in station (rieszStrain L) n..station (rieszStrain L) (n + 1),
          rieszRemainder L t := by
  apply smoothed_gap_count hL hB hn
  exact rieszRemainder_intervalIntegrable hL
    (by linarith [(station_spec (rieszStrain_continuous L) hB hn).1])
    (station_lt (rieszStrain_continuous L) hB hn).le

/-- `gap_count_decomposition` with the integrability hypothesis discharged: the sharp count over a
station gap is one plus the integrated remainder plus the Fejér boundary term. -/
theorem gap_count_decomposition' {L : ℝ} (hL : 0 < L) {B : ℝ} (hB : ∀ t, |rieszStrain L t| ≤ B)
    {n : ℕ} (hn : regClock (rieszStrain L) 10 < stationLevel n) :
    (bandCountMult (station (rieszStrain L) n) (station (rieszStrain L) (n + 1)) : ℝ)
      = 1 + (1 / Real.pi) * (∫ t in station (rieszStrain L) n..station (rieszStrain L) (n + 1),
            rieszRemainder L t)
        + boundaryTerm L (station (rieszStrain L) n) (station (rieszStrain L) (n + 1)) := by
  apply gap_count_decomposition hL hB hn
  exact rieszRemainder_intervalIntegrable hL
    (by linarith [(station_spec (rieszStrain_continuous L) hB hn).1])
    (station_lt (rieszStrain_continuous L) hB hn).le

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.rieszZeroDensity_measurable
#print axioms CriticalLinePhasor.ContourArgument.rieszRemainder_intervalIntegrable
#print axioms CriticalLinePhasor.ContourArgument.smoothed_gap_count'
#print axioms CriticalLinePhasor.ContourArgument.gap_count_decomposition'
