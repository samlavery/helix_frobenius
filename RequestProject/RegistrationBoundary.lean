import RequestProject.RegistrationGapCount
import RequestProject.StExplicitBridge

/-!
# The boundary term: the smoothed gap count as a sum of per-zero weights (ledger 609)

The smoothed count over a gap `(a, b]` is `(1/π) ∫_a^b Re Σ'_ρ m_ρ K_L(ρ − ½ − it) dt`. Exchanging the
integral with the zero sum gives

  `smoothed count = Σ'_ρ m_ρ · gapWeight L a b ρ`,   `gapWeight L a b ρ := (1/π) ∫_a^b Re K_L(ρ − ½ − it) dt`

(`smoothed_count_eq_tsum_weights`). For an on-line zero `ρ = ½ + iγ` the weight is the Fejér mass
of the gap at `γ`: `Re K_L(iu) = (1 − cos Lu)/(L u²) ≥ 0` (`rieszKernel_re_line_eq`), bounded by
`L/2`. So, against the compiled DC of one (608), the one-per-gap count is decided by the boundary
term `Σ'_ρ m_ρ (1_{(a,b]}(Im ρ) − gapWeight ρ)`: mass lost by zeros inside the gap and mass leaked
from zeros outside it, plus the complex-argument weights of any off-line zero.

The exchange rests on two bounds, both compiled here: for a fixed zero the kernel's real part is
bounded uniformly in the height (`rieszKernel_re_bound_fixed`), and for `‖ρ‖` large it is
`O(‖ρ‖⁻²)` uniformly on a compact range of heights (`rieszKernel_bound_uniform`), which with the
compiled `Σ m_ρ/‖ρ‖² < ∞` gives summability of the integrated norms.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. The kernel on the line and the per-zero weight -/

/-- The Fejér kernel on the line: `Re K_L(iu) = (1 − cos Lu)/(L u²)` for `u ≠ 0`. -/
theorem rieszKernel_re_line_eq {L : ℝ} (hL : 0 < L) {u : ℝ} (hu : u ≠ 0) :
    (rieszKernel L (u * I)).re = (1 - Real.cos (L * u)) / (u ^ 2 * L) := by
  have hw : (u : ℂ) * I ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact hu (by exact_mod_cast h')
    · exact I_ne_zero h'
  rw [rieszKernel_eq hL.ne' hw]
  have hsq : ((u : ℂ) * I) ^ 2 = -((u : ℂ) ^ 2) := by
    rw [mul_pow, Complex.I_sq]; ring
  rw [hsq]
  have e : (Complex.exp (L * ((u : ℂ) * I)) - 1) / (-((u : ℂ) ^ 2) * L)
      = ((1 - Complex.exp ((L * u : ℝ) * I)) / ((u ^ 2 * L : ℝ) : ℂ)) := by
    have : (L : ℂ) * ((u : ℂ) * I) = ((L * u : ℝ) : ℂ) * I := by push_cast; ring
    rw [this]
    have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
    have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp
    ring
  rw [e, Complex.div_ofReal_re, sub_re, one_re, Complex.exp_ofReal_mul_I_re]

/-- On the line the kernel's real part is at most `L/2`. -/
theorem rieszKernel_re_line_le {L : ℝ} (hL : 0 < L) (u : ℝ) :
    (rieszKernel L (u * I)).re ≤ L / 2 := by
  by_cases hu : u = 0
  · subst hu; simp [rieszKernel]; positivity
  rw [rieszKernel_re_line_eq hL hu]
  have hpos : 0 < u ^ 2 * L := by positivity
  rw [div_le_iff₀ hpos]
  have := Real.one_sub_sq_div_two_le_cos (x := L * u)
  nlinarith [sq_nonneg u, sq_nonneg L]

/-- The per-zero gap weight. -/
noncomputable def gapWeight (L a b : ℝ) (ρ : ℂ) : ℝ :=
  (1 / Real.pi) * ∫ t in a..b, (rieszKernel L (ρ - (1 / 2 + (t : ℂ) * I))).re

theorem online_shift {ρ : ℂ} (hρ : ρ.re = 1 / 2) (t : ℝ) :
    ρ - (1 / 2 + (t : ℂ) * I) = ((ρ.im - t : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [hρ]

/-- For an on-line zero the weight is nonnegative: the Fejér mass of the gap. -/
theorem gapWeight_nonneg_of_online {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) : 0 ≤ gapWeight L a b ρ := by
  unfold gapWeight
  apply mul_nonneg (by positivity)
  apply intervalIntegral.integral_nonneg hab
  intro t _
  rw [online_shift hρ t]
  exact rieszKernel_re_on_line_nonneg hL _

/-! ## 2. Bounds on the kernel -/

/-- For a fixed point `ρ` the kernel's real part is bounded uniformly in the height. -/
theorem rieszKernel_re_bound_fixed {L : ℝ} (hL : 0 < L) (ρ : ℂ) (hρ : ρ.re ≤ 1) :
    ∃ M : ℝ, ∀ t : ℝ, |(rieszKernel L (ρ - (1 / 2 + (t : ℂ) * I))).re| ≤ M := by
  obtain ⟨C₀, hC₀, hbound⟩ := expRatio_bound hL (b' := 1 / 2) (by norm_num)
  by_cases hline : ρ.re = 1 / 2
  · refine ⟨L / 2, fun t => ?_⟩
    rw [online_shift hline t, abs_of_nonneg (rieszKernel_re_on_line_nonneg hL _)]
    exact rieszKernel_re_line_le hL _
  · have hδ : 0 < |ρ.re - 1 / 2| := abs_pos.2 (sub_ne_zero.2 hline)
    refine ⟨C₀ / |ρ.re - 1 / 2|, fun t => ?_⟩
    have hre : (ρ - (1 / 2 + (t : ℂ) * I)).re = ρ.re - 1 / 2 := by simp
    have hw : ρ - (1 / 2 + (t : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; exact hline (by linarith)
    calc |(rieszKernel L (ρ - (1 / 2 + (t : ℂ) * I))).re|
        ≤ ‖rieszKernel L (ρ - (1 / 2 + (t : ℂ) * I))‖ := Complex.abs_re_le_norm _
      _ = ‖expRatio L (ρ - (1 / 2 + (t : ℂ) * I))‖ / ‖ρ - (1 / 2 + (t : ℂ) * I)‖ := by
          unfold rieszKernel; rw [norm_div]
      _ ≤ C₀ / ‖ρ - (1 / 2 + (t : ℂ) * I)‖ := by
          apply div_le_div_of_nonneg_right _ (norm_nonneg _)
          have := hbound _ (by rw [hre]; linarith)
          exact this.trans (div_le_self hC₀ (by linarith [abs_nonneg ((ρ - (1 / 2 + (t : ℂ) * I)).im)]))
      _ ≤ C₀ / |ρ.re - 1 / 2| := by
          apply div_le_div_of_nonneg_left hC₀ hδ
          rw [← hre]; exact Complex.abs_re_le_norm _

/-- For `‖ρ‖` large the kernel is `O(‖ρ‖⁻²)` uniformly for heights in `[a, b]`. -/
theorem rieszKernel_bound_uniform {L : ℝ} (hL : 0 < L) (a b : ℝ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧ ∀ ρ : ℂ, 0 ≤ ρ.re → ρ.re ≤ 1 → R ≤ ‖ρ‖ → ∀ t ∈ Icc a b,
      ‖rieszKernel L (ρ - (1 / 2 + (t : ℂ) * I))‖ ≤ C / ‖ρ‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hbound⟩ := expRatio_bound hL (b' := 1 / 2) (by norm_num)
  set T : ℝ := max |a| |b| with hT
  refine ⟨4 * C₀, 4 * (T + 2), by positivity, by positivity, fun ρ hre0 hre1 hR t ht => ?_⟩
  have hT0 : 0 ≤ T := le_trans (abs_nonneg a) (le_max_left _ _)
  have htT : |t| ≤ T := by
    rcases ht with ⟨h1, h2⟩
    rw [abs_le]; constructor
    · linarith [neg_abs_le a, le_max_left |a| |b|]
    · linarith [le_abs_self b, le_max_right |a| |b|]
  set w : ℂ := ρ - (1 / 2 + (t : ℂ) * I) with hw
  have hwre : w.re = ρ.re - 1 / 2 := by simp [hw]
  have hwim : w.im = ρ.im - t := by simp [hw]
  -- |Im ρ| ≥ ‖ρ‖ − 1 and ‖s₀‖ ≤ 1/2 + |t|
  have him : ‖ρ‖ - 1 ≤ |ρ.im| := by
    have := Complex.norm_le_abs_re_add_abs_im ρ
    have : |ρ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hs₀ : ‖(1 / 2 + (t : ℂ) * I)‖ ≤ 1 / 2 + T := by
    calc ‖(1 / 2 + (t : ℂ) * I)‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 1 / 2 + |t| := by simp
      _ ≤ 1 / 2 + T := by linarith
  have hnw : ‖ρ‖ / 2 ≤ ‖w‖ := by
    have := norm_sub_norm_le ρ (1 / 2 + (t : ℂ) * I)
    have hρ2 : 4 * (T + 2) ≤ ‖ρ‖ := hR
    rw [hw]; linarith
  have hnim : ‖ρ‖ / 2 ≤ 1 + |w.im| := by
    rw [hwim]
    have h1 : |ρ.im| - |t| ≤ |ρ.im - t| := abs_sub_abs_le_abs_sub _ _
    have hρ2 : 4 * (T + 2) ≤ ‖ρ‖ := hR
    linarith
  have hexp : ‖expRatio L w‖ ≤ C₀ / (1 + |w.im|) := hbound w (by rw [hwre]; linarith)
  have hρpos : 0 < ‖ρ‖ := by linarith [hR, show (0:ℝ) < 4 * (T + 2) by positivity]
  have hwpos : 0 < ‖w‖ := by linarith
  calc ‖rieszKernel L w‖ = ‖expRatio L w‖ / ‖w‖ := by unfold rieszKernel; rw [norm_div]
    _ ≤ (C₀ / (1 + |w.im|)) / ‖w‖ := div_le_div_of_nonneg_right hexp (norm_nonneg _)
    _ ≤ (C₀ / (‖ρ‖ / 2)) / (‖ρ‖ / 2) := by
        gcongr
    _ = 4 * C₀ / ‖ρ‖ ^ 2 := by field_simp; ring

/-! ## 3. Measurability, integrability, and the exchange -/

/-- The kernel's real part is measurable in the height (no removable-singularity argument needed:
`expRatio` is continuous and division is measurable). -/
theorem rieszKernel_re_measurable (L : ℝ) (ρ : ℂ) :
    Measurable (fun t : ℝ => (rieszKernel L (ρ - (1 / 2 + (t : ℂ) * I))).re) := by
  have hK : Measurable (fun w : ℂ => rieszKernel L w) := by
    unfold rieszKernel
    exact (expRatio_differentiable L).continuous.measurable.div measurable_id
  have hshift : Continuous (fun t : ℝ => ρ - (1 / 2 + (t : ℂ) * I)) := by fun_prop
  exact Complex.continuous_re.measurable.comp (hK.comp hshift.measurable)

/-- Each zero's weighted kernel is integrable on the gap. -/
theorem integrableOn_weight {L : ℝ} (hL : 0 < L) (a b : ℝ) (ρ : Zero) :
    IntegrableOn (fun t : ℝ => (ZD.xiOrderNat ρ.val : ℝ)
      * (rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re) (Ioc a b) := by
  obtain ⟨M, hM⟩ := rieszKernel_re_bound_fixed hL ρ.val ρ.2.2.1.le
  apply Measure.integrableOn_of_bounded (M := (ZD.xiOrderNat ρ.val : ℝ) * M)
  · simp
  · exact (measurable_const.mul (rieszKernel_re_measurable L ρ.val)).aestronglyMeasurable
  · refine Eventually.of_forall (fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ))]
    exact mul_le_mul_of_nonneg_left (hM t) (by positivity)

/-- The pointwise density is the sum of the weighted kernels. -/
theorem rieszZeroDensity_eq_tsum_re {L : ℝ} (hL : 0 < L) (a b : ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    rieszZeroDensity L t
      = ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℝ) * (rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re := by
  unfold rieszZeroDensity
  obtain ⟨C, R, hC, hR, hbound⟩ := rieszKernel_bound_uniform hL a b
  have hsum : Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ)
      * rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))) := by
    have hg : Summable (fun ρ : Zero => C * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :=
      (ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros).mul_left C
    apply Summable.of_norm_bounded_eventually hg
    filter_upwards [CriticalLinePhasor.StBridge.eventually_cofinite_norm_ge R] with ρ hρR
    rw [norm_mul, Complex.norm_natCast]
    have := hbound ρ.val ρ.2.1.le ρ.2.2.1.le hρR t ht
    calc (ZD.xiOrderNat ρ.val : ℝ) * ‖rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))‖
        ≤ (ZD.xiOrderNat ρ.val : ℝ) * (C / ‖ρ.val‖ ^ 2) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = C * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by ring
  rw [Complex.re_tsum hsum]
  refine tsum_congr (fun ρ => ?_)
  rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]

/-- The integrated norms are summable over the zeros. -/
theorem summable_integral_norm_weight {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) :
    Summable (fun ρ : Zero => ∫ t in Ioc a b, ‖(ZD.xiOrderNat ρ.val : ℝ)
      * (rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re‖) := by
  obtain ⟨C, R, hC, hR, hbound⟩ := rieszKernel_bound_uniform hL a b
  have hg : Summable (fun ρ : Zero => ((b - a) * C) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :=
    (ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros).mul_left _
  apply Summable.of_norm_bounded_eventually hg
  filter_upwards [CriticalLinePhasor.StBridge.eventually_cofinite_norm_ge R] with ρ hρR
  have hnn : 0 ≤ ∫ t in Ioc a b, ‖(ZD.xiOrderNat ρ.val : ℝ)
      * (rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hnn]
  have hconst : IntegrableOn (fun _ : ℝ => (ZD.xiOrderNat ρ.val : ℝ) * (C / ‖ρ.val‖ ^ 2)) (Ioc a b) :=
    integrableOn_const (by simp)
  calc ∫ t in Ioc a b, ‖(ZD.xiOrderNat ρ.val : ℝ) * (rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re‖
      ≤ ∫ t in Ioc a b, (ZD.xiOrderNat ρ.val : ℝ) * (C / ‖ρ.val‖ ^ 2) := by
        apply setIntegral_mono_on (integrableOn_weight hL a b ρ).norm hconst measurableSet_Ioc
        intro t ht
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ))]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (Complex.abs_re_le_norm _).trans (hbound ρ.val ρ.2.1.le ρ.2.2.1.le hρR t ⟨ht.1.le, ht.2⟩)
    _ = ((b - a) * C) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
        rw [setIntegral_const, smul_eq_mul]
        have hvol : (volume : Measure ℝ).real (Ioc a b) = b - a := by
          rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
        rw [hvol]
        ring

/-- **The smoothed count over a gap is the sum of the per-zero weights.** -/
theorem smoothed_count_eq_tsum_weights {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) :
    (1 / Real.pi) * ∫ t in a..b, rieszZeroDensity L t
      = ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℝ) * gapWeight L a b ρ.val := by
  rw [intervalIntegral.integral_of_le hab]
  have hpt : ∀ t ∈ Ioc a b, rieszZeroDensity L t
      = ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℝ) * (rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re :=
    fun t ht => rieszZeroDensity_eq_tsum_re hL a b ⟨ht.1.le, ht.2⟩
  rw [setIntegral_congr_fun measurableSet_Ioc hpt]
  rw [← integral_tsum_of_summable_integral_norm (fun ρ => integrableOn_weight hL a b ρ)
    (summable_integral_norm_weight hL hab)]
  rw [← tsum_mul_left]
  refine tsum_congr (fun ρ => ?_)
  unfold gapWeight
  rw [intervalIntegral.integral_of_le hab, integral_const_mul]
  ring

/-- The boundary term: sharp count minus smoothed count over the gap. -/
noncomputable def boundaryTerm (L a b : ℝ) : ℝ :=
  (bandCountMult a b : ℝ) - ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℝ) * gapWeight L a b ρ.val

/-- **Sharp count = 1 + integrated remainder + boundary term** on a station gap of the
Riesz-strained clock (608 + the exchange). -/
theorem gap_count_decomposition {L : ℝ} (hL : 0 < L) {B : ℝ} (hB : ∀ t, |rieszStrain L t| ≤ B)
    {n : ℕ} (hn : regClock (rieszStrain L) 10 < stationLevel n)
    (hrem : IntervalIntegrable (rieszRemainder L) volume
      (station (rieszStrain L) n) (station (rieszStrain L) (n + 1))) :
    (bandCountMult (station (rieszStrain L) n) (station (rieszStrain L) (n + 1)) : ℝ)
      = 1 + (1 / Real.pi) * (∫ t in station (rieszStrain L) n..station (rieszStrain L) (n + 1),
            rieszRemainder L t)
        + boundaryTerm L (station (rieszStrain L) n) (station (rieszStrain L) (n + 1)) := by
  have hlt := station_lt (rieszStrain_continuous L) hB hn
  have h1 := smoothed_gap_count hL hB hn hrem
  have h2 := smoothed_count_eq_tsum_weights hL (a := station (rieszStrain L) n)
    (b := station (rieszStrain L) (n + 1)) hlt.le
  unfold boundaryTerm
  linarith

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.rieszKernel_re_line_eq
#print axioms CriticalLinePhasor.ContourArgument.rieszKernel_bound_uniform
#print axioms CriticalLinePhasor.ContourArgument.rieszZeroDensity_eq_tsum_re
#print axioms CriticalLinePhasor.ContourArgument.smoothed_count_eq_tsum_weights
#print axioms CriticalLinePhasor.ContourArgument.gap_count_decomposition
