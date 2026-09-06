import RequestProject.RieszStrainDeriv
import RequestProject.RegistrationStations

/-!
# The smoothed count over a station gap is one (ledger 608)

Integrate `density_on_line` over a station gap `(t_n, t_{n+1}]` of the Riesz-strained clock
`ϑ/π + rieszStrain L`. The identity holds at every good height, and the non-good heights in a gap are
the finitely many zero ordinates there, so it holds almost everywhere on the gap. The prime bank
integrates to the strain difference (`rieszStrain_hasDerivAt`), the clock rate to the clock
difference (`theta_sub_theta`), and the station equation makes their sum exactly one:

  `(1/π) ∫_{t_n}^{t_{n+1}} Re Σ'_ρ m_ρ K_L(ρ − ½ − it) dt
     = 1 + (1/π) ∫_{t_n}^{t_{n+1}} Re[K_L(1−s₀) + K_L(−s₀) + rem_L(s₀)] dt`

(`smoothed_gap_count`). This is the registry's design identity: the Fejér-smoothed zero count per
station gap is one, by construction, up to the explicit archimedean remainders. The sharp count differs
from the smoothed one by the Fejér boundary term alone.

The integrability of the archimedean remainder `rem_L(½ + it)` in `t` over the gap is taken as a
hypothesis here (`hrem`); it is the continuity in `t` of the two clock line integrals, a dominated
convergence statement, owed as the next small compile.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real
open CriticalLinePhasor.CarrierScale (theta clockRate continuous_clockRate)

namespace CriticalLinePhasor.ContourArgument

/-- The strip window used throughout: `a = −1`, `b = 2`. -/
theorem window_neg_one : (-1 : ℝ) < 0 := by norm_num
theorem window_two : (1 : ℝ) < 2 := by norm_num

/-- The Riesz-smoothed zero density on the line. -/
noncomputable def rieszZeroDensity (L : ℝ) (t : ℝ) : ℝ :=
  (∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re

/-- The explicit archimedean remainder density on the line (window `a = −1`, `b = 2`). -/
noncomputable def rieszRemainder (L : ℝ) (t : ℝ) : ℝ :=
  (rieszKernel L (1 - (1 / 2 + (t : ℂ) * I)) + rieszKernel L (-(1 / 2 + (t : ℂ) * I))).re
    + (rieszClockRemainder L (-1) 2 (1 / 2 + (t : ℂ) * I)).re

/-- The density identity, rearranged: at a good height the zero density is the clock rate minus the
bank's real part plus the remainder. -/
theorem rieszZeroDensity_eq {L : ℝ} (hL : 0 < L) {t : ℝ} (ht : GoodHeight t) :
    rieszZeroDensity L t
      = clockRate t - (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re + rieszRemainder L t := by
  unfold rieszZeroDensity rieszRemainder
  rw [density_on_line hL ht window_neg_one window_two]
  ring

/-- Non-good heights in `(0, ∞)` are zero ordinates: finitely many below any bound. -/
theorem goodHeight_ae {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b → GoodHeight t := by
  classical
  -- the bad set is contained in the finite set of ordinates of zeros with `0 < Im ≤ max a b`
  set T : ℝ := max a b
  have hfin : ((fun ρ : ℂ => ρ.im) '' stripZeroWindow T).Finite :=
    (stripZeroWindow_finite T).image _
  have hsub : {t : ℝ | t ∈ Ι a b ∧ ¬ GoodHeight t} ⊆ (fun ρ : ℂ => ρ.im) '' stripZeroWindow T := by
    intro t ⟨htI, hbad⟩
    have hpos : 0 < t := by
      rcases Set.mem_uIoc.1 htI with h | h
      · linarith [h.1]
      · linarith [h.1]
    have hle : t ≤ T := by
      rcases Set.mem_uIoc.1 htI with h | h
      · exact h.2.trans (le_max_right _ _)
      · exact h.2.trans (le_max_left _ _)
    unfold GoodHeight at hbad
    push_neg at hbad
    obtain ⟨ρ, hρ, hρt⟩ := hbad hpos
    exact ⟨ρ, ⟨hρ, by rw [hρt]; exact hpos, by rw [hρt]; exact hle⟩, hρt⟩
  have hnull : (volume : Measure ℝ) {t : ℝ | t ∈ Ι a b ∧ ¬ GoodHeight t} = 0 :=
    measure_mono_null hsub (hfin.measure_zero _)
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun t ht => ?_) hnull
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [Classical.not_imp] at ht
  exact ht

/-- The two end kernels are continuous in `t`. -/
theorem endKernels_continuous {L : ℝ} :
    Continuous (fun t : ℝ =>
      (rieszKernel L (1 - (1 / 2 + (t : ℂ) * I)) + rieszKernel L (-(1 / 2 + (t : ℂ) * I))).re) := by
  have h1 : Continuous (fun t : ℝ => rieszKernel L ((1 / 2 : ℝ) + (-t : ℝ) * I - 0)) :=
    (rieszKernel_line_continuous L (σ := 1 / 2) (s₀ := 0) (by norm_num)).comp continuous_neg
  have h2 : Continuous (fun t : ℝ => rieszKernel L ((-1 / 2 : ℝ) + (-t : ℝ) * I - 0)) :=
    (rieszKernel_line_continuous L (σ := -1 / 2) (s₀ := 0) (by norm_num)).comp continuous_neg
  have : Continuous (fun t : ℝ => rieszKernel L (1 - (1 / 2 + (t : ℂ) * I))
      + rieszKernel L (-(1 / 2 + (t : ℂ) * I))) := by
    refine (h1.add h2).congr (fun t => ?_)
    simp only [Pi.add_apply]
    congr 1 <;> (congr 1; push_cast; ring)
  exact Complex.continuous_re.comp this

/-- The bank's real part is continuous in `t`. -/
theorem rieszPrimeSum_re_continuous {L : ℝ} (hL : 0 < L) :
    Continuous (fun t : ℝ => (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re) := by
  have h : ∀ t : ℝ, (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re
      = ∑ n ∈ Finset.range (⌊Real.exp L⌋₊ + 1),
          rieszProfile L (Real.log n) * ((ArithmeticFunction.vonMangoldt n)
            * Real.exp (-(1 / 2) * Real.log n) * Real.cos (t * Real.log n)) := by
    intro t
    rw [rieszPrimeSum_eq_finset hL, Complex.re_sum]
    exact Finset.sum_congr rfl (fun n _ => by rw [Complex.re_ofReal_mul, re_term_line])
  simp_rw [h]
  fun_prop

/-- The bank integrates to `−π` times the strain difference. -/
theorem integral_rieszPrimeSum_re {L : ℝ} (hL : 0 < L) (a b : ℝ) :
    ∫ t in a..b, (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re
      = -Real.pi * (rieszStrain L b - rieszStrain L a) := by
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (rieszStrain L)
      (-(1 / Real.pi) * (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re) t :=
    fun t _ => rieszStrain_hasDerivAt hL t
  have hint : IntervalIntegrable (fun t : ℝ => -(1 / Real.pi) * (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re)
      volume a b :=
    (continuous_const.mul (rieszPrimeSum_re_continuous hL)).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hftc
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  generalize hX : ∫ t in a..b, (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re = X at hftc ⊢
  field_simp at hftc
  linarith

/-- **The smoothed count over a station gap is one plus the integrated remainders.** -/
theorem smoothed_gap_count {L : ℝ} (hL : 0 < L) {B : ℝ} (hB : ∀ t, |rieszStrain L t| ≤ B)
    {n : ℕ} (hn : regClock (rieszStrain L) 10 < stationLevel n)
    (hrem : IntervalIntegrable (rieszRemainder L) volume
      (station (rieszStrain L) n) (station (rieszStrain L) (n + 1))) :
    (1 / Real.pi) * ∫ t in station (rieszStrain L) n..station (rieszStrain L) (n + 1),
        rieszZeroDensity L t
      = 1 + (1 / Real.pi) * ∫ t in station (rieszStrain L) n..station (rieszStrain L) (n + 1),
          rieszRemainder L t := by
  set a := station (rieszStrain L) n with ha
  set b := station (rieszStrain L) (n + 1) with hb
  have hn' : regClock (rieszStrain L) 10 < stationLevel (n + 1) := by
    rw [stationLevel_succ]; linarith
  obtain ⟨ha10, hGa⟩ := station_spec (rieszStrain_continuous L) hB hn
  obtain ⟨hb10, hGb⟩ := station_spec (rieszStrain_continuous L) hB hn'
  have hπ := Real.pi_pos
  -- the density equals the explicit right side almost everywhere on the gap
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b →
      rieszZeroDensity L t
        = clockRate t - (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re + rieszRemainder L t := by
    filter_upwards [goodHeight_ae (a := a) (b := b) (by linarith) (by linarith)] with t ht htI
    exact rieszZeroDensity_eq hL (ht htI)
  rw [intervalIntegral.integral_congr_ae hae]
  -- split the right side
  have i1 : IntervalIntegrable clockRate volume a b := continuous_clockRate.intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t : ℝ => (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re) volume a b :=
    (rieszPrimeSum_re_continuous hL).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (i1.sub i2) hrem, intervalIntegral.integral_sub i1 i2,
    ← CriticalLinePhasor.ResidueJump.theta_sub_theta, integral_rieszPrimeSum_re hL]
  -- the station equation: (ϑ/π + Ŝ)(b) − (ϑ/π + Ŝ)(a) = 1
  unfold regClock at hGa hGb
  rw [stationLevel_succ] at hGb
  have hstation : (theta b - theta a) / Real.pi + (rieszStrain L b - rieszStrain L a) = 1 := by
    have e1 : theta a / Real.pi + rieszStrain L a = stationLevel n := hGa
    have e2 : theta b / Real.pi + rieszStrain L b = stationLevel n + 1 := hGb
    have : (theta b - theta a) / Real.pi = theta b / Real.pi - theta a / Real.pi := by ring
    linarith
  have hpi : (1 / Real.pi) * (theta b - theta a - (-Real.pi * (rieszStrain L b - rieszStrain L a)))
      = (theta b - theta a) / Real.pi + (rieszStrain L b - rieszStrain L a) := by
    field_simp
    ring
  rw [mul_add, hpi, hstation]

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.goodHeight_ae
#print axioms CriticalLinePhasor.ContourArgument.integral_rieszPrimeSum_re
#print axioms CriticalLinePhasor.ContourArgument.smoothed_gap_count
