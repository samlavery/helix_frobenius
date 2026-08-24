import RequestProject.ClockRateStirling
import RequestProject.CarrierScaleCompensation
import RequestProject.DVPArctanEnclosure
import Zeta23.GammaFacts.Series

/-!
# The two-sided θ enclosure over `[1, T]` with EXPLICIT constants

Zeta23's `mu_stirling` is existential, but its witness is explicit in the
proof: `C = 20/(2π) = 10/π`.  Restating it explicitly and integrating gives
`θ(T) − θ(1)` to within `10·(1 − 1/T)` of the closed Stirling main term —
the count-formula ingredient for the finite conjunct (RH_LEDGER 342).
-/

open Complex Filter Topology intervalIntegral
open CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **Explicit Stirling for μ**: `|μ(τ) − (1/2π)·log(|τ|/2π)| ≤ (10/π)/τ²`
for `|τ| ≥ 1` (the witness inside `Zeta23.StirlingVert.mu_stirling`,
restated with its constant). -/
theorem mu_stirling_explicit {τ : ℝ} (hτ : 1 ≤ |τ|) :
    |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))|
      ≤ (10 / Real.pi) / τ ^ 2 := by
  have hπ := Real.pi_pos
  have hτ0 : 0 < |τ| := by linarith
  have hτne : τ ≠ 0 := by
    intro h
    rw [h] at hτ0
    simp at hτ0
  have hτ2 : (0:ℝ) < τ ^ 2 := by positivity
  have ht : 1 / 2 ≤ |τ / 2| := by
    rw [abs_div, abs_two]
    linarith
  have h := Zeta23.StirlingVert.re_digamma_stirling' (a := 1 / 4)
    (by norm_num) (by norm_num) ht
  set D : ℝ := (Complex.digamma ((((1:ℝ) / 4 : ℝ)) + Complex.I * ((τ / 2 : ℝ) : ℂ))).re
    - Real.log |τ / 2| with hD
  have hD5 : |D| ≤ 5 / (τ / 2) ^ 2 := h
  have hD20 : |D| ≤ 20 / τ ^ 2 := by
    have hval : 5 / (τ / 2) ^ 2 = 20 / τ ^ 2 := by
      field_simp
      ring
    rwa [hval] at hD5
  have hlogs : Real.log (|τ| / (2 * Real.pi))
      = Real.log |τ / 2| - Real.log Real.pi := by
    rw [abs_div, abs_two, Real.log_div hτ0.ne' (by positivity),
      Real.log_div (by positivity : |τ| ≠ 0) two_ne_zero,
      Real.log_mul two_ne_zero hπ.ne']
    ring
  have key : Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))
      = (1 / (2 * Real.pi)) * D := by
    rw [Zeta23.MuFields.mu_eq τ, hlogs, hD]
    ring
  rw [key, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi))]
  calc (1 / (2 * Real.pi)) * |D|
      ≤ (1 / (2 * Real.pi)) * (20 / τ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hD20 (by positivity)
    _ = (10 / Real.pi) / τ ^ 2 := by
        field_simp
        ring

/-- The Stirling antiderivative for the θ main term. -/
def thetaMain (x : ℝ) : ℝ := (x * Real.log (x / (2 * Real.pi)) - x) / 2

/-- **The θ-increment enclosure**: on `[1, T]`,
`|（θ(T) − θ(1)) − (M(T) − M(1))| ≤ 10·(1 − 1/T)` with
`M(x) = (x·log(x/2π) − x)/2`.  Every constant is explicit. -/
theorem theta_increment_enclosure {T : ℝ} (hT : 1 ≤ T) :
    |(theta T - theta 1) - (thetaMain T - thetaMain 1)|
      ≤ 10 * (1 - 1 / T) := by
  have hπ := Real.pi_pos
  have hT0 : (0:ℝ) < T := by linarith
  -- θ increment as an interval integral of clockRate
  have hderiv : ∀ t ∈ Set.uIcc (1:ℝ) T,
      HasDerivAt theta (clockRate t) t := fun t _ => theta_hasDerivAt t
  have hint : IntervalIntegrable clockRate MeasureTheory.volume 1 T :=
    (continuous_clockRate.intervalIntegrable _ _)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- the main antiderivative
  have hmder : ∀ t ∈ Set.uIcc (1:ℝ) T,
      HasDerivAt thetaMain (Real.log (t / (2 * Real.pi)) / 2) t := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    have ht0 : (0:ℝ) < t := by linarith [ht.1]
    have h1 : HasDerivAt (fun x : ℝ => x / (2 * Real.pi))
        (1 / (2 * Real.pi)) t := (hasDerivAt_id t).div_const _
    have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)))
        ((t / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi))) t :=
      (Real.hasDerivAt_log (by positivity)).comp t h1
    have h3 : HasDerivAt (fun x : ℝ => x * Real.log (x / (2 * Real.pi)))
        (1 * Real.log (t / (2 * Real.pi))
          + t * ((t / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi)))) t :=
      (hasDerivAt_id t).mul h2
    have h4 := (h3.sub (hasDerivAt_id t)).div_const 2
    have hval : (1 * Real.log (t / (2 * Real.pi))
        + t * ((t / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi))) - 1) / 2
        = Real.log (t / (2 * Real.pi)) / 2 := by
      have hcancel : t * ((t / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi))) = 1 := by
        field_simp
      rw [hcancel]
      ring
    rw [hval] at h4
    exact h4
  have hmint : IntervalIntegrable
      (fun t : ℝ => Real.log (t / (2 * Real.pi)) / 2)
      MeasureTheory.volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div_const
    apply ContinuousOn.log
    · exact (continuous_id.div_const _).continuousOn
    · intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      have : (0:ℝ) < t := by linarith [ht.1]
      positivity
  have hmftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hmder hmint
  -- the difference is the integrated Stirling error
  have hdiff : (theta T - theta 1) - (thetaMain T - thetaMain 1)
      = ∫ t in (1:ℝ)..T,
          (clockRate t - Real.log (t / (2 * Real.pi)) / 2) := by
    rw [intervalIntegral.integral_sub hint hmint, hftc, hmftc]
  rw [hdiff]
  -- pointwise: |clockRate − main'| ≤ 10/t²
  have hpt : ∀ t ∈ Set.uIcc (1:ℝ) T,
      |clockRate t - Real.log (t / (2 * Real.pi)) / 2| ≤ 10 / t ^ 2 := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    have ht1 : (1:ℝ) ≤ t := ht.1
    have ht0 : (0:ℝ) < t := by linarith
    have habs : |t| = t := abs_of_pos ht0
    have hmu := mu_stirling_explicit (τ := t) (by rwa [habs])
    rw [habs] at hmu
    have hcr := CriticalLinePhasor.CarrierScale.clockRate_eq_pi_mul_mu t
    have hkey : clockRate t - Real.log (t / (2 * Real.pi)) / 2
        = Real.pi * (Zeta23.mu t
            - (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))) := by
      rw [hcr]
      field_simp
    rw [hkey, abs_mul, abs_of_pos hπ]
    calc Real.pi * |Zeta23.mu t
        - (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))|
        ≤ Real.pi * ((10 / Real.pi) / t ^ 2) :=
          mul_le_mul_of_nonneg_left hmu hπ.le
      _ = 10 / t ^ 2 := by
          field_simp
  -- integrate the majorant: ∫₁^T 10/t² = 10(1 − 1/T)
  have hmajder : ∀ t ∈ Set.uIcc (1:ℝ) T,
      HasDerivAt (fun x : ℝ => 10 * (1 - 1 / x)) (10 / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    have ht0 : (0:ℝ) < t := by linarith [ht.1]
    have h1 : HasDerivAt (fun x : ℝ => 1 / x) (-(1 / t ^ 2)) t := by
      have h0 := hasDerivAt_inv ht0.ne'
      have heq : (fun x : ℝ => 1 / x) = fun x : ℝ => x⁻¹ := by
        funext x
        rw [one_div]
      rw [heq, show -(1 / t ^ 2) = -(t ^ 2)⁻¹ by rw [one_div]]
      exact h0
    have h2 := ((hasDerivAt_const t (1:ℝ)).sub h1).const_mul (10:ℝ)
    have hval : (10:ℝ) * (0 - -(1 / t ^ 2)) = 10 / t ^ 2 := by
      ring
    rw [hval] at h2
    exact h2
  have hmajint : IntervalIntegrable (fun t : ℝ => 10 / t ^ 2)
      MeasureTheory.volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact (continuous_pow 2).continuousOn
    · intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      have : (0:ℝ) < t := by linarith [ht.1]
      positivity
  have hmajftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hmajder hmajint
  have hmajval : (fun x : ℝ => 10 * (1 - 1 / x)) T
      - (fun x : ℝ => 10 * (1 - 1 / x)) 1 = 10 * (1 - 1 / T) := by
    simp only
    norm_num
  rw [hmajval] at hmajftc
  -- the norm of the integral
  have hsub : IntervalIntegrable
      (fun t : ℝ => clockRate t - Real.log (t / (2 * Real.pi)) / 2)
      MeasureTheory.volume 1 T := hint.sub hmint
  calc |∫ t in (1:ℝ)..T,
        (clockRate t - Real.log (t / (2 * Real.pi)) / 2)|
      ≤ ∫ t in (1:ℝ)..T, 10 / t ^ 2 := by
        rw [show |∫ t in (1:ℝ)..T,
            (clockRate t - Real.log (t / (2 * Real.pi)) / 2)|
          = ‖∫ t in (1:ℝ)..T,
            (clockRate t - Real.log (t / (2 * Real.pi)) / 2)‖ from
          (Real.norm_eq_abs _).symm]
        apply intervalIntegral.norm_integral_le_of_norm_le hT _ hmajint
        apply Filter.Eventually.of_forall
        intro t ht
        rw [Real.norm_eq_abs]
        apply hpt t
        rw [Set.uIcc_of_le hT]
        exact Set.Ioc_subset_Icc_self ht
    _ = 10 * (1 - 1 / T) := hmajftc

/-- **The θ(1) closed form**: the base value of the census clock is
`θ(1) = (S − γ − 2·arctan 2 − log π)/2` with
`S = Σ'ₙ (1/(n+1) − 2·arctan(1/(2n+5/2)))` — every piece certifiable. -/
theorem theta_one_eq :
    theta 1 = ((∑' n : ℕ,
        (1/((n:ℝ)+1) - 2 * Real.arctan (1/(2*((n:ℝ)+5/4)))))
      - Real.eulerMascheroniConstant - 2 * Real.arctan 2
      - Real.log Real.pi) / 2 := by
  have hπ := Real.pi_pos
  -- the pointwise identity
  have hpt : ∀ t : ℝ,
      (∑' n : ℕ, (1/((n:ℝ)+1) - ((n:ℝ)+5/4)/(((n:ℝ)+5/4)^2 + t^2/4)))
      = 2 * clockRate t + Real.eulerMascheroniConstant
        + (1/4)/((1/4)^2 + t^2/4) + Real.log Real.pi := by
    intro t
    set w : ℂ := (((1:ℝ)/4 : ℝ) : ℂ) + Complex.I * ((t/2 : ℝ) : ℂ) with hw
    have hwre : w.re = 1/4 := by
      rw [hw]
      simp
    have hwim : w.im = t/2 := by
      rw [hw]
      simp
    have hwmem : w ∈ Complex.integerComplement := by
      intro hmem
      rcases hmem with ⟨m, hm⟩
      have hre := congrArg Complex.re hm
      rw [hwre] at hre
      simp only [Complex.intCast_re] at hre
      have h4 : (4 : ℝ) * (m : ℝ) = 1 := by linarith
      have h4' : (4 * m : ℤ) = 1 := by exact_mod_cast h4
      omega
    have hs := Zeta23.DigammaSeries.hasSum_digamma_series hwmem
    have hre := Complex.hasSum_re hs
    have hterm : ∀ n : ℕ,
        ((1 / ((n:ℂ) + 1) - 1 / (w + n + 1)).re)
        = 1/((n:ℝ)+1) - ((n:ℝ)+5/4)/(((n:ℝ)+5/4)^2 + t^2/4) := by
      intro n
      rw [Complex.sub_re]
      congr 1
      · rw [one_div, Complex.inv_re]
        have h1 : ((n:ℂ) + 1).re = (n:ℝ) + 1 := by
          simp
        have h2 : Complex.normSq ((n:ℂ) + 1) = ((n:ℝ)+1)^2 := by
          rw [Complex.normSq_apply]
          simp
          ring
        rw [h1, h2]
        rw [one_div]
        rw [sq]
        field_simp
      · rw [one_div, Complex.inv_re]
        have h1 : (w + n + 1).re = (n:ℝ) + 5/4 := by
          rw [Complex.add_re, Complex.add_re, hwre]
          simp
          ring
        have h2 : (w + n + 1).im = t/2 := by
          rw [Complex.add_im, Complex.add_im, hwim]
          simp
        rw [Complex.normSq_apply, h1, h2]
        congr 1
        ring
    have hdig : (Complex.digamma w).re
        = 2 * clockRate t + Real.log Real.pi := by
      have hmu := Zeta23.MuFields.mu_eq t
      have hcr := CriticalLinePhasor.CarrierScale.clockRate_eq_pi_mul_mu t
      have hwc : w = (((1 : ℝ) / 4 : ℝ) : ℂ)
          + Complex.I * ((t / 2 : ℝ) : ℂ) := hw
      rw [← hwc] at hmu
      have hexpand : Real.pi * Zeta23.mu t
          = (Complex.digamma w).re / 2 - Real.log Real.pi / 2 := by
        rw [hmu]
        field_simp
      rw [hcr, hexpand]
      ring
    have hval : (Complex.digamma w
          + ((Real.eulerMascheroniConstant : ℝ) : ℂ) + 1 / w).re
        = 2 * clockRate t + Real.log Real.pi
          + Real.eulerMascheroniConstant + (1/4)/((1/4)^2 + t^2/4) := by
      rw [Complex.add_re, Complex.add_re, hdig, Complex.ofReal_re,
        one_div, Complex.inv_re, Complex.normSq_apply, hwre, hwim]
      ring
    have htsum := hre.tsum_eq
    rw [hval] at htsum
    calc (∑' n : ℕ, (1/((n:ℝ)+1) - ((n:ℝ)+5/4)/(((n:ℝ)+5/4)^2 + t^2/4)))
        = ∑' n : ℕ, ((1 / ((n:ℂ) + 1) - 1 / (w + n + 1)).re) :=
          (tsum_congr hterm).symm
      _ = 2 * clockRate t + Real.log Real.pi
          + Real.eulerMascheroniConstant + (1/4)/((1/4)^2 + t^2/4) := htsum
      _ = 2 * clockRate t + Real.eulerMascheroniConstant
          + (1/4)/((1/4)^2 + t^2/4) + Real.log Real.pi := by ring
  -- integrate both sides
  have hint_lor : IntervalIntegrable
      (fun t : ℝ => (1/4)/((1/4)^2 + t^2/4)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    apply continuous_const.div
    · continuity
    · intro t
      positivity
  have hL := integral_lorentz_eq_arctan (a := (1/4:ℝ)) (by norm_num)
  have harctan2 : (1:ℝ)/(2 * (1/4)) = 2 := by norm_num
  rw [harctan2] at hL
  have hRHS : ∫ t in (0:ℝ)..1,
      (2 * clockRate t + Real.eulerMascheroniConstant
        + (1/4)/((1/4)^2 + t^2/4) + Real.log Real.pi)
      = 2 * theta 1 + Real.eulerMascheroniConstant
        + 2 * Real.arctan 2 + Real.log Real.pi := by
    have hi1 : IntervalIntegrable (fun t : ℝ => 2 * clockRate t)
        MeasureTheory.volume 0 1 :=
      (continuous_clockRate.intervalIntegrable _ _).const_mul _
    have hi2 : IntervalIntegrable
        (fun _ : ℝ => Real.eulerMascheroniConstant)
        MeasureTheory.volume 0 1 := intervalIntegrable_const
    have hi4 : IntervalIntegrable (fun _ : ℝ => Real.log Real.pi)
        MeasureTheory.volume 0 1 := intervalIntegrable_const
    rw [intervalIntegral.integral_add
        ((hi1.add hi2).add hint_lor) hi4,
      intervalIntegral.integral_add (hi1.add hi2) hint_lor,
      intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, hL,
      intervalIntegral.integral_const, intervalIntegral.integral_const]
    have hth : ∫ u in (0:ℝ)..1, clockRate u = theta 1 := rfl
    rw [hth]
    simp
  have hexch := theta_one_series_integral
  have hcomb : (∑' n : ℕ,
      (1/((n:ℝ)+1) - 2 * Real.arctan (1/(2*((n:ℝ)+5/4)))))
      = 2 * theta 1 + Real.eulerMascheroniConstant
        + 2 * Real.arctan 2 + Real.log Real.pi := by
    rw [← hexch, ← hRHS]
    apply intervalIntegral.integral_congr
    intro t _
    exact hpt t
  linarith

/-- **The general-base θ increment**: on `[T₁, T]`,
`|(θ(T) − θ(T₁)) − (M(T) − M(T₁))| ≤ 10·(1/T₁ − 1/T)` — at `T₁ = 30`,
`T = 58` the error is `0.161`. -/
theorem theta_increment_enclosure_from {T₁ T : ℝ} (h1 : 1 ≤ T₁)
    (hT : T₁ ≤ T) :
    |(theta T - theta T₁) - (thetaMain T - thetaMain T₁)|
      ≤ 10 * (1/T₁ - 1/T) := by
  have hπ := Real.pi_pos
  have hT0 : (0:ℝ) < T := by linarith
  have hT10 : (0:ℝ) < T₁ := by linarith
  have hderiv : ∀ t ∈ Set.uIcc T₁ T,
      HasDerivAt theta (clockRate t) t := fun t _ => theta_hasDerivAt t
  have hint : IntervalIntegrable clockRate MeasureTheory.volume T₁ T :=
    (continuous_clockRate.intervalIntegrable _ _)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hmder : ∀ t ∈ Set.uIcc T₁ T,
      HasDerivAt thetaMain (Real.log (t / (2 * Real.pi)) / 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have ht0 : (0:ℝ) < t := by linarith [ht.1]
    have h1' : HasDerivAt (fun x : ℝ => x / (2 * Real.pi))
        (1 / (2 * Real.pi)) t := (hasDerivAt_id t).div_const _
    have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)))
        ((t / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi))) t :=
      (Real.hasDerivAt_log (by positivity)).comp t h1'
    have h3 : HasDerivAt (fun x : ℝ => x * Real.log (x / (2 * Real.pi)))
        (1 * Real.log (t / (2 * Real.pi))
          + t * ((t / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi)))) t :=
      (hasDerivAt_id t).mul h2
    have h4 := (h3.sub (hasDerivAt_id t)).div_const 2
    have hval : (1 * Real.log (t / (2 * Real.pi))
        + t * ((t / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi))) - 1) / 2
        = Real.log (t / (2 * Real.pi)) / 2 := by
      have hcancel : t * ((t / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi))) = 1 := by
        field_simp
      rw [hcancel]
      ring
    rw [hval] at h4
    exact h4
  have hmint : IntervalIntegrable
      (fun t : ℝ => Real.log (t / (2 * Real.pi)) / 2)
      MeasureTheory.volume T₁ T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div_const
    apply ContinuousOn.log
    · exact (continuous_id.div_const _).continuousOn
    · intro t ht
      rw [Set.uIcc_of_le hT] at ht
      have : (0:ℝ) < t := by linarith [ht.1]
      positivity
  have hmftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hmder hmint
  have hdiff : (theta T - theta T₁) - (thetaMain T - thetaMain T₁)
      = ∫ t in T₁..T,
          (clockRate t - Real.log (t / (2 * Real.pi)) / 2) := by
    rw [intervalIntegral.integral_sub hint hmint, hftc, hmftc]
  rw [hdiff]
  have hpt : ∀ t ∈ Set.uIcc T₁ T,
      |clockRate t - Real.log (t / (2 * Real.pi)) / 2| ≤ 10 / t ^ 2 := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have ht1 : (1:ℝ) ≤ t := by linarith [ht.1]
    have ht0 : (0:ℝ) < t := by linarith
    have habs : |t| = t := abs_of_pos ht0
    have hmu := mu_stirling_explicit (τ := t) (by rwa [habs])
    rw [habs] at hmu
    have hcr := CriticalLinePhasor.CarrierScale.clockRate_eq_pi_mul_mu t
    have hkey : clockRate t - Real.log (t / (2 * Real.pi)) / 2
        = Real.pi * (Zeta23.mu t
            - (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))) := by
      rw [hcr]
      field_simp
    rw [hkey, abs_mul, abs_of_pos hπ]
    calc Real.pi * |Zeta23.mu t
        - (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))|
        ≤ Real.pi * ((10 / Real.pi) / t ^ 2) :=
          mul_le_mul_of_nonneg_left hmu hπ.le
      _ = 10 / t ^ 2 := by
          field_simp
  have hmajder : ∀ t ∈ Set.uIcc T₁ T,
      HasDerivAt (fun x : ℝ => 10 * (1 - 1 / x)) (10 / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have ht0 : (0:ℝ) < t := by linarith [ht.1]
    have h1' : HasDerivAt (fun x : ℝ => 1 / x) (-(1 / t ^ 2)) t := by
      have h0 := hasDerivAt_inv ht0.ne'
      have heq : (fun x : ℝ => 1 / x) = fun x : ℝ => x⁻¹ := by
        funext x
        rw [one_div]
      rw [heq, show -(1 / t ^ 2) = -(t ^ 2)⁻¹ by rw [one_div]]
      exact h0
    have h2 := ((hasDerivAt_const t (1:ℝ)).sub h1').const_mul (10:ℝ)
    have hval : (10:ℝ) * (0 - -(1 / t ^ 2)) = 10 / t ^ 2 := by
      ring
    rw [hval] at h2
    exact h2
  have hmajint : IntervalIntegrable (fun t : ℝ => 10 / t ^ 2)
      MeasureTheory.volume T₁ T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact (continuous_pow 2).continuousOn
    · intro t ht
      rw [Set.uIcc_of_le hT] at ht
      have : (0:ℝ) < t := by linarith [ht.1]
      positivity
  have hmajftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hmajder hmajint
  have hmajval : (fun x : ℝ => 10 * (1 - 1 / x)) T
      - (fun x : ℝ => 10 * (1 - 1 / x)) T₁ = 10 * (1/T₁ - 1/T) := by
    simp only
    ring
  rw [hmajval] at hmajftc
  calc |∫ t in T₁..T,
        (clockRate t - Real.log (t / (2 * Real.pi)) / 2)|
      ≤ ∫ t in T₁..T, 10 / t ^ 2 := by
        rw [show |∫ t in T₁..T,
            (clockRate t - Real.log (t / (2 * Real.pi)) / 2)|
          = ‖∫ t in T₁..T,
            (clockRate t - Real.log (t / (2 * Real.pi)) / 2)‖ from
          (Real.norm_eq_abs _).symm]
        apply intervalIntegral.norm_integral_le_of_norm_le hT _ hmajint
        apply Filter.Eventually.of_forall
        intro t ht
        rw [Real.norm_eq_abs]
        apply hpt t
        rw [Set.uIcc_of_le hT]
        exact Set.Ioc_subset_Icc_self ht
    _ = 10 * (1/T₁ - 1/T) := hmajftc

/-- **THE θ CLOSED FORM AT EVERY HEIGHT**: for `T ≥ 0`,
`θ(T) = (Σ'ₙ (T/(n+1) − 2·arctan(T/(2n+5/2))) − γT − 2·arctan(2T) − T·log π)/2`
— the direct census-clock anchor (design 368); no Stirling error enters. -/
theorem theta_eq {T : ℝ} (hT : 0 ≤ T) :
    theta T = ((∑' n : ℕ,
        (T/((n:ℝ)+1) - 2 * Real.arctan (T/(2*((n:ℝ)+5/4)))))
      - Real.eulerMascheroniConstant * T - 2 * Real.arctan (2*T)
      - T * Real.log Real.pi) / 2 := by
  have hπ := Real.pi_pos
  have hpt : ∀ t : ℝ,
      (∑' n : ℕ, (1/((n:ℝ)+1) - ((n:ℝ)+5/4)/(((n:ℝ)+5/4)^2 + t^2/4)))
      = 2 * clockRate t + Real.eulerMascheroniConstant
        + (1/4)/((1/4)^2 + t^2/4) + Real.log Real.pi := by
    intro t
    set w : ℂ := (((1:ℝ)/4 : ℝ) : ℂ) + Complex.I * ((t/2 : ℝ) : ℂ) with hw
    have hwre : w.re = 1/4 := by
      rw [hw]
      simp
    have hwim : w.im = t/2 := by
      rw [hw]
      simp
    have hwmem : w ∈ Complex.integerComplement := by
      intro hmem
      rcases hmem with ⟨m, hm⟩
      have hre := congrArg Complex.re hm
      rw [hwre] at hre
      simp only [Complex.intCast_re] at hre
      have h4 : (4 : ℝ) * (m : ℝ) = 1 := by linarith
      have h4' : (4 * m : ℤ) = 1 := by exact_mod_cast h4
      omega
    have hs := Zeta23.DigammaSeries.hasSum_digamma_series hwmem
    have hre := Complex.hasSum_re hs
    have hterm : ∀ n : ℕ,
        ((1 / ((n:ℂ) + 1) - 1 / (w + n + 1)).re)
        = 1/((n:ℝ)+1) - ((n:ℝ)+5/4)/(((n:ℝ)+5/4)^2 + t^2/4) := by
      intro n
      rw [Complex.sub_re]
      congr 1
      · rw [one_div, Complex.inv_re]
        have h1 : ((n:ℂ) + 1).re = (n:ℝ) + 1 := by
          simp
        have h2 : Complex.normSq ((n:ℂ) + 1) = ((n:ℝ)+1)^2 := by
          rw [Complex.normSq_apply]
          simp
          ring
        rw [h1, h2]
        rw [one_div]
        rw [sq]
        field_simp
      · rw [one_div, Complex.inv_re]
        have h1 : (w + n + 1).re = (n:ℝ) + 5/4 := by
          rw [Complex.add_re, Complex.add_re, hwre]
          simp
          ring
        have h2 : (w + n + 1).im = t/2 := by
          rw [Complex.add_im, Complex.add_im, hwim]
          simp
        rw [Complex.normSq_apply, h1, h2]
        congr 1
        ring
    have hdig : (Complex.digamma w).re
        = 2 * clockRate t + Real.log Real.pi := by
      have hmu := Zeta23.MuFields.mu_eq t
      have hcr := CriticalLinePhasor.CarrierScale.clockRate_eq_pi_mul_mu t
      have hwc : w = (((1 : ℝ) / 4 : ℝ) : ℂ)
          + Complex.I * ((t / 2 : ℝ) : ℂ) := hw
      rw [← hwc] at hmu
      have hexpand : Real.pi * Zeta23.mu t
          = (Complex.digamma w).re / 2 - Real.log Real.pi / 2 := by
        rw [hmu]
        field_simp
      rw [hcr, hexpand]
      ring
    have hval : (Complex.digamma w
          + ((Real.eulerMascheroniConstant : ℝ) : ℂ) + 1 / w).re
        = 2 * clockRate t + Real.log Real.pi
          + Real.eulerMascheroniConstant + (1/4)/((1/4)^2 + t^2/4) := by
      rw [Complex.add_re, Complex.add_re, hdig, Complex.ofReal_re,
        one_div, Complex.inv_re, Complex.normSq_apply, hwre, hwim]
      ring
    have htsum := hre.tsum_eq
    rw [hval] at htsum
    calc (∑' n : ℕ, (1/((n:ℝ)+1) - ((n:ℝ)+5/4)/(((n:ℝ)+5/4)^2 + t^2/4)))
        = ∑' n : ℕ, ((1 / ((n:ℂ) + 1) - 1 / (w + n + 1)).re) :=
          (tsum_congr hterm).symm
      _ = 2 * clockRate t + Real.log Real.pi
          + Real.eulerMascheroniConstant + (1/4)/((1/4)^2 + t^2/4) := htsum
      _ = 2 * clockRate t + Real.eulerMascheroniConstant
          + (1/4)/((1/4)^2 + t^2/4) + Real.log Real.pi := by ring
  have hint_lor : IntervalIntegrable
      (fun t : ℝ => (1/4)/((1/4)^2 + t^2/4)) MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    apply continuous_const.div
    · continuity
    · intro t
      positivity
  have hL := integral_lorentz_eq_arctan_T (a := (1/4:ℝ)) (T := T)
    (by norm_num)
  have harctan2 : T/(2 * (1/4)) = 2*T := by
    field_simp
    ring
  rw [harctan2] at hL
  have hRHS : ∫ t in (0:ℝ)..T,
      (2 * clockRate t + Real.eulerMascheroniConstant
        + (1/4)/((1/4)^2 + t^2/4) + Real.log Real.pi)
      = 2 * theta T + Real.eulerMascheroniConstant * T
        + 2 * Real.arctan (2*T) + T * Real.log Real.pi := by
    have hi1 : IntervalIntegrable (fun t : ℝ => 2 * clockRate t)
        MeasureTheory.volume 0 T :=
      (continuous_clockRate.intervalIntegrable _ _).const_mul _
    have hi2 : IntervalIntegrable
        (fun _ : ℝ => Real.eulerMascheroniConstant)
        MeasureTheory.volume 0 T := intervalIntegrable_const
    have hi4 : IntervalIntegrable (fun _ : ℝ => Real.log Real.pi)
        MeasureTheory.volume 0 T := intervalIntegrable_const
    rw [intervalIntegral.integral_add
        ((hi1.add hi2).add hint_lor) hi4,
      intervalIntegral.integral_add (hi1.add hi2) hint_lor,
      intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, hL,
      intervalIntegral.integral_const, intervalIntegral.integral_const]
    have hth : ∫ u in (0:ℝ)..T, clockRate u = theta T := rfl
    rw [hth]
    simp
    ring
  have hexch := theta_T_series_integral hT
  have hcomb : (∑' n : ℕ,
      (T/((n:ℝ)+1) - 2 * Real.arctan (T/(2*((n:ℝ)+5/4)))))
      = 2 * theta T + Real.eulerMascheroniConstant * T
        + 2 * Real.arctan (2*T) + T * Real.log Real.pi := by
    rw [← hexch, ← hRHS]
    apply intervalIntegral.integral_congr
    intro t _
    exact hpt t
  linarith

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.mu_stirling_explicit
#print axioms CriticalLinePhasor.DVP.theta_increment_enclosure
#print axioms CriticalLinePhasor.DVP.theta_one_eq
#print axioms CriticalLinePhasor.DVP.theta_eq
#print axioms CriticalLinePhasor.DVP.theta_increment_enclosure_from
end AxiomAudit
