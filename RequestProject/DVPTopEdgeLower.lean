import RequestProject.DVPLandauValue
import RequestProject.DVPGrowthBounds
import RequestProject.DVPWeightedCount

/-!
# The top-edge lower bound: `∫_{1/2}^2 log‖ζ(u+iT)‖ du ≥ −800·log T`

The L9 configuration (398): center `2+iT` (compiled floor `‖ζ‖ ≥ 1/2`),
`r = 12/7`, `β = 7/8` — full ball inside the quarter strip (B2″ growth,
`M = 24(T+2)^{3/4}`), `βr`-ball covering `[1/2,2]×{T}` exactly.  The zero
mass is counted by Mathlib's Jensen bound at `R = 7/4` (`N ≤ 97·log(2M)`,
Bernoulli floor `log(49/48) ≥ 1/97`), and each zero's integral costs `≥ −2`
(`integral_log_norm_dist_lower`).  DC first: every constant is computed
before the single final linear assembly.
-/

open Metric Complex

noncomputable section

namespace CriticalLinePhasor.DVP

/-- Bernoulli floor for the Jensen ratio: `log(49/48) ≥ 1/97`. -/
theorem log_49_48_ge : (1:ℝ)/97 ≤ Real.log (49/48) := by
  have hb : (1:ℝ) + 97 * (1/48) ≤ (1 + 1/48)^(97:ℕ) :=
    one_add_mul_le_pow (by norm_num) 97
  have he : Real.exp 1 ≤ ((49:ℝ)/48)^(97:ℕ) := by
    have hlt := Real.exp_one_lt_d9
    have h4948 : ((49:ℝ)/48) = 1 + 1/48 := by norm_num
    rw [h4948]
    nlinarith [hb]
  have hlog := Real.log_le_log (Real.exp_pos 1) he
  rw [Real.log_exp, Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- `log(45/14) ≤ 6/5` via fifth powers. -/
theorem log_45_14_le : Real.log ((1 + 7/8) * (12/7 : ℝ)) ≤ 6/5 := by
  have harg : ((1 + 7/8) * (12/7 : ℝ)) = 45/14 := by norm_num
  rw [harg]
  rw [Real.log_le_iff_le_exp (by norm_num)]
  by_contra hc
  push_neg at hc
  have h5 : Real.exp (6/5) ^ (5:ℕ) = Real.exp 6 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he3 : (20.08:ℝ) ≤ Real.exp 3 := by
    have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  have he6 : (403:ℝ) ≤ Real.exp 6 := by
    have h6 : Real.exp 6 = Real.exp 3 * Real.exp 3 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [he3, Real.exp_pos 3]
  have hpow : Real.exp (6/5) ^ (5:ℕ) < (45/14:ℝ)^(5:ℕ) :=
    pow_lt_pow_left₀ hc (Real.exp_pos _).le (by norm_num)
  rw [h5] at hpow
  norm_num at hpow
  linarith

/-- The `σ ≥ 2` edge: `‖ζ‖ ≤ 2` (DC term `1` plus the compiled tail). -/
theorem zeta_norm_le_edge {z : ℂ} (hz : 2 ≤ z.re) : ‖riemannZeta z‖ ≤ 2 := by
  have h := zeta_sub_one_norm_le (by linarith : 1 < z.re)
  have h1 : (2:ℝ)^(-z.re) ≤ 1/4 := by
    have hmono : (2:ℝ)^(-z.re) ≤ (2:ℝ)^(-(2:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 : (2:ℝ)^(-(2:ℝ)) = 1/4 := by
      rw [show (-(2:ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    exact hmono.trans h4.le
  have h2 : (2:ℝ)^(1 - z.re) / (z.re - 1) ≤ 1/2 := by
    have h2σ : (2:ℝ)^(1-z.re) ≤ 1/2 := by
      have hmono : (2:ℝ)^(1-z.re) ≤ (2:ℝ)^(-(1:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have hhalf : (2:ℝ)^(-(1:ℝ)) = 1/2 := by
        rw [show (-(1:ℝ)) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
      exact hmono.trans hhalf.le
    calc (2:ℝ)^(1 - z.re) / (z.re - 1) ≤ (2:ℝ)^(1 - z.re) :=
          div_le_self (by positivity) (by linarith)
      _ ≤ 1/2 := h2σ
  have heq : riemannZeta z = 1 + (riemannZeta z - 1) := by ring
  calc ‖riemannZeta z‖ = ‖(1:ℂ) + (riemannZeta z - 1)‖ := by rw [← heq]
    _ ≤ ‖(1:ℂ)‖ + ‖riemannZeta z - 1‖ := norm_add_le _ _
    _ ≤ 2 := by
        rw [norm_one]
        linarith

/-- The uniform bound on the Jensen ball: `‖ζ‖ ≤ 24(T+2)^{3/4}` on
`closedBall (2+iT) (7/4)`. -/
theorem zeta_ball_bound {T : ℝ} (hT : Real.exp 4 ≤ T) :
    ∀ z ∈ closedBall ((2:ℂ) + (T:ℂ) * Complex.I) (7/4),
      ‖riemannZeta z‖ ≤ 24 * (T + 2) ^ ((3:ℝ)/4) := by
  intro z hz
  have hT50 : (50:ℝ) ≤ T := by
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
        * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    nlinarith [he2, Real.exp_pos 1]
  have hdist : ‖z - ((2:ℂ) + (T:ℂ) * Complex.I)‖ ≤ 7/4 := by
    have := mem_closedBall.mp hz
    rwa [dist_eq_norm] at this
  have hre : |z.re - 2| ≤ 7/4 := by
    have h1 := Complex.abs_re_le_norm (z - ((2:ℂ) + (T:ℂ) * Complex.I))
    have h2 : (z - ((2:ℂ) + (T:ℂ) * Complex.I)).re = z.re - 2 := by simp
    rw [h2] at h1
    linarith
  have him : |z.im - T| ≤ 7/4 := by
    have h1 := Complex.abs_im_le_norm (z - ((2:ℂ) + (T:ℂ) * Complex.I))
    have h2 : (z - ((2:ℂ) + (T:ℂ) * Complex.I)).im = z.im - T := by simp
    rw [h2] at h1
    linarith
  have himpos : (0:ℝ) < z.im := by
    have := (abs_le.mp him).1
    linarith
  have him2 : (2:ℝ) ≤ |z.im| := by
    rw [abs_of_pos himpos]
    have := (abs_le.mp him).1
    linarith
  have himT2 : |z.im| ≤ T + 2 := by
    rw [abs_of_pos himpos]
    have := (abs_le.mp him).2
    linarith
  have hrp1 : (1:ℝ) ≤ (T + 2) ^ ((3:ℝ)/4) := by
    calc (1:ℝ) = 1 ^ ((3:ℝ)/4) := (Real.one_rpow _).symm
      _ ≤ (T + 2) ^ ((3:ℝ)/4) :=
          Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  rcases le_or_gt z.re 2 with hre2 | hre2
  · have hrel : (1:ℝ)/4 ≤ z.re := by
      have := (abs_le.mp hre).1
      linarith
    have hg := zeta_polynomial_growth_quarter him2 hrel hre2
    calc ‖riemannZeta z‖ ≤ 24 * |z.im| ^ ((3:ℝ)/4) := hg
      _ ≤ 24 * (T + 2) ^ ((3:ℝ)/4) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.rpow_le_rpow (abs_nonneg _) himT2 (by norm_num)
  · have h2 := zeta_norm_le_edge (le_of_lt hre2)
    nlinarith [hrp1]

/-- Integrability of the log-distance integrand at every height and center. -/
theorem intervalIntegrable_log_norm_dist (a b T : ℝ) (ρ : ℂ) :
    IntervalIntegrable
      (fun u : ℝ => Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖)
      MeasureTheory.volume a b := by
  rcases eq_or_ne T ρ.im with hT | hT
  · have hcong : (fun u : ℝ => Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖)
        = fun u : ℝ => Real.log |u - ρ.re| := by
      funext u
      have hz : (u:ℂ) + (T:ℂ) * Complex.I - ρ = ((u - ρ.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hT]
      rw [hz, Complex.norm_real, Real.norm_eq_abs]
    rw [hcong]
    exact intervalIntegrable_log_abs_sub a b ρ.re
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.log
    · exact (((Complex.continuous_ofReal.add continuous_const).sub
        continuous_const).norm).continuousOn
    · intro u _
      apply norm_ne_zero_iff.mpr
      intro h
      apply hT
      have him := congrArg Complex.im h
      simp at him
      linarith [him]

/-- **The top-edge lower bound**: on any zero-free top edge at height
`T ≥ e⁴`, `∫_{1/2}^2 log‖ζ(u+iT)‖ du ≥ −800·log T`. -/
theorem zeta_top_edge_log_lower {T : ℝ} (hT : Real.exp 4 ≤ T)
    (hnz : ∀ u ∈ Set.Icc (1/2 : ℝ) 2,
      riemannZeta ((u:ℂ) + (T:ℂ) * Complex.I) ≠ 0) :
    -(800 * Real.log T)
      ≤ ∫ u in (1/2 : ℝ)..2,
          Real.log ‖riemannZeta ((u:ℂ) + (T:ℂ) * Complex.I)‖ := by
  set c : ℂ := (2:ℂ) + (T:ℂ) * Complex.I with hcdef
  set M : ℝ := 24 * (T + 2) ^ ((3:ℝ)/4) with hMdef
  have hT50 : (50:ℝ) ≤ T := by
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
        * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    nlinarith [he2, Real.exp_pos 1]
  have hL4 : (4:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 4) hT
    rwa [Real.log_exp] at this
  have hrp1 : (1:ℝ) ≤ (T + 2) ^ ((3:ℝ)/4) := by
    calc (1:ℝ) = 1 ^ ((3:ℝ)/4) := (Real.one_rpow _).symm
      _ ≤ (T + 2) ^ ((3:ℝ)/4) :=
          Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  have hM24 : (24:ℝ) ≤ M := by
    rw [hMdef]
    nlinarith [hrp1]
  have hMpos : (0:ℝ) < M := by linarith
  -- the pole is far from the ball
  have hone_not : ∀ z ∈ closedBall c (7/4), z ≠ 1 := by
    intro z hz h1
    have hdist : ‖z - c‖ ≤ 7/4 := by
      have := mem_closedBall.mp hz
      rwa [dist_eq_norm] at this
    have h2 : (z - c).im = z.im - T := by
      rw [hcdef]
      simp
    have h3 := Complex.abs_im_le_norm (z - c)
    rw [h2] at h3
    rw [h1] at h3 hdist
    simp at h3
    linarith [le_abs_self T, h3, hdist]
  have hdiffOn : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hanal74 : AnalyticOnNhd ℂ riemannZeta (closedBall c (7/4)) :=
    fun z hz => hdiffOn.analyticAt (isOpen_ne.mem_nhds (hone_not z hz))
  have hanal : AnalyticOnNhd ℂ riemannZeta (closedBall c (12/7)) :=
    fun z hz => hanal74 z
      (closedBall_subset_closedBall (by norm_num) hz)
  have hMball := zeta_ball_bound hT
  have hMinner : ∀ z ∈ closedBall c (12/7), ‖riemannZeta z‖ ≤ M := by
    intro z hz
    exact hMball z (closedBall_subset_closedBall (by norm_num) hz)
  have hcre : c.re = 2 := by
    rw [hcdef]
    simp
  have hmc : (1/2 : ℝ) ≤ ‖riemannZeta c‖ :=
    zeta_center_lower_bound (by rw [hcre])
  have hc0 : riemannZeta c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hmc
    linarith
  have hlogMm : (0:ℝ) < Real.log (M / (1/2)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 1/2)]
    linarith
  -- L9 at the configuration
  obtain ⟨S, n, hS_mem, hn_eq, hd_zero, hbound⟩ :=
    landau_value_lower (c := c) (r := 12/7) (M := M) (m := 1/2) (β := 7/8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hanal hMinner hmc hlogMm
  set N : ℝ := ∑ u ∈ S, (n u : ℝ) with hNdef
  have hN0 : (0:ℝ) ≤ N :=
    Finset.sum_nonneg fun u _ => Nat.cast_nonneg _
  -- Jensen count at R = 7/4
  have habs74 : |(7/4 : ℝ)| = 7/4 := by norm_num
  have habs127 : |(12/7 : ℝ)| = 12/7 := by norm_num
  have hsphere : ∀ z ∈ Metric.sphere c |(7/4:ℝ)|, ‖riemannZeta z‖ ≤ M := by
    intro z hz
    rw [habs74] at hz
    exact hMball z (sphere_subset_closedBall hz)
  have hanal74' : AnalyticOnNhd ℂ riemannZeta (closedBall c |(7/4:ℝ)|) := by
    rw [habs74]
    exact hanal74
  have hjensen := AnalyticOnNhd.sum_divisor_le (r := (12/7:ℝ)) (R := (7/4:ℝ))
    (by rw [habs127]; norm_num) (by rw [habs127, habs74]; norm_num)
    (by linarith : (1:ℝ) ≤ M) hanal74' hc0 hsphere
  rw [habs127] at hjensen
  -- link the finsum to N
  have hsupp : (Function.support fun u =>
      MeromorphicOn.divisor riemannZeta (closedBall c (12/7)) u) ⊆ ↑S := by
    intro u hu
    by_contra hus
    exact hu (hd_zero u hus)
  have hfin : (∑ᶠ u, MeromorphicOn.divisor riemannZeta (closedBall c (12/7)) u)
      = ∑ u ∈ S, MeromorphicOn.divisor riemannZeta (closedBall c (12/7)) u :=
    finsum_eq_finsetSum_of_support_subset _ hsupp
  have hNeq : ((∑ᶠ u, MeromorphicOn.divisor riemannZeta
      (closedBall c (12/7)) u : ℤ) : ℝ) = N := by
    rw [hfin, Finset.sum_congr rfl (fun u hu => (hn_eq u hu).symm), hNdef]
    push_cast
    rfl
  have hlog2 : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    nlinarith [Real.exp_one_gt_d9]
  have hlog2M : Real.log (2 * M) ≤ 2 * Real.log T := by
    have h48 : Real.log (2 * M) = Real.log 48 + (3/4) * Real.log (T + 2) := by
      rw [hMdef, show (2 * (24 * (T+2)^((3:ℝ)/4))) = 48 * (T+2)^((3:ℝ)/4) by ring,
        Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by linarith)]
    have hlog48 : Real.log 48 ≤ 4 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
        nlinarith [Real.exp_one_gt_d9]
      have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
          * (Real.exp 1 * Real.exp 1) := by
        rw [← Real.exp_add, ← Real.exp_add]
        norm_num
      nlinarith [he2, Real.exp_pos 1]
    have hlogT2 : Real.log (T + 2) ≤ Real.log T + 1 := by
      calc Real.log (T + 2) ≤ Real.log (2 * T) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 2 + Real.log T :=
            Real.log_mul (by norm_num) (by linarith)
        _ ≤ Real.log T + 1 := by linarith
    rw [h48]
    nlinarith [hL4]
  have hNle : N ≤ 194 * Real.log T := by
    have hnum : Real.log (M / ‖riemannZeta c‖) ≤ Real.log (2 * M) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hmc)]
      nlinarith [hmc]
    have hden : (1:ℝ)/97 ≤ Real.log ((7/4:ℝ)/(12/7)) := by
      rw [show ((7/4:ℝ)/(12/7)) = 49/48 by norm_num]
      exact log_49_48_ge
    have hden0 : (0:ℝ) < Real.log ((7/4:ℝ)/(12/7)) :=
      lt_of_lt_of_le (by norm_num) hden
    have hnum0 : (0:ℝ) ≤ Real.log (2 * M) := by
      apply Real.log_nonneg
      linarith
    have hquot : Real.log (M / ‖riemannZeta c‖) / Real.log ((7/4:ℝ)/(12/7))
        ≤ Real.log (2 * M) / (1/97) := by
      apply div_le_div₀ hnum0 hnum (by norm_num) hden
    rw [← hNeq]
    calc ((∑ᶠ u, MeromorphicOn.divisor riemannZeta
          (closedBall c (12/7)) u : ℤ) : ℝ)
        ≤ Real.log (M / ‖riemannZeta c‖) / Real.log ((7/4:ℝ)/(12/7)) := hjensen
      _ ≤ Real.log (2 * M) / (1/97) := hquot
      _ = 97 * Real.log (2 * M) := by ring
      _ ≤ 194 * Real.log T := by linarith [hlog2M]
  -- segment membership in the βr-ball
  have hseg : ∀ u ∈ Set.Icc (1/2:ℝ) 2,
      ((u:ℂ) + (T:ℂ) * Complex.I) ∈ closedBall c ((7/8) * (12/7)) := by
    intro u hu
    rw [mem_closedBall, dist_eq_norm]
    have hz : (u:ℂ) + (T:ℂ) * Complex.I - c = ((u - 2 : ℝ) : ℂ) := by
      rw [hcdef]
      apply Complex.ext <;> simp
    rw [hz, Complex.norm_real, Real.norm_eq_abs,
      show ((7:ℝ)/8) * (12/7) = 3/2 by norm_num, abs_le]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  -- pointwise bound, integral-ready
  have hpt : ∀ u ∈ Set.Icc (1/2:ℝ) 2,
      (Real.log (1/2) - 2 * (7/8 / (1 - 7/8)) * Real.log (M / (1/2))
          - N * Real.log ((1 + 7/8) * (12/7)))
        + (∑ ρ ∈ S, (n ρ : ℝ) * Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖)
      ≤ Real.log ‖riemannZeta ((u:ℂ) + (T:ℂ) * Complex.I)‖ := by
    intro u hu
    have hb := hbound _ (hseg u hu) (hnz u hu)
    linarith [hb]
  -- integrability
  have hint_term : ∀ ρ ∈ S, IntervalIntegrable
      (fun u : ℝ => (n ρ : ℝ) * Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖)
      MeasureTheory.volume (1/2) 2 :=
    fun ρ _ => (intervalIntegrable_log_norm_dist (1/2) 2 T ρ).const_mul _
  have hint_sum : IntervalIntegrable
      (fun u : ℝ => ∑ ρ ∈ S,
        (n ρ : ℝ) * Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖)
      MeasureTheory.volume (1/2) 2 := by
    have heq : (∑ i ∈ S, fun u : ℝ =>
          (n i : ℝ) * Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - i‖)
        = fun u : ℝ => ∑ ρ ∈ S,
            (n ρ : ℝ) * Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖ := by
      funext u
      simp [Finset.sum_apply]
    rw [← heq]
    exact IntervalIntegrable.sum S hint_term
  have hint_lhs : IntervalIntegrable
      (fun u : ℝ =>
        (Real.log (1/2) - 2 * (7/8 / (1 - 7/8)) * Real.log (M / (1/2))
            - N * Real.log ((1 + 7/8) * (12/7)))
          + ∑ ρ ∈ S, (n ρ : ℝ) * Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖)
      MeasureTheory.volume (1/2) 2 :=
    intervalIntegrable_const.add hint_sum
  have hint_rhs : IntervalIntegrable
      (fun u : ℝ => Real.log ‖riemannZeta ((u:ℂ) + (T:ℂ) * Complex.I)‖)
      MeasureTheory.volume (1/2) 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)]
    apply ContinuousOn.log
    · apply ContinuousOn.norm
      intro u hu
      have hne1 : (u:ℂ) + (T:ℂ) * Complex.I ≠ 1 := by
        intro h1
        have him := congrArg Complex.im h1
        simp at him
        linarith
      have hc' : ContinuousAt
          (riemannZeta ∘ fun τ : ℝ => (τ:ℂ) + (T:ℂ) * Complex.I) u :=
        ContinuousAt.comp (differentiableAt_riemannZeta hne1).continuousAt
          ((Complex.continuous_ofReal.add continuous_const).continuousAt)
      exact hc'.continuousWithinAt
    · intro u hu
      exact norm_ne_zero_iff.mpr (hnz u hu)
  -- integrate the pointwise bound
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (1/2:ℝ) ≤ 2) hint_lhs hint_rhs hpt
  rw [intervalIntegral.integral_add intervalIntegrable_const hint_sum,
    intervalIntegral.integral_const,
    intervalIntegral.integral_finsetSum hint_term] at hmono
  -- per-zero integrals cost ≥ −2 each
  have hsum_low : -2 * N ≤ ∑ ρ ∈ S,
      ∫ u in (1/2:ℝ)..2,
        (n ρ : ℝ) * Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖ := by
    calc -2 * N = ∑ ρ ∈ S, (-2 * (n ρ : ℝ)) := by
          rw [hNdef, Finset.mul_sum]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro ρ _
          rw [intervalIntegral.integral_const_mul]
          have h2 := integral_log_norm_dist_lower
            (by norm_num : (1/2:ℝ) ≤ 2) T ρ
          nlinarith [Nat.cast_nonneg (α := ℝ) (n ρ), h2]
  -- numeric assembly
  have hY0 : (0:ℝ) ≤ Real.log ((1 + 7/8) * (12/7:ℝ)) :=
    Real.log_nonneg (by norm_num)
  have hX : Real.log (M / (1/2)) ≤ 2 * Real.log T := by
    rw [show M / (1/2:ℝ) = 2 * M by ring]
    exact hlog2M
  have hlogm : (-1:ℝ) ≤ Real.log (1/2) := by
    rw [show ((1:ℝ)/2) = 2⁻¹ by norm_num, Real.log_inv]
    linarith
  have hNY : N * Real.log ((1 + 7/8) * (12/7:ℝ))
      ≤ (194 * Real.log T) * (6/5) :=
    mul_le_mul hNle log_45_14_le hY0 (by positivity)
  simp only [smul_eq_mul] at hmono
  nlinarith [hmono, hsum_low, hNY, hX, hlogm, hL4, hlogMm, hN0]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.log_49_48_ge
#print axioms CriticalLinePhasor.DVP.log_45_14_le
#print axioms CriticalLinePhasor.DVP.zeta_norm_le_edge
#print axioms CriticalLinePhasor.DVP.zeta_ball_bound
#print axioms CriticalLinePhasor.DVP.intervalIntegrable_log_norm_dist
#print axioms CriticalLinePhasor.DVP.zeta_top_edge_log_lower
end AxiomAudit
