import RequestProject.LittlewoodRegisterDoor

/-!
# Littlewood's radial identity: the integrated warp driver is a boundary term (ledger 687)

For good heights `0 < t₀ ≤ t₁`,
  **`π · ∫_{t₀}^{t₁} S_all(t) dt = R(t₁) − R(t₀)`,  `R(t) := ∫_{½}^{∞} log‖ζ(x + it)‖ dx`.**
The cumulative registration gap between two heights is the difference of the fiber's radial log-masses at those
heights — a state function of the endpoints, with no accumulated residue.  Measured to 5 decimals at four heights
(ledger 686); here compiled from the tree's contour representation of `S_all`, the box collapse on `[½, 2]`, and a
new right-edge identity on `[2, ∞)`.
-/

open Complex MeasureTheory Set Filter Topology
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale CriticalLinePhasor.ResidueJump
open DoubleCoshProgram

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The radial log-mass of the fiber at height `t`. -/
def radialLogMass (t : ℝ) : ℝ := ∫ x in Ioi (1 / 2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖

/-! ## Tail bounds on `Re s ≥ 2` -/

theorem norm_log_zeta_le {z : ℂ} (hz : 2 ≤ z.re) :
    ‖Complex.log (riemannZeta z)‖ ≤ 3 * ‖riemannZeta z - 1‖ := by
  have h34 := zeta_sub_one_le_three_quarters hz
  have hlt : ‖riemannZeta z - 1‖ < 1 := by linarith
  have h := Complex.norm_log_one_add_le hlt
  rw [show (1 : ℂ) + (riemannZeta z - 1) = riemannZeta z by ring] at h
  set a := ‖riemannZeta z - 1‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hpos : 0 < 1 - a := by linarith
  have h1 : a ^ 2 * (1 - a)⁻¹ / 2 ≤ 3 / 2 * a := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2), ← div_eq_mul_inv, div_le_iff₀ hpos]
    nlinarith
  linarith

theorem zeta_sub_one_le_tail {z : ℂ} (hz : 2 ≤ z.re) :
    ‖riemannZeta z - 1‖ ≤ 3 * (2 : ℝ) ^ (-z.re) := by
  have h := zeta_sub_one_norm_le (by linarith : 1 < z.re)
  have hp : 0 < (2 : ℝ) ^ (-z.re) := by positivity
  have h2 : (2 : ℝ) ^ (1 - z.re) / (z.re - 1) ≤ 2 * (2 : ℝ) ^ (-z.re) := by
    rw [show (1 - z.re) = 1 + (-z.re) by ring, Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one,
      div_le_iff₀ (by linarith)]
    nlinarith
  linarith

theorem two_rpow_neg_eq_exp (x : ℝ) : (2 : ℝ) ^ (-x) = Real.exp (-Real.log 2 * x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  congr 1; ring

/-- `|log‖ζ(x+it)‖| ≤ 9·2^{−x}` for `x ≥ 2`. -/
theorem abs_log_norm_zeta_le {x t : ℝ} (hx : 2 ≤ x) :
    |Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖| ≤ 9 * (2 : ℝ) ^ (-x) := by
  have hre : ((x : ℂ) + (t : ℂ) * I).re = x := by simp
  have h1 : |Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖|
      ≤ ‖Complex.log (riemannZeta ((x : ℂ) + (t : ℂ) * I))‖ := by
    rw [← Complex.log_re]; exact Complex.abs_re_le_norm _
  have h2 := norm_log_zeta_le (z := (x : ℂ) + (t : ℂ) * I) (by rw [hre]; exact hx)
  have h3 := zeta_sub_one_le_tail (z := (x : ℂ) + (t : ℂ) * I) (by rw [hre]; exact hx)
  rw [hre] at h3
  linarith

theorem zeta_ne_zero_of_two_le {z : ℂ} (hz : 2 ≤ z.re) : riemannZeta z ≠ 0 := by
  intro h0
  have := zeta_sub_one_le_three_quarters hz
  rw [h0] at this
  norm_num at this

theorem ne_one_of_pos_im {x t : ℝ} (ht : 0 < t) : ((x : ℂ) + (t : ℂ) * I) ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- The radial log-density is integrable on `[2, ∞)` at every positive height. -/
theorem integrableOn_log_norm_zeta_Ioi {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖) (Ioi 2) := by
  have hg : IntegrableOn (fun x : ℝ => 9 * Real.exp (-Real.log 2 * x)) (Ioi 2) :=
    (integrableOn_exp_mul_Ioi (by have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith) 2).const_mul 9
  refine hg.mono' ?_ ?_
  · -- continuity on Ioi 2
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.log
    · apply ContinuousOn.norm
      intro x hx
      have hc : ContinuousAt (riemannZeta ∘ fun ξ : ℝ => (ξ : ℂ) + (t : ℂ) * I) x :=
        ContinuousAt.comp (differentiableAt_riemannZeta (ne_one_of_pos_im ht)).continuousAt
          ((Complex.continuous_ofReal.add continuous_const).continuousAt)
      exact hc.continuousWithinAt
    · intro x hx
      have hre : ((x : ℂ) + (t : ℂ) * I).re = x := by simp
      exact norm_ne_zero_iff.mpr (zeta_ne_zero_of_two_le (by rw [hre]; exact le_of_lt hx))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, ← two_rpow_neg_eq_exp]
    exact abs_log_norm_zeta_le (le_of_lt hx)

/-! ## The horizontal fundamental theorem for `log ζ` on `Re s ≥ 2` -/

theorem continuousOn_deriv_zeta : ContinuousOn (deriv riemannZeta) ({1}ᶜ : Set ℂ) := by
  have hd : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact ((hd.analyticOnNhd isOpen_compl_singleton).deriv).continuousOn

theorem hasDerivAt_log_zeta_horizontal {x t : ℝ} (ht : 0 < t) (hx : 2 ≤ x) :
    HasDerivAt (fun ξ : ℝ => Complex.log (riemannZeta ((ξ : ℂ) + (t : ℂ) * I)))
      (deriv riemannZeta ((x : ℂ) + (t : ℂ) * I) / riemannZeta ((x : ℂ) + (t : ℂ) * I)) x := by
  have hne := ne_one_of_pos_im (x := x) ht
  have hre : ((x : ℂ) + (t : ℂ) * I).re = x := by simp
  have h1 : HasDerivAt (fun z : ℂ => riemannZeta (z + (t : ℂ) * I))
      (deriv riemannZeta ((x : ℂ) + (t : ℂ) * I)) (x : ℂ) := by
    exact (differentiableAt_riemannZeta hne).hasDerivAt.comp_add_const (x : ℂ) ((t : ℂ) * I)
  have h2 := h1.clog (zeta_mem_slitPlane_of_two_le (by rw [hre]; exact hx))
  exact h2.comp_ofReal

theorem intervalIntegrable_logDeriv_horizontal {t a b : ℝ} (ht : 0 < t) (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun ξ : ℝ => deriv riemannZeta ((ξ : ℂ) + (t : ℂ) * I) / riemannZeta ((ξ : ℂ) + (t : ℂ) * I))
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro x hx
  have hne := ne_one_of_pos_im (x := x) ht
  have hre : ((x : ℂ) + (t : ℂ) * I).re = x := by simp
  have hline : ContinuousAt (fun ξ : ℝ => (ξ : ℂ) + (t : ℂ) * I) x :=
    (Complex.continuous_ofReal.add continuous_const).continuousAt
  have hd : ContinuousAt (deriv riemannZeta ∘ fun ξ : ℝ => (ξ : ℂ) + (t : ℂ) * I) x :=
    ContinuousAt.comp (continuousOn_deriv_zeta.continuousAt (isOpen_compl_singleton.mem_nhds hne)) hline
  have hz : ContinuousAt (riemannZeta ∘ fun ξ : ℝ => (ξ : ℂ) + (t : ℂ) * I) x :=
    ContinuousAt.comp (differentiableAt_riemannZeta hne).continuousAt hline
  have hz0 : riemannZeta ((x : ℂ) + (t : ℂ) * I) ≠ 0 :=
    zeta_ne_zero_of_two_le (by rw [hre]; linarith [hx.1])
  exact (hd.div hz hz0).continuousWithinAt

/-- `Im log ζ(2+it) = Im log ζ(B+it) − ∫_2^B Im(ζ'/ζ)(x+it) dx`. -/
theorem im_log_zeta_two_eq {t B : ℝ} (ht : 0 < t) (hB : 2 ≤ B) :
    (Complex.log (riemannZeta ((2 : ℂ) + (t : ℂ) * I))).im
      = (Complex.log (riemannZeta ((B : ℂ) + (t : ℂ) * I))).im
        - ∫ x in (2 : ℝ)..B,
            (deriv riemannZeta ((x : ℂ) + (t : ℂ) * I) / riemannZeta ((x : ℂ) + (t : ℂ) * I)).im := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun ξ : ℝ => Complex.log (riemannZeta ((ξ : ℂ) + (t : ℂ) * I)))
    (f' := fun ξ : ℝ => deriv riemannZeta ((ξ : ℂ) + (t : ℂ) * I) / riemannZeta ((ξ : ℂ) + (t : ℂ) * I))
    (a := 2) (b := B)
    (fun x hx => hasDerivAt_log_zeta_horizontal ht (by rw [uIcc_of_le hB] at hx; exact hx.1))
    (intervalIntegrable_logDeriv_horizontal ht le_rfl hB)
  have him := congrArg Complex.im hftc
  have hcomm := Complex.imCLM.intervalIntegral_comp_comm
    (intervalIntegrable_logDeriv_horizontal ht le_rfl hB)
  simp only [Complex.imCLM_apply] at hcomm
  rw [hcomm]
  simp only [Complex.sub_im] at him
  push_cast at him ⊢
  linarith

/-! ## The right edge: `∫_{t₀}^{t₁} Im log ζ(2+it) dt = ∫_{2}^{∞} [log‖ζ(x+it₁)‖ − log‖ζ(x+it₀)‖] dx` -/

theorem intervalIntegrable_im_log_zeta_vertical {B t₀ t₁ : ℝ} (hB : 2 ≤ B) (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) :
    IntervalIntegrable (fun t : ℝ => (Complex.log (riemannZeta ((B : ℂ) + (t : ℂ) * I))).im) volume t₀ t₁ := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le ht]
  intro t htm
  have htpos : 0 < t := lt_of_lt_of_le ht₀ htm.1
  have hne := ne_one_of_pos_im (x := B) htpos
  have hre : ((B : ℂ) + (t : ℂ) * I).re = B := by simp
  have hinner : ContinuousAt (fun t : ℝ => (B : ℂ) + (t : ℂ) * I) t :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
  have hζ : ContinuousAt riemannZeta ((B : ℂ) + (t : ℂ) * I) :=
    (differentiableAt_riemannZeta hne).continuousAt
  have hlog : ContinuousAt Complex.log (riemannZeta ((B : ℂ) + (t : ℂ) * I)) :=
    continuousAt_clog (zeta_mem_slitPlane_of_two_le (by rw [hre]; exact hB))
  have hz_at : ContinuousAt (riemannZeta ∘ fun t : ℝ => (B : ℂ) + (t : ℂ) * I) t :=
    ContinuousAt.comp hζ hinner
  have hlog_at : ContinuousAt (Complex.log ∘ riemannZeta ∘ fun t : ℝ => (B : ℂ) + (t : ℂ) * I) t :=
    ContinuousAt.comp hlog hz_at
  have hcomp : ContinuousAt (Complex.im ∘ Complex.log ∘ riemannZeta ∘ fun t : ℝ => (B : ℂ) + (t : ℂ) * I) t :=
    ContinuousAt.comp Complex.continuous_im.continuousAt hlog_at
  exact hcomp.continuousWithinAt

theorem intervalIntegrable_of_integrableOn_Ioi {f : ℝ → ℝ} {a b c : ℝ}
    (h : IntegrableOn f (Ioi c)) (hca : c ≤ a) (hcb : c ≤ b) : IntervalIntegrable f volume a b :=
  ⟨h.mono_set (fun x hx => lt_of_le_of_lt hca hx.1), h.mono_set (fun x hx => lt_of_le_of_lt hcb hx.1)⟩

/-- Finite-box form of the right edge. -/
theorem right_edge_finite {t₀ t₁ B : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) (hB : 2 ≤ B) :
    ∫ t in t₀..t₁, (Complex.log (riemannZeta ((2 : ℂ) + (t : ℂ) * I))).im
      = (∫ t in t₀..t₁, (Complex.log (riemannZeta ((B : ℂ) + (t : ℂ) * I))).im)
        + ∫ x in (2 : ℝ)..B,
            (Real.log ‖riemannZeta ((x : ℂ) + (t₁ : ℂ) * I)‖ - Real.log ‖riemannZeta ((x : ℂ) + (t₀ : ℂ) * I)‖) := by
  have hpt : ∀ t ∈ uIcc t₀ t₁,
      (Complex.log (riemannZeta ((2 : ℂ) + (t : ℂ) * I))).im
        = (Complex.log (riemannZeta ((B : ℂ) + (t : ℂ) * I))).im
          - ∫ x in (2 : ℝ)..B,
              (deriv riemannZeta ((x : ℂ) + (t : ℂ) * I) / riemannZeta ((x : ℂ) + (t : ℂ) * I)).im := by
    intro t htm
    rw [uIcc_of_le ht] at htm
    exact im_log_zeta_two_eq (lt_of_lt_of_le ht₀ htm.1) hB
  have hcongr : ∫ t in t₀..t₁, (Complex.log (riemannZeta ((2 : ℂ) + (t : ℂ) * I))).im
      = ∫ t in t₀..t₁, ((Complex.log (riemannZeta ((B : ℂ) + (t : ℂ) * I))).im
          - ∫ x in (2 : ℝ)..B,
              (deriv riemannZeta ((x : ℂ) + (t : ℂ) * I) / riemannZeta ((x : ℂ) + (t : ℂ) * I)).im) :=
    intervalIntegral.integral_congr hpt
  rw [hcongr, intervalIntegral.integral_sub (intervalIntegrable_im_log_zeta_vertical hB ht₀ ht)
    (inner_integral_intervalIntegrable hB ht ht₀),
    box_vertical_collapse hB ht ht₀]
  have hint₀ : IntervalIntegrable (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + (t₀ : ℂ) * I)‖) volume 2 B :=
    intervalIntegrable_of_integrableOn_Ioi (integrableOn_log_norm_zeta_Ioi ht₀) le_rfl hB
  have hint₁ : IntervalIntegrable (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + (t₁ : ℂ) * I)‖) volume 2 B :=
    intervalIntegrable_of_integrableOn_Ioi (integrableOn_log_norm_zeta_Ioi (lt_of_lt_of_le ht₀ ht)) le_rfl hB
  rw [intervalIntegral.integral_sub hint₀ hint₁, intervalIntegral.integral_sub hint₁ hint₀]
  ring

/-- The right-edge tail vanishes: `|∫_{t₀}^{t₁} Im log ζ(B+it) dt| ≤ 9·2^{−B}·|t₁ − t₀|`. -/
theorem right_edge_tail_bound {t₀ t₁ B : ℝ} (ht : t₀ ≤ t₁) (hB : 2 ≤ B) :
    ‖∫ t in t₀..t₁, (Complex.log (riemannZeta ((B : ℂ) + (t : ℂ) * I))).im‖
      ≤ 9 * (2 : ℝ) ^ (-B) * |t₁ - t₀| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t htm
  rw [uIoc_of_le ht] at htm
  have hre : ((B : ℂ) + (t : ℂ) * I).re = B := by simp
  have h1 : ‖(Complex.log (riemannZeta ((B : ℂ) + (t : ℂ) * I))).im‖
      ≤ ‖Complex.log (riemannZeta ((B : ℂ) + (t : ℂ) * I))‖ := by
    rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm _
  have h2 := norm_log_zeta_le (z := (B : ℂ) + (t : ℂ) * I) (by rw [hre]; exact hB)
  have h3 := zeta_sub_one_le_tail (z := (B : ℂ) + (t : ℂ) * I) (by rw [hre]; exact hB)
  rw [hre] at h3
  linarith

theorem tendsto_two_rpow_neg : Tendsto (fun B : ℝ => (2 : ℝ) ^ (-B)) atTop (𝓝 0) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Tendsto (fun B : ℝ => Real.log 2 * B) atTop atTop := tendsto_id.const_mul_atTop hl
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  refine h2.congr' (Eventually.of_forall fun B => ?_)
  simp only [Function.comp, two_rpow_neg_eq_exp]
  congr 1; ring

/-- **The right-edge identity.** -/
theorem right_edge_identity {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) :
    ∫ t in t₀..t₁, (Complex.log (riemannZeta ((2 : ℂ) + (t : ℂ) * I))).im
      = ∫ x in Ioi (2 : ℝ),
          (Real.log ‖riemannZeta ((x : ℂ) + (t₁ : ℂ) * I)‖ - Real.log ‖riemannZeta ((x : ℂ) + (t₀ : ℂ) * I)‖) := by
  set F : ℝ → ℝ := fun B => ∫ t in t₀..t₁, (Complex.log (riemannZeta ((B : ℂ) + (t : ℂ) * I))).im with hF
  set G : ℝ → ℝ := fun B => ∫ x in (2 : ℝ)..B,
      (Real.log ‖riemannZeta ((x : ℂ) + (t₁ : ℂ) * I)‖ - Real.log ‖riemannZeta ((x : ℂ) + (t₀ : ℂ) * I)‖) with hG
  have hFG : ∀ B : ℝ, 2 ≤ B →
      ∫ t in t₀..t₁, (Complex.log (riemannZeta ((2 : ℂ) + (t : ℂ) * I))).im = F B + G B :=
    fun B hB => right_edge_finite ht₀ ht hB
  have hF0 : Tendsto F atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_two_rpow_neg.const_mul 9).mul_const |t₁ - t₀| |>.trans_eq (by simp))
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with B hB
    exact right_edge_tail_bound ht hB
  have hint : IntegrableOn (fun x : ℝ =>
      Real.log ‖riemannZeta ((x : ℂ) + (t₁ : ℂ) * I)‖ - Real.log ‖riemannZeta ((x : ℂ) + (t₀ : ℂ) * I)‖) (Ioi 2) :=
    (integrableOn_log_norm_zeta_Ioi (lt_of_lt_of_le ht₀ ht)).sub (integrableOn_log_norm_zeta_Ioi ht₀)
  have hG : Tendsto G atTop (𝓝 (∫ x in Ioi (2 : ℝ),
      (Real.log ‖riemannZeta ((x : ℂ) + (t₁ : ℂ) * I)‖ - Real.log ‖riemannZeta ((x : ℂ) + (t₀ : ℂ) * I)‖))) :=
    intervalIntegral_tendsto_integral_Ioi 2 hint tendsto_id
  have hsum : Tendsto (fun B => F B + G B) atTop (𝓝 (0 + ∫ x in Ioi (2 : ℝ),
      (Real.log ‖riemannZeta ((x : ℂ) + (t₁ : ℂ) * I)‖ - Real.log ‖riemannZeta ((x : ℂ) + (t₀ : ℂ) * I)‖))) :=
    hF0.add hG
  have hconst : Tendsto (fun B => F B + G B) atTop
      (𝓝 (∫ t in t₀..t₁, (Complex.log (riemannZeta ((2 : ℂ) + (t : ℂ) * I))).im)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with B hB
    exact hFG B hB
  have := tendsto_nhds_unique hconst hsum
  rw [zero_add] at this
  exact this

/-! ## Assembly -/

theorem continuousOn_log_norm_zeta_Icc {t : ℝ} (hg : GoodHeight t) :
    ContinuousOn (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖) (Icc (1 / 2 : ℝ) 2) := by
    apply ContinuousOn.log
    · apply ContinuousOn.norm
      intro x hx
      have hne1 : (x : ℂ) + (t : ℂ) * I ≠ 1 := ne_one_of_pos_im hg.1
      have hc : ContinuousAt (riemannZeta ∘ fun ξ : ℝ => (ξ : ℂ) + (t : ℂ) * I) x :=
        ContinuousAt.comp (differentiableAt_riemannZeta hne1).continuousAt
          ((Complex.continuous_ofReal.add continuous_const).continuousAt)
      exact hc.continuousWithinAt
    · intro x hx
      exact norm_ne_zero_iff.mpr (zeta_top_ne_zero' hg hx)

theorem integrableOn_log_norm_zeta_Ioc {t : ℝ} (hg : GoodHeight t) :
    IntegrableOn (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖) (Ioc (1 / 2 : ℝ) 2) :=
  ((continuousOn_log_norm_zeta_Icc hg).integrableOn_Icc).mono_set Ioc_subset_Icc_self

theorem integrableOn_log_norm_zeta_Ioi_half {t : ℝ} (hg : GoodHeight t) :
    IntegrableOn (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖) (Ioi (1 / 2 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 / 2 : ℝ) ≤ 2)]
  exact (integrableOn_log_norm_zeta_Ioc hg).union (integrableOn_log_norm_zeta_Ioi hg.1)

/-- **Littlewood's radial identity, window form:** for good heights `0 < t₀ ≤ t₁`,
`π ∫_{t₀}^{t₁} S_all = R(t₁) − R(t₀)`. -/
theorem integral_SAll_eq_radialLogMass_sub {t₀ t₁ : ℝ} (h₀ : GoodHeight t₀) (h₁ : GoodHeight t₁) (ht : t₀ ≤ t₁) :
    Real.pi * ∫ t in t₀..t₁, SAll t = radialLogMass t₁ - radialLogMass t₀ := by
  have ht₀ : 0 < t₀ := h₀.1
  have hπ := Real.pi_pos
  -- a.e. contour representation of S_all on the window
  have hae : ∀ᵐ t ∂volume, t ∈ uIoc t₀ t₁ →
      SAll t = (1 / Real.pi) *
        ((Complex.log (riemannZeta ((2:ℂ) + (t:ℂ) * I))).im
          - ∫ x in (1/2 : ℝ)..2,
              (deriv riemannZeta ((x:ℂ) + (t:ℂ) * I) / riemannZeta ((x:ℂ) + (t:ℂ) * I)).im) := by
    have hbadfin : (Complex.im '' stripZeroWindow t₁).Finite := (stripZeroWindow_finite t₁).image _
    have hnull := hbadfin.measure_zero volume
    rw [ae_iff]
    refine measure_mono_null ?_ hnull
    intro t hmem
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hmem
    obtain ⟨htI, hne⟩ := hmem
    rw [Set.uIoc_of_le ht] at htI
    by_contra htbad
    apply hne
    have hgood : GoodHeight t := by
      refine ⟨by linarith [htI.1], ?_⟩
      intro ρ hρ him
      apply htbad
      refine ⟨ρ, ⟨hρ, ?_, ?_⟩, him⟩
      · rw [him]; linarith [htI.1]
      · rw [him]; exact htI.2
    have hcensus := classicalSContour_eq_Smult_add_offLine hgood
    have hident := classicalSContour_eq_log_sub_integral hgood
    rw [SAll, ← hcensus]
    field_simp
    linarith [hident]
  have hi1 := intervalIntegrable_im_log_zeta_vertical (B := 2) le_rfl ht₀ ht
  simp only [Complex.ofReal_ofNat] at hi1
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hi1 (inner_integral_intervalIntegrable (by norm_num) ht ht₀),
    box_vertical_collapse (by norm_num) ht ht₀, right_edge_identity ht₀ ht]
  -- the two radial pieces
  have hI₀ := integrableOn_log_norm_zeta_Ioc h₀
  have hI₁ := integrableOn_log_norm_zeta_Ioc h₁
  have hint₀ : IntervalIntegrable (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + (t₀ : ℂ) * I)‖) volume (1/2) 2 :=
    (continuousOn_log_norm_zeta_Icc h₀).intervalIntegrable_of_Icc (by norm_num)
  have hint₁ : IntervalIntegrable (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + (t₁ : ℂ) * I)‖) volume (1/2) 2 :=
    (continuousOn_log_norm_zeta_Icc h₁).intervalIntegrable_of_Icc (by norm_num)
  have hR : radialLogMass t₁ - radialLogMass t₀
      = (∫ x in Ioc (1/2 : ℝ) 2, (Real.log ‖riemannZeta ((x : ℂ) + (t₁ : ℂ) * I)‖
            - Real.log ‖riemannZeta ((x : ℂ) + (t₀ : ℂ) * I)‖))
        + ∫ x in Ioi (2 : ℝ), (Real.log ‖riemannZeta ((x : ℂ) + (t₁ : ℂ) * I)‖
            - Real.log ‖riemannZeta ((x : ℂ) + (t₀ : ℂ) * I)‖) := by
    unfold radialLogMass
    rw [← integral_sub (integrableOn_log_norm_zeta_Ioi_half h₁) (integrableOn_log_norm_zeta_Ioi_half h₀),
      ← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 / 2 : ℝ) ≤ 2)]
    apply setIntegral_union
    · exact disjoint_left.mpr fun x hx hx' => by simp only [mem_Ioc, mem_Ioi] at hx hx'; linarith [hx.2]
    · exact measurableSet_Ioi
    · exact hI₁.sub hI₀
    · exact (integrableOn_log_norm_zeta_Ioi h₁.1).sub (integrableOn_log_norm_zeta_Ioi h₀.1)
  rw [hR, ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2),
    intervalIntegral.integral_sub hint₁ hint₀, intervalIntegral.integral_sub hint₀ hint₁]
  field_simp
  ring

/-! ## The crossing-driven driver: the residue is the off-line depth -/

theorem integral_smult_window (t₀ t₁ : ℝ) :
    ∫ t in t₀..t₁, Smult t
      = (∫ t in t₀..t₁, SAll t) - ∫ t in t₀..t₁, (offLineStripZeroCountMult t : ℝ) := by
  rw [← intervalIntegral.integral_sub (sall_intervalIntegrable t₀ t₁) (offline_intervalIntegrable t₀ t₁)]
  apply intervalIntegral.integral_congr
  intro t _
  simp [SAll]

/-- **The residue identity:** the crossing-driven cumulative warp minus the radial log-mass difference is minus
the off-line depth integral. -/
theorem residue_identity {t₀ t₁ : ℝ} (h₀ : GoodHeight t₀) (h₁ : GoodHeight t₁) (ht : t₀ ≤ t₁) :
    Real.pi * (∫ t in t₀..t₁, Smult t) - (radialLogMass t₁ - radialLogMass t₀)
      = -(Real.pi * ∫ t in t₀..t₁, (offLineStripZeroCountMult t : ℝ)) := by
  rw [integral_smult_window, ← integral_SAll_eq_radialLogMass_sub h₀ h₁ ht]
  ring

/-- The residue never exceeds zero. -/
theorem residue_nonpos {t₀ t₁ : ℝ} (h₀ : GoodHeight t₀) (h₁ : GoodHeight t₁) (ht : t₀ ≤ t₁) :
    Real.pi * (∫ t in t₀..t₁, Smult t) ≤ radialLogMass t₁ - radialLogMass t₀ := by
  have h := residue_identity h₀ h₁ ht
  have hnn : 0 ≤ ∫ t in t₀..t₁, (offLineStripZeroCountMult t : ℝ) :=
    intervalIntegral.integral_nonneg ht (fun t _ => Nat.cast_nonneg _)
  have hπ := Real.pi_pos
  nlinarith

/-- **The crossing-driven cumulative warp is a pure boundary term on every window.**  Stated purely in the
fiber's own terms — the on-line crossing ledger `Smult` (events of the readout on the line, with multiplicity,
against the clock) and the radial log-mass `radialLogMass` — with no reference to any zero set or height selection. -/
def RadialNoResidue : Prop :=
  ∀ t₀ t₁ : ℝ, 0 < t₀ → t₀ ≤ t₁ →
    Real.pi * (∫ t in t₀..t₁, Smult t) = radialLogMass t₁ - radialLogMass t₀

/-- **The radial door:** no residue ⟹ no off-line zeros. -/
theorem noOffline_of_radialNoResidue (h : RadialNoResidue) : NoOfflineZeros := by
  intro ρ hρ
  by_contra hoff
  -- normalise to the upper half (as in the limit door)
  have him_ne : ρ.im ≠ 0 := by
    intro h0
    have hρre : ρ = ((ρ.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using h0
    obtain ⟨ha, hb, hc⟩ := hρ
    rw [hρre] at hc
    exact zeta_ne_zero_of_real_unit ha hb hc
  set ρ' : ℂ := if 0 < ρ.im then ρ else (starRingEnd ℂ) ρ with hρ'def
  have hρ'_mem : ρ' ∈ ZD.NontrivialZeros := by
    rw [hρ'def]
    split_ifs with hh
    · exact hρ
    · obtain ⟨ha, hb, hc⟩ := hρ
      refine ⟨by simpa using ha, by simpa using hb, ?_⟩
      rw [riemannZeta_conj, hc, map_zero]
  have hρ'_im_pos : 0 < ρ'.im := by
    rw [hρ'def]
    split_ifs with hh
    · exact hh
    · simp only [Complex.conj_im]
      rcases lt_trichotomy ρ.im 0 with h1 | h1 | h1
      · linarith
      · exact absurd h1 him_ne
      · exact absurd h1 hh
  have hρ'_re : ρ'.re ≠ 1 / 2 := by
    rw [hρ'def]
    split_ifs with hh
    · exact hoff
    · simpa using hoff
  obtain ⟨t₀, ht₀, hg₀⟩ := exists_goodHeight_gt ρ'.im
  obtain ⟨t₁, ht₁, hg₁⟩ := exists_goodHeight_gt (t₀ + 1)
  have hle : t₀ ≤ t₁ := by linarith
  have hN : ∀ t, t₀ ≤ t → 1 ≤ offLineStripZeroCountMult t :=
    fun t htt => offLine_count_ge_one hρ'_mem hρ'_re hρ'_im_pos (by linarith)
  have hlow : ∫ t in t₀..t₁, (1 : ℝ) ≤ ∫ t in t₀..t₁, (offLineStripZeroCountMult t : ℝ) :=
    intervalIntegral.integral_mono_on hle (by simp) (offline_intervalIntegrable t₀ t₁)
      (fun t htm => by exact_mod_cast hN t htm.1)
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hlow
  have hres := residue_identity hg₀ hg₁ hle
  rw [h t₀ t₁ hg₀.1 hle, sub_self] at hres
  have hπ := Real.pi_pos
  nlinarith

theorem rh_of_radialNoResidue (h : RadialNoResidue) : RiemannHypothesis :=
  RiemannHypothesis_of_no_offline (noOffline_of_radialNoResidue h)

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.integral_SAll_eq_radialLogMass_sub
#print axioms CriticalLinePhasor.DVP.residue_identity
#print axioms CriticalLinePhasor.DVP.rh_of_radialNoResidue
