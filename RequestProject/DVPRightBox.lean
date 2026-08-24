import RequestProject.DVPZetaTopLift

/-!
# The right box: `∫ Im Log ζ(2+it) dt` is absolutely bounded by 12

Assembly step (iii) of the 405 map.  Per height, the clamped-lift FTC
transports `Im Log ζ(2+it)` to `σ₀`; integrating in `t` and collapsing the
box (404) leaves the two `σ ≥ 2` tail edges (≤ 6 each by 400) plus a right
edge that vanishes as `σ₀ → ∞` (`norm_log_zeta_edge`).  The bound `12` is
uniform in the height window.
-/

open Metric Complex MeasureTheory Topology Filter Set
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- `ζ'/ζ` is interval-integrable on `σ ≥ 2` horizontal segments off the
real axis. -/
theorem intervalIntegrable_zeta_logDeriv_ge_two {t σ₀ : ℝ} (htt : t ≠ 0)
    (hσ : 2 ≤ σ₀) :
    IntervalIntegrable
      (fun x : ℝ => deriv riemannZeta ((x:ℂ) + (t:ℂ) * I) /
        riemannZeta ((x:ℂ) + (t:ℂ) * I)) MeasureTheory.volume 2 σ₀ := by
  have hne1 : ∀ x : ℝ, ((x:ℂ) + (t:ℂ) * I) ≠ 1 := by
    intro x h1
    have := congrArg Complex.im h1
    simp at this
    exact htt this
  have haff : Continuous (fun x : ℝ => (x:ℂ) + (t:ℂ) * I) := by fun_prop
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hσ]
  have hdiffOn : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hdc : ContinuousOn
      (fun x : ℝ => deriv riemannZeta ((x:ℂ) + (t:ℂ) * I))
      (Icc (2:ℝ) σ₀) := by
    intro x _
    have hana : AnalyticAt ℂ riemannZeta ((x:ℂ) + (t:ℂ) * I) :=
      hdiffOn.analyticAt (isOpen_ne.mem_nhds (hne1 x))
    have hc : ContinuousAt
        (deriv riemannZeta ∘ fun ξ : ℝ => (ξ:ℂ) + (t:ℂ) * I) x :=
      ContinuousAt.comp hana.deriv.continuousAt haff.continuousAt
    exact hc.continuousWithinAt
  have hzc : ContinuousOn
      (fun x : ℝ => riemannZeta ((x:ℂ) + (t:ℂ) * I)) (Icc (2:ℝ) σ₀) := by
    intro x _
    have hc : ContinuousAt
        (riemannZeta ∘ fun ξ : ℝ => (ξ:ℂ) + (t:ℂ) * I) x :=
      ContinuousAt.comp (differentiableAt_riemannZeta
        (hne1 x)).continuousAt haff.continuousAt
    exact hc.continuousWithinAt
  refine hdc.div hzc (fun x hx => ?_)
  apply riemannZeta_ne_zero_of_one_lt_re
  have hre : ((x:ℂ) + (t:ℂ) * I).re = x := by simp
  rw [hre]
  linarith [hx.1]

/-- The horizontal FTC for the principal log on `σ ≥ 2` segments:
`∫₂^{σ₀} (ζ'/ζ)(x+it) dx = Log ζ(σ₀+it) − Log ζ(2+it)` for `t ≠ 0`. -/
theorem log_zeta_horizontal_ftc {t σ₀ : ℝ} (htt : t ≠ 0) (hσ : 2 ≤ σ₀) :
    ∫ x in (2:ℝ)..σ₀,
        deriv riemannZeta ((x:ℂ) + (t:ℂ) * I) /
          riemannZeta ((x:ℂ) + (t:ℂ) * I)
      = Complex.log (riemannZeta ((σ₀:ℂ) + (t:ℂ) * I))
        - Complex.log (riemannZeta ((2:ℂ) + (t:ℂ) * I)) := by
  have hne1 : ∀ x : ℝ, ((x:ℂ) + (t:ℂ) * I) ≠ 1 := by
    intro x h1
    have := congrArg Complex.im h1
    simp at this
    exact htt this
  have hre : ∀ x : ℝ, ((x:ℂ) + (t:ℂ) * I).re = x := by
    intro x
    simp
  have hzne : ∀ x : ℝ, 2 ≤ x → riemannZeta ((x:ℂ) + (t:ℂ) * I) ≠ 0 := by
    intro x hx
    apply riemannZeta_ne_zero_of_one_lt_re
    rw [hre]
    linarith
  set c : ℝ → ℝ := fun x => (Set.projIcc (2:ℝ) σ₀ hσ x : ℝ) with hcdef
  have hc_cont : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hc_mem : ∀ x, c x ∈ Set.Icc (2:ℝ) σ₀ := fun x => (Set.projIcc _ _ hσ x).2
  have hc_of_mem : ∀ x ∈ Set.Icc (2:ℝ) σ₀, c x = x := by
    intro x hx
    rw [hcdef]
    simp only []
    rw [Set.projIcc_of_mem hσ hx]
  set L : ℝ → ℂ := fun x =>
    Complex.log (riemannZeta (((c x):ℂ) + (t:ℂ) * I)) with hLdef
  have hL : Continuous L := by
    rw [continuous_iff_continuousAt]
    intro x
    have h2cx : 2 ≤ c x := (hc_mem x).1
    have hinner : ContinuousAt (fun x : ℝ => ((c x):ℂ) + (t:ℂ) * I) x :=
      (((Complex.continuous_ofReal.comp hc_cont).add continuous_const)).continuousAt
    have hζ : ContinuousAt riemannZeta (((c x):ℂ) + (t:ℂ) * I) :=
      (differentiableAt_riemannZeta (hne1 (c x))).continuousAt
    have hlog : ContinuousAt Complex.log
        (riemannZeta (((c x):ℂ) + (t:ℂ) * I)) :=
      continuousAt_clog (zeta_mem_slitPlane_of_two_le (by rw [hre]; exact h2cx))
    have hz_at : ContinuousAt
        (riemannZeta ∘ fun x : ℝ => ((c x):ℂ) + (t:ℂ) * I) x :=
      ContinuousAt.comp hζ hinner
    have hcomp : ContinuousAt
        (Complex.log ∘ riemannZeta ∘ fun x : ℝ => ((c x):ℂ) + (t:ℂ) * I) x :=
      ContinuousAt.comp hlog hz_at
    exact hcomp
  have hexp : ∀ x ∈ Set.Icc (2:ℝ) σ₀,
      Complex.exp (L x) = riemannZeta ((x:ℂ) + (t:ℂ) * I) := by
    intro x hx
    rw [hLdef]
    simp only []
    rw [hc_of_mem x hx]
    exact Complex.exp_log (hzne x hx.1)
  have hF : ∀ x ∈ Set.Ioo (2:ℝ) σ₀,
      HasDerivAt (fun ξ : ℝ => riemannZeta ((ξ:ℂ) + (t:ℂ) * I))
        (deriv riemannZeta ((x:ℂ) + (t:ℂ) * I)) x := by
    intro x _
    have haff : HasDerivAt (fun ξ : ℝ => (ξ:ℂ) + (t:ℂ) * I) 1 x := by
      have hid : HasDerivAt (fun ξ : ℝ => ((ξ:ℝ):ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
      simpa using hid.add_const ((t:ℂ) * I)
    have h := (differentiableAt_riemannZeta (hne1 x)).hasDerivAt.comp x haff
    simpa [Function.comp_def] using h
  have hFTC := intervalIntegral_logDeriv_eq_lift_sub_of_le hσ hL hexp hF
    (intervalIntegrable_zeta_logDeriv_ge_two htt hσ)
  rw [hFTC, hLdef]
  simp only []
  rw [hc_of_mem σ₀ ⟨hσ, le_refl _⟩, hc_of_mem 2 ⟨le_refl _, hσ⟩]
  norm_num

/-- **The right-box identity**: transporting the `σ = 2` argument integral
to `σ₀` and collapsing the box. -/
theorem right_box_identity {σ₀ t₀ t₁ : ℝ} (hσ : 2 ≤ σ₀)
    (h2 : 2 ≤ t₀) (ht : t₀ ≤ t₁) :
    ∫ t in t₀..t₁, (Complex.log (riemannZeta ((2:ℂ) + (t:ℂ) * I))).im
      = (∫ t in t₀..t₁,
          (Complex.log (riemannZeta ((σ₀:ℂ) + (t:ℂ) * I))).im)
        - ∫ x in (2:ℝ)..σ₀,
            (Real.log ‖riemannZeta ((x:ℂ) + (t₀:ℂ) * I)‖
              - Real.log ‖riemannZeta ((x:ℂ) + (t₁:ℂ) * I)‖) := by
  have hcont2 : ∀ σ : ℝ, 2 ≤ σ → ContinuousOn
      (fun t : ℝ => (Complex.log (riemannZeta ((σ:ℂ) + (t:ℂ) * I))).im)
      (Set.Icc t₀ t₁) := by
    intro σ hσ' t htm
    have htne : ((σ:ℂ) + (t:ℂ) * I) ≠ 1 := by
      intro h1
      have := congrArg Complex.im h1
      simp at this
      linarith [htm.1]
    have hre : ((σ:ℂ) + (t:ℂ) * I).re = σ := by simp
    have hinner : ContinuousAt (fun t : ℝ => (σ:ℂ) + (t:ℂ) * I) t :=
      (continuous_const.add (Complex.continuous_ofReal.mul
        continuous_const)).continuousAt
    have hζ : ContinuousAt riemannZeta ((σ:ℂ) + (t:ℂ) * I) :=
      (differentiableAt_riemannZeta htne).continuousAt
    have hlog : ContinuousAt Complex.log (riemannZeta ((σ:ℂ) + (t:ℂ) * I)) :=
      continuousAt_clog (zeta_mem_slitPlane_of_two_le (by rw [hre]; exact hσ'))
    have hz_at : ContinuousAt
        (riemannZeta ∘ fun t : ℝ => (σ:ℂ) + (t:ℂ) * I) t :=
      ContinuousAt.comp hζ hinner
    have hlog_at : ContinuousAt
        (Complex.log ∘ riemannZeta ∘ fun t : ℝ => (σ:ℂ) + (t:ℂ) * I) t :=
      ContinuousAt.comp hlog hz_at
    have hcomp : ContinuousAt
        (Complex.im ∘ Complex.log ∘ riemannZeta ∘
          fun t : ℝ => (σ:ℂ) + (t:ℂ) * I) t :=
      ContinuousAt.comp Complex.continuous_im.continuousAt hlog_at
    exact hcomp.continuousWithinAt
  have hpt : Set.EqOn
      (fun t : ℝ => (Complex.log (riemannZeta ((2:ℂ) + (t:ℂ) * I))).im)
      (fun t : ℝ => (Complex.log (riemannZeta ((σ₀:ℂ) + (t:ℂ) * I))).im
        - ∫ x in (2:ℝ)..σ₀,
            (deriv riemannZeta ((x:ℂ) + (t:ℂ) * I) /
              riemannZeta ((x:ℂ) + (t:ℂ) * I)).im)
      (Set.uIcc t₀ t₁) := by
    rw [Set.uIcc_of_le ht]
    intro t htm
    have htt : t ≠ 0 := by
      intro h
      have := htm.1
      rw [h] at this
      linarith
    have hftc := log_zeta_horizontal_ftc htt hσ
    have him := congrArg Complex.im hftc
    rw [Complex.sub_im] at him
    have hswap : (∫ x in (2:ℝ)..σ₀,
          deriv riemannZeta ((x:ℂ) + (t:ℂ) * I) /
            riemannZeta ((x:ℂ) + (t:ℂ) * I)).im
        = ∫ x in (2:ℝ)..σ₀,
            (deriv riemannZeta ((x:ℂ) + (t:ℂ) * I) /
              riemannZeta ((x:ℂ) + (t:ℂ) * I)).im :=
      (intervalIntegral.intervalIntegral_im
        (intervalIntegrable_zeta_logDeriv_ge_two htt hσ)).symm
    simp only []
    rw [← hswap]
    linarith [him]
  rw [intervalIntegral.integral_congr hpt]
  have hi1 : IntervalIntegrable
      (fun t : ℝ => (Complex.log (riemannZeta ((σ₀:ℂ) + (t:ℂ) * I))).im)
      MeasureTheory.volume t₀ t₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht]
    exact hcont2 σ₀ hσ
  have hi2 : IntervalIntegrable
      (fun t : ℝ => ∫ x in (2:ℝ)..σ₀,
        (deriv riemannZeta ((x:ℂ) + (t:ℂ) * I) /
          riemannZeta ((x:ℂ) + (t:ℂ) * I)).im)
      MeasureTheory.volume t₀ t₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht]
    have hgeq : Set.EqOn
        (fun t : ℝ => ∫ x in (2:ℝ)..σ₀,
          (deriv riemannZeta ((x:ℂ) + (t:ℂ) * I) /
            riemannZeta ((x:ℂ) + (t:ℂ) * I)).im)
        (fun t : ℝ =>
          (Complex.log (riemannZeta ((σ₀:ℂ) + (t:ℂ) * I))).im
            - (Complex.log (riemannZeta ((2:ℂ) + (t:ℂ) * I))).im)
        (Set.Icc t₀ t₁) := by
      intro t htm
      have := hpt (by rwa [Set.uIcc_of_le ht])
      simp only [] at this ⊢
      linarith [this]
    exact ((hcont2 σ₀ hσ).sub (hcont2 2 (le_refl 2))).congr hgeq
  rw [intervalIntegral.integral_sub hi1 hi2]
  congr 1
  exact box_vertical_collapse hσ ht (by linarith : (0:ℝ) < t₀)

/-- **The right-edge argument integral is absolutely bounded by 12**,
uniformly in the height window. -/
theorem right_edge_arg_integral_bound {t₀ t₁ : ℝ} (h2 : 2 ≤ t₀) (ht : t₀ ≤ t₁) :
    |∫ t in t₀..t₁,
        (Complex.log (riemannZeta ((2:ℂ) + (t:ℂ) * I))).im| ≤ 12 := by
  by_contra hcon
  push_neg at hcon
  set A : ℝ := |∫ t in t₀..t₁,
    (Complex.log (riemannZeta ((2:ℂ) + (t:ℂ) * I))).im| with hAdef
  have hA12 : 12 < A := hcon
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show (0:ℝ) < (A - 12) / (3 * (t₁ - t₀) + 1) by
      have : (0:ℝ) < 3 * (t₁ - t₀) + 1 := by linarith
      positivity)
    (show (1/2 : ℝ) < 1 by norm_num)
  set σ₀ : ℝ := max 3 (n:ℝ) with hσ₀def
  have hσ3 : (3:ℝ) ≤ σ₀ := le_max_left _ _
  have hσn : (n:ℝ) ≤ σ₀ := le_max_right _ _
  have hσ2 : (2:ℝ) ≤ σ₀ := by linarith
  have hid := right_box_identity hσ2 h2 ht
  -- right edge: pointwise ≤ 3·2^{−σ₀}
  have hedge : ∀ t ∈ Set.uIoc t₀ t₁,
      ‖(Complex.log (riemannZeta ((σ₀:ℂ) + (t:ℂ) * I))).im‖
        ≤ 3 * (2:ℝ)^(-σ₀) := by
    intro t htm
    have hre : ((σ₀:ℂ) + (t:ℂ) * I).re = σ₀ := by simp
    have h := norm_log_zeta_edge (z := (σ₀:ℂ) + (t:ℂ) * I)
      (by rw [hre]; exact hσ3)
    rw [hre] at h
    calc ‖(Complex.log (riemannZeta ((σ₀:ℂ) + (t:ℂ) * I))).im‖
        = |(Complex.log (riemannZeta ((σ₀:ℂ) + (t:ℂ) * I))).im| :=
          Real.norm_eq_abs _
      _ ≤ ‖Complex.log (riemannZeta ((σ₀:ℂ) + (t:ℂ) * I))‖ :=
          Complex.abs_im_le_norm _
      _ ≤ 3 * (2:ℝ)^(-σ₀) := h
  have hright : |∫ t in t₀..t₁,
      (Complex.log (riemannZeta ((σ₀:ℂ) + (t:ℂ) * I))).im|
        ≤ 3 * (2:ℝ)^(-σ₀) * |t₁ - t₀| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const hedge
    rwa [Real.norm_eq_abs] at this
  -- the two tail edges: ≤ 6 each
  have htail : ∀ s : ℝ, 2 ≤ |s| → |∫ x in (2:ℝ)..σ₀,
      Real.log ‖riemannZeta ((x:ℂ) + (s:ℂ) * I)‖| ≤ 6 := by
    intro s hs
    have h6 := zeta_tail_edge_abs_le (T := s) hs hσ2
    have habs := intervalIntegral.abs_integral_le_integral_abs
      (f := fun x : ℝ => Real.log ‖riemannZeta ((x:ℂ) + (s:ℂ) * I)‖)
      (μ := MeasureTheory.volume) hσ2
    exact le_trans habs h6
  have ht₀2 : (2:ℝ) ≤ |t₀| := by
    rw [abs_of_pos (by linarith)]
    exact h2
  have ht₁2 : (2:ℝ) ≤ |t₁| := by
    rw [abs_of_pos (by linarith)]
    linarith
  -- integrability of the two tail integrands to split the difference
  have htint : ∀ s : ℝ, 2 ≤ s → IntervalIntegrable
      (fun x : ℝ => Real.log ‖riemannZeta ((x:ℂ) + (s:ℂ) * I)‖)
      MeasureTheory.volume 2 σ₀ := by
    intro s hs
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ2]
    apply ContinuousOn.log
    · apply ContinuousOn.norm
      intro x hx
      have hne1 : ((x:ℂ) + (s:ℂ) * I) ≠ 1 := by
        intro h1
        have := congrArg Complex.im h1
        simp at this
        linarith
      have hc : ContinuousAt
          (riemannZeta ∘ fun ξ : ℝ => (ξ:ℂ) + (s:ℂ) * I) x :=
        ContinuousAt.comp (differentiableAt_riemannZeta hne1).continuousAt
          ((Complex.continuous_ofReal.add continuous_const).continuousAt)
      exact hc.continuousWithinAt
    · intro x hx
      apply norm_ne_zero_iff.mpr
      apply riemannZeta_ne_zero_of_one_lt_re
      have hre : ((x:ℂ) + (s:ℂ) * I).re = x := by simp
      rw [hre]
      linarith [hx.1]
  have hsplit : ∫ x in (2:ℝ)..σ₀,
      (Real.log ‖riemannZeta ((x:ℂ) + (t₀:ℂ) * I)‖
        - Real.log ‖riemannZeta ((x:ℂ) + (t₁:ℂ) * I)‖)
      = (∫ x in (2:ℝ)..σ₀, Real.log ‖riemannZeta ((x:ℂ) + (t₀:ℂ) * I)‖)
        - ∫ x in (2:ℝ)..σ₀, Real.log ‖riemannZeta ((x:ℂ) + (t₁:ℂ) * I)‖ :=
    intervalIntegral.integral_sub (htint t₀ h2) (htint t₁ (by linarith))
  -- 2^{−σ₀} ≤ (1/2)^n
  have hpow : (2:ℝ)^(-σ₀) ≤ (1/2:ℝ)^n := by
    have h1 : (2:ℝ)^(-σ₀) ≤ (2:ℝ)^(-(n:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2' : (2:ℝ)^(-(n:ℝ)) = (1/2:ℝ)^n := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast,
        one_div, inv_pow]
    calc (2:ℝ)^(-σ₀) ≤ (2:ℝ)^(-(n:ℝ)) := h1
      _ = (1/2:ℝ)^n := h2'
  -- assemble the contradiction
  have hA_le : A ≤ 3 * (2:ℝ)^(-σ₀) * |t₁ - t₀| + 12 := by
    rw [hAdef, hid, hsplit]
    have h1 := hright
    have h2' := htail t₀ ht₀2
    have h3 := htail t₁ ht₁2
    calc |(∫ t in t₀..t₁,
          (Complex.log (riemannZeta ((σ₀:ℂ) + (t:ℂ) * I))).im)
          - ((∫ x in (2:ℝ)..σ₀, Real.log ‖riemannZeta ((x:ℂ) + (t₀:ℂ) * I)‖)
            - ∫ x in (2:ℝ)..σ₀, Real.log ‖riemannZeta ((x:ℂ) + (t₁:ℂ) * I)‖)|
        ≤ |∫ t in t₀..t₁,
            (Complex.log (riemannZeta ((σ₀:ℂ) + (t:ℂ) * I))).im|
          + |(∫ x in (2:ℝ)..σ₀, Real.log ‖riemannZeta ((x:ℂ) + (t₀:ℂ) * I)‖)
            - ∫ x in (2:ℝ)..σ₀, Real.log ‖riemannZeta ((x:ℂ) + (t₁:ℂ) * I)‖| := by
          rw [sub_eq_add_neg]
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg]
      _ ≤ 3 * (2:ℝ)^(-σ₀) * |t₁ - t₀| + 12 := by
          have h4 : |(∫ x in (2:ℝ)..σ₀,
              Real.log ‖riemannZeta ((x:ℂ) + (t₀:ℂ) * I)‖)
              - ∫ x in (2:ℝ)..σ₀,
                Real.log ‖riemannZeta ((x:ℂ) + (t₁:ℂ) * I)‖| ≤ 12 := by
            rw [sub_eq_add_neg]
            refine (abs_add_le _ _).trans ?_
            rw [abs_neg]
            linarith
          linarith
  have hrpos : (0:ℝ) < (2:ℝ)^(-σ₀) := by positivity
  have habs_t : |t₁ - t₀| = t₁ - t₀ := abs_of_nonneg (by linarith)
  rw [habs_t] at hA_le
  have hfinal : 3 * (2:ℝ)^(-σ₀) * (t₁ - t₀) < A - 12 := by
    have hnn : (0:ℝ) ≤ t₁ - t₀ := by linarith
    calc 3 * (2:ℝ)^(-σ₀) * (t₁ - t₀)
        ≤ 3 * (1/2:ℝ)^n * (t₁ - t₀) := by
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ) ≤ 3)) hnn
          linarith
      _ < (A - 12) / (3 * (t₁ - t₀) + 1) * (3 * (t₁ - t₀) + 1) := by
          have hden : (0:ℝ) < 3 * (t₁ - t₀) + 1 := by linarith
          have hquot : (0:ℝ) < (A - 12) / (3 * (t₁ - t₀) + 1) := by
            positivity
          have hstep : 3 * (1/2:ℝ)^n * (t₁ - t₀)
              < (A - 12) / (3 * (t₁ - t₀) + 1) * (3 * (t₁ - t₀) + 1) := by
            have hp0 : (0:ℝ) ≤ (1/2:ℝ)^n := by positivity
            nlinarith [hn, hp0, hnn]
          exact hstep
      _ = A - 12 := by
          field_simp
  linarith [hA_le, hfinal]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.intervalIntegrable_zeta_logDeriv_ge_two
#print axioms CriticalLinePhasor.DVP.log_zeta_horizontal_ftc
#print axioms CriticalLinePhasor.DVP.right_box_identity
#print axioms CriticalLinePhasor.DVP.right_edge_arg_integral_bound
end AxiomAudit
