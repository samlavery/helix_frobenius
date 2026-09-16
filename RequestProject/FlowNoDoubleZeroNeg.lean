import RequestProject.FlowNoDoubleZero

/-!
# The negative-curvature case

Mirror of `FlowLamAnti` / `FlowSectionConvex` / `FlowNoDoubleZero` with every inequality flipped.
With `∂_x²Ξ_{λ₀}(x₀) = −c < 0` we have `jR λ₀ x₀ = c > 0`, so `s ↦ xiR s x` is strictly MONOTONE in
the warp parameter and `x₀` is a local MAXIMUM of value `0`; descending in `λ` therefore makes the
section strictly negative, and the same Hurwitz step closes it.
-/

open Complex Filter Topology Set Metric

namespace CriticalLinePhasor.XiKernel

theorem jR_pos_on_rect {lam₀ : ℝ} (h0 : 0 < lam₀) (h1 : lam₀ ≤ 1) {x₀ : ℝ}
    (hc : (deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re < 0) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ δ < lam₀ ∧
      ∀ s ∈ Icc (lam₀ - δ) lam₀, ∀ x : ℝ, |x - x₀| ≤ r →
        -((deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re) / 2 ≤ jR s x := by
  set c : ℝ := -((deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hj0 : jR lam₀ x₀ = c := by rw [jR_eq_neg_deriv2 h0.le h1, hcdef]
  have hcont := continuous_jR_snd h0.le h1
  have hxcont : ∀ᶠ x in 𝓝 x₀, |jR lam₀ x - jR lam₀ x₀| < c / 4 :=
    (hcont.tendsto x₀).eventually
      (eventually_abs_sub_lt (jR lam₀ x₀) (by positivity : (0:ℝ) < c / 4))
  obtain ⟨r, hrpos, hr⟩ := Metric.eventually_nhds_iff.mp hxcont
  obtain ⟨C, hC, hlip⟩ := jR_lipschitz h1 h0.le
  set δ : ℝ := min (lam₀ / 2) (c / (4 * (C + 1))) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
  have hδlt : δ < lam₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨r / 2, δ, by positivity, hδpos, hδlt, ?_⟩
  intro s hs x hx
  have hs0 : 0 ≤ s := by have := hs.1; linarith [hδlt]
  have hsl : s ≤ lam₀ := hs.2
  have hx' : |jR lam₀ x - jR lam₀ x₀| < c / 4 := by
    refine hr ?_
    rw [Real.dist_eq]
    calc |x - x₀| ≤ r / 2 := hx
      _ < r := by linarith
  have hs' : |jR s x - jR lam₀ x| ≤ |s - lam₀| * C := hlip s lam₀ hs0 h0.le hsl le_rfl x
  have hsd : |s - lam₀| ≤ δ := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith [hs.1]
  have hCbd : |s - lam₀| * C ≤ c / 4 := by
    have h1' : |s - lam₀| * C ≤ δ * C := mul_le_mul_of_nonneg_right hsd hC
    have h2' : δ * C ≤ (c / (4 * (C + 1))) * C := mul_le_mul_of_nonneg_right (min_le_right _ _) hC
    have h3' : (c / (4 * (C + 1))) * C ≤ c / 4 := by
      have hCp : (0:ℝ) < 4 * (C + 1) := by linarith
      have hnn : (0:ℝ) ≤ c / (4 * (C + 1)) := div_nonneg hcpos.le hCp.le
      have key : c / 4 - (c / (4 * (C + 1))) * C = c / (4 * (C + 1)) := by field_simp; ring
      linarith
    linarith
  have hlow : jR lam₀ x₀ - c / 4 - c / 4 ≤ jR s x := by
    have a1 : jR lam₀ x - jR s x ≤ |jR s x - jR lam₀ x| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have a2 : jR lam₀ x₀ - jR lam₀ x ≤ |jR lam₀ x - jR lam₀ x₀| := by
      rw [abs_sub_comm]; exact le_abs_self _
    linarith
  rw [hj0] at hlow
  linarith

theorem xiR_gt_of_lam_lt {lam₀ : ℝ} (h0 : 0 < lam₀) (h1 : lam₀ < 1) {x₀ : ℝ}
    (hc : (deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re < 0) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ δ < lam₀ ∧
      ∀ x : ℝ, |x - x₀| ≤ r → ∀ lam ∈ Ico (lam₀ - δ) lam₀, xiR lam x < xiR lam₀ x := by
  obtain ⟨r, δ, hr, hδ, hδl, hrect⟩ := jR_pos_on_rect h0 h1.le hc
  refine ⟨r, δ, hr, hδ, hδl, ?_⟩
  intro x hx lam hlam
  set lam₁ : ℝ := (lam₀ + 1) / 2 with hl1
  have hl1lt : lam₀ < lam₁ := by rw [hl1]; linarith
  have hl1le : lam₁ ≤ 1 := by rw [hl1]; linarith
  have hderiv : ∀ s ∈ Icc (lam₀ - δ) lam₀, HasDerivAt (fun t : ℝ => xiR t x) (jR s x) s := by
    intro s hs
    have hs0 : 0 ≤ s := by have := hs.1; linarith
    exact hasDerivAt_xiR_lam hs0 (lt_of_le_of_lt hs.2 hl1lt) hl1le x
  have hcontD : ContinuousOn (fun t : ℝ => xiR t x) (Icc (lam₀ - δ) lam₀) := fun s hs =>
    ((hderiv s hs).continuousAt).continuousWithinAt
  have hposD : ∀ s ∈ interior (Icc (lam₀ - δ) lam₀), 0 < deriv (fun t : ℝ => xiR t x) s := by
    intro s hs
    rw [interior_Icc] at hs
    have hsD : s ∈ Icc (lam₀ - δ) lam₀ := ⟨hs.1.le, hs.2.le⟩
    rw [(hderiv s hsD).deriv]
    have := hrect s hsD x hx
    have hcpos : 0 < -((deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re) := by linarith
    linarith
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc _ _) hcontD hposD
  exact hmono ⟨hlam.1, le_of_lt hlam.2⟩ ⟨by linarith [hδ], le_rfl⟩ hlam.2

theorem xiR_nonpos_near {lam₀ : ℝ} (h0 : 0 ≤ lam₀) (h1 : lam₀ ≤ 1) {x₀ : ℝ}
    (hval : xiR lam₀ x₀ = 0) (hd : deriv (xiR lam₀) x₀ = 0)
    (hc : (deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : ℝ, |x - x₀| ≤ ρ → xiR lam₀ x ≤ 0 := by
  have hd2 : Differentiable ℂ (deriv (deriv (flowStage lam₀))) := by
    have hA2 : AnalyticOnNhd ℂ (deriv (flowStage lam₀)) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_deriv_flowStage h0 h1)
    exact fun z => ((hA2 z (Set.mem_univ z)).deriv).differentiableAt
  have hcont : Continuous (fun y : ℝ => (deriv (deriv (flowStage lam₀)) (y : ℂ)).re) :=
    Complex.continuous_re.comp (hd2.continuous.comp Complex.continuous_ofReal)
  have hneg : ∀ᶠ y : ℝ in 𝓝 x₀, (deriv (deriv (flowStage lam₀)) ((y : ℝ) : ℂ)).re < 0 :=
    (hcont.tendsto x₀).eventually (eventually_lt_nhds hc)
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.eventually_nhds_iff.mp hneg
  have hxiDiff : Differentiable ℝ (xiR lam₀) := fun y =>
    (hasDerivAt_xiR_fst h0 h1 y).differentiableAt
  refine ⟨ρ₀ / 2, by positivity, ?_⟩
  intro x hx
  have hmemD : ∀ y ∈ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2), dist y x₀ < ρ₀ := by
    intro y hy
    rw [Real.dist_eq, abs_lt]
    constructor <;> [linarith [hy.1]; linarith [hy.2]]
  have hderiv2 : ∀ y ∈ interior (Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2)),
      deriv (deriv (xiR lam₀)) y < 0 := by
    intro y hy
    rw [interior_Icc] at hy
    rw [deriv2_xiR_eq h0 h1]
    exact hball (hmemD y ⟨hy.1.le, hy.2.le⟩)
  have hcontD : ContinuousOn (deriv (xiR lam₀)) (Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2)) := fun y _ =>
    ((hasDerivAt_deriv_xiR h0 h1 y).continuousAt).continuousWithinAt
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2)) hcontD hderiv2
  have hxD : x ∈ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2) := by
    obtain ⟨ha, hb⟩ := abs_le.mp hx
    constructor <;> [linarith; linarith]
  have hx₀D : x₀ ∈ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2) := by constructor <;> linarith
  rcases le_total x x₀ with hle | hle
  · have hsub : Icc x x₀ ⊆ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2) := Icc_subset_Icc hxD.1 hx₀D.2
    have hnn : ∀ y ∈ interior (Icc x x₀), 0 ≤ deriv (xiR lam₀) y := by
      intro y hy
      rw [interior_Icc] at hy
      have := hanti (hsub ⟨hy.1.le, hy.2.le⟩) hx₀D hy.2
      rw [hd] at this
      linarith
    have hmon := monotoneOn_of_deriv_nonneg (convex_Icc x x₀)
      (hxiDiff.continuous.continuousOn) (hxiDiff.differentiableOn) hnn
    have := hmon (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) hle
    rw [hval] at this
    linarith
  · have hsub : Icc x₀ x ⊆ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2) := Icc_subset_Icc hx₀D.1 hxD.2
    have hnp : ∀ y ∈ interior (Icc x₀ x), deriv (xiR lam₀) y ≤ 0 := by
      intro y hy
      rw [interior_Icc] at hy
      have := hanti hx₀D (hsub ⟨hy.1.le, hy.2.le⟩) hy.1
      rw [hd] at this
      linarith
    have hant := antitoneOn_of_deriv_nonpos (convex_Icc x₀ x)
      (hxiDiff.continuous.continuousOn) (hxiDiff.differentiableOn) hnp
    have := hant (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) hle
    rw [hval] at this
    linarith


/-- **The negative-curvature case.** -/
theorem flowStage_no_double_zero_neg {lam₀ : ℝ} (h8 : 1 / 8 < lam₀) (h1 : lam₀ < 1) {x₀ : ℝ}
    (hz : flowStage lam₀ (x₀ : ℂ) = 0)
    (hdz : deriv (flowStage lam₀) (x₀ : ℂ) = 0)
    (hc : (deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re < 0) : False := by
  have h0 : 0 < lam₀ := by linarith
  have h1le : lam₀ ≤ 1 := h1.le
  obtain ⟨r, δ₁, hr, hδ₁, hδ₁l, hmono⟩ := xiR_gt_of_lam_lt h0 h1 hc
  have hval : xiR lam₀ x₀ = 0 := by rw [xiR_eq_zero_iff]; exact hz
  have hd : deriv (xiR lam₀) x₀ = 0 := by rw [deriv_xiR_eq h0.le h1le]; simp [hdz]
  obtain ⟨ρ, hρ, hnp⟩ := xiR_nonpos_near h0.le h1le hval hd hc
  set δ : ℝ := min δ₁ ((lam₀ - 1 / 8) / 2) with hδdef
  have hδpos : 0 < δ := lt_min hδ₁ (by linarith)
  have hδ8 : 1 / 8 < lam₀ - δ := by
    have : δ ≤ (lam₀ - 1 / 8) / 2 := min_le_right _ _
    linarith
  set R : ℝ := min r ρ with hR
  have hRpos : 0 < R := lt_min hr hρ
  have hnozero : ∀ lam ∈ Ico (lam₀ - δ) lam₀, ∀ z ∈ ball ((x₀ : ℝ) : ℂ) R,
      flowStage lam z ≠ 0 := by
    intro lam hlam z hzb hcon
    have hlam8 : 1 / 8 ≤ lam := by have := hlam.1; linarith
    have hlam1 : lam ≤ 1 := by have := hlam.2; linarith
    have hzim : z.im = 0 := flowFrontier_one_eighth lam hlam8 hlam1 z hcon
    have hzre : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hzim]
    have hdist : |z.re - x₀| < R := by
      have hb := mem_ball.mp hzb
      rw [Complex.dist_eq] at hb
      calc |z.re - x₀| = |(z - ((x₀ : ℝ) : ℂ)).re| := by simp
        _ ≤ ‖z - ((x₀ : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
        _ < R := hb
    have hlamI : lam ∈ Ico (lam₀ - δ₁) lam₀ :=
      ⟨by have := hlam.1; have : δ ≤ δ₁ := min_le_left _ _; linarith, hlam.2⟩
    have h1' : xiR lam z.re < xiR lam₀ z.re :=
      hmono z.re (le_of_lt (lt_of_lt_of_le hdist (min_le_left _ _))) lam hlamI
    have h2' : xiR lam₀ z.re ≤ 0 :=
      hnp z.re (le_of_lt (lt_of_lt_of_le hdist (min_le_right _ _)))
    have hne : xiR lam z.re ≠ 0 := by linarith
    exact hne (by rw [xiR_eq_zero_iff, ← hzre]; exact hcon)
  set lamSeq : ℕ → ℝ := fun n => lam₀ - δ / (n + 2) with hls
  have hseqI : ∀ n, lamSeq n ∈ Ico (lam₀ - δ) lam₀ := by
    intro n
    have hn : (0:ℝ) < (n : ℝ) + 2 := by positivity
    constructor
    · have : δ / ((n : ℝ) + 2) ≤ δ := by rw [div_le_iff₀ hn]; nlinarith [hδpos.le]
      simp only [hls]; linarith
    · have : 0 < δ / ((n : ℝ) + 2) := by positivity
      simp only [hls]; linarith
  obtain ⟨C, hC, hlip⟩ := flowStage_lipschitz_lam (lam₁ := lam₀) h1le h0.le (a := R) hRpos.le
  have hzim : ∀ z ∈ ball ((x₀ : ℝ) : ℂ) R, |z.im| ≤ R := by
    intro z hzb
    have hb := mem_ball.mp hzb
    rw [Complex.dist_eq] at hb
    calc |z.im| = |(z - ((x₀ : ℝ) : ℂ)).im| := by simp
      _ ≤ ‖z - ((x₀ : ℝ) : ℂ)‖ := Complex.abs_im_le_norm _
      _ ≤ R := hb.le
  have hunif : TendstoUniformlyOn (fun n => flowStage (lamSeq n)) (flowStage lam₀) atTop
      (ball ((x₀ : ℝ) : ℂ) R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2) * C) atTop (𝓝 0) := by
      have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      have hq : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        Tendsto.const_div_atTop hden δ
      simpa using hq.mul_const C
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
    intro z hzb
    have hdd := hlip (lamSeq n) lam₀ (by have := (hseqI n).1; linarith) h0.le
      (le_of_lt (hseqI n).2) le_rfl z (hzim z hzb)
    have habs : |lamSeq n - lam₀| = δ / ((n : ℝ) + 2) := by
      simp only [hls]
      rw [show lam₀ - δ / ((n : ℝ) + 2) - lam₀ = -(δ / ((n : ℝ) + 2)) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
    rw [Complex.dist_eq, norm_sub_rev]
    calc ‖flowStage (lamSeq n) z - flowStage lam₀ z‖ ≤ |lamSeq n - lam₀| * C := hdd
      _ = δ / ((n : ℝ) + 2) * C := by rw [habs]
      _ < ε := hn
  have hconn : IsPreconnected (ball ((x₀ : ℝ) : ℂ) R) := (convex_ball _ _).isPreconnected
  have hdiffn : ∀ n, DifferentiableOn ℂ (flowStage (lamSeq n)) (ball ((x₀ : ℝ) : ℂ) R) := fun n =>
    (differentiable_flowStage (by have := (hseqI n).1; linarith)
      (by have := (hseqI n).2; linarith)).differentiableOn
  have hFne : ∀ n, ∀ z ∈ ball ((x₀ : ℝ) : ℂ) R, flowStage (lamSeq n) z ≠ 0 :=
    fun n z hzb => hnozero (lamSeq n) (hseqI n) z hzb
  have hfne : ∃ z ∈ ball ((x₀ : ℝ) : ℂ) R, flowStage lam₀ z ≠ 0 := by
    by_contra hall
    push_neg at hall
    obtain ⟨z₁, hz₁⟩ := flowStage_ne_zero h0.le h1le
    apply hz₁
    have hA : AnalyticOnNhd ℂ (flowStage lam₀) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_flowStage h0.le h1le)
    have hev : flowStage lam₀ =ᶠ[𝓝 ((x₀ : ℝ) : ℂ)] 0 := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hRpos)] with w hw
      exact hall w hw
    exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ _) hev (Set.mem_univ z₁)
  have hfinal := CriticalLinePhasor.Hurwitz.ne_zero_of_tendstoLocallyUniformlyOn isOpen_ball
    hconn hdiffn hFne hunif.tendstoLocallyUniformlyOn hfne
  exact hfinal ((x₀ : ℝ) : ℂ) (mem_ball_self hRpos) hz

/-- **No double zero, either curvature.**  A real zero of `Ξ_{λ₀}` at which the first derivative
vanishes must also have vanishing second derivative — i.e. there is no zero of order exactly two. -/
theorem flowStage_deriv2_eq_zero_of_double {lam₀ : ℝ} (h8 : 1 / 8 < lam₀) (h1 : lam₀ < 1) {x₀ : ℝ}
    (hz : flowStage lam₀ (x₀ : ℂ) = 0)
    (hdz : deriv (flowStage lam₀) (x₀ : ℂ) = 0) :
    (deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re = 0 := by
  rcases lt_trichotomy ((deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re) 0 with h | h | h
  · exact absurd h (fun hlt => (flowStage_no_double_zero_neg h8 h1 hz hdz hlt).elim)
  · exact h
  · exact absurd h (fun hgt => (flowStage_no_double_zero_pos h8 h1 hz hdz hgt).elim)

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.jR_pos_on_rect
#print axioms CriticalLinePhasor.XiKernel.xiR_gt_of_lam_lt
#print axioms CriticalLinePhasor.XiKernel.xiR_nonpos_near
#print axioms CriticalLinePhasor.XiKernel.flowStage_no_double_zero_neg
#print axioms CriticalLinePhasor.XiKernel.flowStage_deriv2_eq_zero_of_double
