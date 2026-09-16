import RequestProject.FlowDerivSection

/-!
# No zero of order exactly two, at every order of derivative
-/

open Complex Filter Topology Set Metric

namespace CriticalLinePhasor.XiKernel

/-- The `λ`-derivative of the order-`k` section stays negative on a rectangle. -/
theorem jRD_neg_on_rect (k : ℕ) {lam₀ : ℝ} (h0 : 0 < lam₀) (h1 : lam₀ ≤ 1) {x₀ : ℝ}
    (hc : 0 < (flowD (k + 2) lam₀ (x₀ : ℂ)).re) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ δ < lam₀ ∧
      ∀ s ∈ Icc (lam₀ - δ) lam₀, ∀ x : ℝ, |x - x₀| ≤ r →
        jRD k s x ≤ -((flowD (k + 2) lam₀ (x₀ : ℂ)).re) / 2 := by
  set c : ℝ := (flowD (k + 2) lam₀ (x₀ : ℂ)).re with hcdef
  have hj0 : jRD k lam₀ x₀ = -c := rfl
  have hcont := continuous_jRD k h0.le h1
  have hxcont : ∀ᶠ x in 𝓝 x₀, |jRD k lam₀ x - jRD k lam₀ x₀| < c / 4 :=
    (hcont.tendsto x₀).eventually
      (eventually_abs_sub_lt (jRD k lam₀ x₀) (by positivity : (0:ℝ) < c / 4))
  obtain ⟨r, hrpos, hr⟩ := Metric.eventually_nhds_iff.mp hxcont
  obtain ⟨C, hC, hlip⟩ := jRD_lipschitz k h1 h0.le
  refine ⟨r / 2, min (lam₀ / 2) (c / (4 * (C + 1))), by positivity,
    lt_min (by linarith) (by positivity),
    lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
  intro s hs x hx
  have hδlt : min (lam₀ / 2) (c / (4 * (C + 1))) ≤ lam₀ / 2 := min_le_left _ _
  have hs0 : 0 ≤ s := by have := hs.1; linarith
  have hsl : s ≤ lam₀ := hs.2
  have hx' : |jRD k lam₀ x - jRD k lam₀ x₀| < c / 4 := by
    refine hr ?_
    rw [Real.dist_eq]
    calc |x - x₀| ≤ r / 2 := hx
      _ < r := by linarith
  have hs' : |jRD k s x - jRD k lam₀ x| ≤ |s - lam₀| * C := hlip s lam₀ hs0 h0.le hsl le_rfl x
  have hsd : |s - lam₀| ≤ min (lam₀ / 2) (c / (4 * (C + 1))) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith [hs.1]
  have hCbd : |s - lam₀| * C ≤ c / 4 := by
    have h1' : |s - lam₀| * C ≤ (c / (4 * (C + 1))) * C :=
      mul_le_mul_of_nonneg_right (le_trans hsd (min_le_right _ _)) hC
    have hCp : (0:ℝ) < 4 * (C + 1) := by linarith
    have hnn : (0:ℝ) ≤ c / (4 * (C + 1)) := div_nonneg hc.le hCp.le
    have key : c / 4 - (c / (4 * (C + 1))) * C = c / (4 * (C + 1)) := by field_simp; ring
    linarith
  have a1 : jRD k s x - jRD k lam₀ x ≤ |jRD k s x - jRD k lam₀ x| := le_abs_self _
  have a2 : jRD k lam₀ x - jRD k lam₀ x₀ ≤ |jRD k lam₀ x - jRD k lam₀ x₀| := le_abs_self _
  linarith [hj0]

/-- Descending in `λ` strictly raises the order-`k` section. -/
theorem xiRD_lt_of_lam_lt (k : ℕ) {lam₀ : ℝ} (h0 : 0 < lam₀) (h1 : lam₀ < 1) {x₀ : ℝ}
    (hc : 0 < (flowD (k + 2) lam₀ (x₀ : ℂ)).re) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ δ < lam₀ ∧
      ∀ x : ℝ, |x - x₀| ≤ r → ∀ lam ∈ Ico (lam₀ - δ) lam₀, xiRD k lam₀ x < xiRD k lam x := by
  obtain ⟨r, δ, hr, hδ, hδl, hrect⟩ := jRD_neg_on_rect k h0 h1.le hc
  refine ⟨r, δ, hr, hδ, hδl, ?_⟩
  intro x hx lam hlam
  have hl1lt : lam₀ < (lam₀ + 1) / 2 := by linarith
  have hl1le : (lam₀ + 1) / 2 ≤ 1 := by linarith
  have hderiv : ∀ s ∈ Icc (lam₀ - δ) lam₀,
      HasDerivAt (fun t : ℝ => xiRD k t x) (jRD k s x) s := by
    intro s hs
    have hs0 : 0 ≤ s := by have := hs.1; linarith
    exact hasDerivAt_xiRD_lam k hs0 (lt_of_le_of_lt hs.2 hl1lt) hl1le x
  have hcontD : ContinuousOn (fun t : ℝ => xiRD k t x) (Icc (lam₀ - δ) lam₀) := fun s hs =>
    ((hderiv s hs).continuousAt).continuousWithinAt
  have hnegD : ∀ s ∈ interior (Icc (lam₀ - δ) lam₀), deriv (fun t : ℝ => xiRD k t x) s < 0 := by
    intro s hs
    rw [interior_Icc] at hs
    have hsD : s ∈ Icc (lam₀ - δ) lam₀ := ⟨hs.1.le, hs.2.le⟩
    rw [(hderiv s hsD).deriv]
    have := hrect s hsD x hx
    linarith
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc _ _) hcontD hnegD
  exact hanti ⟨hlam.1, le_of_lt hlam.2⟩ ⟨by linarith, le_rfl⟩ hlam.2

/-- At a double zero of positive curvature the order-`k` section is `≥ 0` nearby. -/
theorem xiRD_nonneg_near (k : ℕ) {lam₀ : ℝ} (h0 : 0 ≤ lam₀) (h1 : lam₀ ≤ 1) {x₀ : ℝ}
    (hval : xiRD k lam₀ x₀ = 0) (hd : (flowD (k + 1) lam₀ (x₀ : ℂ)).re = 0)
    (hc : 0 < (flowD (k + 2) lam₀ (x₀ : ℂ)).re) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : ℝ, |x - x₀| ≤ ρ → 0 ≤ xiRD k lam₀ x := by
  refine CriticalLinePhasor.Merger.nonneg_near_of_deriv2_pos
    (f' := fun y : ℝ => (flowD (k + 1) lam₀ (y : ℂ)).re)
    (f'' := fun y : ℝ => (flowD (k + 2) lam₀ (y : ℂ)).re)
    (fun x => hasDerivAt_xiRD_fst k h0 h1 x) (fun x => ?_) ?_ hval hd hc
  · have h := ((differentiable_flowD (k + 1) h0 h1 ((x : ℝ) : ℂ)).hasDerivAt).real_of_complex
    rwa [(hasDerivAt_flowD_z (k + 1) h0 h1 ((x : ℝ) : ℂ)).deriv] at h
  · exact Complex.continuous_re.comp
      ((differentiable_flowD (k + 2) h0 h1).continuous.comp Complex.continuous_ofReal)


/-- Non-vanishing at `λ₀` propagates to nearby `λ`, by the uniform Lipschitz bound. -/
theorem flowD_ne_zero_near (k : ℕ) {lam₀ : ℝ} (h0 : 0 < lam₀) (h1 : lam₀ ≤ 1)
    (hne : ∃ z, flowD k lam₀ z ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ lam : ℝ, 0 ≤ lam → lam ≤ lam₀ → lam₀ - lam < η →
      ∃ z, flowD k lam z ≠ 0 := by
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨C, hC, hlip⟩ := flowD_lipschitz_lam k h1 h0.le (a := |z₀.im|) (abs_nonneg _)
  have hpos : 0 < ‖flowD k lam₀ z₀‖ := norm_pos_iff.mpr hz₀
  refine ⟨‖flowD k lam₀ z₀‖ / (C + 1), by positivity, ?_⟩
  intro lam hl0 hle hlt
  refine ⟨z₀, ?_⟩
  intro hcon
  have hd := hlip lam lam₀ hl0 h0.le hle le_rfl z₀ le_rfl
  rw [hcon, zero_sub, norm_neg] at hd
  have habs : |lam - lam₀| = lam₀ - lam := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [habs] at hd
  have hstep : (lam₀ - lam) * C < ‖flowD k lam₀ z₀‖ := by
    have h1' : (lam₀ - lam) * C ≤ (‖flowD k lam₀ z₀‖ / (C + 1)) * C :=
      mul_le_mul_of_nonneg_right hlt.le hC
    have hCp : (0:ℝ) < C + 1 := by linarith
    have key : ‖flowD k lam₀ z₀‖ - (‖flowD k lam₀ z₀‖ / (C + 1)) * C
        = ‖flowD k lam₀ z₀‖ / (C + 1) := by field_simp; ring
    have : (0:ℝ) < ‖flowD k lam₀ z₀‖ / (C + 1) := by positivity
    linarith
  linarith

/-- **No zero of order exactly two, positive curvature, at order `k`.** -/
theorem flowD_no_double_zero_pos (k : ℕ) {lam₀ : ℝ} (h8 : 1 / 8 < lam₀) (h1 : lam₀ < 1) {x₀ : ℝ}
    (hne : ∃ z, flowD k lam₀ z ≠ 0)
    (hz : flowD k lam₀ (x₀ : ℂ) = 0)
    (hdz : (flowD (k + 1) lam₀ (x₀ : ℂ)).re = 0)
    (hc : 0 < (flowD (k + 2) lam₀ (x₀ : ℂ)).re) : False := by
  have h0 : 0 < lam₀ := by linarith
  have h1le : lam₀ ≤ 1 := h1.le
  obtain ⟨r, δ₁, hr, hδ₁, hδ₁l, hanti⟩ := xiRD_lt_of_lam_lt k h0 h1 hc
  have hval : xiRD k lam₀ x₀ = 0 := by rw [xiRD_eq_zero_iff]; exact hz
  obtain ⟨ρ, hρ, hnn⟩ := xiRD_nonneg_near k h0.le h1le hval hdz hc
  obtain ⟨η, hη, hnear⟩ := flowD_ne_zero_near k h0 h1le hne
  set δ : ℝ := min (min δ₁ (η / 2)) ((lam₀ - 1 / 8) / 2) with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ₁ (by positivity)) (by linarith)
  have hδ8 : 1 / 8 < lam₀ - δ := by
    have : δ ≤ (lam₀ - 1 / 8) / 2 := min_le_right _ _
    linarith
  have hδ1 : δ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδη : δ ≤ η / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  set R : ℝ := min r ρ with hR
  have hRpos : 0 < R := lt_min hr hρ
  have hnozero : ∀ lam ∈ Ico (lam₀ - δ) lam₀, ∀ z ∈ ball ((x₀ : ℝ) : ℂ) R,
      flowD k lam z ≠ 0 := by
    intro lam hlam z hzb hcon
    have hlam8 : 1 / 8 ≤ lam := by have := hlam.1; linarith
    have hlam1 : lam ≤ 1 := by have := hlam.2; linarith
    have hlow : lam₀ - δ ≤ lam := hlam.1
    have hlamne : ∃ w, flowD k lam w ≠ 0 :=
      hnear lam (by linarith) hlam.2.le (by linarith)
    have hzim : z.im = 0 := flowD_real_rooted k hlam8 hlam1 hlamne z hcon
    have hzre : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hzim]
    have hdist : |z.re - x₀| < R := by
      have hb := mem_ball.mp hzb
      rw [Complex.dist_eq] at hb
      calc |z.re - x₀| = |(z - ((x₀ : ℝ) : ℂ)).re| := by simp
        _ ≤ ‖z - ((x₀ : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
        _ < R := hb
    have hlamI : lam ∈ Ico (lam₀ - δ₁) lam₀ := ⟨by have := hlam.1; linarith, hlam.2⟩
    have hA : xiRD k lam₀ z.re < xiRD k lam z.re :=
      hanti z.re (le_of_lt (lt_of_lt_of_le hdist (min_le_left _ _))) lam hlamI
    have hB : 0 ≤ xiRD k lam₀ z.re :=
      hnn z.re (le_of_lt (lt_of_lt_of_le hdist (min_le_right _ _)))
    have hne' : xiRD k lam z.re ≠ 0 := by linarith
    exact hne' (by rw [xiRD_eq_zero_iff, ← hzre]; exact hcon)
  set lamSeq : ℕ → ℝ := fun n => lam₀ - δ / (n + 2) with hls
  have hseqI : ∀ n, lamSeq n ∈ Ico (lam₀ - δ) lam₀ := by
    intro n
    have hn : (0:ℝ) < (n : ℝ) + 2 := by positivity
    constructor
    · have : δ / ((n : ℝ) + 2) ≤ δ := by rw [div_le_iff₀ hn]; nlinarith [hδpos.le]
      simp only [hls]; linarith
    · have : 0 < δ / ((n : ℝ) + 2) := by positivity
      simp only [hls]; linarith
  obtain ⟨C, hC, hlip⟩ := flowD_lipschitz_lam k h1le h0.le (a := R) hRpos.le
  have hzim : ∀ z ∈ ball ((x₀ : ℝ) : ℂ) R, |z.im| ≤ R := by
    intro z hzb
    have hb := mem_ball.mp hzb
    rw [Complex.dist_eq] at hb
    calc |z.im| = |(z - ((x₀ : ℝ) : ℂ)).im| := by simp
      _ ≤ ‖z - ((x₀ : ℝ) : ℂ)‖ := Complex.abs_im_le_norm _
      _ ≤ R := hb.le
  have hunif : TendstoUniformlyOn (fun n => flowD k (lamSeq n)) (flowD k lam₀) atTop
      (ball ((x₀ : ℝ) : ℂ) R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2) * C) atTop (𝓝 0) := by
      have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      simpa using (Tendsto.const_div_atTop hden δ).mul_const C
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
    intro z hzb
    have hdd := hlip (lamSeq n) lam₀ (by have := (hseqI n).1; linarith) h0.le
      (le_of_lt (hseqI n).2) le_rfl z (hzim z hzb)
    have habs : |lamSeq n - lam₀| = δ / ((n : ℝ) + 2) := by
      simp only [hls]
      rw [show lam₀ - δ / ((n : ℝ) + 2) - lam₀ = -(δ / ((n : ℝ) + 2)) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
    rw [Complex.dist_eq, norm_sub_rev]
    calc ‖flowD k (lamSeq n) z - flowD k lam₀ z‖ ≤ |lamSeq n - lam₀| * C := hdd
      _ = δ / ((n : ℝ) + 2) * C := by rw [habs]
      _ < ε := hn
  have hconn : IsPreconnected (ball ((x₀ : ℝ) : ℂ) R) := (convex_ball _ _).isPreconnected
  have hdiffn : ∀ n, DifferentiableOn ℂ (flowD k (lamSeq n)) (ball ((x₀ : ℝ) : ℂ) R) := fun n =>
    (differentiable_flowD k (by have := (hseqI n).1; linarith)
      (by have := (hseqI n).2; linarith)).differentiableOn
  have hFne : ∀ n, ∀ z ∈ ball ((x₀ : ℝ) : ℂ) R, flowD k (lamSeq n) z ≠ 0 :=
    fun n z hzb => hnozero (lamSeq n) (hseqI n) z hzb
  have hfne : ∃ z ∈ ball ((x₀ : ℝ) : ℂ) R, flowD k lam₀ z ≠ 0 := by
    by_contra hall
    push_neg at hall
    obtain ⟨z₁, hz₁⟩ := hne
    apply hz₁
    have hA : AnalyticOnNhd ℂ (flowD k lam₀) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_flowD k h0.le h1le)
    have hev : flowD k lam₀ =ᶠ[𝓝 ((x₀ : ℝ) : ℂ)] 0 := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hRpos)] with w hw
      exact hall w hw
    exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ _) hev (Set.mem_univ z₁)
  exact (CriticalLinePhasor.Hurwitz.ne_zero_of_tendstoLocallyUniformlyOn isOpen_ball
    hconn hdiffn hFne hunif.tendstoLocallyUniformlyOn hfne) ((x₀ : ℝ) : ℂ)
    (mem_ball_self hRpos) hz

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.xiRD_lt_of_lam_lt
#print axioms CriticalLinePhasor.XiKernel.xiRD_nonneg_near
#print axioms CriticalLinePhasor.XiKernel.flowD_no_double_zero_pos
