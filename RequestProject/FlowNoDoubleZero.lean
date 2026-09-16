import RequestProject.FlowSectionConvex
import RequestProject.DeBruijnFlowFrontier

/-!
# The warped fiber has no double zero above the frontier

Assembly of the merger argument.  Suppose `Ξ_{λ₀}` has a zero of order exactly two at a real `x₀`,
with `1/8 < λ₀ < 1`.  Then:
* descending in `λ` strictly raises the section on a rectangle (`xiR_lt_of_lam_lt`);
* at `λ₀` the section is `≥ 0` near `x₀` (`xiR_nonneg_near`);
so `Ξ_λ > 0` on a real interval for every `λ` just below `λ₀`.  Those `Ξ_λ` are real-rooted
(`flowFrontier_one_eighth`), so they have no zero in the DISC either; the compiled Hurwitz
non-vanishing lemma then forces `Ξ_{λ₀} ≠ 0` on that disc — contradicting `Ξ_{λ₀}(x₀) = 0`.
-/

open Complex Filter Topology Set Metric

namespace CriticalLinePhasor.XiKernel

theorem flowStage_no_double_zero_pos {lam₀ : ℝ} (h8 : 1 / 8 < lam₀) (h1 : lam₀ < 1) {x₀ : ℝ}
    (hz : flowStage lam₀ (x₀ : ℂ) = 0)
    (hdz : deriv (flowStage lam₀) (x₀ : ℂ) = 0)
    (hc : 0 < (deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re) : False := by
  have h0 : 0 < lam₀ := by linarith
  have h1le : lam₀ ≤ 1 := h1.le
  obtain ⟨r, δ₁, hr, hδ₁, hδ₁l, hanti⟩ := xiR_lt_of_lam_lt h0 h1 hc
  have hval : xiR lam₀ x₀ = 0 := by rw [xiR_eq_zero_iff]; exact hz
  have hd : deriv (xiR lam₀) x₀ = 0 := by
    rw [deriv_xiR_eq h0.le h1le]; simp [hdz]
  obtain ⟨ρ, hρ, hnn⟩ := xiR_nonneg_near h0.le h1le hval hd hc
  set δ : ℝ := min δ₁ ((lam₀ - 1 / 8) / 2) with hδdef
  have hδpos : 0 < δ := lt_min hδ₁ (by linarith)
  have hδle : δ ≤ δ₁ := min_le_left _ _
  have hδ8 : 1 / 8 < lam₀ - δ := by
    have : δ ≤ (lam₀ - 1 / 8) / 2 := min_le_right _ _
    linarith
  set R : ℝ := min r ρ with hR
  have hRpos : 0 < R := lt_min hr hρ
  -- (1) for `λ` just below `λ₀`, no zero in the disc
  have hnozero : ∀ lam ∈ Ico (lam₀ - δ) lam₀, ∀ z ∈ ball ((x₀ : ℝ) : ℂ) R,
      flowStage lam z ≠ 0 := by
    intro lam hlam z hzb hcon
    have hlam8 : 1 / 8 ≤ lam := by have := hlam.1; linarith
    have hlam1 : lam ≤ 1 := by have := hlam.2; linarith
    have hzim : z.im = 0 := flowFrontier_one_eighth lam hlam8 hlam1 z hcon
    have hzre : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hzim]
    have hdist : |z.re - x₀| < R := by
      have := mem_ball.mp hzb
      rw [Complex.dist_eq] at this
      calc |z.re - x₀| = |(z - ((x₀ : ℝ) : ℂ)).re| := by simp
        _ ≤ ‖z - ((x₀ : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
        _ < R := this
    have hlamI : lam ∈ Ico (lam₀ - δ₁) lam₀ := ⟨by have := hlam.1; linarith, hlam.2⟩
    have h1' : xiR lam₀ z.re < xiR lam z.re :=
      hanti z.re (le_of_lt (lt_of_lt_of_le hdist (min_le_left _ _))) lam hlamI
    have h2' : 0 ≤ xiR lam₀ z.re :=
      hnn z.re (le_of_lt (lt_of_lt_of_le hdist (min_le_right _ _)))
    have : xiR lam z.re ≠ 0 := by linarith
    exact this (by rw [xiR_eq_zero_iff, ← hzre]; exact hcon)
  -- (2) the approximating sequence
  set lamSeq : ℕ → ℝ := fun n => lam₀ - δ / (n + 2) with hls
  have hseqI : ∀ n, lamSeq n ∈ Ico (lam₀ - δ) lam₀ := by
    intro n
    have hn : (0:ℝ) < (n : ℝ) + 2 := by positivity
    constructor
    · have : δ / ((n : ℝ) + 2) ≤ δ := by
        rw [div_le_iff₀ hn]; nlinarith [hδpos.le]
      simp only [hls]; linarith
    · have : 0 < δ / ((n : ℝ) + 2) := by positivity
      simp only [hls]; linarith
  -- (3) uniform convergence on the ball
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
  -- (4) Hurwitz on the disc
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

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.flowStage_no_double_zero_pos
