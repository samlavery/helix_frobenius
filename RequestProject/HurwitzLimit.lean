import Mathlib

/-!
# A Hurwitz-type limit lemma (T2c, the strip-narrowing compile)

If holomorphic functions `F n` converge locally uniformly on an open connected set `U` to `f`, no `F n` has a
zero in `U`, and `f` is not identically zero on `U`, then `f` has no zero in `U`.  Proof: the maximum modulus
principle for `1/F n` on a small disc around a putative zero of `f`.

Corollary `im_eq_zero_of_tendstoLocallyUniformly`: a locally uniform limit on `ℂ` of entire functions with only
real zeros, not identically zero, has only real zeros.
-/

open Complex Filter Topology Metric Set

namespace CriticalLinePhasor.Hurwitz

/-- **Hurwitz, nonvanishing form.** -/
theorem ne_zero_of_tendstoLocallyUniformlyOn {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hFne : ∀ n, ∀ z ∈ U, F n z ≠ 0)
    (hlim : TendstoLocallyUniformlyOn F f atTop U)
    (hf : ∃ z ∈ U, f z ≠ 0) :
    ∀ z ∈ U, f z ≠ 0 := by
  intro z₀ hz₀ hf0
  have hfd : DifferentiableOn ℂ f U := hlim.differentiableOn (Eventually.of_forall hF) hU
  have hfa : AnalyticOnNhd ℂ f U := hfd.analyticOnNhd hU
  -- `f` is not eventually zero near `z₀`
  have hnot : ¬ (∀ᶠ z in 𝓝 z₀, f z = 0) := by
    intro hev
    obtain ⟨z₁, hz₁, hfz₁⟩ := hf
    exact hfz₁ (hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz₀ hev hz₁)
  have hne : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
    rcases (hfa z₀ hz₀).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact (hnot h).elim
    · exact h
  -- a radius with the closed disc inside `U` and `f ≠ 0` on the punctured disc
  obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  obtain ⟨r₂, hr₂, hpunct⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hne)
  set r : ℝ := min (r₁ / 2) (r₂ / 2) with hr_def
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hr1 : r < r₁ := (min_le_left _ _).trans_lt (by linarith)
  have hr2 : r < r₂ := (min_le_right _ _).trans_lt (by linarith)
  have hsub : closedBall z₀ r ⊆ U := fun z hz =>
    hball (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt hr1))
  have hsphere_ne : ∀ z ∈ sphere z₀ r, f z ≠ 0 := by
    intro z hz
    have hd : dist z z₀ = r := Metric.mem_sphere.mp hz
    have hzne : z ≠ z₀ := by
      intro h; rw [h, dist_self] at hd; exact hr.ne hd
    exact hpunct (by rw [hd]; exact hr2) (Set.mem_compl_singleton_iff.mpr hzne)
  -- the minimum of `‖f‖` on the sphere
  obtain ⟨w, hw, hwmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    ((hfd.continuousOn.mono (sphere_subset_closedBall.trans hsub)).norm)
  set m : ℝ := ‖f w‖ with hm_def
  have hm : 0 < m := norm_pos_iff.mpr (hsphere_ne w hw)
  -- uniform convergence on the closed disc
  have hunif : TendstoUniformlyOn F f atTop (closedBall z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim _ hsub (isCompact_closedBall _ _)
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hunif (m / 2) (by positivity)).exists
  -- on the sphere `‖F n‖ > m/2`, at the centre `‖F n z₀‖ < m/2`
  have hFsph : ∀ z ∈ sphere z₀ r, m / 2 < ‖F n z‖ := by
    intro z hz
    have h1 := hn z (sphere_subset_closedBall hz)
    have h2 : m ≤ ‖f z‖ := hwmin hz
    rw [dist_eq_norm] at h1
    have := norm_sub_norm_le (f z) (F n z)
    linarith
  have hFc : ‖F n z₀‖ < m / 2 := by
    have h1 := hn z₀ (Metric.mem_closedBall_self hr.le)
    rw [dist_eq_norm, hf0, zero_sub, norm_neg] at h1
    exact h1
  -- maximum modulus for `1/F n` on the disc
  have hFn_ne : ∀ z ∈ closedBall z₀ r, F n z ≠ 0 := fun z hz => hFne n z (hsub hz)
  have hinv : DifferentiableOn ℂ (fun z => (F n z)⁻¹) (closedBall z₀ r) :=
    ((hF n).mono hsub).inv hFn_ne
  have hdc : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (ball z₀ r) := by
    apply DifferentiableOn.diffContOnCl
    rwa [closure_ball z₀ hr.ne']
  have hbound : ∀ z ∈ frontier (ball z₀ r), ‖(F n z)⁻¹‖ ≤ 2 / m := by
    intro z hz
    rw [frontier_ball z₀ hr.ne'] at hz
    rw [norm_inv]
    have := hFsph z hz
    rw [inv_le_comm₀ (by linarith) (by positivity)]
    rw [inv_div]
    linarith
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hbound
    (z := z₀) (by rw [closure_ball z₀ hr.ne']; exact Metric.mem_closedBall_self hr.le)
  rw [norm_inv] at hmax
  have hFc0 : 0 < ‖F n z₀‖ := norm_pos_iff.mpr (hFn_ne z₀ (Metric.mem_closedBall_self hr.le))
  rw [inv_le_comm₀ hFc0 (by positivity), inv_div] at hmax
  linarith

/-- **Real zeros survive locally uniform limits.**  If every `F n` is entire with only real zeros, `F n → f`
locally uniformly on `ℂ`, and `f` is not identically zero, then `f` has only real zeros. -/
theorem im_eq_zero_of_tendstoLocallyUniformly {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n))
    (hFreal : ∀ n, ∀ z : ℂ, F n z = 0 → z.im = 0)
    (hlim : TendstoLocallyUniformly F f atTop)
    (hf : ∃ z, f z ≠ 0) :
    ∀ z : ℂ, f z = 0 → z.im = 0 := by
  intro z hz
  by_contra him
  have hfd : Differentiable ℂ f := by
    have := (hlim.tendstoLocallyUniformlyOn (s := univ)).differentiableOn
      (Eventually.of_forall fun n => (hF n).differentiableOn) isOpen_univ
    exact differentiableOn_univ.mp this
  have hfa : AnalyticOnNhd ℂ f univ := hfd.differentiableOn.analyticOnNhd isOpen_univ
  -- the open half-plane containing `z`
  have key : ∀ (U : Set ℂ), IsOpen U → IsPreconnected U → z ∈ U →
      (∀ n, ∀ w ∈ U, F n w ≠ 0) → False := by
    intro U hUo hUc hzU hFneU
    have hfU : ∃ w ∈ U, f w ≠ 0 := by
      by_contra hall
      push Not at hall
      obtain ⟨z₁, hz₁⟩ := hf
      apply hz₁
      have hev : f =ᶠ[𝓝 z] 0 := by
        filter_upwards [hUo.mem_nhds hzU] with w hw
        exact hall w hw
      exact hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) hev
        (mem_univ z₁)
    exact ne_zero_of_tendstoLocallyUniformlyOn hUo hUc (fun n => (hF n).differentiableOn) hFneU
      ((hlim.tendstoLocallyUniformlyOn (s := univ)).mono (subset_univ U)) hfU z hzU hz
  rcases lt_or_gt_of_ne him with hneg | hpos
  · exact key {w : ℂ | w.im < 0} (isOpen_lt Complex.continuous_im continuous_const)
      (convex_halfSpace_im_lt (r := 0)).isPreconnected hneg
      (fun n w hw h0 => by have := hFreal n w h0; simp only [Set.mem_ofPred_eq] at hw; linarith)
  · exact key {w : ℂ | 0 < w.im} (isOpen_lt continuous_const Complex.continuous_im)
      (convex_halfSpace_im_gt (r := 0)).isPreconnected hpos
      (fun n w hw h0 => by have := hFreal n w h0; simp only [Set.mem_ofPred_eq] at hw; linarith)

end CriticalLinePhasor.Hurwitz

#print axioms CriticalLinePhasor.Hurwitz.ne_zero_of_tendstoLocallyUniformlyOn
#print axioms CriticalLinePhasor.Hurwitz.im_eq_zero_of_tendstoLocallyUniformly
