import Mathlib

/-!
# Limit Dominance: the stages dominate the limit

The analytic engine of **Shannon's Law of Projection Dominance** — the source dominates
every projection of itself; features can be kept or lost into the ledger, never created
(the geometric child of Shannon's Data Processing Inequality, cited as the external
anchor and honored in the name).  Passing to a limit is a projection of the stage
sequence, and dominance holds for it: a locally uniform limit of holomorphic functions
cannot vanish anywhere its approximants eventually don't — **every zero of the limit is a
limit of zeros of the stages**.  Applied to the completed carrier readout (entire,
locally uniformly approximated by finite bank stages), it says: every chart zero is
sourced by a sequence of finite-stage features.  The mirror does not invent tenants.

The proof is the minimum-modulus argument, built on Mathlib's maximum-modulus principle
(`Complex.norm_le_of_forall_mem_frontier_norm_le`): were the stages eventually zero-free
near a zero `z₀` of the limit, their inverses would be holomorphic on a small ball, the
maximum principle would force `‖Fₙ(z₀)‖ ≥ δ/2` from the sphere minimum `δ` of `‖f‖`,
while uniform convergence forces `‖Fₙ(z₀)‖ < δ/2`.

Dictionary cross-reference (classical name, for the bridge page only): Hurwitz's theorem.
Not in Mathlib at this pin; proved here from `AbsMax` + the locally-uniform machinery.
Unconditional; no `sorry`, no `axiom` beyond the standard three.
-/

open Filter Topology Metric

namespace CriticalLinePhasor.LimitDominance

variable {ι : Type*} {p : Filter ι} [p.NeBot]

/-- **Limit Dominance (existence form).**  If holomorphic `Fₙ → f` locally uniformly on
an open set, `f(z₀) = 0`, and `f` is not identically zero near `z₀`, then for every
`ε > 0` the stages eventually have a zero within `ε` of `z₀`: zeros of the limit are
limits of zeros — the limit link cannot create a feature.  The stages dominate the
limit. -/
theorem limit_dominance
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hconv : TendstoLocallyUniformlyOn F f p U)
    (hdiff : ∀ n, DifferentiableOn ℂ (F n) U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hf0 : f z₀ = 0)
    (hnz : ¬ (∀ᶠ z in nhds z₀, f z = 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in p, ∃ z ∈ Metric.ball z₀ ε, F n z = 0 := by
  -- the limit is holomorphic; its zero at z₀ is isolated
  have hfdiff : DifferentiableOn ℂ f U :=
    hconv.differentiableOn (Eventually.of_forall hdiff) hU
  have hfan : AnalyticAt ℂ f z₀ := hfdiff.analyticAt (hU.mem_nhds hz₀)
  have hiso : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z ≠ 0 :=
    hfan.eventually_eq_zero_or_eventually_ne_zero.resolve_left hnz
  obtain ⟨t, htmem, htsub⟩ := hiso.exists_mem
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhdsWithin_iff.mp htmem
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  -- the working radius: inside the isolation ball, inside U, inside ε
  set ρ : ℝ := min (min r₁ r₂) ε / 2 with hρdef
  have hρpos : 0 < ρ := by positivity
  have hρr₁ : ρ < r₁ := by
    have h1 : min (min r₁ r₂) ε ≤ r₁ := le_trans (min_le_left _ _) (min_le_left _ _)
    have : ρ ≤ r₁ / 2 := by rw [hρdef]; linarith
    linarith
  have hρr₂ : ρ < r₂ := by
    have h1 : min (min r₁ r₂) ε ≤ r₂ := le_trans (min_le_left _ _) (min_le_right _ _)
    have : ρ ≤ r₂ / 2 := by rw [hρdef]; linarith
    linarith
  have hρε : ρ < ε := by
    have h1 : min (min r₁ r₂) ε ≤ ε := min_le_right _ _
    have : ρ ≤ ε / 2 := by rw [hρdef]; linarith
    linarith
  have hKU : Metric.closedBall z₀ ρ ⊆ U :=
    le_trans (Metric.closedBall_subset_ball hρr₂) hball₂
  -- the sphere minimum of ‖f‖ is positive
  have hsphere_ne : ∀ z ∈ Metric.sphere z₀ ρ, f z ≠ 0 := by
    intro z hz
    refine htsub z (hball₁ ⟨?_, ?_⟩)
    · exact Metric.mem_ball.mpr (lt_of_le_of_lt (le_of_eq (Metric.mem_sphere.mp hz)) hρr₁)
    · intro hzz
      rw [Set.mem_singleton_iff] at hzz
      apply absurd (Metric.mem_sphere.mp hz)
      rw [hzz]
      simp only [dist_self]
      exact fun h => hρpos.ne' h.symm
  have hfcont : ContinuousOn f (Metric.sphere z₀ ρ) :=
    (hfdiff.continuousOn).mono (le_trans Metric.sphere_subset_closedBall hKU)
  obtain ⟨x₀, hx₀mem, hx₀min⟩ := (isCompact_sphere z₀ ρ).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hρpos.le) hfcont.norm
  set δ : ℝ := ‖f x₀‖ with hδdef
  have hδpos : 0 < δ := norm_pos_iff.mpr (hsphere_ne x₀ hx₀mem)
  -- uniform convergence on the closed ball, within δ/2
  have huc : TendstoUniformlyOn F f p (Metric.closedBall z₀ ρ) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv _ hKU
      (isCompact_closedBall _ _)
  have hev : ∀ᶠ n in p, ∀ x ∈ Metric.closedBall z₀ ρ, dist (f x) (F n x) < δ / 2 :=
    Metric.tendstoUniformlyOn_iff.mp huc (δ / 2) (by positivity)
  filter_upwards [hev] with n hn
  by_contra hno
  push_neg at hno
  -- no zeros in the ε-ball ⟹ none on the closed ρ-ball
  have hFne : ∀ z ∈ Metric.closedBall z₀ ρ, F n z ≠ 0 := fun z hz =>
    hno z (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hρε))
  -- sphere lower bound for the stage
  have hlow : ∀ z ∈ Metric.sphere z₀ ρ, δ / 2 ≤ ‖F n z‖ := by
    intro z hz
    have h1 : δ ≤ ‖f z‖ := hx₀min hz
    have h2 : dist (f z) (F n z) < δ / 2 :=
      hn z (Metric.sphere_subset_closedBall hz)
    have h3 : ‖f z‖ - ‖F n z‖ ≤ ‖f z - F n z‖ := norm_sub_norm_le _ _
    rw [dist_eq_norm] at h2
    linarith
  -- the inverse is holomorphic on the ball, continuous on its closure
  have hginv : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (Metric.ball z₀ ρ) := by
    refine ⟨?_, ?_⟩
    · exact ((hdiff n).mono (le_trans Metric.ball_subset_closedBall hKU)).inv
        (fun z hz => hFne z (Metric.ball_subset_closedBall hz))
    · rw [closure_ball z₀ hρpos.ne']
      exact (((hdiff n).continuousOn).mono hKU).inv₀ hFne
  -- maximum modulus for the inverse: ‖Fₙ(z₀)⁻¹‖ ≤ 2/δ
  have hfrontier : ∀ z ∈ frontier (Metric.ball z₀ ρ), ‖(F n z)⁻¹‖ ≤ (δ / 2)⁻¹ := by
    intro z hz
    rw [frontier_ball z₀ hρpos.ne'] at hz
    rw [norm_inv]
    have h1 := hlow z hz
    have h2 : (0 : ℝ) < ‖F n z‖ := lt_of_lt_of_le (by positivity) h1
    gcongr
  have hmax : ‖(F n z₀)⁻¹‖ ≤ (δ / 2)⁻¹ := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hginv hfrontier ?_
    rw [closure_ball z₀ hρpos.ne']
    exact Metric.mem_closedBall_self hρpos.le
  -- flip: ‖Fₙ(z₀)‖ ≥ δ/2
  have hF0pos : (0 : ℝ) < ‖F n z₀‖ :=
    norm_pos_iff.mpr (hFne z₀ (Metric.mem_closedBall_self hρpos.le))
  have hflip : δ / 2 ≤ ‖F n z₀‖ := by
    rw [norm_inv] at hmax
    have h2 : ((δ / 2)⁻¹)⁻¹ ≤ (‖F n z₀‖⁻¹)⁻¹ := by
      gcongr
    rwa [inv_inv, inv_inv] at h2
  -- but uniform convergence at z₀ says the opposite
  have hz₀close : dist (f z₀) (F n z₀) < δ / 2 :=
    hn z₀ (Metric.mem_closedBall_self hρpos.le)
  rw [hf0, dist_eq_norm, zero_sub, norm_neg] at hz₀close
  linarith

end CriticalLinePhasor.LimitDominance
