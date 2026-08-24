import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# R-campaign, brick R4 (Landau's lemma): the log-derivative partial fraction

The exponent-1 zero-free region needs the classical Landau lemma: for `f`
analytic and bounded on a disk with `f(c) ≠ 0`, the logarithmic derivative
equals the sum of `m_ρ/(s-ρ)` over nearby zeros up to an error `≲ log(M/|f(c)|)`.
No Lean corpus (mathlib, PNT+, zeta-23) contains it; this file constructs it
from mathlib's `extract_zeros_poles`, Borel–Carathéodory, disk primitives,
and the maximum principle.

Brick sequence:
* L0 `eqOn_of_codiscreteWithin` — codiscrete a.e.-equality of continuous
  functions upgrades to pointwise equality on an open set.
* L1 `extract_analytic_pointwise` — the zero factorization `f = P·g` with
  `g` analytic nonvanishing, POINTWISE on the open ball.
-/

open Complex Metric Set

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **L0: the codiscrete upgrade.**  Two functions continuous on an open set
and equal codiscretely within it are equal everywhere on it.  (The
complement of a codiscrete set has no accumulation point inside `U`, so
every point of `U` is a limit of agreement points; continuity finishes.) -/
theorem eqOn_of_codiscreteWithin {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hfg : f =ᶠ[Filter.codiscreteWithin U] g)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) :
    Set.EqOn f g U := by
  intro x hx
  have hS : {y | f y = g y} ∪ Uᶜ ∈ nhdsWithin x {x}ᶜ :=
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfg) x hx
  have hUx : U ∈ nhdsWithin x {x}ᶜ :=
    nhdsWithin_le_nhds (hU.mem_nhds hx)
  have hSU : {y | f y = g y} ∈ nhdsWithin x {x}ᶜ := by
    filter_upwards [hS, hUx] with y hy hyU
    rcases hy with h | h
    · exact h
    · exact absurd hyU h
  have hfx : Filter.Tendsto f (nhdsWithin x {x}ᶜ) (nhds (f x)) :=
    ((hf x hx).continuousAt (hU.mem_nhds hx)).continuousWithinAt.tendsto
  have hgx : Filter.Tendsto g (nhdsWithin x {x}ᶜ) (nhds (g x)) :=
    ((hg x hx).continuousAt (hU.mem_nhds hx)).continuousWithinAt.tendsto
  have hfx' : Filter.Tendsto f (nhdsWithin x {x}ᶜ) (nhds (g x)) := by
    apply hgx.congr'
    filter_upwards [hSU] with y hy
    exact hy.symm
  exact tendsto_nhds_unique hfx hfx'

/-- Analytic order is finite everywhere on a preconnected region once the
function is nonzero somewhere on it. -/
theorem analyticOrderAt_ne_top_of_ne_zero {W : Set ℂ} (hW : IsPreconnected W)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f W) {c : ℂ} (hc : c ∈ W)
    (hne : f c ≠ 0) {u : ℂ} (hu : u ∈ W) :
    analyticOrderAt f u ≠ ⊤ := by
  intro htop
  have hzero : f =ᶠ[nhds u] 0 := by
    have h := analyticOrderAt_eq_top.mp htop
    filter_upwards [h] with z hz
    exact hz
  have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hW hu hzero hc
  exact hne this

/-- **L1: pointwise zero extraction.**  For `f` analytic on a closed ball
with `f(c) ≠ 0`, there is an analytic nonvanishing `g` on the closed ball
with `f = P·g` POINTWISE on the open ball, `P` the factorized rational
function of the divisor.  (Mathlib's `extract_zeros_poles` gives the
identity only codiscretely; L0 upgrades it.) -/
theorem extract_analytic_pointwise {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hne : f c ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧
      (∀ u ∈ closedBall c R, g u ≠ 0) ∧
      ∀ z ∈ ball c R,
        f z = (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f (closedBall c R) u)) z
          * g z := by
  have hCBpre : IsPreconnected (closedBall c R) :=
    (convex_closedBall c R).isPreconnected
  have hcmem : c ∈ closedBall c R := mem_closedBall_self hR.le
  have hordtop : ∀ u : closedBall c R, meromorphicOrderAt f u ≠ ⊤ := by
    intro ⟨u, hu⟩
    have hanal : AnalyticAt ℂ f u := hf u hu
    rw [hanal.meromorphicOrderAt_eq]
    intro htop
    exact analyticOrderAt_ne_top_of_ne_zero hCBpre hf hcmem hne hu
      (ENat.map_eq_top_iff.mp htop)
  have hsupp : (MeromorphicOn.divisor f (closedBall c R)).support.Finite :=
    (MeromorphicOn.divisor f (closedBall c R)).finiteSupport
      (isCompact_closedBall c R)
  obtain ⟨g, hg_anal, hg_ne, hfg⟩ :=
    hf.meromorphicOn.extract_zeros_poles hordtop hsupp
  refine ⟨g, hg_anal, fun u hu => hg_ne ⟨u, hu⟩, ?_⟩
  have hd_nonneg : ∀ x : ℂ,
      0 ≤ MeromorphicOn.divisor f (closedBall c R) x := by
    intro x
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf x
  have hP_cont : ContinuousOn
      (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f (closedBall c R) u))
      (ball c R) := by
    intro x _
    exact (Function.FactorizedRational.analyticAt
      (hd_nonneg x)).continuousAt.continuousWithinAt
  have hRHS_cont : ContinuousOn
      ((∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f (closedBall c R) u)) • g)
      (ball c R) := by
    apply ContinuousOn.smul hP_cont
    exact (hg_anal.mono ball_subset_closedBall).continuousOn
  have hf_cont : ContinuousOn f (ball c R) :=
    (hf.mono ball_subset_closedBall).continuousOn
  have hfg_ball : f =ᶠ[Filter.codiscreteWithin (ball c R)]
      (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f (closedBall c R) u)) • g :=
    hfg.filter_mono (Filter.codiscreteWithin.mono ball_subset_closedBall)
  have heq := eqOn_of_codiscreteWithin isOpen_ball hfg_ball hf_cont hRHS_cont
  intro z hz
  have := heq hz
  simpa using this

/-- **L2a: extraction in Finset form, on the closed ball.**  The factorized
rational function becomes a genuine polynomial product `∏_{u ∈ S} (z-u)^{n u}`
with natural exponents, and the identity `f = P·g` extends to the closed
ball by continuity (`closure_ball`). -/
theorem extract_analytic_finset {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hne : f c ≠ 0) :
    ∃ (g : ℂ → ℂ) (S : Finset ℂ) (n : ℂ → ℕ),
      AnalyticOnNhd ℂ g (closedBall c R) ∧
      (∀ u ∈ closedBall c R, g u ≠ 0) ∧
      (∀ u ∈ S, u ∈ closedBall c R) ∧
      (∀ u ∈ S, (n u : ℤ) = MeromorphicOn.divisor f (closedBall c R) u) ∧
      (∀ u, u ∉ S → MeromorphicOn.divisor f (closedBall c R) u = 0) ∧
      ∀ z ∈ closedBall c R,
        f z = (∏ u ∈ S, (z - u) ^ (n u)) * g z := by
  obtain ⟨g, hg_anal, hg_ne, hfg⟩ := extract_analytic_pointwise hR hf hne
  have hsupp : (MeromorphicOn.divisor f (closedBall c R)).support.Finite :=
    (MeromorphicOn.divisor f (closedBall c R)).finiteSupport
      (isCompact_closedBall c R)
  have hd_nonneg : ∀ x : ℂ,
      0 ≤ MeromorphicOn.divisor f (closedBall c R) x := fun x =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf x
  refine ⟨g, hsupp.toFinset,
    fun u => (MeromorphicOn.divisor f (closedBall c R) u).toNat,
    hg_anal, hg_ne, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have : u ∈ (MeromorphicOn.divisor f (closedBall c R)).support :=
      hsupp.mem_toFinset.mp hu
    exact (MeromorphicOn.divisor f (closedBall c R)).supportWithinDomain this
  · intro u _
    exact Int.toNat_of_nonneg (hd_nonneg u)
  · intro u hu
    by_contra hne'
    exact hu (hsupp.mem_toFinset.mpr hne')
  -- refine_4: the identity on the closed ball, by continuity from the open ball
  have hprod_eq : ∀ z : ℂ,
      (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f (closedBall c R) u)) z
        = ∏ u ∈ hsupp.toFinset,
            (z - u) ^ (MeromorphicOn.divisor f (closedBall c R) u).toNat := by
    intro z
    have h1 : (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f (closedBall c R) u)) z
        = ∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor f (closedBall c R) u) := by
      rw [finprod_eq_prod_of_mulSupport_subset
          (s := hsupp.toFinset) _ (by
            rw [Function.FactorizedRational.mulSupport]
            intro u hu
            exact hsupp.mem_toFinset.mpr hu),
        finprod_eq_prod_of_mulSupport_subset
          (s := hsupp.toFinset) _ (by
            intro u hu
            apply hsupp.mem_toFinset.mpr
            intro h0
            apply hu
            simp [h0]),
        Finset.prod_apply]
      simp
    rw [h1]
    rw [finprod_eq_prod_of_mulSupport_subset
        (s := hsupp.toFinset) _ (by
          intro u hu
          apply hsupp.mem_toFinset.mpr
          intro h0
          apply hu
          simp [h0])]
    apply Finset.prod_congr rfl
    intro u _
    rw [← zpow_natCast, Int.toNat_of_nonneg (hd_nonneg u)]
  have heq_ball : ∀ z ∈ ball c R,
      f z = (∏ u ∈ hsupp.toFinset,
        (z - u) ^ (MeromorphicOn.divisor f (closedBall c R) u).toNat) * g z := by
    intro z hz
    rw [← hprod_eq z]
    exact hfg z hz
  -- extend to the closed ball by continuity
  have hcont_f : ContinuousOn f (closedBall c R) := hf.continuousOn
  have hcont_rhs : ContinuousOn (fun z =>
      (∏ u ∈ hsupp.toFinset,
        (z - u) ^ (MeromorphicOn.divisor f (closedBall c R) u).toNat) * g z)
      (closedBall c R) := by
    apply ContinuousOn.mul _ hg_anal.continuousOn
    apply Continuous.continuousOn
    apply continuous_finset_prod
    intro u _
    exact (continuous_id.sub continuous_const).pow _
  have hEq : Set.EqOn f (fun z =>
      (∏ u ∈ hsupp.toFinset,
        (z - u) ^ (MeromorphicOn.divisor f (closedBall c R) u).toNat) * g z)
      (closedBall c R) := by
    apply Set.EqOn.of_subset_closure (s := ball c R)
      (fun z hz => heq_ball z hz) hcont_f hcont_rhs
    · exact ball_subset_closedBall
    · rw [closure_ball c hR.ne']
  intro z hz
  exact hEq hz

/-- **L2b: the Blaschke sphere identity.**  On the sphere `‖z-c‖ = r`, the
reflected numerator has norm exactly `r·‖z-u‖`. -/
theorem blaschke_sphere_identity {c u z : ℂ} {r : ℝ} (hz : ‖z - c‖ = r) :
    ‖((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)‖ = r * ‖z - u‖ := by
  have key : ((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)
      = (z - c) * (starRingEnd ℂ) (z - u) := by
    have hww : (z - c) * (starRingEnd ℂ) (z - c) = ((r:ℂ))^2 := by
      rw [Complex.mul_conj', hz]
    calc ((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)
        = (z - c) * (starRingEnd ℂ) (z - c)
          - (starRingEnd ℂ) (u - c) * (z - c) := by rw [hww]
      _ = (z - c) * (starRingEnd ℂ) (z - u) := by
          simp only [map_sub]
          ring
  rw [key, norm_mul, RCLike.norm_conj, hz]

/-- **L2c: the Blaschke-reflected function.**  For `f` analytic on
`closedBall c r` with `f(c) ≠ 0`, there are `g, S, n` (the extraction data)
and `G := g·∏(Bnum_u/r)^{n_u}` with `Bnum_u(z) := r² - conj(u-c)(z-c)`,
satisfying: `G` analytic on the closed ball, nonvanishing on the OPEN ball,
`‖G‖ = ‖f‖` on the sphere, and `‖f(c)‖ ≤ ‖G(c)‖`. -/
theorem blaschke_package {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hne : f c ≠ 0) :
    ∃ (g G : ℂ → ℂ) (S : Finset ℂ) (n : ℂ → ℕ),
      AnalyticOnNhd ℂ g (closedBall c r) ∧
      (∀ u ∈ closedBall c r, g u ≠ 0) ∧
      (∀ u ∈ S, u ∈ closedBall c r) ∧
      (∀ u ∈ S, (n u : ℤ) = MeromorphicOn.divisor f (closedBall c r) u) ∧
      (∀ u, u ∉ S → MeromorphicOn.divisor f (closedBall c r) u = 0) ∧
      (∀ z ∈ closedBall c r, f z = (∏ u ∈ S, (z - u) ^ (n u)) * g z) ∧
      G = (fun z => g z * ∏ u ∈ S,
        ((((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)) / (r:ℂ)) ^ (n u)) ∧
      AnalyticOnNhd ℂ G (closedBall c r) ∧
      (∀ z ∈ ball c r, G z ≠ 0) ∧
      (∀ z, ‖z - c‖ = r → ‖G z‖ = ‖f z‖) ∧
      ‖f c‖ ≤ ‖G c‖ := by
  obtain ⟨g, S, n, hg_anal, hg_ne, hS_mem, hn_eq, hd_zero, hfact⟩ :=
    extract_analytic_finset hr hf hne
  set G : ℂ → ℂ := fun z => g z * ∏ u ∈ S,
    ((((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)) / (r:ℂ)) ^ (n u)
    with hGdef
  have hrC : ((r:ℂ)) ≠ 0 := by
    exact_mod_cast hr.ne'
  refine ⟨g, G, S, n, hg_anal, hg_ne, hS_mem, hn_eq, hd_zero, hfact,
    hGdef, ?_, ?_, ?_, ?_⟩
  · -- G analytic on the closed ball
    intro z hz
    apply AnalyticAt.mul (hg_anal z hz)
    apply Finset.analyticAt_fun_prod
    intro u _
    apply AnalyticAt.pow
    apply AnalyticAt.div
    · apply AnalyticAt.sub analyticAt_const
      exact (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))
    · exact analyticAt_const
    · exact hrC
  · -- G nonvanishing on the open ball
    intro z hz
    rw [hGdef]
    apply mul_ne_zero (hg_ne z (ball_subset_closedBall hz))
    rw [Finset.prod_ne_zero_iff]
    intro u hu
    apply pow_ne_zero
    apply div_ne_zero _ hrC
    intro h0
    have hzc : ‖z - c‖ < r := by
      rw [← dist_eq_norm]
      exact mem_ball.mp hz
    have huc : ‖u - c‖ ≤ r := by
      rw [← dist_eq_norm]
      exact mem_closedBall.mp (hS_mem u hu)
    have heq : ((r:ℂ))^2 = (starRingEnd ℂ) (u - c) * (z - c) := by
      linear_combination h0
    have := congrArg norm heq
    rw [norm_mul, RCLike.norm_conj] at this
    have hr2 : ‖((r:ℂ))^2‖ = r^2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    rw [hr2] at this
    nlinarith [norm_nonneg (u - c), norm_nonneg (z - c)]
  · -- ‖G‖ = ‖f‖ on the sphere
    intro z hz
    rw [hGdef]
    simp only [norm_mul, norm_prod, norm_pow, norm_div]
    have hstep : ∀ u ∈ S,
        (‖((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)‖ / ‖((r:ℂ))‖) ^ (n u)
          = ‖z - u‖ ^ (n u) := by
      intro u _
      rw [blaschke_sphere_identity hz, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, mul_div_cancel_left₀ _ hr.ne']
    rw [Finset.prod_congr rfl hstep]
    have hzmem : z ∈ closedBall c r := by
      rw [mem_closedBall, dist_eq_norm, hz]
    rw [hfact z hzmem, norm_mul, norm_prod]
    simp only [norm_pow]
    ring
  · -- center lower bound
    have hGc : ‖G c‖ = ‖g c‖ * ∏ u ∈ S, r ^ (n u) := by
      rw [hGdef]
      simp only [sub_self, mul_zero, sub_zero]
      rw [norm_mul, norm_prod]
      congr 1
      apply Finset.prod_congr rfl
      intro u _
      rw [norm_pow, norm_div, norm_pow]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      congr 1
      rw [sq, mul_div_cancel_left₀ _ hr.ne']
    have hfc : ‖f c‖ = (∏ u ∈ S, ‖c - u‖ ^ (n u)) * ‖g c‖ := by
      rw [hfact c (mem_closedBall_self hr.le), norm_mul, norm_prod]
      simp only [norm_pow]
    rw [hfc, hGc, mul_comm (‖g c‖)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Finset.prod_le_prod
    · intro u _
      positivity
    · intro u hu
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_sub_rev, ← dist_eq_norm]
      exact mem_closedBall.mp (hS_mem u hu)

/-- **L3: max modulus for the reflected function.**  `‖G‖ = ‖f‖ ≤ M` on the
sphere propagates to the whole closed ball. -/
theorem blaschke_max_modulus {c : ℂ} {r M : ℝ} (hr : 0 < r) {f G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (closedBall c r))
    (hsphere : ∀ z, ‖z - c‖ = r → ‖G z‖ = ‖f z‖)
    (hM : ∀ z ∈ closedBall c r, ‖f z‖ ≤ M) :
    ∀ z ∈ closedBall c r, ‖G z‖ ≤ M := by
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball (x := c) (r := r)) ?_ ?_
    (by rw [closure_ball c hr.ne']; exact hz)
  · exact ⟨(hG.mono ball_subset_closedBall).differentiableOn, by
      rw [closure_ball c hr.ne']
      exact hG.continuousOn⟩
  · intro w hw
    rw [frontier_ball c hr.ne'] at hw
    have hwc : ‖w - c‖ = r := mem_sphere_iff_norm.mp hw
    rw [hsphere w hwc]
    apply hM
    rw [mem_closedBall, dist_eq_norm, hwc]

/-- **L4: the logarithm via a primitive.**  For `G` analytic on the closed
ball, nonvanishing on the open ball, bounded by `M`, with `m ≤ ‖G c‖`:
there is `h` with `h' = G'/G`, `h(c) = 0`, `G = G(c)·exp h`, and
`Re h ≤ log(M/m)` on the open ball. -/
theorem blaschke_log_re_bound {c : ℂ} {r M m : ℝ} (hr : 0 < r) (hm : 0 < m)
    {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (closedBall c r))
    (hG_ne : ∀ z ∈ ball c r, G z ≠ 0)
    (hGM : ∀ z ∈ closedBall c r, ‖G z‖ ≤ M)
    (hGc : m ≤ ‖G c‖) :
    ∃ h : ℂ → ℂ, (∀ z ∈ ball c r, HasDerivAt h (logDeriv G z) z) ∧
      h c = 0 ∧
      (∀ z ∈ ball c r, G z = G c * Complex.exp (h z)) ∧
      (∀ z ∈ ball c r, (h z).re ≤ Real.log (M / m)) := by
  have hld_anal : ∀ z ∈ ball c r, AnalyticAt ℂ (logDeriv G) z := by
    intro z hz
    have hGz : AnalyticAt ℂ G z := hG z (ball_subset_closedBall hz)
    have : AnalyticAt ℂ (fun w => deriv G w / G w) z :=
      hGz.deriv.div hGz (hG_ne z hz)
    apply this.congr
    filter_upwards with w
    rfl
  -- primitive with value 0 at c
  have hexact : IsExactOn (logDeriv G) (ball c r) := by
    apply IsConservativeOn.isExactOn_ball
    · exact fun z hz => (hld_anal z hz).continuousAt.continuousWithinAt
    · apply DifferentiableOn.isConservativeOn
      exact fun z hz => (hld_anal z hz).differentiableAt.differentiableWithinAt
  obtain ⟨h, hc0, hderiv⟩ := hexact.with_val_at c 0
  -- G = G(c)·exp(h) via the vanishing derivative of G·exp(-h)
  have hrep : ∀ z ∈ ball c r, G z = G c * Complex.exp (h z) := by
    have hkey : ∀ z ∈ ball c r, G z * Complex.exp (-h z)
        = G c * Complex.exp (-h c) := by
      intro z hz
      set F : ℂ → ℂ := fun w => G w * Complex.exp (-h w) with hFdef
      have hF' : ∀ w ∈ ball c r, HasDerivAt F 0 w := by
        intro w hw
        have hGw : HasDerivAt G (deriv G w) w :=
          ((hG w (ball_subset_closedBall hw)).differentiableAt).hasDerivAt
        have hhw : HasDerivAt h (logDeriv G w) w := hderiv w hw
        have hexpw : HasDerivAt (fun v => Complex.exp (-h v))
            (Complex.exp (-h w) * (-(logDeriv G w))) w := by
          have := (hhw.neg).cexp
          simpa using this
        have := hGw.mul hexpw
        have hzero : deriv G w * Complex.exp (-h w)
            + G w * (Complex.exp (-h w) * (-(logDeriv G w))) = 0 := by
          rw [logDeriv_apply]
          field_simp [hG_ne w hw]
          ring
        rwa [hzero] at this
      have hFdiff : DifferentiableOn ℂ F (ball c r) :=
        fun w hw => ((hF' w hw).differentiableAt).differentiableWithinAt
      have hFconst := (convex_ball c r).is_const_of_fderivWithin_eq_zero
        hFdiff ?_ hz (mem_ball_self hr)
      · exact hFconst
      · intro w hw
        rw [fderivWithin_of_isOpen isOpen_ball hw]
        have h0 : HasFDerivAt F (0 : ℂ →L[ℂ] ℂ) w := by
          have hf1 := (hF' w hw).hasFDerivAt
          rwa [show ContinuousLinearMap.toSpanSingleton ℂ (0:ℂ)
              = (0 : ℂ →L[ℂ] ℂ) by
            ext v
            simp] at hf1
        exact h0.fderiv
    intro z hz
    have := hkey z hz
    rw [hc0] at this
    simp only [neg_zero, Complex.exp_zero, mul_one] at this
    calc G z = G z * Complex.exp (-h z) * Complex.exp (h z) := by
          rw [mul_assoc, ← Complex.exp_add]
          simp
      _ = G c * Complex.exp (h z) := by rw [this]
  refine ⟨h, hderiv, hc0, hrep, ?_⟩
  -- the real-part bound: exp(Re h) = ‖G z‖/‖G c‖ ≤ M/m
  intro z hz
  have hGcpos : (0:ℝ) < ‖G c‖ := lt_of_lt_of_le hm hGc
  have hnorm : ‖G z‖ = ‖G c‖ * Real.exp ((h z).re) := by
    rw [hrep z hz, norm_mul, Complex.norm_exp]
  have hexp_le : Real.exp ((h z).re) ≤ M / m := by
    have h1 : ‖G c‖ * Real.exp ((h z).re) ≤ M :=
      hnorm ▸ hGM z (ball_subset_closedBall hz)
    have h2 : m * Real.exp ((h z).re) ≤ M := by
      calc m * Real.exp ((h z).re)
          ≤ ‖G c‖ * Real.exp ((h z).re) := by
            apply mul_le_mul_of_nonneg_right hGc (Real.exp_pos _).le
        _ ≤ M := h1
    rw [le_div_iff₀ hm]
    linarith [h2]
  calc (h z).re = Real.log (Real.exp ((h z).re)) := (Real.log_exp _).symm
    _ ≤ Real.log (M / m) := by
        apply Real.log_le_log (Real.exp_pos _) hexp_le

/-- **L5: Borel–Carathéodory for the primitive.**  `h(c) = 0` and
`Re h ≤ log(M/m)` give `‖h z‖ ≤ 2·log(M/m)·‖z-c‖/(r-‖z-c‖)` on the ball. -/
theorem blaschke_h_norm_bound {c : ℂ} {r M m : ℝ} (hr : 0 < r)
    {G h : ℂ → ℂ}
    (hderiv : ∀ z ∈ ball c r, HasDerivAt h (logDeriv G z) z)
    (hc0 : h c = 0)
    (hre : ∀ z ∈ ball c r, (h z).re ≤ Real.log (M / m))
    (hlog : 0 < Real.log (M / m)) :
    ∀ z ∈ ball c r,
      ‖h z‖ ≤ 2 * Real.log (M / m) * ‖z - c‖ / (r - ‖z - c‖) := by
  intro z hz
  have hshift : ∀ w ∈ ball (0:ℂ) r, HasDerivAt (fun v => h (c + v))
      (logDeriv G (c + w)) w := by
    intro w hw
    have hcw : c + w ∈ ball c r := by
      rw [mem_ball]
      simpa [dist_eq_norm] using mem_ball_zero_iff.mp hw
    have hinner : HasDerivAt (fun v : ℂ => c + v) 1 w := by
      simpa using (hasDerivAt_id w).const_add c
    have h2 := (hderiv (c + w) hcw).comp w hinner
    rw [mul_one] at h2
    exact h2.congr_of_eventuallyEq (by filter_upwards with v; rfl)
  have hBC := Complex.borelCaratheodory (M := Real.log (M / m)) hlog
    (f := fun v => h (c + v)) (R := r)
    (fun w hw => ((hshift w hw).differentiableAt).differentiableWithinAt)
    (fun w hw => by
      have hcw : c + w ∈ ball c r := by
        rw [mem_ball]
        simpa [dist_eq_norm] using mem_ball_zero_iff.mp hw
      exact hre (c + w) hcw)
    hr (z := z - c)
    (by
      rw [mem_ball_zero_iff]
      rw [← dist_eq_norm]
      exact mem_ball.mp hz)
  simp only [add_sub_cancel] at hBC
  rw [add_zero c, hc0] at hBC
  simpa using hBC

/-- **L6: the log-derivative bound for the reflected function.**
Cauchy's estimate on the Borel–Carathéodory bound:
`‖logDeriv G s‖ ≤ 8·log(M/m)/r` for `s ∈ closedBall c (r/4)`. -/
theorem blaschke_logDeriv_bound {c : ℂ} {r M m : ℝ} (hr : 0 < r)
    {G h : ℂ → ℂ}
    (hderiv : ∀ z ∈ ball c r, HasDerivAt h (logDeriv G z) z)
    (hc0 : h c = 0)
    (hre : ∀ z ∈ ball c r, (h z).re ≤ Real.log (M / m))
    (hlog : 0 < Real.log (M / m)) :
    ∀ s ∈ closedBall c (r/4),
      ‖logDeriv G s‖ ≤ 8 * Real.log (M / m) / r := by
  intro s hs
  have hsc : ‖s - c‖ ≤ r/4 := by
    rw [← dist_eq_norm]
    exact mem_closedBall.mp hs
  have hnorm := blaschke_h_norm_bound hr hderiv hc0 hre hlog
  -- ‖h‖ ≤ 2·log(M/m) on the closed half-ball
  have hh_half : ∀ z ∈ closedBall c (r/2), ‖h z‖ ≤ 2 * Real.log (M / m) := by
    intro z hz
    have hzc : ‖z - c‖ ≤ r/2 := by
      rw [← dist_eq_norm]
      exact mem_closedBall.mp hz
    have hzball : z ∈ ball c r := by
      rw [mem_ball, dist_eq_norm]
      linarith
    calc ‖h z‖ ≤ 2 * Real.log (M / m) * ‖z - c‖ / (r - ‖z - c‖) :=
        hnorm z hzball
      _ ≤ 2 * Real.log (M / m) := by
          rw [div_le_iff₀ (by linarith)]
          have h1 : ‖z - c‖ ≤ r - ‖z - c‖ := by linarith
          calc 2 * Real.log (M / m) * ‖z - c‖
              ≤ 2 * Real.log (M / m) * (r - ‖z - c‖) := by
                apply mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = 2 * Real.log (M / m) * (r - ‖z - c‖) := rfl
  -- Cauchy on the sphere of radius r/4 around s
  have hd : DiffContOnCl ℂ h (ball s (r/4)) := by
    constructor
    · intro w hw
      have hwball : w ∈ ball c r := by
        rw [mem_ball, dist_eq_norm]
        have : ‖w - s‖ < r/4 := by
          rw [← dist_eq_norm]
          exact mem_ball.mp hw
        calc ‖w - c‖ = ‖(w - s) + (s - c)‖ := by ring_nf
          _ ≤ ‖w - s‖ + ‖s - c‖ := norm_add_le _ _
          _ < r := by linarith
      exact ((hderiv w hwball).differentiableAt).differentiableWithinAt
    · intro w hw
      have hwc : w ∈ closedBall c (r/2) := by
        have hcl : closure (ball s (r/4)) ⊆ closedBall s (r/4) :=
          closure_ball_subset_closedBall
        have : ‖w - s‖ ≤ r/4 := by
          rw [← dist_eq_norm]
          exact mem_closedBall.mp (hcl hw)
        rw [mem_closedBall, dist_eq_norm]
        calc ‖w - c‖ = ‖(w - s) + (s - c)‖ := by ring_nf
          _ ≤ ‖w - s‖ + ‖s - c‖ := norm_add_le _ _
          _ ≤ r/2 := by linarith
      have hwball : w ∈ ball c r := by
        rw [mem_ball, dist_eq_norm]
        have := mem_closedBall.mp hwc
        rw [dist_eq_norm] at this
        linarith
      exact ((hderiv w hwball).differentiableAt).continuousAt.continuousWithinAt
  have hC : ∀ z ∈ sphere s (r/4), ‖h z‖ ≤ 2 * Real.log (M / m) := by
    intro z hz
    apply hh_half
    have hzs : ‖z - s‖ = r/4 := mem_sphere_iff_norm.mp hz
    rw [mem_closedBall, dist_eq_norm]
    calc ‖z - c‖ = ‖(z - s) + (s - c)‖ := by ring_nf
      _ ≤ ‖z - s‖ + ‖s - c‖ := norm_add_le _ _
      _ ≤ r/2 := by rw [hzs]; linarith
  have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le
    (by linarith : (0:ℝ) < r/4) hd hC
  have hsball : s ∈ ball c r := by
    rw [mem_ball, dist_eq_norm]
    linarith
  have hds : deriv h s = logDeriv G s := (hderiv s hsball).deriv
  rw [hds] at hcauchy
  calc ‖logDeriv G s‖ ≤ 2 * Real.log (M / m) / (r/4) := hcauchy
    _ = 8 * Real.log (M / m) / r := by
        field_simp
        ring

/-- `logDeriv` only depends on the local germ. -/
theorem logDeriv_congr_nhds {f₁ f₂ : ℂ → ℂ} {z : ℂ}
    (h : f₁ =ᶠ[nhds z] f₂) :
    logDeriv f₁ z = logDeriv f₂ z := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

/-- `logDeriv` of a power of a linear factor: `n/(z-u)`, valid whenever the
factor is nonzero (in particular at `z = u` with exponent `0`, where both
sides vanish). -/
theorem logDeriv_sub_pow {u z : ℂ} {k : ℕ} (h : (z - u) ^ k ≠ 0) :
    logDeriv (fun w => (w - u) ^ k) z = (k : ℂ) / (z - u) := by
  by_cases hzu : z = u
  · subst hzu
    have hk : k = 0 := by
      by_contra hk0
      apply h
      rw [sub_self]
      exact zero_pow hk0
    subst hk
    simp [logDeriv_apply]
  · have hdiff : DifferentiableAt ℂ (fun w => w - u) z :=
      differentiableAt_id.sub_const u
    rw [logDeriv_fun_pow hdiff]
    have hld : logDeriv (fun w => w - u) z = 1 / (z - u) := by
      rw [logDeriv_apply]
      rw [show deriv (fun w => w - u) z = 1 by
        rw [deriv_sub_const]
        exact deriv_id z]
    rw [hld]
    rw [mul_one_div]

/-- `logDeriv` of a power of a Blaschke numerator factor. -/
theorem logDeriv_blaschke_pow {c u z : ℂ} {r : ℝ} (hrC : ((r:ℂ)) ≠ 0) {k : ℕ}
    (h : ((((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)) / (r:ℂ)) ^ k ≠ 0) :
    logDeriv (fun w =>
        ((((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (w - c)) / (r:ℂ)) ^ k) z
      = (k : ℂ) * (-(starRingEnd ℂ) (u - c))
          / (((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)) := by
  set a : ℂ := (starRingEnd ℂ) (u - c) with ha
  by_cases hq : ((r:ℂ))^2 - a * (z - c) = 0
  · have hk : k = 0 := by
      by_contra hk0
      apply h
      rw [hq, zero_div]
      exact zero_pow hk0
    subst hk
    simp [logDeriv_apply]
  · have hbase_diff : DifferentiableAt ℂ
        (fun w => (((r:ℂ))^2 - a * (w - c)) / (r:ℂ)) z := by
      apply DifferentiableAt.div_const
      exact (differentiableAt_const _).sub
        ((differentiableAt_const _).mul (differentiableAt_id.sub_const c))
    rw [logDeriv_fun_pow hbase_diff]
    have hld : logDeriv (fun w => (((r:ℂ))^2 - a * (w - c)) / (r:ℂ)) z
        = (-a) / (((r:ℂ))^2 - a * (z - c)) := by
      have hrw : (fun w => (((r:ℂ))^2 - a * (w - c)) / (r:ℂ))
          = fun w => (((r:ℂ))^2 - a * (w - c)) * ((r:ℂ))⁻¹ := by
        ext w
        rw [div_eq_mul_inv]
      rw [hrw, logDeriv_mul_const _ _ (inv_ne_zero hrC)]
      rw [logDeriv_apply]
      have hderiv_q : deriv (fun w => (((r:ℂ))^2 - a * (w - c))) z = -a := by
        rw [deriv_const_sub]
        rw [show (fun w => a * (w - c)) = fun w => a * w - a * c by
          ext w
          ring]
        rw [deriv_sub_const]
        rw [deriv_const_mul _ differentiableAt_id]
        simp
      rw [hderiv_q]
    rw [hld]
    ring

set_option maxHeartbeats 1600000 in
/-- **L7: the log-derivative decomposition.**  At any point of the open ball
where `f ≠ 0`:
`logDeriv f = Σ n_u/(z-u) + logDeriv G + Σ n_u·conj(u-c)/(r² - conj(u-c)(z-c))`. -/
theorem landau_decomposition {c : ℂ} {r : ℝ} (hr : 0 < r) {f g G : ℂ → ℂ}
    {S : Finset ℂ} {n : ℂ → ℕ}
    (hg_anal : AnalyticOnNhd ℂ g (closedBall c r))
    (hg_ne : ∀ u ∈ closedBall c r, g u ≠ 0)
    (hfact : ∀ z ∈ closedBall c r, f z = (∏ u ∈ S, (z - u) ^ (n u)) * g z)
    (hGdef : G = fun z => g z * ∏ u ∈ S,
      ((((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)) / (r:ℂ)) ^ (n u))
    (hG_ne : ∀ z ∈ ball c r, G z ≠ 0) :
    ∀ z ∈ ball c r, f z ≠ 0 →
      logDeriv f z = (∑ u ∈ S, (n u : ℂ) / (z - u)) + logDeriv G z
        + ∑ u ∈ S, (n u : ℂ) * (starRingEnd ℂ) (u - c)
            / (((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)) := by
  intro z hz hfz
  have hrC : ((r:ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
  have hzc : z ∈ closedBall c r := ball_subset_closedBall hz
  have hgz : g z ≠ 0 := hg_ne z hzc
  have hPz : (∏ u ∈ S, (z - u) ^ (n u)) ≠ 0 := by
    intro h0
    apply hfz
    rw [hfact z hzc, h0, zero_mul]
  have hBz : (∏ u ∈ S,
      ((((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)) / (r:ℂ)) ^ (n u))
        ≠ 0 := by
    intro h0
    apply hG_ne z hz
    rw [hGdef]
    dsimp only
    rw [h0, mul_zero]
  have hg_diff : DifferentiableAt ℂ g z :=
    (hg_anal z hzc).differentiableAt
  have hP_diff : DifferentiableAt ℂ
      (fun w => ∏ u ∈ S, (w - u) ^ (n u)) z := by
    apply AnalyticAt.differentiableAt
    apply Finset.analyticAt_fun_prod
    intro u _
    exact (analyticAt_id.sub analyticAt_const).pow _
  have hB_diff : DifferentiableAt ℂ (fun w => ∏ u ∈ S,
      ((((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (w - c)) / (r:ℂ)) ^ (n u)) z := by
    apply AnalyticAt.differentiableAt
    apply Finset.analyticAt_fun_prod
    intro u _
    apply AnalyticAt.pow
    apply AnalyticAt.div
    · exact analyticAt_const.sub
        (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))
    · exact analyticAt_const
    · exact hrC
  -- logDeriv f = logDeriv P + logDeriv g
  have hfP : f =ᶠ[nhds z] fun w => (∏ u ∈ S, (w - u) ^ (n u)) * g w := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hfact w (ball_subset_closedBall hw)
  have hstep1 : logDeriv f z
      = logDeriv (fun w => ∏ u ∈ S, (w - u) ^ (n u)) z + logDeriv g z := by
    rw [logDeriv_congr_nhds hfP]
    exact logDeriv_mul z hPz hgz hP_diff hg_diff
  -- logDeriv G = logDeriv g + Σ logDeriv(Blaschke factors)
  have hstep2 : logDeriv G z = logDeriv g z
      + ∑ u ∈ S, (n u : ℂ) * (-(starRingEnd ℂ) (u - c))
          / (((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)) := by
    rw [hGdef]
    rw [logDeriv_mul z hgz hBz hg_diff hB_diff]
    congr 1
    rw [logDeriv_prod]
    · apply Finset.sum_congr rfl
      intro u hu
      have hfac_ne : ((((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)) / (r:ℂ))
          ^ (n u) ≠ 0 := by
        have := Finset.prod_ne_zero_iff.mp hBz u hu
        exact this
      rw [logDeriv_blaschke_pow hrC hfac_ne]
    · intro u hu
      exact Finset.prod_ne_zero_iff.mp hBz u hu
    · intro u _
      apply DifferentiableAt.pow
      apply DifferentiableAt.div_const
      exact (differentiableAt_const _).sub
        ((differentiableAt_const _).mul (differentiableAt_id.sub_const c))
  -- logDeriv P = Σ n/(z−u)
  have hstep3 : logDeriv (fun w => ∏ u ∈ S, (w - u) ^ (n u)) z
      = ∑ u ∈ S, (n u : ℂ) / (z - u) := by
    rw [logDeriv_prod]
    · apply Finset.sum_congr rfl
      intro u hu
      exact logDeriv_sub_pow (Finset.prod_ne_zero_iff.mp hPz u hu)
    · intro u hu
      exact Finset.prod_ne_zero_iff.mp hPz u hu
    · intro u _
      exact (differentiableAt_id.sub_const u).pow _
  rw [hstep1, hstep2, hstep3]
  have hsplit : ∑ u ∈ S, (n u : ℂ) * (-(starRingEnd ℂ) (u - c))
      / (((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c))
      = - ∑ u ∈ S, (n u : ℂ) * (starRingEnd ℂ) (u - c)
          / (((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [hsplit]
  ring

set_option maxHeartbeats 1600000 in
/-- **L8: Landau's lemma.**  For `f` analytic on `closedBall c r` with
`‖f‖ ≤ M`, `m ≤ ‖f(c)‖`: at every `s ∈ closedBall c (r/4)` with `f(s) ≠ 0`,
the log-derivative equals the sum of `n_u/(s-u)` over the divisor of the
ball up to an error `8·log(M/m)/r + N·4/(3r)`. -/
theorem landau_lemma {c : ℂ} {r M m : ℝ} (hr : 0 < r) (hm : 0 < m)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hM : ∀ z ∈ closedBall c r, ‖f z‖ ≤ M)
    (hmc : m ≤ ‖f c‖) (hlog : 0 < Real.log (M / m)) :
    ∃ (S : Finset ℂ) (n : ℂ → ℕ),
      (∀ u ∈ S, u ∈ closedBall c r) ∧
      (∀ u ∈ S, (n u : ℤ) = MeromorphicOn.divisor f (closedBall c r) u) ∧
      (∀ u, u ∉ S → MeromorphicOn.divisor f (closedBall c r) u = 0) ∧
      ∀ s ∈ closedBall c (r/4), f s ≠ 0 →
        ‖logDeriv f s - ∑ u ∈ S, (n u : ℂ) / (s - u)‖
          ≤ 8 * Real.log (M / m) / r
            + (∑ u ∈ S, (n u : ℝ)) * (4 / (3 * r)) := by
  have hne : f c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hmc
    linarith
  obtain ⟨g, G, S, n, hg_anal, hg_ne, hS_mem, hn_eq, hd_zero, hfact, hGdef,
    hG_anal, hG_ne, hG_sphere, hG_c⟩ := blaschke_package hr hf hne
  refine ⟨S, n, hS_mem, hn_eq, hd_zero, ?_⟩
  intro s hs hfs
  have hGM : ∀ z ∈ closedBall c r, ‖G z‖ ≤ M :=
    blaschke_max_modulus hr hG_anal hG_sphere hM
  have hGc_m : m ≤ ‖G c‖ := le_trans hmc hG_c
  obtain ⟨h, hderiv, hc0, hrep, hre⟩ :=
    blaschke_log_re_bound hr hm hG_anal hG_ne hGM hGc_m
  have hld_G := blaschke_logDeriv_bound hr hderiv hc0 hre hlog s hs
  have hsball : s ∈ ball c r := by
    have hdist := mem_closedBall.mp hs
    rw [mem_ball]
    linarith
  have hdec := landau_decomposition hr hg_anal hg_ne hfact hGdef hG_ne
    s hsball hfs
  have hdiff_eq : logDeriv f s - ∑ u ∈ S, (n u : ℂ) / (s - u)
      = logDeriv G s + ∑ u ∈ S, (n u : ℂ) * (starRingEnd ℂ) (u - c)
          / (((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (s - c)) := by
    rw [hdec]
    ring
  rw [hdiff_eq]
  apply le_trans (norm_add_le _ _)
  apply add_le_add hld_G
  have hterm : ∀ u ∈ S,
      ‖(n u : ℂ) * (starRingEnd ℂ) (u - c)
        / (((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (s - c))‖
      ≤ (n u : ℝ) * (4 / (3 * r)) := by
    intro u hu
    have hsc : ‖s - c‖ ≤ r/4 := by
      rw [← dist_eq_norm]
      exact mem_closedBall.mp hs
    have huc : ‖u - c‖ ≤ r := by
      rw [← dist_eq_norm]
      exact mem_closedBall.mp (hS_mem u hu)
    have hden : (3/4) * r^2
        ≤ ‖((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (s - c)‖ := by
      have h1 : ‖(starRingEnd ℂ) (u - c) * (s - c)‖ ≤ r * (r/4) := by
        rw [norm_mul, RCLike.norm_conj]
        apply mul_le_mul huc hsc (norm_nonneg _) hr.le
      have h2 : ‖((r:ℂ))^2‖ = r^2 := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      calc (3/4) * r^2 = r^2 - r * (r/4) := by ring
        _ ≤ ‖((r:ℂ))^2‖ - ‖(starRingEnd ℂ) (u - c) * (s - c)‖ := by
            rw [h2]
            linarith
        _ ≤ ‖((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (s - c)‖ :=
            norm_sub_norm_le _ _
    rw [norm_div, norm_mul, RCLike.norm_conj, Complex.norm_natCast]
    have hden_pos : (0:ℝ) < (3/4) * r^2 := by positivity
    calc (n u : ℝ) * ‖u - c‖
          / ‖((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (s - c)‖
        ≤ (n u : ℝ) * r / ((3/4) * r^2) := by
          apply div_le_div₀ (by positivity)
            (mul_le_mul_of_nonneg_left huc (Nat.cast_nonneg _))
            hden_pos hden
      _ = (n u : ℝ) * (4 / (3 * r)) := by
          field_simp
  calc ‖∑ u ∈ S, (n u : ℂ) * (starRingEnd ℂ) (u - c)
        / (((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (s - c))‖
      ≤ ∑ u ∈ S, ‖(n u : ℂ) * (starRingEnd ℂ) (u - c)
        / (((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (s - c))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ u ∈ S, (n u : ℝ) * (4 / (3 * r)) :=
        Finset.sum_le_sum hterm
    _ = (∑ u ∈ S, (n u : ℝ)) * (4 / (3 * r)) := by
        rw [← Finset.sum_mul]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.eqOn_of_codiscreteWithin
#print axioms CriticalLinePhasor.DVP.extract_analytic_finset
#print axioms CriticalLinePhasor.DVP.blaschke_package
#print axioms CriticalLinePhasor.DVP.blaschke_log_re_bound
#print axioms CriticalLinePhasor.DVP.blaschke_logDeriv_bound
#print axioms CriticalLinePhasor.DVP.landau_decomposition
#print axioms CriticalLinePhasor.DVP.landau_lemma
end AxiomAudit
