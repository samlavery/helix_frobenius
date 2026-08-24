import RequestProject.DVPLandauLemma
import RequestProject.DVPLogDistance

/-!
# L9: the value-level Landau lower bound (any interior ratio)

`landau_lemma` (L8) controls `logDeriv f` on `ball c (r/4)`.  The VALUE
version needs only the Blaschke factorization plus Borel–Carathéodory, and
works on `closedBall c (βr)` for ANY `β < 1`:

`log‖f z‖ ≥ Σ n_u·log‖z−u‖ + log m − (2β/(1−β))·log(M/m) − N·log((1+β)r)`,

with `N = Σ n_u` the windowed zero mass.  This is the missing supply for the
top-edge LOWER bound of Littlewood's box, and the ratio freedom is what
makes it fit the compiled growth: at `c = 2+iT`, `r = 12/7`, `β = 7/8` the
full ball stays in the quarter strip `σ ≥ 2/7 > 1/4` (where B2″ growth is
compiled) while the `βr`-ball covers all of `[1/2,2]×{T}`.  The `r/4`
log-derivative instrument cannot reach this configuration; the value
instrument can.  Each `log‖z−u‖` then integrates to `≥ −2` by
`integral_log_norm_dist_lower`.
-/

open Metric

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **L9: the value-level Landau lower bound at interior ratio `β`.**
For `f` analytic on `closedBall c r` with `‖f‖ ≤ M`, `‖f c‖ ≥ m > 0`:
with `S, n` the divisor of `f` on the ball, every `z ∈ closedBall c (β·r)`
with `f z ≠ 0` satisfies

`log‖f z‖ ≥ log m − (2β/(1−β))·log(M/m) − (Σ n_u)·log((1+β)r)
            + Σ n_u·log‖z−u‖`. -/
theorem landau_value_lower {c : ℂ} {r M m β : ℝ} (hr : 0 < r) (hm : 0 < m)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hM : ∀ z ∈ closedBall c r, ‖f z‖ ≤ M)
    (hmc : m ≤ ‖f c‖) (hlog : 0 < Real.log (M / m)) :
    ∃ (S : Finset ℂ) (n : ℂ → ℕ),
      (∀ u ∈ S, u ∈ closedBall c r) ∧
      (∀ u ∈ S, (n u : ℤ) = MeromorphicOn.divisor f (closedBall c r) u) ∧
      (∀ u, u ∉ S → MeromorphicOn.divisor f (closedBall c r) u = 0) ∧
      ∀ z ∈ closedBall c (β * r), f z ≠ 0 →
        Real.log m - 2 * (β / (1 - β)) * Real.log (M / m)
            - (∑ u ∈ S, (n u : ℝ)) * Real.log ((1 + β) * r)
            + (∑ u ∈ S, (n u : ℝ) * Real.log ‖z - u‖)
          ≤ Real.log ‖f z‖ := by
  have hne : f c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hmc
    linarith
  obtain ⟨g, G, S, n, hg_anal, hg_ne, hS_mem, hn_eq, hd_zero, hfact, hGdef,
    hG_anal, hG_ne, hG_sphere, hG_c⟩ := blaschke_package hr hf hne
  refine ⟨S, n, hS_mem, hn_eq, hd_zero, ?_⟩
  intro z hz hfz
  have hGM : ∀ w ∈ closedBall c r, ‖G w‖ ≤ M :=
    blaschke_max_modulus hr hG_anal hG_sphere hM
  have hGc_m : m ≤ ‖G c‖ := le_trans hmc hG_c
  obtain ⟨h, hderiv, hc0, hrep, hre⟩ :=
    blaschke_log_re_bound hr hm hG_anal hG_ne hGM hGc_m
  have hhb := blaschke_h_norm_bound hr hderiv hc0 hre hlog
  have hβr : β * r < r := by nlinarith
  have hzc : ‖z - c‖ ≤ β * r := by
    have := mem_closedBall.mp hz
    rwa [dist_eq_norm] at this
  have hzr : z ∈ ball c r := by
    rw [mem_ball, dist_eq_norm]
    linarith
  have hzcr : z ∈ closedBall c r := ball_subset_closedBall hzr
  have hzc0 : (0:ℝ) ≤ ‖z - c‖ := norm_nonneg _
  -- ‖h z‖ ≤ (2β/(1−β)) log(M/m) on the βr-ball
  have hh2 : ‖h z‖ ≤ 2 * (β / (1 - β)) * Real.log (M / m) := by
    have hb := hhb z hzr
    have hq : ‖z - c‖ / (r - ‖z - c‖) ≤ β / (1 - β) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    calc ‖h z‖ ≤ 2 * Real.log (M / m) * ‖z - c‖ / (r - ‖z - c‖) := hb
      _ = 2 * Real.log (M / m) * (‖z - c‖ / (r - ‖z - c‖)) := by ring
      _ ≤ 2 * Real.log (M / m) * (β / (1 - β)) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = 2 * (β / (1 - β)) * Real.log (M / m) := by ring
  have hre_low : -(2 * (β / (1 - β)) * Real.log (M / m)) ≤ (h z).re := by
    have habs := Complex.abs_re_le_norm (h z)
    have := (abs_le.mp habs).1
    linarith
  -- log‖G z‖ ≥ log m − (2β/(1−β)) log(M/m)
  have hGz_ne : ‖G c‖ ≠ 0 := by
    have : (0:ℝ) < ‖G c‖ := lt_of_lt_of_le hm hGc_m
    linarith
  have hGnorm : ‖G z‖ = ‖G c‖ * Real.exp ((h z).re) := by
    rw [hrep z hzr, norm_mul, Complex.norm_exp]
  have hlogG_low : Real.log m - 2 * (β / (1 - β)) * Real.log (M / m)
      ≤ Real.log ‖G z‖ := by
    rw [hGnorm, Real.log_mul hGz_ne (Real.exp_ne_zero _), Real.log_exp]
    have h1 : Real.log m ≤ Real.log ‖G c‖ :=
      Real.log_le_log hm hGc_m
    linarith
  -- the reflection factors: pinned in [(1−β)r, (1+β)r] on the βr-ball
  set fac : ℂ → ℂ := fun u =>
    ((((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c)) / (r:ℂ)) with hfacdef
  have hrn : ‖((r:ℝ):ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hfac_ub : ∀ u ∈ S, ‖fac u‖ ≤ (1 + β) * r := by
    intro u hu
    have huc : ‖u - c‖ ≤ r := by
      have := mem_closedBall.mp (hS_mem u hu)
      rwa [dist_eq_norm] at this
    have hnum : ‖(((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c))‖
        ≤ r^2 + r * (β * r) := by
      calc ‖(((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c))‖
          ≤ ‖(((r:ℂ)))^2‖ + ‖(starRingEnd ℂ) (u - c) * (z - c)‖ :=
            norm_sub_le _ _
        _ ≤ r^2 + r * (β * r) := by
            rw [norm_pow, norm_mul, RCLike.norm_conj, hrn]
            have h2 : ‖u - c‖ * ‖z - c‖ ≤ r * (β * r) :=
              mul_le_mul huc hzc hzc0 (by linarith)
            linarith
    rw [hfacdef]
    simp only [norm_div]
    rw [hrn, div_le_iff₀ hr]
    calc ‖(((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c))‖
        ≤ r^2 + r * (β * r) := hnum
      _ = (1 + β) * r * r := by ring
  have hfac_lb : ∀ u ∈ S, (1 - β) * r ≤ ‖fac u‖ := by
    intro u hu
    have huc : ‖u - c‖ ≤ r := by
      have := mem_closedBall.mp (hS_mem u hu)
      rwa [dist_eq_norm] at this
    have hnum : r^2 - r * (β * r)
        ≤ ‖(((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c))‖ := by
      have h1 : ‖(((r:ℂ)))^2‖ - ‖(starRingEnd ℂ) (u - c) * (z - c)‖
          ≤ ‖(((r:ℂ))^2 - (starRingEnd ℂ) (u - c) * (z - c))‖ :=
        norm_sub_norm_le _ _
      rw [norm_pow, norm_mul, RCLike.norm_conj, hrn] at h1
      have h2 : ‖u - c‖ * ‖z - c‖ ≤ r * (β * r) :=
        mul_le_mul huc hzc hzc0 (by linarith)
      nlinarith [h1, h2]
    rw [hfacdef]
    simp only [norm_div]
    rw [hrn, le_div_iff₀ hr]
    calc (1 - β) * r * r = r^2 - r * (β * r) := by ring
      _ ≤ _ := hnum
  have hfac_ne : ∀ u ∈ S, fac u ≠ 0 := by
    intro u hu h0
    have := hfac_lb u hu
    rw [h0, norm_zero] at this
    nlinarith
  -- log‖g z‖ from log‖G z‖ minus the factor logs
  have hgz_ne : g z ≠ 0 := hg_ne z hzcr
  have hGz_eq : G z = g z * ∏ u ∈ S, (fac u) ^ (n u) := by
    rw [hGdef]
  have hGz_norm : ‖G z‖ = ‖g z‖ * ∏ u ∈ S, ‖fac u‖ ^ (n u) := by
    rw [hGz_eq, norm_mul, norm_prod]
    congr 1
    exact Finset.prod_congr rfl fun u _ => norm_pow _ _
  have hprod_ne : ∀ u ∈ S, ‖fac u‖ ^ (n u) ≠ 0 := by
    intro u hu
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hfac_ne u hu))
  have hlogG_split : Real.log ‖G z‖
      = Real.log ‖g z‖ + ∑ u ∈ S, (n u : ℝ) * Real.log ‖fac u‖ := by
    rw [hGz_norm, Real.log_mul (norm_ne_zero_iff.mpr hgz_ne)
      (Finset.prod_ne_zero_iff.mpr hprod_ne), Real.log_prod hprod_ne]
    congr 1
    exact Finset.sum_congr rfl fun u _ => Real.log_pow _ _
  have hfac_log_ub : ∑ u ∈ S, (n u : ℝ) * Real.log ‖fac u‖
      ≤ (∑ u ∈ S, (n u : ℝ)) * Real.log ((1 + β) * r) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro u hu
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.log_le_log
      (lt_of_lt_of_le (by nlinarith) (hfac_lb u hu))
    exact hfac_ub u hu
  have hlogg_low : Real.log m - 2 * (β / (1 - β)) * Real.log (M / m)
      - (∑ u ∈ S, (n u : ℝ)) * Real.log ((1 + β) * r)
      ≤ Real.log ‖g z‖ := by
    have := hlogG_split
    linarith [hlogG_low, hfac_log_ub]
  -- f side: log‖f z‖ = Σ n log‖z−u‖ + log‖g z‖
  have hfz_eq : f z = (∏ u ∈ S, (z - u) ^ (n u)) * g z := hfact z hzcr
  have hlin_ne : ∀ u ∈ S, (z - u) ^ (n u) ≠ 0 := by
    intro u hu h0
    apply hfz
    rw [hfz_eq, Finset.prod_eq_zero hu h0, zero_mul]
  have hlin_norm_ne : ∀ u ∈ S, ‖z - u‖ ^ (n u) ≠ 0 := by
    intro u hu
    rw [← norm_pow]
    exact norm_ne_zero_iff.mpr (hlin_ne u hu)
  have hfz_norm : ‖f z‖ = (∏ u ∈ S, ‖z - u‖ ^ (n u)) * ‖g z‖ := by
    rw [hfz_eq, norm_mul, norm_prod]
    congr 1
    exact Finset.prod_congr rfl fun u _ => norm_pow _ _
  have hlogf_split : Real.log ‖f z‖
      = (∑ u ∈ S, (n u : ℝ) * Real.log ‖z - u‖) + Real.log ‖g z‖ := by
    rw [hfz_norm, Real.log_mul (Finset.prod_ne_zero_iff.mpr hlin_norm_ne)
      (norm_ne_zero_iff.mpr hgz_ne), Real.log_prod hlin_norm_ne]
    congr 1
    exact Finset.sum_congr rfl fun u _ => Real.log_pow _ _
  rw [hlogf_split]
  linarith [hlogg_low]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.landau_value_lower
end AxiomAudit
