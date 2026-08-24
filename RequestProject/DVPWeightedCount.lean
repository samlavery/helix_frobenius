import RequestProject.ZeroCountJensen
import RequestProject.XiOrder
import RequestProject.DVPGrowthBounds
import RequestProject.DVPLandauLemma
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# R-campaign, brick R1: the multiplicity-weighted disk count

`xi_zero_count_disk_bound` counts zeros without multiplicity; the exponent-1
zero-free region needs the weighted count `Σ_{|ρ|≤R} m_ρ ≤ C·R·log R`.  The
Jensen side of the compiled argument is already multiplicity-weighted (the
divisor); this file supplies the bridge `divisor = xiOrderNat` and the
weighted count.
-/

open Real Complex MeasureTheory Filter Topology Set

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The divisor–order bridge**: on any closed ball, the divisor of `ξ`
evaluates to the compiled analytic multiplicity. -/
theorem xi_divisor_eq_orderNat {r : ℝ} {u : ℂ}
    (hu : u ∈ Metric.closedBall (0:ℂ) r) :
    MeromorphicOn.divisor ZD.riemannXi (Metric.closedBall (0:ℂ) r) u
      = (ZD.xiOrderNat u : ℤ) := by
  have hAnal : AnalyticOnNhd ℂ ZD.riemannXi (Metric.closedBall (0:ℂ) r) :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ.mono (Set.subset_univ _)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAnal hu]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
    (ZD.riemannXi_analyticOrderAt_ne_top_everywhere u)
  have horder : ZD.xiOrderNat u = n := by
    unfold ZD.xiOrderNat analyticOrderNatAt
    rw [← hn]
    exact ENat.toNat_coe n
  rw [← hn, horder]
  rfl

set_option maxHeartbeats 3200000 in
/-- **R1: the multiplicity-weighted disk count** —
`Σ_{ρ ∈ zeros ∩ ball R} m_ρ ≤ C·R·log R`.  The Jensen pigeonhole of
`xi_zero_count_disk_bound` with the divisor–order bridge keeping the
multiplicities. -/
theorem xi_weighted_zero_count_disk_bound :
    ∃ C > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ R, R₀ ≤ R →
      (∑ ρ ∈ (ZD.ZeroCount.riemannXi_zeros_finite_in_closedBall R).toFinset,
        (ZD.xiOrderNat ρ : ℝ))
        ≤ C * R * Real.log R := by
  obtain ⟨C₁, hC₁, R₁, hR₁, hBound⟩ := ZD.ZeroCount.xi_order_one_log_bound
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(8 * C₁ + 4) / Real.log 2, by positivity,
    max (max R₁ 2) (Real.exp 1), ?_, ?_⟩
  · apply lt_of_lt_of_le (Real.exp_pos 1)
    exact le_max_right _ _
  intro R hR
  have hR_R₁ : R₁ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hR_two : (2 : ℝ) ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hR_e : Real.exp 1 ≤ R := le_trans (le_max_right _ _) hR
  have hR_pos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR_two
  have hR_log_ge_1 : (1 : ℝ) ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos 1) hR_e
    rwa [Real.log_exp] at this
  have hR_log_nn : 0 ≤ Real.log R := le_trans zero_le_one hR_log_ge_1
  set CB : Set ℂ := Metric.closedBall (0:ℂ) |2 * R| with hCB_def
  have h2R_pos : (0 : ℝ) < 2 * R := by linarith
  have h2R_R₁ : R₁ ≤ 2 * R := by linarith
  have habs2R : |2 * R| = 2 * R := abs_of_pos h2R_pos
  have hAnal : AnalyticOnNhd ℂ ZD.riemannXi CB :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ.mono (Set.subset_univ _)
  have hMero : MeromorphicOn ZD.riemannXi CB := hAnal.meromorphicOn
  have hJensen := ZD.ZeroCount.xi_jensen_at_zero (2 * R) h2R_pos
  have hlog_xi0 : Real.log ‖ZD.riemannXi 0‖ = -Real.log 2 := by
    rw [ZD.ZeroCount.riemannXi_zero]
    simp
  have hAnalSph : AnalyticOnNhd ℂ ZD.riemannXi (Metric.sphere (0 : ℂ) |2 * R|) :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ.mono (Set.subset_univ _)
  have hCI : CircleIntegrable (fun s => Real.log ‖ZD.riemannXi s‖) 0 (2 * R) :=
    circleIntegrable_log_norm_meromorphicOn hAnalSph.meromorphicOn
  have hCircAvg_le :
      circleAverage (fun s => Real.log ‖ZD.riemannXi s‖) 0 (2 * R) ≤
        C₁ * (2 * R) * Real.log (2 * R) := by
    apply circleAverage_mono_on_of_le_circle hCI
    intro s hs
    rw [Metric.mem_sphere, dist_zero_right, habs2R] at hs
    have h_log_le : Real.log ‖ZD.riemannXi s‖
        ≤ Real.log (‖ZD.riemannXi s‖ + 1) := by
      rcases eq_or_lt_of_le (norm_nonneg (ZD.riemannXi s)) with h0 | hpos
      · rw [← h0, Real.log_zero]
        exact Real.log_nonneg (by linarith [norm_nonneg (ZD.riemannXi s)])
      · exact Real.log_le_log hpos (by linarith)
    have h_bound_s := hBound (2 * R) h2R_R₁ s (le_of_eq hs)
    linarith
  have hD_nn : ∀ u, 0 ≤ MeromorphicOn.divisor ZD.riemannXi CB u := by
    intro u
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnal u
  have h_term_nn :
      ∀ u, 0 ≤ (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
                Real.log (2 * R * ‖u‖⁻¹) := by
    intro u
    by_cases hu : u ∈ CB
    · rw [hCB_def, Metric.mem_closedBall, dist_zero_right, habs2R] at hu
      by_cases hu0 : u = 0
      · simp [hu0, Real.log_zero]
      · have h_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
        have hlog_nn : 0 ≤ Real.log (2 * R * ‖u‖⁻¹) := by
          apply Real.log_nonneg
          rw [show (2 * R * ‖u‖⁻¹) = (2 * R) / ‖u‖ from by ring,
            le_div_iff₀ h_norm_pos]
          linarith
        exact mul_nonneg (by exact_mod_cast hD_nn u) hlog_nn
    · have hD0 := (MeromorphicOn.divisor ZD.riemannXi CB).apply_eq_zero_of_notMem hu
      simp [hD0]
  have hS_fin := ZD.ZeroCount.riemannXi_zeros_finite_in_closedBall R
  set S : Set ℂ := Metric.closedBall (0 : ℂ) R ∩ {z | ZD.riemannXi z = 0}
    with hS_def
  have hS_sub_CB : S ⊆ CB := by
    intro u hu
    obtain ⟨hu_ball, _⟩ := hu
    rw [hCB_def, Metric.mem_closedBall, dist_zero_right, habs2R]
    rw [Metric.mem_closedBall, dist_zero_right] at hu_ball
    linarith
  -- WEIGHTED per-element lower bound, via the divisor–order bridge
  have hS_each_w :
      ∀ ρ ∈ S,
        (ZD.xiOrderNat ρ : ℝ) * Real.log 2 ≤
          (MeromorphicOn.divisor ZD.riemannXi CB ρ : ℝ) *
            Real.log (2 * R * ‖ρ‖⁻¹) := by
    intro ρ hρ
    obtain ⟨hρ_ball, hρ_zero⟩ := hρ
    rw [Metric.mem_closedBall, dist_zero_right] at hρ_ball
    have hρ_zero' : ZD.riemannXi ρ = 0 := hρ_zero
    have hρ_ne_zero : ρ ≠ 0 := fun h0 =>
      ZD.ZeroCount.riemannXi_zero_ne_zero (h0 ▸ hρ_zero')
    have h_norm_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne_zero
    have hρ_mem_CB : ρ ∈ CB :=
      hS_sub_CB ⟨by rwa [Metric.mem_closedBall, dist_zero_right], hρ_zero⟩
    have hDeq : MeromorphicOn.divisor ZD.riemannXi CB ρ
        = (ZD.xiOrderNat ρ : ℤ) := by
      rw [hCB_def]
      exact xi_divisor_eq_orderNat (by
        rw [hCB_def] at hρ_mem_CB
        exact hρ_mem_CB)
    have h_ratio_ge_two : (2 : ℝ) ≤ 2 * R * ‖ρ‖⁻¹ := by
      rw [show (2 * R * ‖ρ‖⁻¹) = (2 * R) / ‖ρ‖ from by ring,
        le_div_iff₀ h_norm_pos]
      linarith
    have hlog_ge : Real.log 2 ≤ Real.log (2 * R * ‖ρ‖⁻¹) :=
      Real.log_le_log (by norm_num) h_ratio_ge_two
    rw [hDeq]
    push_cast
    apply mul_le_mul_of_nonneg_left hlog_ge (Nat.cast_nonneg _)
  have h_D_fs : (MeromorphicOn.divisor ZD.riemannXi CB).support.Finite :=
    (MeromorphicOn.divisor ZD.riemannXi CB).finiteSupport
      (isCompact_closedBall 0 _)
  have hS_sub_Dsupp : S ⊆ (MeromorphicOn.divisor ZD.riemannXi CB).support := by
    intro ρ hρ
    obtain ⟨hρ_ball, hρ_zero⟩ := hρ
    rw [Metric.mem_closedBall, dist_zero_right] at hρ_ball
    have hρ_mem_CB : ρ ∈ CB :=
      hS_sub_CB ⟨by rwa [Metric.mem_closedBall, dist_zero_right], hρ_zero⟩
    have hD_ge_one :
        (1 : ℤ) ≤ MeromorphicOn.divisor ZD.riemannXi CB ρ :=
      ZD.ZeroCount.xi_divisor_ge_one_of_zero hMero ρ hρ_mem_CB hρ_zero
    simp only [Function.mem_support]
    intro hD0
    rw [hD0] at hD_ge_one
    exact absurd hD_ge_one (by norm_num)
  have h_finsum_eq :
      (∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
                Real.log (2 * R * ‖u‖⁻¹)) =
        ∑ u ∈ h_D_fs.toFinset,
          (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
            Real.log (2 * R * ‖u‖⁻¹) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro hD0
    apply hu
    rw [hD0]
    simp
  have h_sub_fs : hS_fin.toFinset ⊆ h_D_fs.toFinset := by
    intro u hu
    simp only [Set.Finite.mem_toFinset] at hu ⊢
    exact hS_sub_Dsupp hu
  -- the weighted lower bound on the finsum
  have h_lower_w :
      (∑ ρ ∈ hS_fin.toFinset, (ZD.xiOrderNat ρ : ℝ)) * Real.log 2 ≤
        ∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
                Real.log (2 * R * ‖u‖⁻¹) := by
    rw [h_finsum_eq]
    calc (∑ ρ ∈ hS_fin.toFinset, (ZD.xiOrderNat ρ : ℝ)) * Real.log 2
        = ∑ ρ ∈ hS_fin.toFinset, (ZD.xiOrderNat ρ : ℝ) * Real.log 2 := by
          rw [Finset.sum_mul]
      _ ≤ ∑ u ∈ hS_fin.toFinset,
            (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
              Real.log (2 * R * ‖u‖⁻¹) := by
          apply Finset.sum_le_sum
          intro u hu
          simp only [Set.Finite.mem_toFinset] at hu
          exact hS_each_w u hu
      _ ≤ ∑ u ∈ h_D_fs.toFinset,
            (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
              Real.log (2 * R * ‖u‖⁻¹) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg h_sub_fs
          intro u _ _
          exact h_term_nn _
  have h_upper_finsum :
      ∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
              Real.log (2 * R * ‖u‖⁻¹)
        ≤ C₁ * (2 * R) * Real.log (2 * R) + Real.log 2 := by
    have h_eq_rearrange :
        ∑ᶠ u, (MeromorphicOn.divisor ZD.riemannXi CB u : ℝ) *
                Real.log (2 * R * ‖u‖⁻¹)
          = circleAverage (fun s => Real.log ‖ZD.riemannXi s‖) 0 (2 * R)
              - Real.log ‖ZD.riemannXi 0‖ := by
      rw [hJensen]
      ring
    rw [h_eq_rearrange, hlog_xi0]
    linarith
  have h_main_ineq :
      (∑ ρ ∈ hS_fin.toFinset, (ZD.xiOrderNat ρ : ℝ)) * Real.log 2 ≤
        C₁ * (2 * R) * Real.log (2 * R) + Real.log 2 :=
    le_trans h_lower_w h_upper_finsum
  have h_log2R_le : Real.log (2 * R) ≤ 2 * Real.log R := by
    rw [Real.log_mul (by norm_num) hR_pos.ne']
    have : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR_two
    linarith
  have hC12R_nn : 0 ≤ C₁ * (2 * R) := by positivity
  have h_bound_2 : C₁ * (2 * R) * Real.log (2 * R)
      ≤ 4 * C₁ * R * Real.log R := by
    calc C₁ * (2 * R) * Real.log (2 * R)
        ≤ C₁ * (2 * R) * (2 * Real.log R) :=
          mul_le_mul_of_nonneg_left h_log2R_le hC12R_nn
      _ = 4 * C₁ * R * Real.log R := by ring
  have h_divide : (∑ ρ ∈ hS_fin.toFinset, (ZD.xiOrderNat ρ : ℝ))
      ≤ (4 * C₁ * R * Real.log R + Real.log 2) / Real.log 2 := by
    rw [le_div_iff₀ hlog2_pos]
    linarith
  have hlog2_le_4RlogR : Real.log 2 ≤ 4 * R * Real.log R := by
    have h : Real.log 2 ≤ 1 := by
      calc Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        _ = 1 := by norm_num
    nlinarith [hR_log_ge_1, hR_two]
  have h_num_le :
      4 * C₁ * R * Real.log R + Real.log 2
        ≤ (8 * C₁ + 4) * R * Real.log R := by
    have h1 : 4 * C₁ * R * Real.log R + Real.log 2 ≤
        4 * C₁ * R * Real.log R + 4 * R * Real.log R := by linarith
    have h3 : (4 * C₁ + 4) * R * Real.log R
        ≤ (8 * C₁ + 4) * R * Real.log R := by
      apply mul_le_mul_of_nonneg_right _ hR_log_nn
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hR_pos)
      linarith
    nlinarith
  have h_final :
      (4 * C₁ * R * Real.log R + Real.log 2) / Real.log 2 ≤
        (8 * C₁ + 4) / Real.log 2 * R * Real.log R := by
    rw [div_le_iff₀ hlog2_pos]
    have heq : (8 * C₁ + 4) / Real.log 2 * R * Real.log R * Real.log 2 =
        (8 * C₁ + 4) * R * Real.log R := by
      field_simp
    rw [heq]
    exact h_num_le
  exact le_trans h_divide h_final

section CenterLowerBound
/-!
## R2b: the center lower bound

`|ζ(s)| ≥ 1/2` for `Re s ≥ 2`, via the Möbius inverse:
`ζ(s)·L(μ,s) = 1` and `‖L(μ,s)‖ ≤ Σ 1/n² ≤ 2` (telescoping majorant —
no Basel constant needed).  This is the Jensen-center floor for the
movable-center local count R2c.
-/

open scoped LSeries.notation ArithmeticFunction.Moebius

/-- The telescoping partial-sum bound `Σ_{n<N} g(n) ≤ 2` for
`g(0)=0, g(n)=1/n²`. -/
theorem partial_inv_sq_le_two (N : ℕ) :
    ∑ n ∈ Finset.range N,
      (if n = 0 then (0:ℝ) else 1 / (n:ℝ) ^ 2) ≤ 2 := by
  have key : ∀ M : ℕ, ∑ n ∈ Finset.range (M + 2),
      (if n = 0 then (0:ℝ) else 1 / (n:ℝ) ^ 2) ≤ 2 - 1 / (M + 1 : ℝ) := by
    intro M
    induction M with
    | zero => norm_num [Finset.sum_range_succ]
    | succ K ih =>
      rw [show K + 1 + 2 = (K + 2) + 1 by ring, Finset.sum_range_succ]
      have hpos : (0:ℝ) < (K:ℝ) + 1 := by positivity
      have hpos2 : (0:ℝ) < (K:ℝ) + 2 := by positivity
      have hstep : (if (K + 2 : ℕ) = 0 then (0:ℝ)
          else 1 / ((K + 2 : ℕ):ℝ) ^ 2)
          ≤ 1 / ((K:ℝ) + 1) - 1 / ((K:ℝ) + 2) := by
        rw [if_neg (by omega)]
        push_cast
        rw [div_sub_div _ _ (ne_of_gt hpos) (ne_of_gt hpos2)]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        ring_nf
        nlinarith [sq_nonneg ((K:ℝ) + 1)]
      have := add_le_add ih hstep
      calc ∑ n ∈ Finset.range (K + 2),
            (if n = 0 then (0:ℝ) else 1 / (n:ℝ) ^ 2)
            + (if (K + 2 : ℕ) = 0 then (0:ℝ) else 1 / ((K + 2 : ℕ):ℝ) ^ 2)
          ≤ (2 - 1 / ((K:ℝ) + 1)) + (1 / ((K:ℝ) + 1) - 1 / ((K:ℝ) + 2)) :=
            this
        _ = 2 - 1 / ((K:ℝ) + 2) := by ring
        _ = 2 - 1 / ((K + 1 : ℕ) + 1 : ℝ) := by push_cast; ring
  match N with
  | 0 => simp
  | 1 => simp
  | (M + 2) =>
    have h := key M
    have : (0:ℝ) < 1 / (M + 1 : ℝ) := by positivity
    linarith

/-- **R2b, the Möbius majorant**: `‖L(μ,s)‖ ≤ 2` for `Re s ≥ 2`. -/
theorem moebius_lseries_norm_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖LSeries ↗ArithmeticFunction.moebius s‖ ≤ 2 := by
  set g : ℕ → ℝ := fun n => if n = 0 then (0:ℝ) else 1 / (n:ℝ) ^ 2 with hg
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n
    rw [hg]
    dsimp only
    split
    · exact le_refl 0
    · positivity
  have hgle : ∀ n, g n ≤ 1 / (n:ℝ) ^ 2 := by
    intro n
    rw [hg]
    dsimp only
    split
    · rename_i h
      subst h
      norm_num
    · exact le_refl _
  have hgsum : Summable g :=
    Summable.of_nonneg_of_le hgnn hgle
      (summable_one_div_nat_pow.mpr one_lt_two)
  have hterm : ∀ n,
      ‖LSeries.term ↗ArithmeticFunction.moebius s n‖ ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [LSeries.term_zero]
      simpa using hgnn 0
    · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      rw [LSeries.term_of_ne_zero hne, norm_div,
        Complex.norm_natCast_cpow_of_pos hpos, hg]
      dsimp only
      rw [if_neg hne]
      have h1 : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have h2 : ((n:ℝ)) ^ (2:ℕ) ≤ (n:ℝ) ^ s.re := by
        have hbase : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hpos
        calc ((n:ℝ)) ^ (2:ℕ) = (n:ℝ) ^ ((2:ℕ):ℝ) :=
              (Real.rpow_natCast (n:ℝ) 2).symm
          _ ≤ (n:ℝ) ^ s.re := by
              apply Real.rpow_le_rpow_of_exponent_le hbase
              push_cast
              exact hs
      have hpow2 : (0:ℝ) < (n:ℝ) ^ (2:ℕ) := by positivity
      calc ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ / (n:ℝ) ^ s.re
          ≤ 1 / (n:ℝ) ^ (2:ℕ) := by
            apply div_le_div₀ (by norm_num) h1 hpow2 h2
        _ = 1 / (n:ℝ) ^ 2 := by norm_num
  have hnsum : Summable
      (fun n => ‖LSeries.term ↗ArithmeticFunction.moebius s n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hgsum
  calc ‖LSeries ↗ArithmeticFunction.moebius s‖
      ≤ ∑' n, ‖LSeries.term ↗ArithmeticFunction.moebius s n‖ :=
        norm_tsum_le_tsum_norm hnsum
    _ ≤ ∑' n, g n := hnsum.tsum_le_tsum hterm hgsum
    _ ≤ 2 := Real.tsum_le_of_sum_range_le hgnn partial_inv_sq_le_two

/-- **R2b: the center lower bound** — `‖ζ(s)‖ ≥ 1/2` for `Re s ≥ 2`.
The Jensen-center floor: `ζ·L(μ) = 1` forces `‖ζ‖ ≥ 1/‖L(μ)‖ ≥ 1/2`. -/
theorem zeta_center_lower_bound {s : ℂ} (hs : 2 ≤ s.re) :
    1 / 2 ≤ ‖riemannZeta s‖ := by
  have h1 : (1:ℝ) < s.re := by linarith
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (s := s) h1
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta h1] at hmul
  have hnorm : ‖riemannZeta s‖
      * ‖LSeries ↗ArithmeticFunction.moebius s‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hle := moebius_lseries_norm_le hs
  nlinarith [norm_nonneg (riemannZeta s),
    norm_nonneg (LSeries ↗ArithmeticFunction.moebius s)]

/-- The rpow analogue of the telescoping majorant: partial sums of
`n^{-σ}` (with the `n = 0` term zeroed) are at most `1 + 1/(σ-1)`. -/
theorem partial_inv_rpow_le {σ : ℝ} (hσ : 1 < σ) (m : ℕ) :
    ∑ n ∈ Finset.range m,
      (if n = 0 then (0:ℝ) else ((n:ℝ)) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hσ1 : (0:ℝ) < σ - 1 := by linarith
  match m with
  | 0 =>
    simp
    positivity
  | 1 =>
    simp
    positivity
  | (M + 2) =>
    rw [Finset.sum_range_succ' _ (M + 1), Finset.sum_range_succ' _ M]
    have h0 : (if (0:ℕ) = 0 then (0:ℝ) else ((0:ℕ):ℝ) ^ (-σ)) = 0 := by
      norm_num
    have h1 : (if (0 + 1 : ℕ) = 0 then (0:ℝ)
        else ((0 + 1 : ℕ):ℝ) ^ (-σ)) = 1 := by
      norm_num
    rw [h0, h1]
    have htail : ∑ k ∈ Finset.range M,
        (if (k + 1 + 1 : ℕ) = 0 then (0:ℝ)
          else ((k + 1 + 1 : ℕ):ℝ) ^ (-σ)) ≤ 1 / (σ - 1) := by
      have hshift : ∀ k ∈ Finset.range M,
          (if (k + 1 + 1 : ℕ) = 0 then (0:ℝ)
            else ((k + 1 + 1 : ℕ):ℝ) ^ (-σ))
          = (((1 + 1 + k : ℕ)):ℝ) ^ (-σ) := by
        intro k _
        rw [if_neg (by omega)]
        congr 2
        omega
      rw [Finset.sum_congr rfl hshift]
      have := rpow_tail_partial (N := 1) le_rfl hσ M
      calc ∑ k ∈ Finset.range M, (((1 + 1 + k : ℕ)):ℝ) ^ (-σ)
          ≤ ((1:ℕ):ℝ) ^ (1 - σ) / (σ - 1) := this
        _ = 1 / (σ - 1) := by
            rw [Nat.cast_one, Real.one_rpow]
    linarith

/-- **The Möbius majorant on the full half-plane** `Re s > 1`:
`‖L(μ,s)‖ ≤ 1 + 1/(Re s − 1)`.  No zeta value appears — the majorant
is the integral-comparison bound on `Σ n^{-σ}`. -/
theorem moebius_lseries_norm_le_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries ↗ArithmeticFunction.moebius s‖ ≤ 1 + 1 / (s.re - 1) := by
  set g : ℕ → ℝ := fun n => if n = 0 then (0:ℝ) else ((n:ℝ)) ^ (-s.re)
    with hg
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n
    rw [hg]
    dsimp only
    split
    · exact le_refl 0
    · positivity
  have hgsum : Summable g :=
    summable_of_sum_range_le hgnn (partial_inv_rpow_le hs)
  have hterm : ∀ n,
      ‖LSeries.term ↗ArithmeticFunction.moebius s n‖ ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [LSeries.term_zero]
      simpa using hgnn 0
    · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      rw [LSeries.term_of_ne_zero hne, norm_div,
        Complex.norm_natCast_cpow_of_pos hpos, hg]
      dsimp only
      rw [if_neg hne]
      have h1 : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hpos
      rw [Real.rpow_neg hnpos.le, ← one_div]
      apply div_le_div₀ (by norm_num) h1 (by positivity) (le_refl _)
  have hnsum : Summable
      (fun n => ‖LSeries.term ↗ArithmeticFunction.moebius s n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hgsum
  calc ‖LSeries ↗ArithmeticFunction.moebius s‖
      ≤ ∑' n, ‖LSeries.term ↗ArithmeticFunction.moebius s n‖ :=
        norm_tsum_le_tsum_norm hnsum
    _ ≤ ∑' n, g n := hnsum.tsum_le_tsum hterm hgsum
    _ ≤ 1 + 1 / (s.re - 1) :=
        Real.tsum_le_of_sum_range_le hgnn (partial_inv_rpow_le hs)

/-- **The movable center floor**: `(σ−1)/σ ≤ ‖ζ(s)‖` for `σ = Re s > 1`.
At `σ = 1 + 1/log T` this is `≥ 1/(log T + 1)` — the Jensen-center
input of the local count. -/
theorem zeta_center_floor {s : ℂ} (hs : 1 < s.re) :
    (s.re - 1) / s.re ≤ ‖riemannZeta s‖ := by
  have hσ1 : (0:ℝ) < s.re - 1 := by linarith
  have hσpos : (0:ℝ) < s.re := by linarith
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (s := s) hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hmul
  have hnorm : ‖riemannZeta s‖
      * ‖LSeries ↗ArithmeticFunction.moebius s‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hle : ‖LSeries ↗ArithmeticFunction.moebius s‖ ≤ s.re / (s.re - 1) := by
    have := moebius_lseries_norm_le_of_one_lt hs
    have hrw : 1 + 1 / (s.re - 1) = s.re / (s.re - 1) := by
      field_simp
      ring
    linarith [hrw ▸ this]
  have hbpos : (0:ℝ) < ‖LSeries ↗ArithmeticFunction.moebius s‖ := by
    rcases (norm_nonneg
        (LSeries ↗ArithmeticFunction.moebius s)).lt_or_eq with h | h
    · exact h
    · rw [← h] at hnorm
      simp at hnorm
  apply le_of_mul_le_mul_right _ hbpos
  calc (s.re - 1) / s.re * ‖LSeries ↗ArithmeticFunction.moebius s‖
      ≤ (s.re - 1) / s.re * (s.re / (s.re - 1)) := by
        apply mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 := by field_simp
    _ = ‖riemannZeta s‖
        * ‖LSeries ↗ArithmeticFunction.moebius s‖ := hnorm.symm

end CenterLowerBound

set_option maxHeartbeats 1600000 in
/-- **R2c: the movable-center local zero count.**  At the Jensen center
`c = 1 + 1/log T + iT` the disk `B(c, 1/8)` holds at most `8·log T`
zeros of `ζ` **with multiplicity** (the divisor sum).  Assembly of
mathlib's Jensen inequality (`AnalyticOnNhd.sum_divisor_le`) with the
compiled polynomial growth bound (sphere) and Möbius center floor. -/
theorem zeta_local_zero_count {T : ℝ} (hT : Real.exp 2 ≤ T) :
    (↑(∑ᶠ u, MeromorphicOn.divisor riemannZeta
        (Metric.closedBall (((1 + 1 / Real.log T : ℝ) : ℂ) + T * Complex.I)
          (1/8)) u) : ℝ)
      ≤ 8 * Real.log T := by
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 2) hT
  have hL2 : (2:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 2) hT
    rwa [Real.log_exp] at this
  have hT7 : (7:ℝ) ≤ T := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  set L : ℝ := Real.log T with hLdef
  have hLpos : (0:ℝ) < L := by linarith
  set c : ℂ := ((1 + 1 / L : ℝ) : ℂ) + T * Complex.I with hcdef
  have hcre : c.re = 1 + 1 / L := by
    rw [hcdef]; simp
  have hcim : c.im = T := by
    rw [hcdef]; simp
  have hinvL : (0:ℝ) < 1 / L := by positivity
  have hinvL2 : 1 / L ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le
    · norm_num
    · linarith
  have hT14ge1 : (1:ℝ) ≤ T ^ ((1:ℝ)/4) := by
    calc (1:ℝ) = 1 ^ ((1:ℝ)/4) := (Real.one_rpow _).symm
      _ ≤ T ^ ((1:ℝ)/4) := Real.rpow_le_rpow (by norm_num) (by linarith)
        (by norm_num)
  -- Analyticity on the closed ball (the pole at 1 is at distance ≥ T)
  have hanal : AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall c |(1/4 : ℝ)|) := by
    apply AnalyticOnNhd.mono
      (DifferentiableOn.analyticOnNhd
        (f := riemannZeta) (s := {z : ℂ | z ≠ 1})
        (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
        isOpen_ne)
    intro z hz
    simp only [Metric.mem_closedBall] at hz
    intro h1
    rw [h1, dist_eq_norm] at hz
    have him : |((1:ℂ) - c).im| ≤ ‖(1:ℂ) - c‖ := Complex.abs_im_le_norm _
    have : ((1:ℂ) - c).im = -T := by
      simp [Complex.sub_im, hcim]
    rw [this, abs_neg, abs_of_pos hTpos] at him
    have : |(1/4 : ℝ)| = 1/4 := by norm_num
    rw [this] at hz
    linarith
  -- Center nonvanishing
  have hcre1 : (1:ℝ) < c.re := by
    rw [hcre]; linarith
  have hζc : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hcre1
  -- Sphere bound from B2′
  have hbound : ∀ z ∈ Metric.sphere c |(1/4 : ℝ)|,
      ‖riemannZeta z‖ ≤ 32 * T ^ ((1:ℝ)/4) := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have habs14 : |(1/4 : ℝ)| = 1/4 := by norm_num
    rw [habs14] at hz
    have hre : |(z - c).re| ≤ 1/4 := hz ▸ Complex.abs_re_le_norm _
    have him : |(z - c).im| ≤ 1/4 := hz ▸ Complex.abs_im_le_norm _
    rw [Complex.sub_re, hcre] at hre
    rw [Complex.sub_im, hcim] at him
    rw [abs_le] at hre him
    have hzim2 : (2:ℝ) ≤ |z.im| := by
      rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
      linarith
    have hzrel : (3:ℝ)/4 ≤ z.re := by linarith
    have hzreu : z.re ≤ 2 := by linarith
    have hgrowth := zeta_polynomial_growth hzim2 hzrel hzreu
    have hzimT : |z.im| ≤ 2 * T := by
      rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
      linarith
    calc ‖riemannZeta z‖ ≤ 16 * |z.im| ^ ((1:ℝ)/4) := hgrowth
      _ ≤ 16 * (2 * T) ^ ((1:ℝ)/4) := by
          apply mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg _) hzimT (by norm_num))
            (by norm_num)
      _ = 16 * ((2:ℝ) ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/4)) := by
          rw [Real.mul_rpow (by norm_num) hTpos.le]
      _ ≤ 16 * (2 * T ^ ((1:ℝ)/4)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _
            (Real.rpow_nonneg hTpos.le _)
          calc (2:ℝ) ^ ((1:ℝ)/4) ≤ 2 ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
      _ = 32 * T ^ ((1:ℝ)/4) := by ring
  have hM1 : (1:ℝ) ≤ 32 * T ^ ((1:ℝ)/4) := by nlinarith
  -- Jensen's inequality, movable center
  have hjensen := AnalyticOnNhd.sum_divisor_le
    (c := c) (r := 1/8) (R := 1/4) (M := 32 * T ^ ((1:ℝ)/4))
    (f := riemannZeta) (by norm_num) (by norm_num) hM1 hanal hζc hbound
  have habs18 : |(1/8 : ℝ)| = 1/8 := by norm_num
  rw [habs18] at hjensen
  refine le_trans hjensen ?_
  -- The right-hand side: log(M/‖ζ(c)‖)/log 2 ≤ 8·L
  have hfloor : 1 / (L + 1) ≤ ‖riemannZeta c‖ := by
    have h := zeta_center_floor hcre1
    have : (c.re - 1) / c.re = 1 / (L + 1) := by
      rw [hcre]
      field_simp
      ring
    rwa [this] at h
  have hζcpos : (0:ℝ) < ‖riemannZeta c‖ :=
    lt_of_lt_of_le (by positivity) hfloor
  have hquot : 32 * T ^ ((1:ℝ)/4) / ‖riemannZeta c‖
      ≤ 32 * T ^ ((1:ℝ)/4) * (L + 1) := by
    rw [div_le_iff₀ hζcpos]
    calc 32 * T ^ ((1:ℝ)/4)
        = 32 * T ^ ((1:ℝ)/4) * (L + 1) * (1 / (L + 1)) := by
          field_simp
      _ ≤ 32 * T ^ ((1:ℝ)/4) * (L + 1) * ‖riemannZeta c‖ := by
          apply mul_le_mul_of_nonneg_left hfloor
          positivity
  have hRr : Real.log ((1/4 : ℝ) / (1/8 : ℝ)) = Real.log 2 := by
    norm_num
  rw [hRr]
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ hlog2pos]
  -- Numerator: log(M/‖ζc‖) ≤ log 32 + L/4 + log(L+1) ≤ 3L
  have hnum : Real.log (32 * T ^ ((1:ℝ)/4) / ‖riemannZeta c‖)
      ≤ 3 * L := by
    have hstep1 : Real.log (32 * T ^ ((1:ℝ)/4) / ‖riemannZeta c‖)
        ≤ Real.log (32 * T ^ ((1:ℝ)/4) * (L + 1)) := by
      apply Real.log_le_log (by positivity) hquot
    have hsplit : Real.log (32 * T ^ ((1:ℝ)/4) * (L + 1))
        = Real.log 32 + (1/4) * L + Real.log (L + 1) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity),
        Real.log_rpow hTpos]
    have hlog32 : Real.log 32 ≤ 3.5 := by
      have h32 : (32:ℝ) = 2 ^ (5:ℕ) := by norm_num
      rw [h32, Real.log_pow]
      push_cast
      nlinarith [Real.log_two_lt_d9]
    have hlogL1 : Real.log (L + 1) ≤ L := by
      calc Real.log (L + 1) ≤ (L + 1) - 1 :=
          Real.log_le_sub_one_of_pos (by linarith)
        _ = L := by ring
    calc Real.log (32 * T ^ ((1:ℝ)/4) / ‖riemannZeta c‖)
        ≤ Real.log 32 + (1/4) * L + Real.log (L + 1) := by
          rw [← hsplit]; exact hstep1
      _ ≤ 3.5 + (1/4) * L + L := by linarith
      _ ≤ 3 * L := by linarith
  calc Real.log (32 * T ^ ((1:ℝ)/4) / ‖riemannZeta c‖)
      ≤ 3 * L := hnum
    _ ≤ 8 * L * Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]

set_option maxHeartbeats 3200000 in
/-- **R4ζ: the partial-fraction inequality for ζ at the movable center.**
At `c = 1 + 1/log T + iT`, for every `s` within `1/32` of `c` where
`ζ(s) ≠ 0`:
`‖ζ'/ζ(s) − Σ_ρ m_ρ/(s−ρ)‖ ≤ 300·log T`, the sum over the divisor of
`B(c, 1/8)`, with certificates that the `ρ` are genuine zeros. -/
theorem zeta_partial_fraction {T : ℝ} (hT : Real.exp 2 ≤ T) :
    ∃ (S : Finset ℂ) (n : ℂ → ℕ),
      (∀ u ∈ S, u ∈ Metric.closedBall
        (((1 + 1 / Real.log T : ℝ) : ℂ) + T * Complex.I) (1/8)) ∧
      (∀ u ∈ S, 1 ≤ n u → riemannZeta u = 0) ∧
      (∀ u ∈ Metric.closedBall
        (((1 + 1 / Real.log T : ℝ) : ℂ) + T * Complex.I) (1/8),
        riemannZeta u = 0 → u ∈ S ∧ 1 ≤ n u) ∧
      ∀ s ∈ Metric.closedBall
          (((1 + 1 / Real.log T : ℝ) : ℂ) + T * Complex.I) (1/32),
        riemannZeta s ≠ 0 →
        ‖logDeriv riemannZeta s - ∑ u ∈ S, (n u : ℂ) / (s - u)‖
          ≤ 300 * Real.log T := by
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 2) hT
  have hL2 : (2:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 2) hT
    rwa [Real.log_exp] at this
  have hT7 : (7:ℝ) ≤ T := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_one_gt_d9]
  set L : ℝ := Real.log T with hLdef
  have hLpos : (0:ℝ) < L := by linarith
  set c : ℂ := ((1 + 1 / L : ℝ) : ℂ) + T * Complex.I with hcdef
  have hcre : c.re = 1 + 1 / L := by
    rw [hcdef]
    simp
  have hcim : c.im = T := by
    rw [hcdef]
    simp
  have hinvL : (0:ℝ) < 1 / L := by positivity
  have hinvL2 : 1 / L ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le
    · norm_num
    · linarith
  have hT14ge1 : (1:ℝ) ≤ T ^ ((1:ℝ)/4) := by
    calc (1:ℝ) = 1 ^ ((1:ℝ)/4) := (Real.one_rpow _).symm
      _ ≤ T ^ ((1:ℝ)/4) := Real.rpow_le_rpow (by norm_num) (by linarith)
        (by norm_num)
  -- analyticity on the 1/8-ball
  have hanal : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c (1/8)) := by
    apply AnalyticOnNhd.mono
      (DifferentiableOn.analyticOnNhd
        (f := riemannZeta) (s := {z : ℂ | z ≠ 1})
        (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
        isOpen_ne)
    intro z hz
    simp only [Metric.mem_closedBall] at hz
    intro h1
    rw [h1, dist_eq_norm] at hz
    have him : |((1:ℂ) - c).im| ≤ ‖(1:ℂ) - c‖ := Complex.abs_im_le_norm _
    have : ((1:ℂ) - c).im = -T := by
      simp [Complex.sub_im, hcim]
    rw [this, abs_neg, abs_of_pos hTpos] at him
    linarith
  -- the M-bound on the 1/8-ball
  have hM : ∀ z ∈ Metric.closedBall c (1/8),
      ‖riemannZeta z‖ ≤ 32 * T ^ ((1:ℝ)/4) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre : |(z - c).re| ≤ 1/8 := le_trans (Complex.abs_re_le_norm _) hz
    have him : |(z - c).im| ≤ 1/8 := le_trans (Complex.abs_im_le_norm _) hz
    rw [Complex.sub_re, hcre] at hre
    rw [Complex.sub_im, hcim] at him
    rw [abs_le] at hre him
    have hzim2 : (2:ℝ) ≤ |z.im| := by
      rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
      linarith
    have hgrowth := zeta_polynomial_growth hzim2 (by linarith) (by linarith)
    have hzimT : |z.im| ≤ 2 * T := by
      rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
      linarith
    calc ‖riemannZeta z‖ ≤ 16 * |z.im| ^ ((1:ℝ)/4) := hgrowth
      _ ≤ 16 * (2 * T) ^ ((1:ℝ)/4) := by
          apply mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg _) hzimT (by norm_num))
            (by norm_num)
      _ = 16 * ((2:ℝ) ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/4)) := by
          rw [Real.mul_rpow (by norm_num) hTpos.le]
      _ ≤ 16 * (2 * T ^ ((1:ℝ)/4)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _
            (Real.rpow_nonneg hTpos.le _)
          calc (2:ℝ) ^ ((1:ℝ)/4) ≤ 2 ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
      _ = 32 * T ^ ((1:ℝ)/4) := by ring
  -- the center floor
  have hcre1 : (1:ℝ) < c.re := by
    rw [hcre]
    linarith
  have hfloor : 1 / (L + 1) ≤ ‖riemannZeta c‖ := by
    have h := zeta_center_floor hcre1
    have heq : (c.re - 1) / c.re = 1 / (L + 1) := by
      rw [hcre]
      field_simp
      ring
    rwa [heq] at h
  have hmpos : (0:ℝ) < 1 / (L + 1) := by positivity
  -- log(M/m) bounds
  have hMm : 32 * T ^ ((1:ℝ)/4) / (1 / (L + 1))
      = 32 * T ^ ((1:ℝ)/4) * (L + 1) := by
    field_simp
  have hlogpos : 0 < Real.log (32 * T ^ ((1:ℝ)/4) / (1 / (L + 1))) := by
    rw [hMm]
    apply Real.log_pos
    nlinarith
  have hlog3L : Real.log (32 * T ^ ((1:ℝ)/4) / (1 / (L + 1))) ≤ 3 * L := by
    rw [hMm]
    have hsplit : Real.log (32 * T ^ ((1:ℝ)/4) * (L + 1))
        = Real.log 32 + (1/4) * L + Real.log (L + 1) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity),
        Real.log_rpow hTpos]
    have hlog32 : Real.log 32 ≤ 3.5 := by
      have h32 : (32:ℝ) = 2 ^ (5:ℕ) := by norm_num
      rw [h32, Real.log_pow]
      push_cast
      nlinarith [Real.log_two_lt_d9]
    have hlogL1 : Real.log (L + 1) ≤ L := by
      calc Real.log (L + 1) ≤ (L + 1) - 1 :=
          Real.log_le_sub_one_of_pos (by linarith)
        _ = L := by ring
    rw [hsplit]
    linarith
  -- Landau's lemma at (c, 1/8)
  obtain ⟨S, n, hS_mem, hn_eq, hd_zero, hbound⟩ :=
    landau_lemma (c := c) (r := 1/8) (by norm_num) hmpos hanal hM hfloor
      hlogpos
  refine ⟨S, n, hS_mem, ?_, ?_, ?_⟩
  · -- zero certificates
    intro u hu hnu
    by_contra hζu
    have hord : analyticOrderAt riemannZeta u = 0 :=
      (hanal u (hS_mem u hu)).analyticOrderAt_eq_zero.mpr hζu
    have hdiv := hn_eq u hu
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanal (hS_mem u hu),
      hord] at hdiv
    simp at hdiv
    omega
  · -- completeness: every zero in the ball is seated in S with n ≥ 1
    intro u hu hζu
    have hζc : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hcre1
    have hordne : analyticOrderAt riemannZeta u ≠ 0 := by
      rw [analyticOrderAt_ne_zero]
      exact ⟨hanal u hu, hζu⟩
    have hordtop : analyticOrderAt riemannZeta u ≠ ⊤ :=
      analyticOrderAt_ne_top_of_ne_zero
        (convex_closedBall c (1/8)).isPreconnected hanal
        (Metric.mem_closedBall_self (by norm_num)) hζc hu
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℕ∞) = analyticOrderAt riemannZeta u :=
      ENat.ne_top_iff_exists.mp hordtop
    have hm_ne : m ≠ 0 := fun h => hordne (by rw [← hm, h]; rfl)
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm_ne
    have hdivge : 1 ≤ MeromorphicOn.divisor riemannZeta
        (Metric.closedBall c (1/8)) u := by
      rw [MeromorphicOn.divisor_apply hanal.meromorphicOn hu,
        (hanal u hu).meromorphicOrderAt_eq, ← hm]
      simp
      exact hm1
    have huS : u ∈ S := by
      by_contra huS
      have := hd_zero u huS
      omega
    refine ⟨huS, ?_⟩
    have := hn_eq u huS
    omega
  · intro s hs hζs
    have hs32 : s ∈ Metric.closedBall c ((1/8)/4) := by
      have := Metric.mem_closedBall.mp hs
      rw [Metric.mem_closedBall]
      linarith
    have hb := hbound s hs32 hζs
    -- N ≤ 8·L via the local count
    have hNle : (∑ u ∈ S, (n u : ℝ)) ≤ 8 * L := by
      have hsupp : Function.support
          (fun u => MeromorphicOn.divisor riemannZeta
            (Metric.closedBall c (1/8)) u) ⊆ (S : Set ℂ) := by
        intro u hu
        by_contra huS
        exact hu (hd_zero u huS)
      have hfin : (∑ᶠ u, MeromorphicOn.divisor riemannZeta
          (Metric.closedBall c (1/8)) u)
          = ∑ u ∈ S, MeromorphicOn.divisor riemannZeta
              (Metric.closedBall c (1/8)) u :=
        finsum_eq_sum_of_support_subset _ hsupp
      have hcast : (∑ u ∈ S, (n u : ℝ))
          = ((∑ᶠ u, MeromorphicOn.divisor riemannZeta
              (Metric.closedBall c (1/8)) u : ℤ) : ℝ) := by
        rw [hfin]
        push_cast
        apply Finset.sum_congr rfl
        intro u hu
        exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) (hn_eq u hu)
      rw [hcast]
      exact zeta_local_zero_count hT
    -- assemble the constants
    calc ‖logDeriv riemannZeta s - ∑ u ∈ S, (n u : ℂ) / (s - u)‖
        ≤ 8 * Real.log (32 * T ^ ((1:ℝ)/4) / (1 / (L + 1))) / (1/8)
          + (∑ u ∈ S, (n u : ℝ)) * (4 / (3 * (1/8))) := hb
      _ ≤ 8 * (3 * L) / (1/8) + (8 * L) * (4 / (3 * (1/8))) := by
          apply add_le_add
          · apply div_le_div_of_nonneg_right _ (by norm_num)
            apply mul_le_mul_of_nonneg_left hlog3L (by norm_num)
          · apply mul_le_mul_of_nonneg_right hNle (by norm_num)
      _ = 192 * L + (256/3) * L := by ring
      _ ≤ 300 * L := by linarith

section PoleRung
/-!
## R3: the real-axis pole rung

`‖ζ'/ζ(σ)‖ ≤ 10/(σ-1)` for `σ ∈ (1, 9/8]`.  DC first: the N=1 truncated
representation gives `ζ(σ) = 1 + 1/(σ-1) - σ·Tail` EXACTLY; only the tail
is estimated (`‖Tail‖ ≤ 1 + 1/σ`).  The derivative comes from Cauchy on
the compiled majorant `‖ζ(z)‖ ≤ 1 + 1/(Re z - 1)`.
-/

/-- The norm majorant on the open half-plane: `‖ζ(z)‖ ≤ 1 + 1/(Re z − 1)`. -/
theorem zeta_norm_le_of_one_lt {z : ℂ} (hz : 1 < z.re) :
    ‖riemannZeta z‖ ≤ 1 + 1 / (z.re - 1) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
    linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hz]
  set g : ℕ → ℝ := fun n => if n = 0 then (0:ℝ) else ((n:ℝ)) ^ (-z.re)
    with hg
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n
    rw [hg]
    dsimp only
    split
    · exact le_refl 0
    · positivity
  have hgsum : Summable g :=
    summable_of_sum_range_le hgnn (partial_inv_rpow_le hz)
  have hterm : ∀ n : ℕ, ‖1 / ((n:ℂ)) ^ z‖ ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [Nat.cast_zero, zero_cpow hz0]
      simpa using hgnn 0
    · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hpos, hg]
      dsimp only
      rw [if_neg hne]
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hpos
      rw [Real.rpow_neg hnpos.le, ← one_div]
  have hnsum : Summable (fun n : ℕ => ‖1 / ((n:ℂ)) ^ z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hgsum
  calc ‖∑' n : ℕ, 1 / ((n:ℂ)) ^ z‖
      ≤ ∑' n : ℕ, ‖1 / ((n:ℂ)) ^ z‖ := norm_tsum_le_tsum_norm hnsum
    _ ≤ ∑' n, g n := hnsum.tsum_le_tsum hterm hgsum
    _ ≤ 1 + 1 / (z.re - 1) :=
        Real.tsum_le_of_sum_range_le hgnn (partial_inv_rpow_le hz)

/-- **The pole floor, exactly**: `Re ζ(σ) ≥ 1/(2(σ−1))` on `(1, 9/8]`,
from the N=1 truncated representation
`ζ(σ) = 1 + 1/(σ−1) − σ·Tail`, `‖Tail‖ ≤ 1 + 1/σ ≤ 2`. -/
theorem zeta_re_pole_floor {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 9/8) :
    1 / (2 * (σ - 1)) ≤ (riemannZeta ((σ:ℝ):ℂ)).re := by
  have hs1 : ((σ:ℝ):ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hσre : (0:ℝ) < (((σ:ℝ):ℂ)).re := by
    simp
    linarith
  rw [truncated_zeta_pos_re (N := 1) le_rfl hσre hs1]
  unfold truncatedRep
  -- head at N = 1: 0 + 1
  have hhead : (∑ n ∈ Finset.range (1 + 1), (((n : ℝ)) : ℂ) ^ (-((σ:ℝ):ℂ)))
      = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : (((0 : ℕ) : ℝ) : ℂ) ^ (-((σ:ℝ):ℂ)) = 0 := by
      rw [Nat.cast_zero, Complex.ofReal_zero, zero_cpow]
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have h1' : (((1 : ℕ) : ℝ) : ℂ) ^ (-((σ:ℝ):ℂ)) = 1 := by
      rw [Nat.cast_one, Complex.ofReal_one, one_cpow]
    rw [h0, h1']
    ring
  -- boundary at N = 1: 1/(σ−1)
  have hbdry : (((1:ℕ) : ℝ) : ℂ) ^ (1 - ((σ:ℝ):ℂ)) / (((σ:ℝ):ℂ) - 1)
      = 1 / (((σ:ℝ):ℂ) - 1) := by
    rw [Nat.cast_one, Complex.ofReal_one, one_cpow]
  rw [hhead, hbdry]
  -- the tail bound
  set Tail : ℂ := ∑' k : ℕ, ∫ x : ℝ in ((1 + k : ℕ) : ℝ)..(((1 + k : ℕ) : ℝ) + 1),
    ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ:ℝ):ℂ) - 1) with hTail
  have hp1 : (1:ℝ) < σ + 1 := by linarith
  have hmaj_sum : Summable (fun k : ℕ => (((1 + k : ℕ)):ℝ) ^ (-(σ + 1))) := by
    have hbase : Summable (fun n : ℕ => ((n:ℝ)) ^ (-(σ + 1))) := by
      rw [Real.summable_nat_rpow]
      linarith
    apply Summable.congr ((summable_nat_add_iff 1).mpr hbase)
    intro k
    congr 2
    omega
  have hterm_le : ∀ k : ℕ,
      ‖∫ x : ℝ in ((1 + k : ℕ) : ℝ)..(((1 + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ:ℝ):ℂ) - 1)‖
      ≤ (((1 + k : ℕ)):ℝ) ^ (-(σ + 1)) := by
    intro k
    have := interval_fract_norm_le (n := 1 + k) (by omega)
      (s := ((σ:ℝ):ℂ)) (by simp; linarith)
    have hexp : (-(((σ:ℝ):ℂ)).re - 1) = -(σ + 1) := by
      rw [Complex.ofReal_re]
      ring
    rw [hexp] at this
    exact this
  have hTail_sum : Summable (fun k : ℕ =>
      ‖∫ x : ℝ in ((1 + k : ℕ) : ℝ)..(((1 + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ:ℝ):ℂ) - 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le hmaj_sum
  have hmaj_tsum : (∑' k : ℕ, (((1 + k : ℕ)):ℝ) ^ (-(σ + 1)))
      ≤ 1 + 1/σ := by
    rw [hmaj_sum.tsum_eq_zero_add]
    have hz : (((1 + 0 : ℕ)):ℝ) ^ (-(σ + 1)) = 1 := by
      norm_num
    rw [hz]
    have hshift : (∑' k : ℕ, (((1 + (k + 1) : ℕ)):ℝ) ^ (-(σ + 1)))
        ≤ 1/σ := by
      have hcongr : ∀ k : ℕ, (((1 + (k + 1) : ℕ)):ℝ) ^ (-(σ + 1))
          = (((1 + 1 + k : ℕ)):ℝ) ^ (-(σ + 1)) := by
        intro k
        congr 2
        omega
      rw [tsum_congr hcongr]
      have := rpow_tail_tsum_le (N := 1) le_rfl hp1
      calc (∑' k : ℕ, (((1 + 1 + k : ℕ)):ℝ) ^ (-(σ + 1)))
          ≤ (((1:ℕ)):ℝ) ^ (1 - (σ + 1)) / ((σ + 1) - 1) := this
        _ = 1/σ := by
            rw [Nat.cast_one, Real.one_rpow]
            ring_nf
    linarith
  have hTail_norm : ‖Tail‖ ≤ 1 + 1/σ := by
    rw [hTail]
    calc ‖∑' k : ℕ, ∫ x : ℝ in ((1 + k : ℕ) : ℝ)..(((1 + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ:ℝ):ℂ) - 1)‖
        ≤ ∑' k : ℕ,
          ‖∫ x : ℝ in ((1 + k : ℕ) : ℝ)..(((1 + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ:ℝ):ℂ) - 1)‖ :=
          norm_tsum_le_tsum_norm hTail_sum
      _ ≤ ∑' k : ℕ, (((1 + k : ℕ)):ℝ) ^ (-(σ + 1)) :=
          hTail_sum.tsum_le_tsum hterm_le hmaj_sum
      _ ≤ 1 + 1/σ := hmaj_tsum
  -- assemble the real part
  have hre_bdry : (1 / (((σ:ℝ):ℂ) - 1)).re = 1/(σ - 1) := by
    rw [show ((σ:ℝ):ℂ) - 1 = (((σ - 1 : ℝ)):ℂ) by push_cast; ring,
      one_div, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  have hre_tail : (((σ:ℝ):ℂ) * Tail).re ≤ σ * (1 + 1/σ) := by
    calc (((σ:ℝ):ℂ) * Tail).re ≤ ‖((σ:ℝ):ℂ) * Tail‖ := Complex.re_le_norm _
      _ = σ * ‖Tail‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith : (0:ℝ) < σ)]
      _ ≤ σ * (1 + 1/σ) :=
          mul_le_mul_of_nonneg_left hTail_norm (by linarith)
  have hσ1 : (0:ℝ) < σ - 1 := by linarith
  calc 1 / (2 * (σ - 1))
      ≤ 1 + 1/(σ - 1) - σ * (1 + 1/σ) := by
        have hexp : σ * (1 + 1/σ) = σ + 1 := by
          field_simp
        rw [hexp]
        have hkey : 1/(2*(σ-1)) ≤ 1/(σ-1) - σ := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*(σ-1))]
          have hprod : (1/(σ-1) - σ) * (2*(σ-1)) = 2 - 2*σ*(σ-1) := by
            field_simp
          rw [hprod]
          nlinarith
        linarith
    _ ≤ 1 + (1 / (((σ:ℝ):ℂ) - 1)).re - (((σ:ℝ):ℂ) * Tail).re := by
        rw [hre_bdry]
        linarith [hre_tail]
    _ = (1 + 1 / (((σ:ℝ):ℂ) - 1) - ((σ:ℝ):ℂ) * Tail).re := by
        simp [Complex.add_re, Complex.sub_re]

/-- **The Cauchy derivative bound at the pole**:
`‖ζ'(σ)‖ ≤ 5/(σ−1)²` on `(1, 9/8]`. -/
theorem zeta_deriv_pole_bound {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 9/8) :
    ‖deriv riemannZeta ((σ:ℝ):ℂ)‖ ≤ 5 / (σ - 1)^2 := by
  have hσ1 : (0:ℝ) < σ - 1 := by linarith
  set r : ℝ := (σ - 1)/2 with hrdef
  have hrpos : (0:ℝ) < r := by positivity
  have hre_ball : ∀ z ∈ Metric.closedBall (((σ:ℝ):ℂ)) r,
      (σ + 1)/2 ≤ z.re := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - ((σ:ℝ):ℂ))
    rw [Complex.sub_re] at this
    have hre : |z.re - σ| ≤ r := by
      simp only [Complex.ofReal_re] at this
      linarith
    rw [abs_le] at hre
    rw [hrdef] at hre
    linarith [hre.1]
  have hd : DiffContOnCl ℂ riemannZeta (Metric.ball (((σ:ℝ):ℂ)) r) := by
    constructor
    · intro z hz
      have hzre := hre_ball z (Metric.ball_subset_closedBall hz)
      have hz1 : z ≠ 1 := by
        intro h
        rw [h] at hzre
        simp at hzre
        linarith
      exact (differentiableAt_riemannZeta hz1).differentiableWithinAt
    · intro z hz
      rw [closure_ball _ hrpos.ne'] at hz
      have hzre := hre_ball z hz
      have hz1 : z ≠ 1 := by
        intro h
        rw [h] at hzre
        simp at hzre
        linarith
      exact (differentiableAt_riemannZeta hz1).continuousAt.continuousWithinAt
  have hC : ∀ z ∈ Metric.sphere (((σ:ℝ):ℂ)) r,
      ‖riemannZeta z‖ ≤ 1 + 2/(σ - 1) := by
    intro z hz
    have hzre := hre_ball z (Metric.sphere_subset_closedBall hz)
    have hz1 : (1:ℝ) < z.re := by linarith
    calc ‖riemannZeta z‖ ≤ 1 + 1/(z.re - 1) := zeta_norm_le_of_one_lt hz1
      _ ≤ 1 + 2/(σ - 1) := by
          have hlow : (σ - 1)/2 ≤ z.re - 1 := by linarith
          have h2' : 1/(z.re - 1) ≤ 1/((σ - 1)/2) := by
            apply one_div_le_one_div_of_le (by positivity) hlow
          have : 1/((σ - 1)/2) = 2/(σ - 1) := by
            field_simp
          linarith [this ▸ h2']
  have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hd hC
  calc ‖deriv riemannZeta ((σ:ℝ):ℂ)‖ ≤ (1 + 2/(σ - 1)) / r := hcauchy
    _ = 2/(σ - 1) + 4/(σ - 1)^2 := by
        rw [hrdef]
        field_simp
        ring
    _ ≤ 5 / (σ - 1)^2 := by
        have h24 : 2/(σ-1) ≤ 1/(σ-1)^2 := by
          rw [div_le_div_iff₀ hσ1 (by positivity)]
          nlinarith [mul_nonneg hσ1.le
            (by linarith : (0:ℝ) ≤ 1 - 2*(σ-1))]
        have h45 : 4/(σ-1)^2 + 1/(σ-1)^2 = 5/(σ-1)^2 := by ring
        linarith

/-- **R3: the pole rung** — `‖ζ'/ζ(σ)‖ ≤ 10/(σ−1)` on `(1, 9/8]`. -/
theorem zeta_logDeriv_pole_rung {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 9/8) :
    ‖logDeriv riemannZeta ((σ:ℝ):ℂ)‖ ≤ 10 / (σ - 1) := by
  have hσ1 : (0:ℝ) < σ - 1 := by linarith
  have hfloor := zeta_re_pole_floor h1 h2
  have hnorm_ge : 1/(2*(σ-1)) ≤ ‖riemannZeta ((σ:ℝ):ℂ)‖ :=
    le_trans hfloor (Complex.re_le_norm _)
  have hpos : (0:ℝ) < 1/(2*(σ-1)) := by positivity
  rw [logDeriv_apply, norm_div]
  calc ‖deriv riemannZeta ((σ:ℝ):ℂ)‖ / ‖riemannZeta ((σ:ℝ):ℂ)‖
      ≤ (5/(σ-1)^2) / (1/(2*(σ-1))) := by
        apply div_le_div₀ (by positivity) (zeta_deriv_pole_bound h1 h2)
          hpos hnorm_ge
    _ = 10 / (σ - 1) := by
        field_simp
        ring

end PoleRung

section ThreeFourOne
/-!
## R5a: the 3-4-1 positivity

`0 ≤ Re(3·L(Λ,σ) + 4·L(Λ,σ+it) + L(Λ,σ+2it))` — termwise
`Λ(n)n^{-σ}(3 + 4cos θ + cos 2θ) = 2Λ(n)n^{-σ}(1+cos θ)² ≥ 0`.
-/

open scoped LSeries.notation

/-- The real part of each von Mangoldt L-series term:
`Λ(n)·n^{-σ}·cos(t·log n)`. -/
theorem vonMangoldt_term_re (σ t : ℝ) (n : ℕ) :
    (LSeries.term (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
      (((σ:ℝ):ℂ) + (t:ℝ) * Complex.I) n).re
      = if n = 0 then 0 else
          ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ)
            * Real.cos (t * Real.log n) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    rw [LSeries.term_zero]
    simp
  · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hpos
    rw [LSeries.term_of_ne_zero hne, if_neg hne]
    have hnC : ((n:ℕ):ℂ) ≠ 0 := by
      exact_mod_cast hne
    rw [div_eq_mul_inv, ← Complex.cpow_neg]
    have hlog : Complex.log ((n:ℕ):ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.natCast_log]
    rw [Complex.cpow_def_of_ne_zero hnC, hlog]
    have harg : ((Real.log n : ℝ) : ℂ) * (-((((σ:ℝ):ℂ)) + (t:ℝ) * Complex.I))
        = ((-σ * Real.log n : ℝ) : ℂ)
          + ((-t * Real.log n : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg]
    have hexp_re : (Complex.exp (((-σ * Real.log n : ℝ) : ℂ)
        + ((-t * Real.log n : ℝ) : ℂ) * Complex.I)).re
        = Real.exp (-σ * Real.log n) * Real.cos (-t * Real.log n) := by
      rw [Complex.exp_re]
      congr 2
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_re, Complex.I_im]
        ring
    have hmul_re : ∀ w : ℂ,
        (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * w).re
          = ArithmeticFunction.vonMangoldt n * w.re := by
      intro w
      rw [Complex.mul_re]
      simp
    rw [hmul_re, hexp_re]
    have hrpow : Real.exp (-σ * Real.log (n:ℝ)) = ((n:ℝ)) ^ (-σ) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    have hcos : Real.cos (-t * Real.log (n:ℝ))
        = Real.cos (t * Real.log (n:ℝ)) := by
      rw [show -t * Real.log (n:ℝ) = -(t * Real.log (n:ℝ)) by ring,
        Real.cos_neg]
    rw [hrpow, hcos]
    ring

set_option maxHeartbeats 1600000 in
/-- **R5a: the 3-4-1 inequality.**  For `σ > 1` and any `t`:
`0 ≤ 3·Re L(Λ,σ) + 4·Re L(Λ,σ+it) + Re L(Λ,σ+2it)`. -/
theorem three_four_one {σ t : ℝ} (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun k =>
          ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re
      + 4 * (LSeries (fun k =>
          ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
            (((σ:ℝ):ℂ) + (t:ℝ) * Complex.I)).re
      + (LSeries (fun k =>
          ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
            (((σ:ℝ):ℂ) + (2*t:ℝ) * Complex.I)).re := by
  have hre : ∀ u : ℝ, ((((σ:ℝ):ℂ)) + (u:ℝ) * Complex.I).re = σ := by
    intro u
    simp
  have hsum : ∀ u : ℝ, LSeriesSummable (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
      (((σ:ℝ):ℂ) + (u:ℝ) * Complex.I) := by
    intro u
    apply ArithmeticFunction.LSeriesSummable_vonMangoldt
    rw [hre u]
    exact hσ
  have hzero : ((σ:ℝ):ℂ) = ((σ:ℝ):ℂ) + ((0:ℝ):ℝ) * Complex.I := by
    simp
  -- real-part series
  have hre_ser : ∀ u : ℝ,
      (LSeries (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
        (((σ:ℝ):ℂ) + (u:ℝ) * Complex.I)).re
      = ∑' n : ℕ, (if n = 0 then (0:ℝ) else
          ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ)
            * Real.cos (u * Real.log n)) := by
    intro u
    rw [show LSeries (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
        (((σ:ℝ):ℂ) + (u:ℝ) * Complex.I)
        = ∑' n, LSeries.term
            (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
            (((σ:ℝ):ℂ) + (u:ℝ) * Complex.I) n from rfl]
    rw [Complex.re_tsum (hsum u)]
    exact tsum_congr (vonMangoldt_term_re σ u)
  -- summability of the real-part series
  have hsum_re : ∀ u : ℝ, Summable (fun n : ℕ =>
      (if n = 0 then (0:ℝ) else
        ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ)
          * Real.cos (u * Real.log n))) := by
    intro u
    have h1 : Summable (fun n : ℕ =>
        (LSeries.term (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          (((σ:ℝ):ℂ) + (u:ℝ) * Complex.I) n).re) :=
      ⟨_, (hsum u).hasSum.mapL Complex.reCLM⟩
    apply Summable.congr h1
    exact vonMangoldt_term_re σ u
  have h0ser : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re
      = ∑' n : ℕ, (if n = 0 then (0:ℝ) else
          ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ)
            * Real.cos (0 * Real.log n)) := by
    rw [hzero]
    exact hre_ser 0
  rw [h0ser, hre_ser t, hre_ser (2*t)]
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← ((hsum_re 0).mul_left 3).tsum_add ((hsum_re t).mul_left 4),
    ← (((hsum_re 0).mul_left 3).add ((hsum_re t).mul_left 4)).tsum_add
      (hsum_re (2*t))]
  apply tsum_nonneg
  intro n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp
  · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    simp only [if_neg hne]
    have hΛ : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hnσ : (0:ℝ) < ((n:ℝ)) ^ (-σ) := by
      have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hpos
      positivity
    set x : ℝ := Real.cos (t * Real.log n) with hx
    have hcos2 : Real.cos ((2*t) * Real.log n) = 2 * x^2 - 1 := by
      rw [show (2*t) * Real.log n = 2 * (t * Real.log n) by ring]
      rw [Real.cos_two_mul, hx]
    rw [hcos2]
    have hkey : 3 + 4*x + (2*x^2 - 1) = 2*(1+x)^2 := by ring
    have hfactor : 3 * (ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ) * 1)
        + 4 * (ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ) * x)
        + ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ) * (2*x^2 - 1)
        = ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ)
            * (2*(1+x)^2) := by
      ring
    have hcos0 : Real.cos (0 * Real.log n) = 1 := by
      rw [zero_mul, Real.cos_zero]
    rw [hcos0, hfactor]
    positivity

end ThreeFourOne

section SharpPoleRung
/-!
## R3′: the SHARP pole rung, coefficient 1

The 3-4-1 assembly requires the σ-rung `Φ(σ) ≤ K/(σ-1) + A` with `K < 4/3`
(Fejér: no nonnegative cosine polynomial has `a₁ ≥ 2a₀`, so no weight
choice rescues a larger `K`; Cauchy cannot give `K < 4`).  This section
builds `K = 1`: the exact integral floor `Re ζ(σ) ≥ 1/(σ-1)` and the
log-series derivative bound.
-/

/-- The exact unit-interval integral of `x^{-σ}` and its endpoint bound:
`(a^{1-σ} - (a+1)^{1-σ})/(σ-1) ≤ a^{-σ}` for `a ≥ 1`. -/
theorem rpow_unit_telescope_le {a σ : ℝ} (ha : 1 ≤ a) (hσ : 1 < σ) :
    (a ^ (1 - σ) - (a + 1) ^ (1 - σ)) / (σ - 1) ≤ a ^ (-σ) := by
  have hapos : (0:ℝ) < a := by linarith
  have h0 : (0:ℝ) ∉ Set.uIcc a (a + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    exact absurd h.1 (by linarith)
  have hderivG : ∀ x ∈ Set.uIcc a (a + 1),
      HasDerivAt (fun y : ℝ => -y ^ (1 - σ) / (σ - 1)) (x ^ (-σ)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0:ℝ) < x := by linarith [hx.1]
    have h1 : HasDerivAt (fun y : ℝ => y ^ (1 - σ))
        ((1 - σ) * x ^ (1 - σ - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hxpos.ne')
    have hne : σ - 1 ≠ 0 := by linarith
    have hval : -((1 - σ) * x ^ (1 - σ - 1)) / (σ - 1) = x ^ (-σ) := by
      rw [show (1 - σ - 1) = -σ by ring, div_eq_iff hne]
      ring
    rw [← hval]
    have := (h1.neg).div_const (σ - 1)
    simpa [neg_div] using this
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (-σ))
      MeasureTheory.volume a (a + 1) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0:ℝ) < x := by linarith [hx.1]
    exact (Real.continuousAt_rpow_const x (-σ)
      (Or.inl hxpos.ne')).continuousWithinAt
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivG hint
  have hmono : ∫ x : ℝ in a..(a + 1), x ^ (-σ)
      ≤ ∫ _ : ℝ in a..(a + 1), a ^ (-σ) := by
    apply intervalIntegral.integral_mono_on (by linarith) hint
      intervalIntegrable_const
    intro x hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith)
  rw [hval] at hmono
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hsimp : -(a + 1) ^ (1 - σ) / (σ - 1) - -a ^ (1 - σ) / (σ - 1)
      = (a ^ (1 - σ) - (a + 1) ^ (1 - σ)) / (σ - 1) := by
    ring
  rw [hsimp] at hmono
  calc (a ^ (1 - σ) - (a + 1) ^ (1 - σ)) / (σ - 1)
      ≤ (a + 1 - a) * a ^ (-σ) := hmono
    _ = a ^ (-σ) := by ring

/-- **The sharp floor**: `1/(σ-1) ≤ Re ζ(σ)` for `σ ∈ (1, 2]`. -/
theorem zeta_re_floor_sharp {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    1 / (σ - 1) ≤ (riemannZeta ((σ:ℝ):ℂ)).re := by
  have hσre : (1:ℝ) < (((σ:ℝ):ℂ)).re := by
    simp
    linarith
  -- the real-part series
  have hsum : Summable (fun n : ℕ => 1 / ((n:ℂ)) ^ ((σ:ℝ):ℂ)) := by
    rw [Complex.summable_one_div_nat_cpow]
    exact hσre
  have hterm_re : ∀ n : ℕ, (1 / ((n:ℂ)) ^ ((σ:ℝ):ℂ)).re
      = if n = 0 then (0:ℝ) else ((n:ℝ)) ^ (-σ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [Nat.cast_zero, zero_cpow (by
          intro h
          have := congrArg Complex.re h
          simp at this
          linarith)]
      simp
    · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      rw [if_neg hne]
      rw [show ((n:ℕ):ℂ) = (((n:ℝ)):ℂ) by push_cast; rfl]
      rw [← Complex.ofReal_cpow hnn]
      rw [one_div, ← Complex.ofReal_inv]
      rw [Complex.ofReal_re]
      rw [← Real.rpow_neg hnn]
  have hre_eq : (riemannZeta ((σ:ℝ):ℂ)).re
      = ∑' n : ℕ, (if n = 0 then (0:ℝ) else ((n:ℝ)) ^ (-σ)) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hσre, Complex.re_tsum hsum]
    exact tsum_congr hterm_re
  rw [hre_eq]
  set g : ℕ → ℝ := fun n => if n = 0 then (0:ℝ) else ((n:ℝ)) ^ (-σ) with hg
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n
    rw [hg]
    dsimp only
    split
    · exact le_refl 0
    · positivity
  have hgsum : Summable g :=
    summable_of_sum_range_le hgnn (partial_inv_rpow_le h1)
  -- partial sums dominate the telescoped integral
  have hpartial : ∀ N : ℕ,
      (1 - (((N + 1:ℕ)):ℝ) ^ (1 - σ)) / (σ - 1)
        ≤ ∑ n ∈ Finset.range (N + 1), g n := by
    intro N
    induction N with
    | zero =>
      rw [Finset.sum_range_one]
      have : g 0 = 0 := by simp [hg]
      rw [this]
      rw [show (((0 + 1:ℕ)):ℝ) = 1 by norm_num, Real.one_rpow]
      norm_num
    | succ M ih =>
      rw [Finset.sum_range_succ]
      have hstep : (((M + 1:ℕ)):ℝ) ^ (1 - σ) / (σ - 1)
          - (((M + 2:ℕ)):ℝ) ^ (1 - σ) / (σ - 1) ≤ g (M + 1) := by
        have hM1 : (1:ℝ) ≤ ((M + 1:ℕ):ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero M)
        have := rpow_unit_telescope_le hM1 h1
        have hcast : (((M + 1:ℕ)):ℝ) + 1 = (((M + 2:ℕ)):ℝ) := by
          push_cast
          ring
        rw [hcast] at this
        rw [hg]
        dsimp only
        rw [if_neg (Nat.succ_ne_zero M)]
        calc (((M + 1:ℕ)):ℝ) ^ (1 - σ) / (σ - 1)
            - (((M + 2:ℕ)):ℝ) ^ (1 - σ) / (σ - 1)
            = ((((M + 1:ℕ)):ℝ) ^ (1 - σ)
              - (((M + 2:ℕ)):ℝ) ^ (1 - σ)) / (σ - 1) := by ring
          _ ≤ (((M + 1:ℕ)):ℝ) ^ (-σ) := this
      have hgoal : (1 - (((M + 2:ℕ)):ℝ) ^ (1 - σ)) / (σ - 1)
          = (1 - (((M + 1:ℕ)):ℝ) ^ (1 - σ)) / (σ - 1)
            + ((((M + 1:ℕ)):ℝ) ^ (1 - σ) / (σ - 1)
              - (((M + 2:ℕ)):ℝ) ^ (1 - σ) / (σ - 1)) := by
        ring
      rw [show (M + 1 + 1 : ℕ) = M + 2 from rfl, hgoal]
      linarith
  -- pass to the limit
  have hle_tsum : ∀ N : ℕ,
      (1 - (((N + 1:ℕ)):ℝ) ^ (1 - σ)) / (σ - 1) ≤ ∑' n, g n := by
    intro N
    calc (1 - (((N + 1:ℕ)):ℝ) ^ (1 - σ)) / (σ - 1)
        ≤ ∑ n ∈ Finset.range (N + 1), g n := hpartial N
      _ ≤ ∑' n, g n := hgsum.sum_le_tsum _ (fun n _ => hgnn n)
  have htend : Filter.Tendsto
      (fun N : ℕ => (1 - (((N + 1:ℕ)):ℝ) ^ (1 - σ)) / (σ - 1))
      Filter.atTop (nhds (1 / (σ - 1))) := by
    have h1' : Filter.Tendsto (fun N : ℕ => (((N + 1:ℕ)):ℝ) ^ (1 - σ))
        Filter.atTop (nhds 0) := by
      have hbase : Filter.Tendsto (fun N : ℕ => (((N + 1:ℕ)):ℝ))
          Filter.atTop Filter.atTop := by
        apply Filter.tendsto_atTop_mono
          (fun N : ℕ => by exact_mod_cast Nat.le_succ N : ∀ N : ℕ,
            ((N:ℝ)) ≤ (((N + 1:ℕ)):ℝ))
        exact tendsto_natCast_atTop_atTop
      have hexp := tendsto_rpow_neg_atTop
        (y := σ - 1) (by linarith)
      have := hexp.comp hbase
      apply this.congr
      intro N
      simp only [Function.comp_apply]
      rw [show -(σ - 1) = 1 - σ by ring]
    have : Filter.Tendsto
        (fun N : ℕ => (1 - (((N + 1:ℕ)):ℝ) ^ (1 - σ)) / (σ - 1))
        Filter.atTop (nhds ((1 - 0) / (σ - 1))) :=
      ((tendsto_const_nhds.sub h1')).div_const (σ - 1)
    simpa using this
  exact le_of_tendsto htend
    (Filter.Eventually.of_forall hle_tsum)

/-- Antitonicity of `x^{-σ}·log x` on `[3, ∞)` (where `log x ≥ 1`):
elementary, via `log y ≤ (y/x)·log x`. -/
theorem rpow_log_antitone {x y σ : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y)
    (hσ : 1 ≤ σ) :
    y ^ (-σ) * Real.log y ≤ x ^ (-σ) * Real.log x := by
  have hxpos : (0:ℝ) < x := by linarith
  have hypos : (0:ℝ) < y := by linarith
  have hlogx1 : (1:ℝ) ≤ Real.log x := by
    have h3 : Real.exp 1 ≤ 3 := by
      nlinarith [Real.exp_one_lt_d9]
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hlog_le : Real.log y ≤ (y/x) * Real.log x := by
    have hdiv : Real.log (y/x) ≤ y/x - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hsplit : Real.log (y/x) = Real.log y - Real.log x :=
      Real.log_div hypos.ne' hxpos.ne'
    have hyx1 : (1:ℝ) ≤ y/x := by
      rw [le_div_iff₀ hxpos]
      linarith
    nlinarith
  calc y ^ (-σ) * Real.log y
      ≤ y ^ (-σ) * ((y/x) * Real.log x) := by
        apply mul_le_mul_of_nonneg_left hlog_le (by positivity)
    _ = y ^ (-σ) * y * (x⁻¹ * Real.log x) := by
        field_simp
    _ = y ^ (-σ + 1) * (x⁻¹ * Real.log x) := by
        congr 1
        rw [Real.rpow_add hypos, Real.rpow_one]
    _ ≤ x ^ (-σ + 1) * (x⁻¹ * Real.log x) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact Real.rpow_le_rpow_of_nonpos hxpos hxy (by linarith)
    _ = x ^ (-σ) * Real.log x := by
        rw [Real.rpow_add hxpos, Real.rpow_one]
        field_simp

/-- The log-weighted unit telescope: for `a ≥ 3`,
`(a+1)^{-σ}·log(a+1) ≤ Flog(a+1) − Flog(a)` with
`Flog(x) = −x^{1-σ}((σ-1)log x + 1)/(σ-1)²`. -/
theorem log_rpow_unit_telescope_le {a σ : ℝ} (ha : 3 ≤ a) (hσ : 1 < σ) :
    (a + 1) ^ (-σ) * Real.log (a + 1)
      ≤ (-((a+1) ^ (1-σ) * ((σ-1) * Real.log (a+1) + 1)) / (σ-1)^2)
        - (-(a ^ (1-σ) * ((σ-1) * Real.log a + 1)) / (σ-1)^2) := by
  have hFderiv : ∀ x ∈ Set.uIcc a (a + 1),
      HasDerivAt (fun y : ℝ =>
        -(y ^ (1-σ) * ((σ-1) * Real.log y + 1)) / (σ-1)^2)
        (x ^ (-σ) * Real.log x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0:ℝ) < x := by linarith [hx.1]
    have hy1 : HasDerivAt (fun y : ℝ => y ^ (1-σ))
        ((1-σ) * x ^ (1-σ-1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hxpos.ne')
    have hy2 : HasDerivAt (fun y : ℝ => (σ-1) * Real.log y + 1)
        ((σ-1) * x⁻¹) x := by
      have := ((Real.hasDerivAt_log hxpos.ne').const_mul (σ-1)).add_const 1
      simpa using this
    have hprod := hy1.mul hy2
    have hne : σ - 1 ≠ 0 := by linarith
    have hval : -((1-σ) * x ^ (1-σ-1) * ((σ-1) * Real.log x + 1)
        + x ^ (1-σ) * ((σ-1) * x⁻¹)) / (σ-1)^2
        = x ^ (-σ) * Real.log x := by
      have hx1 : x ^ (1-σ-1) = x ^ (-σ) := by
        rw [show (1-σ-1) = -σ by ring]
      have hx2 : x ^ (1-σ) * x⁻¹ = x ^ (-σ) := by
        rw [show x⁻¹ = x ^ (-(1:ℝ)) by
          rw [Real.rpow_neg_one]]
        rw [← Real.rpow_add hxpos]
        rw [show (1-σ) + -(1:ℝ) = -σ by ring]
      rw [hx1]
      rw [show x ^ (1-σ) * ((σ-1) * x⁻¹) = (σ-1) * (x ^ (1-σ) * x⁻¹) by ring,
        hx2]
      rw [div_eq_iff (by positivity : ((σ:ℝ)-1)^2 ≠ 0)]
      ring
    rw [← hval]
    have := (hprod.neg).div_const ((σ-1)^2)
    simpa [neg_div] using this
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (-σ) * Real.log x)
      MeasureTheory.volume a (a + 1) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0:ℝ) < x := by linarith [hx.1]
    exact ((Real.continuousAt_rpow_const x (-σ)
      (Or.inl hxpos.ne')).mul
      (Real.continuousAt_log hxpos.ne')).continuousWithinAt
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hFderiv hint
  have hmono : ∫ _ : ℝ in a..(a + 1), (a+1) ^ (-σ) * Real.log (a+1)
      ≤ ∫ x : ℝ in a..(a + 1), x ^ (-σ) * Real.log x := by
    apply intervalIntegral.integral_mono_on (by linarith)
      intervalIntegrable_const hint
    intro x hx
    exact rpow_log_antitone (by linarith [hx.1]) hx.2 hσ.le
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  rw [hval] at hmono
  calc (a + 1) ^ (-σ) * Real.log (a + 1)
      = (a + 1 - a) * ((a+1) ^ (-σ) * Real.log (a+1)) := by ring
    _ ≤ (-((a+1) ^ (1-σ) * ((σ-1) * Real.log (a+1) + 1)) / (σ-1)^2)
        - (-(a ^ (1-σ) * ((σ-1) * Real.log a + 1)) / (σ-1)^2) := hmono

/-- Partial sums of the log-weighted series:
`Σ log n·n^{-σ} ≤ log 2 + log 3 + ((σ-1)log 3 + 1)/(σ-1)²`. -/
theorem log_rpow_partial_le {σ : ℝ} (h1 : 1 < σ) (N : ℕ) :
    ∑ n ∈ Finset.range N,
      (if n = 0 then (0:ℝ) else Real.log n * ((n:ℝ)) ^ (-σ))
      ≤ Real.log 2 + Real.log 3
        + ((σ-1) * Real.log 3 + 1) / (σ-1)^2 := by
  set hfun : ℕ → ℝ := fun n =>
    if n = 0 then (0:ℝ) else Real.log n * ((n:ℝ)) ^ (-σ) with hf
  have hnn : ∀ n, 0 ≤ hfun n := by
    intro n
    rw [hf]
    dsimp only
    split
    · exact le_refl 0
    · rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rename_i hne
        exact absurd h0 hne
      · have h1n : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hpos
        have := Real.log_nonneg h1n
        positivity
  set Flog : ℝ → ℝ := fun x =>
    -(x ^ (1-σ) * ((σ-1) * Real.log x + 1)) / (σ-1)^2 with hFlog
  have hFlog_nonpos : ∀ x : ℝ, 1 ≤ x → Flog x ≤ 0 := by
    intro x hx
    rw [hFlog]
    dsimp only
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    simp only [neg_nonpos]
    have hlognn := Real.log_nonneg hx
    have hrp : (0:ℝ) ≤ x ^ (1-σ) := Real.rpow_nonneg (by linarith) _
    have hB : (0:ℝ) ≤ (σ-1) * Real.log x + 1 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ σ-1) hlognn]
    nlinarith [mul_nonneg hrp hB]
  have hbase : ∑ n ∈ Finset.range 4, hfun n ≤ Real.log 2 + Real.log 3 := by
    have h0 : hfun 0 = 0 := by simp [hf]
    have h1' : hfun 1 = 0 := by simp [hf]
    have h2' : hfun 2 ≤ Real.log 2 := by
      rw [hf]
      dsimp only
      rw [if_neg (by norm_num)]
      calc Real.log 2 * ((2:ℕ):ℝ) ^ (-σ)
          ≤ Real.log 2 * 1 := by
            apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
            apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
              (by linarith)
        _ = Real.log 2 := mul_one _
      -- the cast: ((2:ℕ):ℝ) = 2
    have h3' : hfun 3 ≤ Real.log 3 := by
      rw [hf]
      dsimp only
      rw [if_neg (by norm_num)]
      calc Real.log 3 * ((3:ℕ):ℝ) ^ (-σ)
          ≤ Real.log 3 * 1 := by
            apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
            apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
              (by linarith)
        _ = Real.log 3 := mul_one _
    have hexp : ∑ n ∈ Finset.range 4, hfun n
        = hfun 0 + hfun 1 + hfun 2 + hfun 3 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_one]
    rw [hexp, h0, h1']
    push_cast at h2' h3' ⊢
    linarith
  have hkey : ∀ M : ℕ, ∑ n ∈ Finset.range (M + 4), hfun n
      ≤ Real.log 2 + Real.log 3 + (Flog ((M:ℝ) + 3) - Flog 3) := by
    intro M
    induction M with
    | zero =>
      simpa using hbase
    | succ K ih =>
      rw [show K + 1 + 4 = (K + 4) + 1 from rfl, Finset.sum_range_succ]
      have hstep : hfun (K + 4) ≤ Flog ((K:ℝ) + 4) - Flog ((K:ℝ) + 3) := by
        have htel := log_rpow_unit_telescope_le
          (a := (K:ℝ) + 3) (by linarith [Nat.cast_nonneg' (α := ℝ) K]) h1
        have h4 : ((K:ℝ) + 3) + 1 = (K:ℝ) + 4 := by ring
        rw [h4] at htel
        rw [hf]
        dsimp only
        rw [if_neg (by omega)]
        rw [hFlog]
        dsimp only
        calc Real.log (K + 4 : ℕ) * (((K + 4 : ℕ)):ℝ) ^ (-σ)
            = ((K:ℝ) + 4) ^ (-σ) * Real.log ((K:ℝ) + 4) := by
              push_cast
              ring_nf
          _ ≤ _ := htel
      have hgoal : Flog ((K:ℝ) + 3) - Flog 3
          + (Flog ((K:ℝ) + 4) - Flog ((K:ℝ) + 3))
          = Flog (((K + 1 : ℕ):ℝ) + 3) - Flog 3 := by
        push_cast
        ring_nf
      calc ∑ n ∈ Finset.range (K + 4), hfun n + hfun (K + 4)
          ≤ (Real.log 2 + Real.log 3 + (Flog ((K:ℝ) + 3) - Flog 3))
            + (Flog ((K:ℝ) + 4) - Flog ((K:ℝ) + 3)) := by
            apply add_le_add ih hstep
        _ = Real.log 2 + Real.log 3
            + (Flog (((K + 1 : ℕ):ℝ) + 3) - Flog 3) := by
            rw [← hgoal]
            ring
  have hFbound : ∀ M : ℕ, Flog ((M:ℝ) + 3) - Flog 3
      ≤ ((σ-1) * Real.log 3 + 1) / (σ-1)^2 := by
    intro M
    have h1' := hFlog_nonpos ((M:ℝ) + 3) (by linarith [Nat.cast_nonneg' (α := ℝ) M])
    have h2' : -Flog 3 ≤ ((σ-1) * Real.log 3 + 1) / (σ-1)^2 := by
      rw [hFlog]
      dsimp only
      rw [neg_div, neg_neg]
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc (3:ℝ) ^ (1-σ) * ((σ-1) * Real.log 3 + 1)
          ≤ 1 * ((σ-1) * Real.log 3 + 1) := by
            apply mul_le_mul_of_nonneg_right
            · apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
                (by linarith)
            · have := Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)
              nlinarith
        _ = (σ-1) * Real.log 3 + 1 := one_mul _
    linarith
  rcases Nat.lt_or_ge N 4 with hN | hN
  · have hmono : ∑ n ∈ Finset.range N, hfun n
        ≤ ∑ n ∈ Finset.range 4, hfun n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_range] at hx ⊢
        omega
      · intro n _ _
        exact hnn n
    have hpos_tail : (0:ℝ) ≤ ((σ-1) * Real.log 3 + 1) / (σ-1)^2 := by
      have := Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)
      positivity
    linarith [hbase]
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 4 := ⟨N - 4, by omega⟩
    calc ∑ n ∈ Finset.range (M + 4), hfun n
        ≤ Real.log 2 + Real.log 3 + (Flog ((M:ℝ) + 3) - Flog 3) :=
          hkey M
      _ ≤ Real.log 2 + Real.log 3
          + ((σ-1) * Real.log 3 + 1) / (σ-1)^2 := by
          linarith [hFbound M]

set_option maxHeartbeats 1600000 in
/-- **The sharp derivative bound**:
`‖ζ'(σ)‖ ≤ 1/(σ-1)² + 2/(σ-1) + 2.1` on `(1, 9/8]` — leading coefficient 1,
via the log-weighted Dirichlet series (`LSeries_deriv`), not Cauchy. -/
theorem zeta_deriv_sharp {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 9/8) :
    ‖deriv riemannZeta ((σ:ℝ):ℂ)‖
      ≤ 1/(σ-1)^2 + 2/(σ-1) + 2.1 := by
  have hσre : (1:ℝ) < (((σ:ℝ):ℂ)).re := by
    simp
    linarith
  -- deriv ζ = −L(log·ζ) at σ
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hEE : riemannZeta =ᶠ[nhds ((σ:ℝ):ℂ)]
      LSeries (fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) := by
    filter_upwards [hopen.mem_nhds hσre] with z hz
    exact (ArithmeticFunction.LSeries_zeta_eq_riemannZeta hz).symm
  have hderiv_eq : deriv riemannZeta ((σ:ℝ):ℂ)
      = -LSeries (LSeries.logMul
          (fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ))) ((σ:ℝ):ℂ) := by
    rw [hEE.deriv_eq]
    apply LSeries_deriv
    rw [ArithmeticFunction.abscissaOfAbsConv_zeta]
    exact_mod_cast hσre
  rw [hderiv_eq, norm_neg]
  -- termwise norm = the log-weighted series
  set hfun : ℕ → ℝ := fun n =>
    if n = 0 then (0:ℝ) else Real.log n * ((n:ℝ)) ^ (-σ) with hf
  have hnn : ∀ n, 0 ≤ hfun n := by
    intro n
    rw [hf]
    dsimp only
    split
    · exact le_refl 0
    · rename_i hne
      have hpos : 0 < n := Nat.pos_of_ne_zero hne
      have h1n : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hpos
      have := Real.log_nonneg h1n
      positivity
  have hterm : ∀ n : ℕ,
      ‖LSeries.term (LSeries.logMul
        (fun k => ((ArithmeticFunction.zeta k : ℕ) : ℂ))) ((σ:ℝ):ℂ) n‖
      = hfun n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [LSeries.term_zero]
      simp [hf]
    · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      rw [LSeries.term_of_ne_zero hne, hf]
      dsimp only
      rw [if_neg hne]
      unfold LSeries.logMul
      simp only [ArithmeticFunction.zeta_apply_ne hne, Nat.cast_one, mul_one]
      rw [norm_div]
      rw [Complex.norm_natCast_cpow_of_pos hpos]
      have hlogn : ‖Complex.log ((n:ℕ):ℂ)‖ = Real.log n := by
        rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (Real.log_natCast_nonneg n)
      rw [hlogn, Complex.ofReal_re]
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hpos
      rw [Real.rpow_neg hnpos.le]
      field_simp
  have hsum_hfun : Summable hfun :=
    summable_of_sum_range_le hnn (log_rpow_partial_le h1)
  have hsum_norm : Summable (fun n =>
      ‖LSeries.term (LSeries.logMul
        (fun k => ((ArithmeticFunction.zeta k : ℕ) : ℂ))) ((σ:ℝ):ℂ) n‖) := by
    apply Summable.congr hsum_hfun
    intro n
    exact (hterm n).symm
  calc ‖LSeries (LSeries.logMul
        (fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ))) ((σ:ℝ):ℂ)‖
      ≤ ∑' n, ‖LSeries.term (LSeries.logMul
          (fun k => ((ArithmeticFunction.zeta k : ℕ) : ℂ))) ((σ:ℝ):ℂ) n‖ :=
        norm_tsum_le_tsum_norm hsum_norm
    _ = ∑' n, hfun n := tsum_congr hterm
    _ ≤ Real.log 2 + Real.log 3 + ((σ-1) * Real.log 3 + 1) / (σ-1)^2 :=
        Real.tsum_le_of_sum_range_le hnn (log_rpow_partial_le h1)
    _ ≤ 1/(σ-1)^2 + 2/(σ-1) + 2.1 := by
        have hlog2 : Real.log 2 ≤ 0.7 := by
          nlinarith [Real.log_two_lt_d9]
        have hlog3 : Real.log 3 ≤ 1.4 := by
          calc Real.log 3 ≤ Real.log 4 :=
              Real.log_le_log (by norm_num) (by norm_num)
            _ = Real.log (2^2) := by norm_num
            _ = 2 * Real.log 2 := by
                rw [Real.log_pow]
                push_cast
                ring
            _ ≤ 1.4 := by nlinarith [Real.log_two_lt_d9]
        have hlog3nn : (0:ℝ) ≤ Real.log 3 :=
          Real.log_nonneg (by norm_num)
        have hsplit : ((σ-1) * Real.log 3 + 1) / (σ-1)^2
            = Real.log 3 / (σ-1) + 1/(σ-1)^2 := by
          field_simp
        rw [hsplit]
        have hd1 : Real.log 3 / (σ-1) ≤ 2/(σ-1) := by
          apply div_le_div_of_nonneg_right _ (by linarith)
          linarith
        linarith

/-- **R3′: the SHARP pole rung** — `‖ζ'/ζ(σ)‖ ≤ 1/(σ-1) + 3` on `(1, 9/8]`;
leading coefficient 1, as the 3-4-1 assembly requires. -/
theorem zeta_logDeriv_rung_sharp {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 9/8) :
    ‖logDeriv riemannZeta ((σ:ℝ):ℂ)‖ ≤ 1/(σ-1) + 3 := by
  have hσ1 : (0:ℝ) < σ - 1 := by linarith
  have hfloor := zeta_re_floor_sharp h1 (by linarith)
  have hnorm_ge : 1/(σ-1) ≤ ‖riemannZeta ((σ:ℝ):ℂ)‖ :=
    le_trans hfloor (Complex.re_le_norm _)
  have hpos : (0:ℝ) < 1/(σ-1) := by positivity
  rw [logDeriv_apply, norm_div]
  calc ‖deriv riemannZeta ((σ:ℝ):ℂ)‖ / ‖riemannZeta ((σ:ℝ):ℂ)‖
      ≤ (1/(σ-1)^2 + 2/(σ-1) + 2.1) / (1/(σ-1)) := by
        apply div_le_div₀ _ (zeta_deriv_sharp h1 h2) hpos hnorm_ge
        have : (0:ℝ) < 1/(σ-1)^2 := by positivity
        have : (0:ℝ) < 2/(σ-1) := by positivity
        linarith
    _ = 1/(σ-1) + 2 + 2.1*(σ-1) := by
        field_simp
    _ ≤ 1/(σ-1) + 3 := by
        nlinarith

end SharpPoleRung

section ExponentOneRegion
/-!
## R5b: the exponent-1 zero-free region

`β ≤ 1 − c₀/log|γ|` for every zero, `|γ| ≥ e³²`.  The de la Vallée Poussin
assembly: 3-4-1 positivity + the sharp pole rung (K=1) + the movable-center
partial fraction at `T` and `2T` with the zero seated by the completeness
certificate.
-/

/-- The bridge: `Re L(Λ,s) = −Re(ζ'/ζ)(s)` on `Re s > 1`. -/
theorem vonMangoldt_re_eq_neg_logDeriv {s : ℂ} (hs : 1 < s.re) :
    (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s).re
    = -(logDeriv riemannZeta s).re := by
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have h2 : LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s
      = -logDeriv riemannZeta s := by
    rw [logDeriv_apply]
    rw [neg_div] at h
    exact h
  rw [h2, Complex.neg_re]

/-- Real part of one partial-fraction term. -/
theorem pf_term_re (k : ℕ) (w : ℂ) :
    (((k:ℕ):ℂ) / w).re = (k:ℝ) * (w.re / Complex.normSq w) := by
  rw [div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im]
  simp

set_option maxHeartbeats 3200000 in
/-- The positive-ordinate case of the exponent-1 region. -/
theorem zero_free_region_exponent_one_aux {ρ : ℂ}
    (hζρ : riemannZeta ρ = 0) (hT32 : Real.exp 32 ≤ ρ.im) :
    ρ.re ≤ 1 - (1/50000) / Real.log ρ.im := by
  set T : ℝ := ρ.im with hTdef
  set β : ℝ := ρ.re with hβdef
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 32) hT32
  have hL32 : (32:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 32) hT32
    rwa [Real.log_exp] at this
  set L : ℝ := Real.log T with hLdef
  have hLpos : (0:ℝ) < L := by linarith
  have hexp2T : Real.exp 2 ≤ T := by
    calc Real.exp 2 ≤ Real.exp 32 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ T := hT32
  have hT7 : (7:ℝ) ≤ T := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_one_gt_d9]
  -- β < 1
  have hβ1 : β < 1 := by
    by_contra hc
    push_neg at hc
    exact riemannZeta_ne_zero_of_one_le_re (by rw [← hβdef]; exact hc) hζρ
  -- trivial branch: β far from 1
  by_cases hβtriv : β ≤ 1 - 3/32
  · have hc0 : (1/50000 : ℝ) / L ≤ 3/32 := by
      have h1 : (1/50000 : ℝ) / L ≤ (1/50000 : ℝ) / 32 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL32
      calc (1/50000 : ℝ) / L ≤ (1/50000 : ℝ) / 32 := h1
        _ ≤ 3/32 := by norm_num
    linarith
  push_neg at hβtriv
  -- the anchor
  set σ : ℝ := 1 + 1/(10000*L) with hσdef
  have hinv : (0:ℝ) < 1/(10000*L) := by positivity
  have hσ1 : 1 < σ := by
    rw [hσdef]
    linarith
  have hσ98 : σ ≤ 9/8 := by
    rw [hσdef]
    have : (1:ℝ)/(10000*L) ≤ 1/8 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    linarith
  -- (B) the sharp σ-rung
  have hΦ0 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re
      ≤ 10000*L + 3 := by
    rw [vonMangoldt_re_eq_neg_logDeriv (by simp; linarith)]
    have h1 := zeta_logDeriv_rung_sharp hσ1 hσ98
    have h2 : -(logDeriv riemannZeta ((σ:ℝ):ℂ)).re
        ≤ ‖logDeriv riemannZeta ((σ:ℝ):ℂ)‖ := by
      have := Complex.abs_re_le_norm (logDeriv riemannZeta ((σ:ℝ):ℂ))
      have := neg_abs_le (logDeriv riemannZeta ((σ:ℝ):ℂ)).re
      linarith
    have h3 : 1/(σ-1) = 10000*L := by
      rw [hσdef, show (1 + 1/(10000*L) - 1) = 1/(10000*L) by ring,
        one_div_one_div]
    linarith
  -- (C) the s₁ bound with the seated zero
  obtain ⟨S, n, hS_mem, hcert, hcomp, hbound⟩ := zeta_partial_fraction hexp2T
  set c : ℂ := ((1 + 1 / Real.log T : ℝ) : ℂ) + T * Complex.I with hcdef
  set s₁ : ℂ := ((σ:ℝ):ℂ) + ((T:ℝ):ℂ) * Complex.I with hs₁def
  have hs₁re : s₁.re = σ := by
    rw [hs₁def]
    simp
  have hs₁im : s₁.im = T := by
    rw [hs₁def]
    simp
  have hζs₁ : riemannZeta s₁ ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hs₁re]; exact hσ1)
  have hs₁c : s₁ - c = (((σ - (1 + 1/L) : ℝ)):ℂ) := by
    rw [hs₁def, hcdef, hLdef]
    push_cast
    ring
  have hs₁mem : s₁ ∈ Metric.closedBall c (1/32) := by
    rw [Metric.mem_closedBall, dist_eq_norm, hs₁c, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · rw [hσdef]
      have h1 : (1:ℝ)/L ≤ 1/32 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL32
      have h2 : (0:ℝ) < 1/(10000*L) := hinv
      nlinarith
    · rw [hσdef]
      have h2 : (0:ℝ) < 1/L := by positivity
      have h3 : (1:ℝ)/(10000*L) ≤ 1/32 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        nlinarith
      nlinarith
  have hb₁ := hbound s₁ hs₁mem hζs₁
  -- the zero is seated
  have hρc : ρ - c = (((β - (1 + 1/L) : ℝ)):ℂ) := by
    rw [hcdef, hLdef]
    apply Complex.ext
    · simp [hβdef]
    · simp [hTdef]
  have hρmem : ρ ∈ Metric.closedBall c (1/8) := by
    rw [Metric.mem_closedBall, dist_eq_norm, hρc, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · have h1 : (1:ℝ)/L ≤ 1/32 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL32
      nlinarith
    · have h2 : (0:ℝ) < 1/L := by positivity
      nlinarith
  obtain ⟨hρS, hnρ⟩ := hcomp ρ hρmem hζρ
  -- terms of the partial-fraction sum are nonneg; the ρ-term dominates
  have hure : ∀ u ∈ S, 1 ≤ n u → u.re < 1 := by
    intro u hu hnu
    by_contra hc
    push_neg at hc
    exact riemannZeta_ne_zero_of_one_le_re hc (hcert u hu hnu)
  have hterm_nonneg : ∀ u ∈ S,
      0 ≤ ((n u : ℂ) / (s₁ - u)).re := by
    intro u hu
    rcases Nat.eq_zero_or_pos (n u) with h0 | hpos
    · rw [h0]
      simp
    · have hlt := hure u hu hpos
      rw [pf_term_re]
      apply mul_nonneg (Nat.cast_nonneg _)
      apply div_nonneg _ (Complex.normSq_nonneg _)
      rw [Complex.sub_re, hs₁re]
      linarith
  have hρ_term : 1/(σ - β) ≤ ((n ρ : ℂ) / (s₁ - ρ)).re := by
    have hs₁ρ : s₁ - ρ = (((σ - β : ℝ)):ℂ) := by
      apply Complex.ext
      · simp [hs₁re, hβdef]
      · simp [hs₁im, hTdef]
    rw [pf_term_re, hs₁ρ]
    rw [Complex.normSq_ofReal, Complex.ofReal_re]
    have hσβ : (0:ℝ) < σ - β := by linarith
    have hval : (σ - β) / ((σ - β) * (σ - β)) = 1/(σ - β) := by
      field_simp
    rw [hval]
    have h1n : (1:ℝ) ≤ (n ρ : ℝ) := by exact_mod_cast hnρ
    nlinarith [one_div_pos.mpr hσβ]
  have hsum_ge : 1/(σ - β) ≤ (∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re := by
    rw [Complex.re_sum]
    calc 1/(σ - β) ≤ ((n ρ : ℂ) / (s₁ - ρ)).re := hρ_term
      _ ≤ ∑ u ∈ S, ((n u : ℂ) / (s₁ - u)).re :=
          Finset.single_le_sum hterm_nonneg hρS
  have hΦ1 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₁).re
      ≤ -(1/(σ - β)) + 300*L := by
    have hbr := vonMangoldt_re_eq_neg_logDeriv
      (s := s₁) (by rw [hs₁re]; exact hσ1)
    rw [hbr]
    have hsplit : -(logDeriv riemannZeta s₁).re
        = -((logDeriv riemannZeta s₁
            - ∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re)
          - (∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re := by
      rw [Complex.sub_re]
      ring
    rw [hsplit]
    have h1 : -((logDeriv riemannZeta s₁
        - ∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re) ≤ 300*L := by
      have habs := Complex.abs_re_le_norm (logDeriv riemannZeta s₁
        - ∑ u ∈ S, (n u : ℂ) / (s₁ - u))
      have hneg := neg_abs_le (logDeriv riemannZeta s₁
        - ∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re
      rw [hLdef]
      linarith
    linarith [hsum_ge]
  -- (D) the 2T bound
  have hexp2T2 : Real.exp 2 ≤ 2*T := by linarith
  obtain ⟨S₂, n₂, hS₂_mem, hcert₂, _, hbound₂⟩ :=
    zeta_partial_fraction hexp2T2
  set c₂ : ℂ := ((1 + 1 / Real.log (2*T) : ℝ) : ℂ)
      + ((2*T : ℝ) : ℂ) * Complex.I
    with hc₂def
  set s₂ : ℂ := ((σ:ℝ):ℂ) + ((2*T:ℝ):ℂ) * Complex.I with hs₂def
  have hL₂ : L ≤ Real.log (2*T) := by
    rw [hLdef]
    apply Real.log_le_log hTpos
    linarith
  have hL₂pos : (0:ℝ) < Real.log (2*T) := by linarith
  have hs₂re : s₂.re = σ := by
    rw [hs₂def]
    simp
  have hζs₂ : riemannZeta s₂ ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hs₂re]; exact hσ1)
  have hs₂mem : s₂ ∈ Metric.closedBall c₂ (1/32) := by
    have hs₂c : s₂ - c₂ = (((σ - (1 + 1/Real.log (2*T)) : ℝ)):ℂ) := by
      rw [hs₂def, hc₂def]
      push_cast
      ring
    rw [Metric.mem_closedBall, dist_eq_norm, hs₂c, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_le]
    have hinv₂ : (0:ℝ) < 1/Real.log (2*T) := by positivity
    have hinv₂32 : (1:ℝ)/Real.log (2*T) ≤ 1/32 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    constructor
    · rw [hσdef]
      have h2 : (0:ℝ) < 1/(10000*L) := hinv
      nlinarith
    · rw [hσdef]
      have h3 : (1:ℝ)/(10000*L) ≤ 1/32 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        nlinarith
      nlinarith
  have hb₂ := hbound₂ s₂ hs₂mem hζs₂
  have hure₂ : ∀ u ∈ S₂, 1 ≤ n₂ u → u.re < 1 := by
    intro u hu hnu
    by_contra hc
    push_neg at hc
    exact riemannZeta_ne_zero_of_one_le_re hc (hcert₂ u hu hnu)
  have hterm₂_nonneg : ∀ u ∈ S₂,
      0 ≤ ((n₂ u : ℂ) / (s₂ - u)).re := by
    intro u hu
    rcases Nat.eq_zero_or_pos (n₂ u) with h0 | hpos
    · rw [h0]
      simp
    · have hlt := hure₂ u hu hpos
      rw [pf_term_re]
      apply mul_nonneg (Nat.cast_nonneg _)
      apply div_nonneg _ (Complex.normSq_nonneg _)
      rw [Complex.sub_re, hs₂re]
      linarith
  have hΦ2 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₂).re
      ≤ 307*L := by
    have hbr := vonMangoldt_re_eq_neg_logDeriv
      (s := s₂) (by rw [hs₂re]; exact hσ1)
    rw [hbr]
    have hsplit : -(logDeriv riemannZeta s₂).re
        = -((logDeriv riemannZeta s₂
            - ∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re)
          - (∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re := by
      rw [Complex.sub_re]
      ring
    rw [hsplit]
    have h1 : -((logDeriv riemannZeta s₂
        - ∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re)
        ≤ 300 * Real.log (2*T) := by
      have habs := Complex.abs_re_le_norm (logDeriv riemannZeta s₂
        - ∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u))
      have hneg := neg_abs_le (logDeriv riemannZeta s₂
        - ∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re
      linarith
    have h2 : (0:ℝ) ≤ (∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re := by
      rw [Complex.re_sum]
      exact Finset.sum_nonneg hterm₂_nonneg
    have h3 : Real.log (2*T) = Real.log 2 + L := by
      rw [hLdef, Real.log_mul (by norm_num) hTpos.ne']
    have h4 : Real.log 2 ≤ 0.7 := by
      nlinarith [Real.log_two_lt_d9]
    have h5 : 300 * Real.log (2*T) ≤ 307*L := by
      rw [h3]
      nlinarith
    linarith
  -- (E) the 3-4-1 assembly
  have h341 := three_four_one (σ := σ) (t := T) hσ1
  have hkey : 4/(σ - β) ≤ 31508*L := by
    have hσβ : (0:ℝ) < σ - β := by linarith
    have hc1 : 0 ≤ 3 * (10000*L + 3)
        + 4 * (-(1/(σ - β)) + 300*L) + 307*L := by
      calc (0:ℝ) ≤ 3 * (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re
          + 4 * (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₁).re
          + (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₂).re := h341
        _ ≤ 3 * (10000*L + 3)
            + 4 * (-(1/(σ - β)) + 300*L) + 307*L := by
            have := hΦ0
            have := hΦ1
            have := hΦ2
            linarith
    have h9L : (9:ℝ) ≤ L := by linarith
    have h4d : 4/(σ - β) = 4*(1/(σ - β)) := by ring
    rw [h4d]
    linarith
  -- extract β
  have hσβ : (0:ℝ) < σ - β := by linarith
  have hx : 4/(31508*L) ≤ σ - β := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 31508*L)]
    rw [div_le_iff₀ hσβ] at hkey
    nlinarith [hkey]
  have hfinal : β ≤ 1 - (1/50000)/L := by
    have hnum : (1:ℝ)/10000 + 1/50000 ≤ 4/31508 := by norm_num
    have hkey2 : 1/(10000*L) + (1/50000)/L ≤ 4/(31508*L) := by
      have e1 : (1:ℝ)/(10000*L) = (1/10000)/L := (div_div 1 10000 L).symm
      have e2 : (4:ℝ)/(31508*L) = (4/31508)/L := (div_div 4 31508 L).symm
      rw [e1, e2, ← add_div]
      exact div_le_div_of_nonneg_right hnum hLpos.le
    rw [hσdef] at hx
    linarith
  rw [← hLdef, ← hβdef] at *
  exact hfinal

/-- **R5: the exponent-1 zero-free region.**  Every zero `ρ = β + iγ` of `ζ`
with `|γ| ≥ e³²` satisfies `β ≤ 1 − (1/50000)/log|γ|`.  De la Vallée
Poussin's region, assembled from the compiled 3-4-1 positivity, the sharp
pole rung, and the movable-center partial fraction. -/
theorem zero_free_region_exponent_one :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      Real.exp 32 ≤ |ρ.im| → ρ.re ≤ 1 - c₀ / Real.log |ρ.im| := by
  refine ⟨1/50000, by norm_num, ?_⟩
  intro ρ hζρ him
  rcases abs_cases ρ.im with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq] at him ⊢
    exact zero_free_region_exponent_one_aux hζρ him
  · have hζρ' : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
      rw [riemannZeta_conj, hζρ, map_zero]
    have hconj_im : ((starRingEnd ℂ) ρ).im = -ρ.im := Complex.conj_im ρ
    have him' : Real.exp 32 ≤ ((starRingEnd ℂ) ρ).im := by
      rw [hconj_im]
      rw [heq] at him
      linarith
    have haux := zero_free_region_exponent_one_aux hζρ' him'
    rw [Complex.conj_re, hconj_im] at haux
    rw [heq]
    exact haux

end ExponentOneRegion

section WindowCount
/-!
## R7a: the unit-window ball count

The divisor of ζ over `B(2+iT, 8/5)` is at most `24·log T` — the ball
reaches `σ = 1/4` (its closure touches it; the quarter-strip growth B2″
covers the sphere) and contains every zero with `β ≥ ½`, `|γ−T| ≤ ½`
(distance² ≤ 9/4 + 1/4 < 64/25).  Zeros left of the line enter through
their FE partners.  Feeds the explicit decay of the tail `τ(H)` in the
band floor.
-/

set_option maxHeartbeats 3200000 in
/-- **R7a: the ball count at `2+iT`.** -/
theorem zeta_ball_count_two {T : ℝ} (hT : Real.exp 4 ≤ T) :
    (↑(∑ᶠ u, MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2:ℂ) + T * Complex.I) (8/5)) u) : ℝ)
      ≤ 24 * Real.log T := by
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 4) hT
  have hL4 : (4:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 4) hT
    rwa [Real.log_exp] at this
  have hT7 : (50:ℝ) ≤ T := by
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
        * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    nlinarith [he2, Real.exp_pos 1]
  set L : ℝ := Real.log T with hLdef
  have hLpos : (0:ℝ) < L := by linarith
  set c : ℂ := (2:ℂ) + T * Complex.I with hcdef
  have hcre : c.re = 2 := by
    rw [hcdef]
    simp
  have hcim : c.im = T := by
    rw [hcdef]
    simp
  have hT34ge1 : (1:ℝ) ≤ T ^ ((3:ℝ)/4) := by
    calc (1:ℝ) = 1 ^ ((3:ℝ)/4) := (Real.one_rpow _).symm
      _ ≤ T ^ ((3:ℝ)/4) := Real.rpow_le_rpow (by norm_num) (by linarith)
        (by norm_num)
  -- analyticity on the closed ball
  have hanal : AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall c (7/4)) := by
    apply AnalyticOnNhd.mono
      (DifferentiableOn.analyticOnNhd
        (f := riemannZeta) (s := {z : ℂ | z ≠ 1})
        (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
        isOpen_ne)
    intro z hz
    simp only [Metric.mem_closedBall] at hz
    intro h1
    rw [h1, dist_eq_norm] at hz
    have him : |((1:ℂ) - c).im| ≤ ‖(1:ℂ) - c‖ := Complex.abs_im_le_norm _
    have : ((1:ℂ) - c).im = -T := by
      simp [Complex.sub_im, hcim]
    rw [this, abs_neg, abs_of_pos hTpos] at him
    linarith
  -- the M-bound on the ball
  have hM : ∀ z ∈ Metric.closedBall c (7/4),
      ‖riemannZeta z‖ ≤ 48 * T ^ ((3:ℝ)/4) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre : |(z - c).re| ≤ 7/4 := le_trans (Complex.abs_re_le_norm _) hz
    have him : |(z - c).im| ≤ 7/4 := le_trans (Complex.abs_im_le_norm _) hz
    rw [Complex.sub_re, hcre] at hre
    rw [Complex.sub_im, hcim] at him
    rw [abs_le] at hre him
    rcases le_or_gt z.re 2 with hre2 | hre2
    · -- quarter-strip growth
      have hzim2 : (2:ℝ) ≤ |z.im| := by
        rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
        linarith
      have hgrowth := zeta_polynomial_growth_quarter hzim2
        (by linarith) hre2
      have hzimT : |z.im| ≤ 2 * T := by
        rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
        linarith
      calc ‖riemannZeta z‖ ≤ 24 * |z.im| ^ ((3:ℝ)/4) := hgrowth
        _ ≤ 24 * (2 * T) ^ ((3:ℝ)/4) := by
            apply mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (abs_nonneg _) hzimT (by norm_num))
              (by norm_num)
        _ = 24 * ((2:ℝ) ^ ((3:ℝ)/4) * T ^ ((3:ℝ)/4)) := by
            rw [Real.mul_rpow (by norm_num) hTpos.le]
        _ ≤ 24 * (2 * T ^ ((3:ℝ)/4)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply mul_le_mul_of_nonneg_right _
              (Real.rpow_nonneg hTpos.le _)
            calc (2:ℝ) ^ ((3:ℝ)/4) ≤ 2 ^ (1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
        _ = 48 * T ^ ((3:ℝ)/4) := by ring
    · -- right of the line: the series majorant
      have h1 : ‖riemannZeta z‖ ≤ 1 + 1/(z.re - 1) :=
        zeta_norm_le_of_one_lt (by linarith)
      have h2 : 1/(z.re - 1) ≤ 1 := by
        apply div_le_one_of_le₀ (by linarith) (by linarith)
      calc ‖riemannZeta z‖ ≤ 1 + 1/(z.re - 1) := h1
        _ ≤ 2 := by linarith
        _ ≤ 48 * T ^ ((3:ℝ)/4) := by nlinarith
  -- the center floor
  have hfloor : (1:ℝ)/2 ≤ ‖riemannZeta c‖ := by
    apply zeta_center_lower_bound
    rw [hcre]
  have hM1 : (1:ℝ) ≤ 48 * T ^ ((3:ℝ)/4) := by nlinarith
  -- Jensen
  have hjensen := AnalyticOnNhd.sum_divisor_le
    (c := c) (r := 8/5) (R := 7/4) (M := 48 * T ^ ((3:ℝ)/4))
    (f := riemannZeta) (by norm_num) (by norm_num) hM1
    (by
      rw [show |(7/4 : ℝ)| = 7/4 by norm_num]
      exact hanal)
    (by
      intro h0
      rw [h0, norm_zero] at hfloor
      linarith)
    (by
      rw [show |(7/4 : ℝ)| = 7/4 by norm_num]
      intro z hz
      exact hM z (Metric.sphere_subset_closedBall hz))
  rw [show |(8/5 : ℝ)| = 8/5 by norm_num] at hjensen
  refine le_trans hjensen ?_
  -- numerator ≤ 2L
  have hζcpos : (0:ℝ) < ‖riemannZeta c‖ := by linarith
  have hquot : 48 * T ^ ((3:ℝ)/4) / ‖riemannZeta c‖
      ≤ 96 * T ^ ((3:ℝ)/4) := by
    rw [div_le_iff₀ hζcpos]
    nlinarith [Real.rpow_nonneg hTpos.le ((3:ℝ)/4)]
  have hnum : Real.log (48 * T ^ ((3:ℝ)/4) / ‖riemannZeta c‖)
      ≤ 2 * L := by
    have hstep1 : Real.log (48 * T ^ ((3:ℝ)/4) / ‖riemannZeta c‖)
        ≤ Real.log (96 * T ^ ((3:ℝ)/4)) :=
      Real.log_le_log (by positivity) hquot
    have hsplit : Real.log (96 * T ^ ((3:ℝ)/4))
        = Real.log 96 + (3/4) * L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hTpos]
    have hlog96 : Real.log 96 ≤ 5 := by
      have h96 : (96:ℝ) ≤ 2 ^ (7:ℕ) := by norm_num
      calc Real.log 96 ≤ Real.log (2^(7:ℕ)) :=
          Real.log_le_log (by norm_num) h96
        _ = 7 * Real.log 2 := by
            rw [Real.log_pow]
            push_cast
            ring
        _ ≤ 5 := by nlinarith [Real.log_two_lt_d9]
    rw [hsplit] at hstep1
    have h5L : (5:ℝ) ≤ (5/4) * L := by linarith
    linarith
  -- denominator ≥ 3/35
  have hden : (3:ℝ)/35 ≤ Real.log ((7/4 : ℝ) / (8/5 : ℝ)) := by
    have hval : ((7/4 : ℝ) / (8/5 : ℝ)) = 35/32 := by norm_num
    rw [hval]
    have h1 : Real.log (32/35 : ℝ) ≤ 32/35 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have h2 : Real.log (35/32 : ℝ) = -Real.log (32/35 : ℝ) := by
      rw [← Real.log_inv]
      norm_num
    rw [h2]
    linarith
  have hdenpos : (0:ℝ) < Real.log ((7/4 : ℝ) / (8/5 : ℝ)) := by linarith
  rw [div_le_iff₀ hdenpos]
  calc Real.log (48 * T ^ ((3:ℝ)/4) / ‖riemannZeta c‖)
      ≤ 2 * L := hnum
    _ ≤ 24 * L * (3/35) := by nlinarith
    _ ≤ 24 * Real.log T * Real.log ((7/4 : ℝ) / (8/5 : ℝ)) := by
        rw [← hLdef]
        apply mul_le_mul_of_nonneg_left hden (by positivity)

/-- **R7b: the ξ/ζ order bridge off the real axis.**  For `z.im ≠ 0`,
`analyticOrderAt ξ z = analyticOrderAt ζ z`: near such `z`,
`ξ(s) = (s(s−1)/2)·Gammaℝ(s)·ζ(s)` and the prefactor is a unit
(no poles, no zeros, off the real axis). -/
theorem xi_order_eq_zeta_order {z : ℂ} (hz : z.im ≠ 0) :
    analyticOrderAt ZD.riemannXi z = analyticOrderAt riemannZeta z := by
  set u : ℂ → ℂ := fun s => (s * (s - 1) / 2) * Complex.Gammaℝ s with hu
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hball : Metric.ball z |z.im| ∈ nhds z :=
    Metric.ball_mem_nhds z (abs_pos.mpr hz)
  have him_ball : ∀ s ∈ Metric.ball z |z.im|, s.im ≠ 0 := by
    intro s hs h0
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have habs := Complex.abs_im_le_norm (s - z)
    rw [Complex.sub_im, h0, zero_sub, abs_neg] at habs
    linarith
  have hGpole : ∀ s : ℂ, s.im ≠ 0 → ∀ m : ℕ, s / 2 ≠ -(m:ℂ) := by
    intro s hsim m h
    apply hsim
    have := congrArg Complex.im h
    simp at this
    exact this
  have hGne : ∀ s : ℂ, s.im ≠ 0 → Complex.Gammaℝ s ≠ 0 := by
    intro s hsim
    rw [Complex.Gammaℝ]
    apply mul_ne_zero
    · rw [Complex.cpow_def_of_ne_zero hπ]
      exact Complex.exp_ne_zero _
    · exact Complex.Gamma_ne_zero (hGpole s hsim)
  -- the local identity ξ = u·ζ
  have hEE : ZD.riemannXi =ᶠ[nhds z] fun s => u s * riemannZeta s := by
    filter_upwards [hball] with s hs
    have hsim := him_ball s hs
    have hs0 : s ≠ 0 := by
      intro h
      apply hsim
      rw [h]
      simp
    have hs1 : s ≠ 1 := by
      intro h
      apply hsim
      rw [h]
      simp
    have hΛ : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
      rw [riemannZeta_def_of_ne_zero hs0]
      field_simp [hGne s hsim]
    have hξ : ZD.riemannXi s = (s * (s - 1) / 2) * completedRiemannZeta s := by
      show (s * (s - 1) / 2) * completedRiemannZeta₀ s + 1 / 2 = _
      rw [completedRiemannZeta_eq]
      field_simp
      ring
    rw [hξ, hΛ, hu]
    ring
  rw [analyticOrderAt_congr hEE]
  -- u is analytic and nonvanishing at z
  have hu_anal : AnalyticAt ℂ u z := by
    have hdiff : DifferentiableOn ℂ u (Metric.ball z |z.im|) := by
      intro s hs
      have hsim := him_ball s hs
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.mul
      · exact ((differentiableAt_id.mul
          (differentiableAt_id.sub_const 1)).div_const 2)
      · rw [show Complex.Gammaℝ = fun w : ℂ =>
            ((Real.pi : ℝ) : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) by
          funext w
          rw [Complex.Gammaℝ]]
        apply DifferentiableAt.mul
        · apply DifferentiableAt.const_cpow
          · exact (differentiableAt_id.neg).div_const 2
          · exact Or.inl hπ
        · exact (Complex.differentiableAt_Gamma _
            (hGpole s hsim)).comp s (differentiableAt_id.div_const 2)
    exact (hdiff.analyticOnNhd Metric.isOpen_ball) z
      (Metric.mem_ball_self (abs_pos.mpr hz))
  have hζ_anal : AnalyticAt ℂ riemannZeta z := by
    have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
      fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
    apply (hdiff.analyticOnNhd isOpen_ne) z
    intro h
    apply hz
    rw [h]
    simp
  have hu_ne : u z ≠ 0 := by
    rw [hu]
    apply mul_ne_zero
    · apply div_ne_zero _ (by norm_num)
      apply mul_ne_zero
      · intro h
        apply hz
        rw [h]
        simp
      · intro h
        apply hz
        have : z = 1 := by
          have := congrArg (· + (1:ℂ)) h
          simpa using this
        rw [this]
        simp
    · exact hGne z hz
  rw [show (fun s => u s * riemannZeta s) = u * riemannZeta from rfl]
  rw [analyticOrderAt_mul hu_anal hζ_anal,
    hu_anal.analyticOrderAt_eq_zero.mpr hu_ne, zero_add]

/-- **R7b′: the count bridge** — off the real axis, `xiOrderNat` is the
ζ-multiplicity. -/
theorem xiOrderNat_eq_zeta_orderNat {z : ℂ} (hz : z.im ≠ 0) :
    (ZD.xiOrderNat z : ℤ)
      = ((analyticOrderAt riemannZeta z).map (Nat.cast : ℕ → ℤ)).untop₀ := by
  unfold ZD.xiOrderNat analyticOrderNatAt
  rw [xi_order_eq_zeta_order hz]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℕ∞) = analyticOrderAt riemannZeta z := by
    apply ENat.ne_top_iff_exists.mp
    rw [← xi_order_eq_zeta_order hz]
    exact ZD.riemannXi_analyticOrderAt_ne_top_everywhere z
  rw [← hm]
  rfl

set_option maxHeartbeats 3200000 in
/-- **The FIXED-CENTER local count** (design fix, ledger 336): at
`c = 1 + 1/32 + iT` the Möbius floor is the constant `1/33` and the
membership constraints dissolve; the divisor of `B̄(c, 1/8)` is at most
`13·log T` for `T ≥ e⁴`. -/
theorem zeta_local_zero_count_fixed {T : ℝ} (hT : Real.exp 4 ≤ T) :
    (↑(∑ᶠ u, MeromorphicOn.divisor riemannZeta
        (Metric.closedBall (((1 + 1/32 : ℝ) : ℂ) + T * Complex.I)
          (1/8)) u) : ℝ)
      ≤ 13 * Real.log T := by
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 4) hT
  have hL4 : (4:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 4) hT
    rwa [Real.log_exp] at this
  have hT50 : (50:ℝ) ≤ T := by
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
        * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    nlinarith [he2, Real.exp_pos 1]
  set L : ℝ := Real.log T with hLdef
  have hLpos : (0:ℝ) < L := by linarith
  set c : ℂ := ((1 + 1/32 : ℝ) : ℂ) + T * Complex.I with hcdef
  have hcre : c.re = 1 + 1/32 := by
    rw [hcdef]
    simp
  have hcim : c.im = T := by
    rw [hcdef]
    simp
  have hT14ge1 : (1:ℝ) ≤ T ^ ((1:ℝ)/4) := by
    calc (1:ℝ) = 1 ^ ((1:ℝ)/4) := (Real.one_rpow _).symm
      _ ≤ T ^ ((1:ℝ)/4) := Real.rpow_le_rpow (by norm_num) (by linarith)
        (by norm_num)
  have hanal : AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall c (3/16)) := by
    apply AnalyticOnNhd.mono
      (DifferentiableOn.analyticOnNhd
        (f := riemannZeta) (s := {z : ℂ | z ≠ 1})
        (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
        isOpen_ne)
    intro z hz
    simp only [Metric.mem_closedBall] at hz
    intro h1
    rw [h1, dist_eq_norm] at hz
    have him : |((1:ℂ) - c).im| ≤ ‖(1:ℂ) - c‖ := Complex.abs_im_le_norm _
    have : ((1:ℂ) - c).im = -T := by
      simp [Complex.sub_im, hcim]
    rw [this, abs_neg, abs_of_pos hTpos] at him
    linarith
  have hM : ∀ z ∈ Metric.closedBall c (3/16),
      ‖riemannZeta z‖ ≤ 32 * T ^ ((1:ℝ)/4) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre : |(z - c).re| ≤ 3/16 := le_trans (Complex.abs_re_le_norm _) hz
    have him : |(z - c).im| ≤ 3/16 := le_trans (Complex.abs_im_le_norm _) hz
    rw [Complex.sub_re, hcre] at hre
    rw [Complex.sub_im, hcim] at him
    rw [abs_le] at hre him
    have hzim2 : (2:ℝ) ≤ |z.im| := by
      rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
      linarith
    have hgrowth := zeta_polynomial_growth hzim2 (by linarith) (by linarith)
    have hzimT : |z.im| ≤ 2 * T := by
      rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
      linarith
    calc ‖riemannZeta z‖ ≤ 16 * |z.im| ^ ((1:ℝ)/4) := hgrowth
      _ ≤ 16 * (2 * T) ^ ((1:ℝ)/4) := by
          apply mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg _) hzimT (by norm_num))
            (by norm_num)
      _ = 16 * ((2:ℝ) ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/4)) := by
          rw [Real.mul_rpow (by norm_num) hTpos.le]
      _ ≤ 16 * (2 * T ^ ((1:ℝ)/4)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _
            (Real.rpow_nonneg hTpos.le _)
          calc (2:ℝ) ^ ((1:ℝ)/4) ≤ 2 ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
      _ = 32 * T ^ ((1:ℝ)/4) := by ring
  -- the CONSTANT center floor
  have hcre1 : (1:ℝ) < c.re := by
    rw [hcre]
    norm_num
  have hfloor : (1:ℝ)/33 ≤ ‖riemannZeta c‖ := by
    have h := zeta_center_floor hcre1
    have heq : (c.re - 1) / c.re = 1/33 := by
      rw [hcre]
      norm_num
    rwa [heq] at h
  have hζcpos : (0:ℝ) < ‖riemannZeta c‖ := by linarith
  have hM1 : (1:ℝ) ≤ 32 * T ^ ((1:ℝ)/4) := by nlinarith
  have hjensen := AnalyticOnNhd.sum_divisor_le
    (c := c) (r := 1/8) (R := 3/16) (M := 32 * T ^ ((1:ℝ)/4))
    (f := riemannZeta) (by norm_num) (by norm_num) hM1
    (by
      rw [show |(3/16 : ℝ)| = 3/16 by norm_num]
      exact hanal)
    (by
      intro h0
      rw [h0, norm_zero] at hfloor
      linarith)
    (by
      rw [show |(3/16 : ℝ)| = 3/16 by norm_num]
      intro z hz
      exact hM z (Metric.sphere_subset_closedBall hz))
  rw [show |(1/8 : ℝ)| = 1/8 by norm_num] at hjensen
  refine le_trans hjensen ?_
  have hquot : 32 * T ^ ((1:ℝ)/4) / ‖riemannZeta c‖
      ≤ 1056 * T ^ ((1:ℝ)/4) := by
    rw [div_le_iff₀ hζcpos]
    nlinarith [Real.rpow_nonneg hTpos.le ((1:ℝ)/4)]
  have hRr : Real.log ((3/16 : ℝ) / (1/8 : ℝ)) = Real.log (3/2) := by
    norm_num
  rw [hRr]
  have hlog32pos : (0:ℝ) < Real.log (3/2) :=
    Real.log_pos (by norm_num)
  rw [div_le_iff₀ hlog32pos]
  have hnum : Real.log (32 * T ^ ((1:ℝ)/4) / ‖riemannZeta c‖)
      ≤ 2 * L := by
    have hstep1 : Real.log (32 * T ^ ((1:ℝ)/4) / ‖riemannZeta c‖)
        ≤ Real.log (1056 * T ^ ((1:ℝ)/4)) :=
      Real.log_le_log (by positivity) hquot
    have hsplit : Real.log (1056 * T ^ ((1:ℝ)/4))
        = Real.log 1056 + (1/4) * L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hTpos]
    have hlog1056 : Real.log 1056 ≤ 7 := by
      have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
        nlinarith [Real.exp_one_gt_d9]
      have he1 : (2.71:ℝ) ≤ Real.exp 1 := by
        nlinarith [Real.exp_one_gt_d9]
      have h7 : Real.exp 7 = (Real.exp 1 * Real.exp 1)
          * (Real.exp 1 * Real.exp 1)
          * (Real.exp 1 * Real.exp 1) * Real.exp 1 := by
        rw [show (7:ℝ) = 1+1+(1+1)+(1+1)+1 by norm_num]
        simp only [Real.exp_add]
      have hexp7 : (1056:ℝ) ≤ Real.exp 7 := by
        have hp := Real.exp_pos 1
        have h4 : (54.46:ℝ) ≤ (Real.exp 1 * Real.exp 1)
            * (Real.exp 1 * Real.exp 1) := by
          nlinarith
        have h6 : (401.9:ℝ) ≤ (Real.exp 1 * Real.exp 1)
            * (Real.exp 1 * Real.exp 1) * (Real.exp 1 * Real.exp 1) := by
          nlinarith
        rw [h7]
        nlinarith
      calc Real.log 1056 ≤ Real.log (Real.exp 7) :=
          Real.log_le_log (by norm_num) hexp7
        _ = 7 := Real.log_exp 7
    rw [hsplit] at hstep1
    have h7L : (7:ℝ) ≤ (7/4) * L := by linarith
    linarith
  have hden : (1:ℝ)/3 ≤ Real.log (3/2) := by
    have h1 : Real.log (2/3 : ℝ) ≤ 2/3 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have h2 : Real.log (3/2 : ℝ) = -Real.log (2/3 : ℝ) := by
      rw [← Real.log_inv]
      norm_num
    rw [h2]
    linarith
  calc Real.log (32 * T ^ ((1:ℝ)/4) / ‖riemannZeta c‖)
      ≤ 2 * L := hnum
    _ ≤ 13 * L * (1/3) := by nlinarith
    _ ≤ 13 * Real.log T * Real.log (3/2) := by
        rw [← hLdef]
        apply mul_le_mul_of_nonneg_left hden (by positivity)

set_option maxHeartbeats 3200000 in
/-- **The FIXED-CENTER partial fraction** (design fix): at
`c = 1 + 1/32 + iT`, for `T ≥ e⁴` — no `log T` in the center, threshold
freed from the moving-center artifact. -/
theorem zeta_partial_fraction_fixed {T : ℝ} (hT : Real.exp 4 ≤ T) :
    ∃ (S : Finset ℂ) (n : ℂ → ℕ),
      (∀ u ∈ S, u ∈ Metric.closedBall
        (((1 + 1/32 : ℝ) : ℂ) + T * Complex.I) (1/8)) ∧
      (∀ u ∈ S, 1 ≤ n u → riemannZeta u = 0) ∧
      (∀ u ∈ Metric.closedBall
        (((1 + 1/32 : ℝ) : ℂ) + T * Complex.I) (1/8),
        riemannZeta u = 0 → u ∈ S ∧ 1 ≤ n u) ∧
      ∀ s ∈ Metric.closedBall
          (((1 + 1/32 : ℝ) : ℂ) + T * Complex.I) (1/32),
        riemannZeta s ≠ 0 →
        ‖logDeriv riemannZeta s - ∑ u ∈ S, (n u : ℂ) / (s - u)‖
          ≤ 300 * Real.log T := by
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 4) hT
  have hL4 : (4:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 4) hT
    rwa [Real.log_exp] at this
  have hT50 : (50:ℝ) ≤ T := by
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
        * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    nlinarith [he2, Real.exp_pos 1]
  set L : ℝ := Real.log T with hLdef
  have hLpos : (0:ℝ) < L := by linarith
  set c : ℂ := ((1 + 1/32 : ℝ) : ℂ) + T * Complex.I with hcdef
  have hcre : c.re = 1 + 1/32 := by
    rw [hcdef]
    simp
  have hcim : c.im = T := by
    rw [hcdef]
    simp
  have hT14ge1 : (1:ℝ) ≤ T ^ ((1:ℝ)/4) := by
    calc (1:ℝ) = 1 ^ ((1:ℝ)/4) := (Real.one_rpow _).symm
      _ ≤ T ^ ((1:ℝ)/4) := Real.rpow_le_rpow (by norm_num) (by linarith)
        (by norm_num)
  have hanal : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c (1/8)) := by
    apply AnalyticOnNhd.mono
      (DifferentiableOn.analyticOnNhd
        (f := riemannZeta) (s := {z : ℂ | z ≠ 1})
        (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
        isOpen_ne)
    intro z hz
    simp only [Metric.mem_closedBall] at hz
    intro h1
    rw [h1, dist_eq_norm] at hz
    have him : |((1:ℂ) - c).im| ≤ ‖(1:ℂ) - c‖ := Complex.abs_im_le_norm _
    have : ((1:ℂ) - c).im = -T := by
      simp [Complex.sub_im, hcim]
    rw [this, abs_neg, abs_of_pos hTpos] at him
    linarith
  have hM : ∀ z ∈ Metric.closedBall c (1/8),
      ‖riemannZeta z‖ ≤ 32 * T ^ ((1:ℝ)/4) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre : |(z - c).re| ≤ 1/8 := le_trans (Complex.abs_re_le_norm _) hz
    have him : |(z - c).im| ≤ 1/8 := le_trans (Complex.abs_im_le_norm _) hz
    rw [Complex.sub_re, hcre] at hre
    rw [Complex.sub_im, hcim] at him
    rw [abs_le] at hre him
    have hzim2 : (2:ℝ) ≤ |z.im| := by
      rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
      linarith
    have hgrowth := zeta_polynomial_growth hzim2 (by linarith) (by linarith)
    have hzimT : |z.im| ≤ 2 * T := by
      rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
      linarith
    calc ‖riemannZeta z‖ ≤ 16 * |z.im| ^ ((1:ℝ)/4) := hgrowth
      _ ≤ 16 * (2 * T) ^ ((1:ℝ)/4) := by
          apply mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg _) hzimT (by norm_num))
            (by norm_num)
      _ = 16 * ((2:ℝ) ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/4)) := by
          rw [Real.mul_rpow (by norm_num) hTpos.le]
      _ ≤ 16 * (2 * T ^ ((1:ℝ)/4)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _
            (Real.rpow_nonneg hTpos.le _)
          calc (2:ℝ) ^ ((1:ℝ)/4) ≤ 2 ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
      _ = 32 * T ^ ((1:ℝ)/4) := by ring
  have hcre1 : (1:ℝ) < c.re := by
    rw [hcre]
    norm_num
  have hfloor : (1:ℝ)/33 ≤ ‖riemannZeta c‖ := by
    have h := zeta_center_floor hcre1
    have heq : (c.re - 1) / c.re = 1/33 := by
      rw [hcre]
      norm_num
    rwa [heq] at h
  have hmpos : (0:ℝ) < (1:ℝ)/33 := by norm_num
  have hMm : 32 * T ^ ((1:ℝ)/4) / ((1:ℝ)/33)
      = 1056 * T ^ ((1:ℝ)/4) := by
    field_simp
    ring
  have hlogpos : 0 < Real.log (32 * T ^ ((1:ℝ)/4) / ((1:ℝ)/33)) := by
    rw [hMm]
    apply Real.log_pos
    nlinarith
  have hlog2L : Real.log (32 * T ^ ((1:ℝ)/4) / ((1:ℝ)/33)) ≤ 2 * L := by
    rw [hMm]
    have hsplit : Real.log (1056 * T ^ ((1:ℝ)/4))
        = Real.log 1056 + (1/4) * L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hTpos]
    have hlog1056 : Real.log 1056 ≤ 7 := by
      have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
        nlinarith [Real.exp_one_gt_d9]
      have he1 : (2.71:ℝ) ≤ Real.exp 1 := by
        nlinarith [Real.exp_one_gt_d9]
      have h7 : Real.exp 7 = (Real.exp 1 * Real.exp 1)
          * (Real.exp 1 * Real.exp 1)
          * (Real.exp 1 * Real.exp 1) * Real.exp 1 := by
        rw [show (7:ℝ) = 1+1+(1+1)+(1+1)+1 by norm_num]
        simp only [Real.exp_add]
      have hexp7 : (1056:ℝ) ≤ Real.exp 7 := by
        have hp := Real.exp_pos 1
        have h4' : (54.46:ℝ) ≤ (Real.exp 1 * Real.exp 1)
            * (Real.exp 1 * Real.exp 1) := by
          nlinarith
        have h6' : (401.9:ℝ) ≤ (Real.exp 1 * Real.exp 1)
            * (Real.exp 1 * Real.exp 1) * (Real.exp 1 * Real.exp 1) := by
          nlinarith
        rw [h7]
        nlinarith
      calc Real.log 1056 ≤ Real.log (Real.exp 7) :=
          Real.log_le_log (by norm_num) hexp7
        _ = 7 := Real.log_exp 7
    rw [hsplit]
    linarith
  obtain ⟨S, n, hS_mem, hn_eq, hd_zero, hbound⟩ :=
    landau_lemma (c := c) (r := 1/8) (by norm_num) hmpos hanal hM hfloor
      hlogpos
  refine ⟨S, n, hS_mem, ?_, ?_, ?_⟩
  · intro u hu hnu
    by_contra hζu
    have hord : analyticOrderAt riemannZeta u = 0 :=
      (hanal u (hS_mem u hu)).analyticOrderAt_eq_zero.mpr hζu
    have hdiv := hn_eq u hu
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanal (hS_mem u hu),
      hord] at hdiv
    simp at hdiv
    omega
  · intro u hu hζu
    have hζc : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hcre1
    have hordne : analyticOrderAt riemannZeta u ≠ 0 := by
      rw [analyticOrderAt_ne_zero]
      exact ⟨hanal u hu, hζu⟩
    have hordtop : analyticOrderAt riemannZeta u ≠ ⊤ :=
      analyticOrderAt_ne_top_of_ne_zero
        (convex_closedBall c (1/8)).isPreconnected hanal
        (Metric.mem_closedBall_self (by norm_num)) hζc hu
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℕ∞) = analyticOrderAt riemannZeta u :=
      ENat.ne_top_iff_exists.mp hordtop
    have hm_ne : m ≠ 0 := fun h => hordne (by rw [← hm, h]; rfl)
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm_ne
    have hdivge : 1 ≤ MeromorphicOn.divisor riemannZeta
        (Metric.closedBall c (1/8)) u := by
      rw [MeromorphicOn.divisor_apply hanal.meromorphicOn hu,
        (hanal u hu).meromorphicOrderAt_eq, ← hm]
      simp
      exact hm1
    have huS : u ∈ S := by
      by_contra huS
      have := hd_zero u huS
      omega
    refine ⟨huS, ?_⟩
    have := hn_eq u huS
    omega
  · intro s hs hζs
    have hs32 : s ∈ Metric.closedBall c ((1/8)/4) := by
      have := Metric.mem_closedBall.mp hs
      rw [Metric.mem_closedBall]
      linarith
    have hb := hbound s hs32 hζs
    have hNle : (∑ u ∈ S, (n u : ℝ)) ≤ 13 * L := by
      have hsupp : Function.support
          (fun u => MeromorphicOn.divisor riemannZeta
            (Metric.closedBall c (1/8)) u) ⊆ (S : Set ℂ) := by
        intro u hu
        by_contra huS
        exact hu (hd_zero u huS)
      have hfin : (∑ᶠ u, MeromorphicOn.divisor riemannZeta
          (Metric.closedBall c (1/8)) u)
          = ∑ u ∈ S, MeromorphicOn.divisor riemannZeta
              (Metric.closedBall c (1/8)) u :=
        finsum_eq_sum_of_support_subset _ hsupp
      have hcast : (∑ u ∈ S, (n u : ℝ))
          = ((∑ᶠ u, MeromorphicOn.divisor riemannZeta
              (Metric.closedBall c (1/8)) u : ℤ) : ℝ) := by
        rw [hfin]
        push_cast
        apply Finset.sum_congr rfl
        intro u hu
        exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) (hn_eq u hu)
      rw [hcast]
      exact zeta_local_zero_count_fixed hT
    calc ‖logDeriv riemannZeta s - ∑ u ∈ S, (n u : ℂ) / (s - u)‖
        ≤ 8 * Real.log (32 * T ^ ((1:ℝ)/4) / ((1:ℝ)/33)) / (1/8)
          + (∑ u ∈ S, (n u : ℝ)) * (4 / (3 * (1/8))) := hb
      _ ≤ 8 * (2 * L) / (1/8) + (13 * L) * (4 / (3 * (1/8))) := by
          apply add_le_add
          · apply div_le_div_of_nonneg_right _ (by norm_num)
            apply mul_le_mul_of_nonneg_left hlog2L (by norm_num)
          · apply mul_le_mul_of_nonneg_right hNle (by norm_num)
      _ = 128 * L + (416/3) * L := by ring
      _ ≤ 300 * L := by linarith

end WindowCount

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.xi_divisor_eq_orderNat
#print axioms CriticalLinePhasor.DVP.xi_weighted_zero_count_disk_bound
#print axioms CriticalLinePhasor.DVP.moebius_lseries_norm_le
#print axioms CriticalLinePhasor.DVP.zeta_center_lower_bound
#print axioms CriticalLinePhasor.DVP.moebius_lseries_norm_le_of_one_lt
#print axioms CriticalLinePhasor.DVP.zeta_center_floor
#print axioms CriticalLinePhasor.DVP.zeta_local_zero_count
#print axioms CriticalLinePhasor.DVP.zeta_partial_fraction
#print axioms CriticalLinePhasor.DVP.zeta_norm_le_of_one_lt
#print axioms CriticalLinePhasor.DVP.zeta_re_pole_floor
#print axioms CriticalLinePhasor.DVP.zeta_deriv_pole_bound
#print axioms CriticalLinePhasor.DVP.zeta_logDeriv_pole_rung
#print axioms CriticalLinePhasor.DVP.three_four_one
#print axioms CriticalLinePhasor.DVP.zeta_re_floor_sharp
#print axioms CriticalLinePhasor.DVP.zeta_deriv_sharp
#print axioms CriticalLinePhasor.DVP.zeta_logDeriv_rung_sharp
#print axioms CriticalLinePhasor.DVP.zero_free_region_exponent_one_aux
#print axioms CriticalLinePhasor.DVP.zero_free_region_exponent_one
#print axioms CriticalLinePhasor.DVP.zeta_ball_count_two
#print axioms CriticalLinePhasor.DVP.xi_order_eq_zeta_order
#print axioms CriticalLinePhasor.DVP.xiOrderNat_eq_zeta_orderNat
#print axioms CriticalLinePhasor.DVP.zeta_local_zero_count_fixed
#print axioms CriticalLinePhasor.DVP.zeta_partial_fraction_fixed
end AxiomAudit
