import RequestProject.DVPThetaAsymptotic

/-!
# `S_all` is continuous off the countable ordinate set

Foundation of the a.e.-IBP campaign (417): the nontrivial zeros are
countable (finite in every ball), their ordinates form a countable set,
and off that set the strip census is locally constant, so `S_all` is
continuous — the countable-exception hypothesis the FTC/IBP machinery
consumes.
-/

open Complex
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.ResidueJump

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The nontrivial zeros form a countable set. -/
theorem nontrivialZeros_countable : (ZD.NontrivialZeros).Countable := by
  have hcover : ZD.NontrivialZeros
      = ⋃ n : ℕ, ZD.NontrivialZeros ∩ Metric.closedBall 0 n := by
    ext ρ
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hρ
      obtain ⟨n, hn⟩ := exists_nat_ge ‖ρ‖
      refine ⟨n, hρ, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hn
    · rintro ⟨n, hρ, -⟩
      exact hρ
  rw [hcover]
  apply Set.countable_iUnion
  intro n
  exact (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite n).countable

/-- The zero ordinates form a countable set. -/
theorem zeroOrdinates_countable :
    (Complex.im '' ZD.NontrivialZeros).Countable :=
  nontrivialZeros_countable.image _

/-- Off the ordinate set, the strip census is locally constant. -/
theorem stripZeroCountMult_eventually_const {t : ℝ} (ht : 0 < t)
    (hD : t ∉ Complex.im '' ZD.NontrivialZeros) :
    ∀ᶠ s in nhds t, stripZeroCountMult s = stripZeroCountMult t := by
  have hfin : (ZD.NontrivialZeros ∩ Metric.closedBall 0 (t + 2)).Finite :=
    ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (t + 2)
  set G : Set ℝ := (fun ρ : ℂ => ρ.im) ''
    (ZD.NontrivialZeros ∩ Metric.closedBall 0 (t + 2)) with hGdef
  have hGfin : G.Finite := hfin.image _
  -- a positive gap to the nearby ordinates
  have hgap : ∃ δ, 0 < δ ∧ δ ≤ 1 ∧ ∀ y ∈ G, δ ≤ |y - t| := by
    rcases G.eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, one_pos, le_refl 1, fun y hy => absurd hy (by simp [hemp])⟩
    · obtain ⟨y₀, hy₀G, hy₀min⟩ :=
        Set.exists_min_image G (fun y => |y - t|) hGfin hne
      have hy₀pos : 0 < |y₀ - t| := by
        rw [abs_pos, sub_ne_zero]
        intro heq
        apply hD
        obtain ⟨ρ, hρ, hρim⟩ := hy₀G
        have hρim' : ρ.im = y₀ := by simpa using hρim
        exact ⟨ρ, hρ.1, hρim'.trans heq⟩
      refine ⟨min |y₀ - t| 1, lt_min hy₀pos one_pos, min_le_right _ _, ?_⟩
      intro y hy
      calc min |y₀ - t| 1 ≤ |y₀ - t| := min_le_left _ _
        _ ≤ |y - t| := hy₀min y hy
  obtain ⟨δ, hδ0, hδ1, hδgap⟩ := hgap
  -- the census is constant on the δ/2-ball
  have hconst : ∀ s : ℝ, |s - t| < δ/2 →
      stripZeroCountMult s = stripZeroCountMult t := by
    -- squeeze between the endpoints via monotonicity and equal endpoints
    have hends : stripZeroCountMult (t + δ/2) ≤ stripZeroCountMult (t - δ/2) := by
      have hsub := stripZeroFinset_subset
        (show t - δ/2 ≤ t + δ/2 by linarith)
      have hdiff := Finset.sum_sdiff (f := fun ρ => ZD.xiOrderNat ρ) hsub
      have hempty : stripZeroFinset (t + δ/2) \ stripZeroFinset (t - δ/2)
          = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro ρ hρ
        rw [Finset.mem_sdiff] at hρ
        obtain ⟨hin, hout⟩ := hρ
        have hin' : ρ ∈ stripZeroWindow (t + δ/2) := by
          rw [show stripZeroFinset (t + δ/2)
              = (stripZeroWindow_finite (t + δ/2)).toFinset from rfl,
            Set.Finite.mem_toFinset] at hin
          exact hin
        obtain ⟨hNT, him0, himle⟩ := hin'
        have himgt : t - δ/2 < ρ.im := by
          by_contra hc
          push_neg at hc
          apply hout
          show ρ ∈ (stripZeroWindow_finite (t - δ/2)).toFinset
          rw [Set.Finite.mem_toFinset]
          exact ⟨hNT, him0, hc⟩
        -- ρ is in the local ball, so its ordinate is gap-separated — contradiction
        have hball : ρ ∈ Metric.closedBall (0:ℂ) (t + 2) := by
          rw [Metric.mem_closedBall, dist_zero_right]
          calc ‖ρ‖ = ‖(ρ.re : ℂ) + (ρ.im : ℂ) * I‖ := by rw [Complex.re_add_im]
            _ ≤ ‖(ρ.re : ℂ)‖ + ‖(ρ.im : ℂ) * I‖ := norm_add_le _ _
            _ = |ρ.re| + |ρ.im| := by simp
            _ ≤ 1 + (t + 1) := by
                have h1 : |ρ.re| ≤ 1 := by
                  rw [abs_of_pos hNT.1]
                  exact le_of_lt hNT.2.1
                have h2 : |ρ.im| ≤ t + 1 := by
                  rw [abs_of_pos him0]
                  linarith
                linarith
            _ = t + 2 := by ring
        have hyG : ρ.im ∈ G := ⟨ρ, ⟨hNT, hball⟩, rfl⟩
        have hg := hδgap ρ.im hyG
        have hlt : |ρ.im - t| < δ := by
          rw [abs_lt]
          constructor <;> linarith
        linarith
      show (∑ ρ ∈ stripZeroFinset (t + δ/2), ZD.xiOrderNat ρ)
        ≤ ∑ ρ ∈ stripZeroFinset (t - δ/2), ZD.xiOrderNat ρ
      rw [← hdiff, hempty]
      simp
    intro s hs
    rw [abs_lt] at hs
    have hmono1 : stripZeroCountMult (t - δ/2) ≤ stripZeroCountMult s :=
      stripZeroCountMult_mono (show t - δ/2 ≤ s by linarith)
    have hmono2 : stripZeroCountMult s ≤ stripZeroCountMult (t + δ/2) :=
      stripZeroCountMult_mono (show s ≤ t + δ/2 by linarith)
    have hmono3 : stripZeroCountMult (t - δ/2) ≤ stripZeroCountMult t :=
      stripZeroCountMult_mono (show t - δ/2 ≤ t by linarith)
    have hmono4 : stripZeroCountMult t ≤ stripZeroCountMult (t + δ/2) :=
      stripZeroCountMult_mono (show t ≤ t + δ/2 by linarith)
    omega
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ/2, by linarith, ?_⟩
  intro s hst
  rw [Real.dist_eq] at hst
  exact hconst s hst

/-- **`S_all` is continuous off the countable ordinate set.** -/
theorem sall_continuousAt {t : ℝ} (ht : 0 < t)
    (hD : t ∉ Complex.im '' ZD.NontrivialZeros) :
    ContinuousAt SAll t := by
  have hsplit : SAll = fun s : ℝ =>
      (stripZeroCountMult s : ℝ) - 1 - theta s / Real.pi := by
    funext s
    rw [SAll, Smult]
    have h := stripZeroCountMult_eq_line_add_offLine s
    have hR : (stripZeroCountMult s : ℝ)
        = (zeroEventCountMult s : ℝ) + (offLineStripZeroCountMult s : ℝ) := by
      exact_mod_cast h
    linarith [hR]
  rw [hsplit]
  apply ContinuousAt.sub
  · apply ContinuousAt.sub
    · -- the census is eventually constant, hence continuous
      have hev := stripZeroCountMult_eventually_const ht hD
      apply ContinuousAt.congr (continuousAt_const (y := (stripZeroCountMult t : ℝ)))
      filter_upwards [hev] with s hsev
      rw [hsev]
    · exact continuousAt_const
  · exact (continuous_theta.continuousAt).div_const _

/-- **Right-locally-constant census at EVERY positive height** — no
ordinate-exclusion hypothesis: the open right window avoids the finitely
many local ordinates. -/
theorem stripZeroCountMult_eventually_const_right {t : ℝ} (ht : 0 < t) :
    ∀ᶠ s in nhdsWithin t (Set.Ici t),
      stripZeroCountMult s = stripZeroCountMult t := by
  have hfin : (ZD.NontrivialZeros ∩ Metric.closedBall 0 (t + 2)).Finite :=
    ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (t + 2)
  set G : Set ℝ := ((fun ρ : ℂ => ρ.im) ''
    (ZD.NontrivialZeros ∩ Metric.closedBall 0 (t + 2)))
    ∩ {y : ℝ | t < y} with hGdef
  have hGfin : G.Finite := ((hfin.image _).inter_of_left _)
  have hgap : ∃ δ, 0 < δ ∧ δ ≤ 1 ∧ ∀ y ∈ G, δ ≤ y - t := by
    rcases G.eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, one_pos, le_refl 1, fun y hy => absurd hy (by simp [hemp])⟩
    · obtain ⟨y₀, hy₀G, hy₀min⟩ :=
        Set.exists_min_image G (fun y => y - t) hGfin hne
      have hy₀pos : 0 < y₀ - t := by
        have := hy₀G.2
        simp only [Set.mem_ofPred_eq] at this
        linarith
      refine ⟨min (y₀ - t) 1, lt_min hy₀pos one_pos, min_le_right _ _, ?_⟩
      intro y hy
      calc min (y₀ - t) 1 ≤ y₀ - t := min_le_left _ _
        _ ≤ y - t := hy₀min y hy
  obtain ⟨δ, hδ0, hδ1, hδgap⟩ := hgap
  have hconst : ∀ s : ℝ, t ≤ s → s - t < δ/2 →
      stripZeroCountMult s = stripZeroCountMult t := by
    intro s hts hsδ
    have hsub := stripZeroFinset_subset hts
    have hdiff := Finset.sum_sdiff (f := fun ρ => ZD.xiOrderNat ρ) hsub
    have hempty : stripZeroFinset s \ stripZeroFinset t = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ρ hρ
      rw [Finset.mem_sdiff] at hρ
      obtain ⟨hin, hout⟩ := hρ
      have hin' : ρ ∈ stripZeroWindow s := by
        rw [show stripZeroFinset s
            = (stripZeroWindow_finite s).toFinset from rfl,
          Set.Finite.mem_toFinset] at hin
        exact hin
      obtain ⟨hNT, him0, himle⟩ := hin'
      have himgt : t < ρ.im := by
        by_contra hc
        push_neg at hc
        apply hout
        show ρ ∈ (stripZeroWindow_finite t).toFinset
        rw [Set.Finite.mem_toFinset]
        exact ⟨hNT, him0, hc⟩
      have hball : ρ ∈ Metric.closedBall (0:ℂ) (t + 2) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        calc ‖ρ‖ = ‖(ρ.re : ℂ) + (ρ.im : ℂ) * I‖ := by rw [Complex.re_add_im]
          _ ≤ ‖(ρ.re : ℂ)‖ + ‖(ρ.im : ℂ) * I‖ := norm_add_le _ _
          _ = |ρ.re| + |ρ.im| := by simp
          _ ≤ 1 + (t + 1) := by
              have h1 : |ρ.re| ≤ 1 := by
                rw [abs_of_pos hNT.1]
                exact le_of_lt hNT.2.1
              have h2 : |ρ.im| ≤ t + 1 := by
                rw [abs_of_pos him0]
                linarith
              linarith
          _ = t + 2 := by ring
      have hyG : ρ.im ∈ G := ⟨⟨ρ, ⟨hNT, hball⟩, rfl⟩, by
        simp only [Set.mem_ofPred_eq]
        exact himgt⟩
      have hg := hδgap ρ.im hyG
      linarith
    show (∑ ρ ∈ stripZeroFinset s, ZD.xiOrderNat ρ)
      = ∑ ρ ∈ stripZeroFinset t, ZD.xiOrderNat ρ
    rw [← hdiff, hempty]
    simp
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨δ/2, by linarith, ?_⟩
  intro s hst hIci
  rw [Real.dist_eq] at hst
  have hts : t ≤ s := hIci
  have : s - t < δ/2 := by
    rw [abs_lt] at hst
    linarith [hst.2]
  exact hconst s hts this

/-- **`S_all` is right-continuous at EVERY positive height.** -/
theorem sall_continuousWithinAt_right {t : ℝ} (ht : 0 < t) :
    ContinuousWithinAt SAll (Set.Ici t) t := by
  have hsplit : SAll = fun s : ℝ =>
      (stripZeroCountMult s : ℝ) - 1 - theta s / Real.pi := by
    funext s
    rw [SAll, Smult]
    have h := stripZeroCountMult_eq_line_add_offLine s
    have hR : (stripZeroCountMult s : ℝ)
        = (zeroEventCountMult s : ℝ) + (offLineStripZeroCountMult s : ℝ) := by
      exact_mod_cast h
    linarith [hR]
  rw [hsplit]
  apply ContinuousWithinAt.sub
  · apply ContinuousWithinAt.sub
    · have hev := stripZeroCountMult_eventually_const_right ht
      apply ContinuousWithinAt.congr_of_eventuallyEq
        (continuousWithinAt_const (b := (stripZeroCountMult t : ℝ)))
      · filter_upwards [hev] with s hsev
        rw [hsev]
      · rfl
    · exact continuousWithinAt_const
  · exact ((continuous_theta.continuousAt).div_const _).continuousWithinAt

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.nontrivialZeros_countable
#print axioms CriticalLinePhasor.DVP.zeroOrdinates_countable
#print axioms CriticalLinePhasor.DVP.stripZeroCountMult_eventually_const
#print axioms CriticalLinePhasor.DVP.sall_continuousAt
#print axioms CriticalLinePhasor.DVP.stripZeroCountMult_eventually_const_right
#print axioms CriticalLinePhasor.DVP.sall_continuousWithinAt_right
end AxiomAudit
