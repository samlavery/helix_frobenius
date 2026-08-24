import RequestProject.DVPSegment91
import RequestProject.DVPLiftPrincipal
import RequestProject.DVPTheta58

/-!
# The census at height 91: `N_all(91) = 25` (rung-91)

The segment certificate `segment91_re_pos` keeps `ζ` in the right
half-plane along the WHOLE standard contour at `T = 58`, so the ζ-lift is
principal end to end (covering-map uniqueness, as on the vertical half),
`|S-contour(58)| = |arg ζ(½+58i)|/π < 1/2`, and the compiled census
identity plus the certified `θ(58)` window pin the strip count:
**twelve zeros (with multiplicity) up to height 58.**  Along the way:
`58` is a good height — a strip zero at height exactly `58` on either
side of the critical line contradicts the segment positivity (using the
functional equation and conjugation for the left half).
-/

open Metric Complex MeasureTheory Topology Filter
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.ResidueJump

noncomputable section

namespace CriticalLinePhasor.DVP

/-- Point form of the segment certificate: `Re ζ(z) ≥ 1/5` whenever
`Re z ∈ [1/2, 2]` and `Im z = 58`. -/
theorem re_pos_at_91 {z : ℂ} (hre1 : 1/2 ≤ z.re) (hre2 : z.re ≤ 2)
    (him : z.im = 91) : (1/5 : ℝ) ≤ (riemannZeta z).re := by
  have h := (Complex.re_add_im z).symm
  rw [him] at h
  have hz : z = ↑z.re + ((91:ℕ):ℝ) * Complex.I := by
    rw [h]
    norm_num
  rw [hz]
  exact segment91_re_pos hre1 hre2

/-- **`58` is a good height.**  A strip zero at height `58` with
`Re ≥ 1/2` contradicts the segment positivity directly; one with
`Re < 1/2` reflects through the functional equation and conjugation to a
zero with `Re ∈ (1/2, 1)` at height `58` — same contradiction. -/
theorem goodHeight_91 : GoodHeight 91 := by
  refine ⟨by norm_num, ?_⟩
  intro ρ hρ him
  obtain ⟨h0, h1, hz⟩ := hρ
  by_cases hge : (1/2 : ℝ) ≤ ρ.re
  · have hre := re_pos_at_91 hge (by linarith) him
    rw [hz] at hre
    simp at hre
    linarith
  · have hlt : ρ.re < 1/2 := lt_of_not_ge hge
    have hne1 : ρ ≠ 1 := by
      intro h
      rw [h] at him
      simp at him
    have hnen : ∀ n : ℕ, ρ ≠ -n := by
      intro n h
      have := congrArg Complex.im h
      rw [him] at this
      simp at this
    have hfe := riemannZeta_one_sub hnen hne1
    have hz2 : riemannZeta (1 - ρ) = 0 := by
      rw [hfe, hz, mul_zero]
    have hz3 : riemannZeta ((starRingEnd ℂ) (1 - ρ)) = 0 := by
      rw [riemannZeta_conj, hz2, map_zero]
    have hwre : ((starRingEnd ℂ) (1 - ρ)).re = 1 - ρ.re := by
      simp
    have hwim : ((starRingEnd ℂ) (1 - ρ)).im = 91 := by
      simp [him]
    have hre := re_pos_at_91 (z := (starRingEnd ℂ) (1 - ρ))
      (by rw [hwre]; linarith) (by rw [hwre]; linarith) hwim
    rw [hz3] at hre
    simp at hre
    linarith

/-- Coordinates on the top half of the standard contour. -/
theorem standardContour_top_coords {T : ℝ} {u : unitInterval}
    (hu : ¬((u:ℝ) ≤ 1/2)) :
    (standardContour T u).re = 2 - (3/2) * (2 * (u:ℝ) - 1)
      ∧ (standardContour T u).im = T := by
  constructor
  · rw [standardContour, Path.trans_apply, dif_neg hu]
    change (AffineMap.lineMap (upperRight T) (line T)
      ((2 * (u:ℝ) - 1 : ℝ))).re = _
    rw [AffineMap.lineMap_apply_module]
    simp [upperRight, line, lineC]
    ring
  · rw [standardContour, Path.trans_apply, dif_neg hu]
    change (AffineMap.lineMap (upperRight T) (line T)
      ((2 * (u:ℝ) - 1 : ℝ))).im = _
    rw [AffineMap.lineMap_apply_module]
    simp [upperRight, line, lineC]
    ring

/-- On the whole contour at `T = 58`, `ζ` stays in the right half-plane's
slit region, never vanishes, and the point never hits `1`. -/
theorem standardContour91_facts (u : unitInterval) :
    riemannZeta (standardContour 91 u) ≠ 0
      ∧ standardContour 91 u ≠ 1
      ∧ riemannZeta (standardContour 91 u) ∈ Complex.slitPlane := by
  by_cases hu : (u:ℝ) ≤ 1/2
  · have hre : (standardContour 91 u).re = 2 :=
      standardContour_re_of_le_half hu
    refine ⟨?_, ?_, ?_⟩
    · apply riemannZeta_ne_zero_of_one_le_re
      rw [hre]
      norm_num
    · intro h
      have := congrArg Complex.re h
      rw [hre] at this
      simp at this
    · exact zeta_mem_slitPlane_of_two_le (by rw [hre])
  · have hu' : (1:ℝ)/2 < (u:ℝ) := lt_of_not_ge hu
    have hcoords := standardContour_top_coords (T := 91) (u := u) hu
    have hu1 : (u:ℝ) ≤ 1 := u.2.2
    have hre1 : 1/2 ≤ (standardContour 91 u).re := by
      rw [hcoords.1]
      linarith
    have hre2 : (standardContour 91 u).re ≤ 2 := by
      rw [hcoords.1]
      linarith
    have hpos := re_pos_at_91 hre1 hre2 hcoords.2
    refine ⟨?_, ?_, ?_⟩
    · intro h
      rw [h] at hpos
      simp at hpos
      linarith
    · intro h
      have := congrArg Complex.im h
      rw [hcoords.2] at this
      simp at this
    · exact Or.inl (by linarith)

/-- **Full-contour principality at `T = 58`**: the ζ-lift is the
principal logarithm along the ENTIRE standard contour. -/
theorem contourLogLift91_eq_log (hT : GoodHeight 91) (u : unitInterval) :
    contourLogLift hT u
      = Complex.log (riemannZeta (standardContour 91 u)) := by
  have hs_pre : IsPreconnected (Set.univ : Set unitInterval) :=
    isPreconnected_univ
  have hg₂cont : ContinuousOn
      (fun v : unitInterval =>
        Complex.log (riemannZeta (standardContour 91 v)))
      (Set.univ : Set unitInterval) := by
    intro v _
    have hc : ContinuousAt
        (Complex.log ∘ riemannZeta
          ∘ (standardContour 91 : unitInterval → ℂ)) v := by
      apply ContinuousAt.comp
      · exact continuousAt_clog (standardContour91_facts v).2.2
      · apply ContinuousAt.comp
        · exact (differentiableAt_riemannZeta
            (standardContour91_facts v).2.1).continuousAt
        · exact (standardContour 91).continuous.continuousAt
    exact hc.continuousWithinAt
  have heq := Complex.isCoveringMap_exp.eqOn_of_comp_eqOn hs_pre
    ((contourLogLift hT).continuous.continuousOn) hg₂cont
    (by
      intro v _
      apply Subtype.ext
      show Complex.exp (contourLogLift hT v)
        = Complex.exp (Complex.log (riemannZeta (standardContour 91 v)))
      rw [exp_contourLogLift,
        Complex.exp_log (standardContour91_facts v).1])
    (a := 0) (Set.mem_univ 0)
    (by
      rw [contourLogLift_zero]
      have h0 : standardContour 91 0 = 2 := (standardContour 91).source
      rw [h0]
      rw [riemannZeta_two]
      have hcast : ((Real.pi:ℂ) ^ 2 / 6) = (((Real.pi ^ 2 / 6 : ℝ)):ℂ) := by
        push_cast
        ring
      rw [hcast, ← Complex.ofReal_log (by positivity)]
      rfl)
  exact heq (Set.mem_univ u)

/-- **The Backlund bound at `58`**: `|S-contour(58)| < 1/2`. -/
theorem abs_classicalSContour_91_lt_half (hT : GoodHeight 91) :
    |classicalSContour hT| < 1/2 := by
  have hend := contourLogLift91_eq_log hT 1
  have htarget : standardContour 91 1 = line 91 := (standardContour 91).target
  rw [htarget] at hend
  have hline_re : (line (91:ℝ)).re = 1/2 := by
    simp [line, lineC]
  have hline_im : (line (91:ℝ)).im = 91 := by
    simp [line, lineC]
  have hre := re_pos_at_91 (z := line 91) (by rw [hline_re])
    (by rw [hline_re]; norm_num) hline_im
  have hzne : riemannZeta (line 91) ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have harg : |Complex.arg (riemannZeta (line 91))| < Real.pi / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]
    left
    linarith
  rw [classicalSContour, hend, Complex.log_im, abs_div,
    abs_of_pos Real.pi_pos, div_lt_iff₀ Real.pi_pos]
  linarith [harg]

/-- **The strip census at height 58: exactly twelve zeros** (with
multiplicity).  Census identity + certified `θ(58)` window + the
principal-lift `|S| < 1/2`. -/
theorem stripZeroCountMult_91 : stripZeroCountMult 91 = 25 := by
  have hT := goodHeight_91
  have hS := abs_classicalSContour_91_lt_half hT
  have hcensus := classicalSContour_eq_Smult_add_offLine hT
  have hsplit := stripZeroCountMult_eq_line_add_offLine 91
  have hsplitR : (stripZeroCountMult 91 : ℝ)
      = (zeroEventCountMult 91 : ℝ) + (offLineStripZeroCountMult 91 : ℝ) := by
    exact_mod_cast hsplit
  have hkey : classicalSContour hT
      = (stripZeroCountMult 91 : ℝ) - theta 91 / Real.pi - 1 := by
    rw [hcensus]
    unfold CriticalLinePhasor.ResidueJump.Smult
    linarith [hsplitR]
  -- the θ(63) window from the θ(30) anchor
  have hθ30 := theta30_enclosure
  have hπ0 := Real.pi_pos
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (91:ℝ))
    (by norm_num) (by norm_num)
  have hMain63 : thetaMain (91:ℝ)
      = ((91:ℝ) * (Real.log (91:ℝ) - Real.log 2 - Real.log Real.pi)
          - (91:ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ0.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ0.ne']
    ring
  rw [hMain63, hMain30] at hinc
  have hl91 : ((22554297/5000000 : ℚ) : ℝ) ≤ Real.log (91:ℝ)
      ∧ Real.log (91:ℝ) ≤ ((11277149/2500000 : ℚ) : ℝ) := by
    have h := log_br_91
    norm_num at h ⊢
    exact h
  have hl30 : ((34011973/10000000 : ℚ) : ℝ) ≤ Real.log (30:ℝ)
      ∧ Real.log (30:ℝ) ≤ ((17005987/5000000 : ℚ) : ℝ) := by
    have h := log_br_30
    norm_num at h ⊢
    exact h
  have hl2 : ((6931471/10000000 : ℚ) : ℝ) ≤ Real.log (2:ℝ)
      ∧ Real.log (2:ℝ) ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := log_br_2
    norm_num at h ⊢
    exact h
  have hlπ := log_pi_enclosure
  have hπl := Real.pi_gt_d6
  have hπu := Real.pi_lt_d6
  have hθ30b := abs_le.mp hθ30
  have hincb := abs_le.mp hinc
  push_cast at hincb hl91 hl30 hl2 hlπ
  -- multiply the census through by π
  have hπN : Real.pi * (stripZeroCountMult 91 : ℝ)
      = theta 91 + Real.pi + Real.pi * classicalSContour hT := by
    have hdiv : theta 91 / Real.pi * Real.pi = theta 91 :=
      div_mul_cancel₀ _ hπ0.ne'
    have h2 : classicalSContour hT * Real.pi
        = ((stripZeroCountMult 91 : ℝ) - theta 91 / Real.pi - 1) * Real.pi := by
      rw [hkey]
    rw [sub_mul, sub_mul, hdiv, one_mul] at h2
    linarith [h2]
  have hSb := abs_lt.mp hS
  -- 13 < N < 15 over ℝ
  have hlow : (24:ℝ) < (stripZeroCountMult 91 : ℝ) := by
    nlinarith [hπN, hθ30b.1, hθ30b.2, hincb.1, hincb.2, hSb.1,
      hl91.1, hl91.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπl, hπu, hπ0]
  have hhigh : (stripZeroCountMult 91 : ℝ) < 26 := by
    nlinarith [hπN, hθ30b.1, hθ30b.2, hincb.1, hincb.2, hSb.2,
      hl91.1, hl91.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπl, hπu, hπ0]
  have hlowN : 24 < stripZeroCountMult 91 := by exact_mod_cast hlow
  have hhighN : stripZeroCountMult 91 < 26 := by exact_mod_cast hhigh
  omega

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.goodHeight_91
#print axioms CriticalLinePhasor.DVP.contourLogLift91_eq_log
#print axioms CriticalLinePhasor.DVP.abs_classicalSContour_91_lt_half
#print axioms CriticalLinePhasor.DVP.stripZeroCountMult_91
end AxiomAudit
