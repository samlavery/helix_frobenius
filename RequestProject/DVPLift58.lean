import RequestProject.DVPSegment58
import RequestProject.DVPLiftPrincipal
import RequestProject.DVPTheta58

/-!
# The census at height 58: `N_all(58) = 12`

The segment certificate `segment58_re_pos` keeps `ζ` in the right
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
theorem re_pos_at_58 {z : ℂ} (hre1 : 1/2 ≤ z.re) (hre2 : z.re ≤ 2)
    (him : z.im = 58) : (1/5 : ℝ) ≤ (riemannZeta z).re := by
  have h := (Complex.re_add_im z).symm
  rw [him] at h
  have hz : z = ↑z.re + 58 * Complex.I := by
    rw [h]
    norm_num
  rw [hz]
  exact segment58_re_pos hre1 hre2

/-- **`58` is a good height.**  A strip zero at height `58` with
`Re ≥ 1/2` contradicts the segment positivity directly; one with
`Re < 1/2` reflects through the functional equation and conjugation to a
zero with `Re ∈ (1/2, 1)` at height `58` — same contradiction. -/
theorem goodHeight_58 : GoodHeight 58 := by
  refine ⟨by norm_num, ?_⟩
  intro ρ hρ him
  obtain ⟨h0, h1, hz⟩ := hρ
  by_cases hge : (1/2 : ℝ) ≤ ρ.re
  · have hre := re_pos_at_58 hge (by linarith) him
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
    have hwim : ((starRingEnd ℂ) (1 - ρ)).im = 58 := by
      simp [him]
    have hre := re_pos_at_58 (z := (starRingEnd ℂ) (1 - ρ))
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
theorem standardContour58_facts (u : unitInterval) :
    riemannZeta (standardContour 58 u) ≠ 0
      ∧ standardContour 58 u ≠ 1
      ∧ riemannZeta (standardContour 58 u) ∈ Complex.slitPlane := by
  by_cases hu : (u:ℝ) ≤ 1/2
  · have hre : (standardContour 58 u).re = 2 :=
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
    have hcoords := standardContour_top_coords (T := 58) (u := u) hu
    have hu1 : (u:ℝ) ≤ 1 := u.2.2
    have hre1 : 1/2 ≤ (standardContour 58 u).re := by
      rw [hcoords.1]
      linarith
    have hre2 : (standardContour 58 u).re ≤ 2 := by
      rw [hcoords.1]
      linarith
    have hpos := re_pos_at_58 hre1 hre2 hcoords.2
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
theorem contourLogLift58_eq_log (hT : GoodHeight 58) (u : unitInterval) :
    contourLogLift hT u
      = Complex.log (riemannZeta (standardContour 58 u)) := by
  have hs_pre : IsPreconnected (Set.univ : Set unitInterval) :=
    isPreconnected_univ
  have hg₂cont : ContinuousOn
      (fun v : unitInterval =>
        Complex.log (riemannZeta (standardContour 58 v)))
      (Set.univ : Set unitInterval) := by
    intro v _
    have hc : ContinuousAt
        (Complex.log ∘ riemannZeta
          ∘ (standardContour 58 : unitInterval → ℂ)) v := by
      apply ContinuousAt.comp
      · exact continuousAt_clog (standardContour58_facts v).2.2
      · apply ContinuousAt.comp
        · exact (differentiableAt_riemannZeta
            (standardContour58_facts v).2.1).continuousAt
        · exact (standardContour 58).continuous.continuousAt
    exact hc.continuousWithinAt
  have heq := Complex.isCoveringMap_exp.eqOn_of_comp_eqOn hs_pre
    ((contourLogLift hT).continuous.continuousOn) hg₂cont
    (by
      intro v _
      apply Subtype.ext
      show Complex.exp (contourLogLift hT v)
        = Complex.exp (Complex.log (riemannZeta (standardContour 58 v)))
      rw [exp_contourLogLift,
        Complex.exp_log (standardContour58_facts v).1])
    (a := 0) (Set.mem_univ 0)
    (by
      rw [contourLogLift_zero]
      have h0 : standardContour 58 0 = 2 := (standardContour 58).source
      rw [h0]
      rw [riemannZeta_two]
      have hcast : ((Real.pi:ℂ) ^ 2 / 6) = (((Real.pi ^ 2 / 6 : ℝ)):ℂ) := by
        push_cast
        ring
      rw [hcast, ← Complex.ofReal_log (by positivity)]
      rfl)
  exact heq (Set.mem_univ u)

/-- **The Backlund bound at `58`**: `|S-contour(58)| < 1/2`. -/
theorem abs_classicalSContour_58_lt_half (hT : GoodHeight 58) :
    |classicalSContour hT| < 1/2 := by
  have hend := contourLogLift58_eq_log hT 1
  have htarget : standardContour 58 1 = line 58 := (standardContour 58).target
  rw [htarget] at hend
  have hline_re : (line (58:ℝ)).re = 1/2 := by
    simp [line, lineC]
  have hline_im : (line (58:ℝ)).im = 58 := by
    simp [line, lineC]
  have hre := re_pos_at_58 (z := line 58) (by rw [hline_re])
    (by rw [hline_re]; norm_num) hline_im
  have hzne : riemannZeta (line 58) ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have harg : |Complex.arg (riemannZeta (line 58))| < Real.pi / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]
    left
    linarith
  rw [classicalSContour, hend, Complex.log_im, abs_div,
    abs_of_pos Real.pi_pos, div_lt_iff₀ Real.pi_pos]
  linarith [harg]

/-- **The strip census at height 58: exactly twelve zeros** (with
multiplicity).  Census identity + certified `θ(58)` window + the
principal-lift `|S| < 1/2`. -/
theorem stripZeroCountMult_58 : stripZeroCountMult 58 = 12 := by
  have hT := goodHeight_58
  have hS := abs_classicalSContour_58_lt_half hT
  have hcensus := classicalSContour_eq_Smult_add_offLine hT
  have hsplit := stripZeroCountMult_eq_line_add_offLine 58
  have hsplitR : (stripZeroCountMult 58 : ℝ)
      = (zeroEventCountMult 58 : ℝ) + (offLineStripZeroCountMult 58 : ℝ) := by
    exact_mod_cast hsplit
  have hkey : classicalSContour hT
      = (stripZeroCountMult 58 : ℝ) - theta 58 / Real.pi - 1 := by
    rw [hcensus]
    unfold CriticalLinePhasor.ResidueJump.Smult
    linarith [hsplitR]
  have hθ := theta58_enclosure
  have hπl := Real.pi_gt_d6
  have hπu := Real.pi_lt_d6
  have hπ0 := Real.pi_pos
  -- multiply the census through by π
  have hπN : Real.pi * (stripZeroCountMult 58 : ℝ)
      = theta 58 + Real.pi + Real.pi * classicalSContour hT := by
    have hdiv : theta 58 / Real.pi * Real.pi = theta 58 :=
      div_mul_cancel₀ _ hπ0.ne'
    have h2 : classicalSContour hT * Real.pi
        = ((stripZeroCountMult 58 : ℝ) - theta 58 / Real.pi - 1) * Real.pi := by
      rw [hkey]
    rw [sub_mul, sub_mul, hdiv, one_mul] at h2
    linarith [h2]
  have hθb := abs_le.mp hθ
  have hSb := abs_lt.mp hS
  -- 11 < N < 13 over ℝ
  have hlow : (11:ℝ) < (stripZeroCountMult 58 : ℝ) := by
    nlinarith [hπN, hθb.1, hSb.1, hπ0]
  have hhigh : (stripZeroCountMult 58 : ℝ) < 13 := by
    nlinarith [hπN, hθb.2, hSb.2, hπ0]
  have hlowN : 11 < stripZeroCountMult 58 := by exact_mod_cast hlow
  have hhighN : stripZeroCountMult 58 < 13 := by exact_mod_cast hhigh
  omega

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.goodHeight_58
#print axioms CriticalLinePhasor.DVP.contourLogLift58_eq_log
#print axioms CriticalLinePhasor.DVP.abs_classicalSContour_58_lt_half
#print axioms CriticalLinePhasor.DVP.stripZeroCountMult_58
end AxiomAudit
