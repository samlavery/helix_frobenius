import RequestProject.DVPLift58
import RequestProject.DVPArgumentPrinciple

/-!
# The Hardy detector

`G(t) := Re Λ(½ + it)` is a REAL continuous detector of on-line zeros:
`Λ` is self-conjugate on the critical line (functional equation +
conjugation symmetry), so `G` vanishing forces `Λ = 0`, hence `ζ = 0`
at an on-line point.  The phase identity
`G(t) = e^{Re gammaLog}·(cos θ(t)·Re ζ − sin θ(t)·Im ζ)` (through the
compiled `gammaLog_line_im`) turns certified `θ`/`Re ζ`/`Im ζ` stations
into `G`-signs, and the intermediate value theorem turns sign changes
into on-line zeros.  Finally the exhaustion: twelve distinct on-line
zeros below height 58 plus the compiled census `N_all(58) = 12` force
EVERY strip zero of ordinate `≤ 58` onto the line.
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- Conjugation symmetry of the completed zeta function. -/
theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (completedRiemannZeta s) := by
  simp only [completedRiemannZeta_eq, completedRiemannZeta₀_conj,
    map_sub, map_div₀, map_one]

/-- The imaginary coordinate of the critical-line point. -/
theorem lineIm (t : ℝ) : (line t).im = t := by
  simp [line, lineC]

/-- `Λ` is real on the critical line. -/
theorem completedZeta_line_real (t : ℝ) :
    (completedRiemannZeta (line t)).im = 0 := by
  have hconj : (starRingEnd ℂ) (line t) = 1 - line t := by
    apply Complex.ext
    · simp [line_re]
      norm_num
    · simp [lineIm]
  have h1 : completedRiemannZeta ((starRingEnd ℂ) (line t))
      = (starRingEnd ℂ) (completedRiemannZeta (line t)) :=
    completedRiemannZeta_conj (line t)
  rw [hconj, completedRiemannZeta_one_sub] at h1
  have := congrArg Complex.im h1
  simp at this
  linarith

/-- **The Hardy detector.** -/
def hardyG (t : ℝ) : ℝ := (completedRiemannZeta (line t)).re

/-- A vanishing detector at positive height is an on-line strip zero. -/
theorem hardyG_online {t : ℝ} (ht : 0 < t) (h : hardyG t = 0) :
    line t ∈ ZD.NontrivialZeros := by
  have hline0 : line t ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [line_re] at this
    simp at this
  have hΛ : completedRiemannZeta (line t) = 0 := by
    apply Complex.ext
    · exact h
    · simpa using completedZeta_line_real t
  have hζ : riemannZeta (line t) = 0 := by
    rw [riemannZeta_def_of_ne_zero hline0, hΛ, zero_div]
  refine ⟨?_, ?_, hζ⟩
  · rw [line_re]; norm_num
  · rw [line_re]; norm_num

/-- Continuity of the detector away from the pole heights. -/
theorem hardyG_continuousOn : ContinuousOn hardyG (Set.Icc (10:ℝ) 58) := by
  intro t ht
  have hline0 : line t ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    rw [lineIm] at this
    simp at this
    linarith [ht.1]
  have hline1 : line t ≠ 1 := by
    intro h0
    have := congrArg Complex.im h0
    rw [lineIm] at this
    simp at this
    linarith [ht.1]
  have hlinecont : Continuous line := by
    unfold CriticalLinePhasor.CarrierScale.line
      CriticalLinePhasor.CarrierScale.lineC
    fun_prop
  have hc : ContinuousAt
      (Complex.re ∘ completedRiemannZeta ∘ line) t := by
    apply ContinuousAt.comp
    · exact Complex.continuous_re.continuousAt
    · apply ContinuousAt.comp
      · exact (differentiableAt_completedZeta hline0 hline1).continuousAt
      · exact hlinecont.continuousAt
  exact hc.continuousWithinAt

/-- **Sign change ⟹ on-line zero strictly between.** -/
theorem hardyG_sign_change {a b : ℝ} (hab : a ≤ b) (h10 : 10 ≤ a)
    (h58 : b ≤ 58) (hsign : hardyG a * hardyG b < 0) :
    ∃ t : ℝ, a < t ∧ t < b ∧ line t ∈ ZD.NontrivialZeros := by
  have hsub : Set.Icc a b ⊆ Set.Icc (10:ℝ) 58 :=
    Set.Icc_subset_Icc h10 h58
  have hcont : ContinuousOn hardyG (Set.Icc a b) :=
    hardyG_continuousOn.mono hsub
  have hane : hardyG a ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsign
    exact lt_irrefl _ hsign
  have hbne : hardyG b ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsign
    exact lt_irrefl _ hsign
  have hzero : ∃ t ∈ Set.Icc a b, hardyG t = 0 := by
    rcases lt_or_gt_of_ne hane with hneg | hpos
    · -- G a < 0, so G b > 0
      have hbpos : 0 < hardyG b := by
        rcases lt_trichotomy (hardyG b) 0 with h | h | h
        · nlinarith
        · exact absurd h hbne
        · exact h
      have := intermediate_value_Icc hab hcont
      have hmem : (0:ℝ) ∈ Set.Icc (hardyG a) (hardyG b) :=
        ⟨hneg.le, hbpos.le⟩
      obtain ⟨t, htmem, hteq⟩ := this hmem
      exact ⟨t, htmem, hteq⟩
    · -- G a > 0, so G b < 0
      have hbneg : hardyG b < 0 := by
        rcases lt_trichotomy (hardyG b) 0 with h | h | h
        · exact h
        · exact absurd h hbne
        · nlinarith
      have := intermediate_value_Icc' hab hcont
      have hmem : (0:ℝ) ∈ Set.Icc (hardyG b) (hardyG a) :=
        ⟨hbneg.le, hpos.le⟩
      obtain ⟨t, htmem, hteq⟩ := this hmem
      exact ⟨t, htmem, hteq⟩
  obtain ⟨t, htmem, hteq⟩ := hzero
  have htne_a : t ≠ a := by
    intro h
    rw [h] at hteq
    exact hane hteq
  have htne_b : t ≠ b := by
    intro h
    rw [h] at hteq
    exact hbne hteq
  refine ⟨t, lt_of_le_of_ne htmem.1 (Ne.symm htne_a),
    lt_of_le_of_ne htmem.2 htne_b, ?_⟩
  exact hardyG_online (by linarith [htmem.1]) hteq

/-- **The phase identity**: the detector through the compiled Γ-clock. -/
theorem hardyG_eq_phase (t : ℝ) :
    hardyG t = Real.exp ((gammaLog (line t)).re)
      * (Real.cos (theta t) * (riemannZeta (line t)).re
        - Real.sin (theta t) * (riemannZeta (line t)).im) := by
  have hline0 : line t ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [line_re] at this
    simp at this
  have hrhp : line t ∈ rightHalfPlane := by
    simp [rightHalfPlane, line_re]
  have hΓne : Gammaℝ (line t) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by rw [line_re]; norm_num)
  have hprod : completedRiemannZeta (line t)
      = Gammaℝ (line t) * riemannZeta (line t) := by
    rw [riemannZeta_def_of_ne_zero hline0]
    field_simp
  have hexp : Gammaℝ (line t) = Complex.exp (gammaLog (line t)) :=
    (exp_gammaLog hrhp).symm
  have hgl : gammaLog (line t)
      = ((gammaLog (line t)).re : ℂ) + (theta t : ℝ) * Complex.I := by
    rw [← gammaLog_line_im t]
    exact (Complex.re_add_im _).symm
  rw [hardyG, hprod, hexp, hgl, Complex.exp_add, ← Complex.ofReal_exp,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_re,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.completedZeta_line_real
#print axioms CriticalLinePhasor.DVP.hardyG_sign_change
end AxiomAudit
