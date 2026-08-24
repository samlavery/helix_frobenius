import RequestProject.DVPLittlewoodInterface

/-!
# `OffLineMassLog` IS count-level RH

The second register residual, clarified to an iff: a single off-line zero
makes `∫₀ᵀ N_off` grow linearly (the count is monotone), contradicting the
`O(log)` bound; conversely a vanishing count integrates to zero.  So

`OffLineMassLog ↔ ∀ T, offLineStripZeroCountMult T = 0`,

and the right side is the Riemann Hypothesis at the census level.  The
register road's two residuals are therefore [register content] ∧ [RH] — the
same shape as the seat road's split, with all classical mass now on the
compiled side.
-/

open CriticalLinePhasor.ContourArgument

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The off-line residual is count-level RH**:
`OffLineMassLog ↔ ∀ T, N_off(T) = 0`. -/
theorem offLineMassLog_iff_offLine_zero :
    OffLineMassLog ↔ ∀ T : ℝ, offLineStripZeroCountMult T = 0 := by
  constructor
  · -- one off-line zero forces linear growth
    rintro ⟨C, hC⟩ T
    by_contra hk
    have hk1 : 1 ≤ offLineStripZeroCountMult T := Nat.one_le_iff_ne_zero.mpr hk
    -- C is nonnegative (instantiate at 0)
    have hC0 : (0:ℝ) ≤ C := by
      have h := hC 0 (le_refl 0)
      rw [intervalIntegral.integral_same] at h
      simpa using h
    -- WLOG T ≥ 0 (the count vanishes for T < 0 — its window is empty… we
    -- instead just work with T' := max T 0, where the count is ≥ 1 by
    -- monotonicity)
    set T' : ℝ := max T 0 with hT'def
    have hT'0 : (0:ℝ) ≤ T' := le_max_right _ _
    have hk1' : 1 ≤ offLineStripZeroCountMult T' :=
      le_trans hk1 (offLineStripZeroCountMult_mono (le_max_left _ _))
    -- the linear floor: for S ≥ T', ∫₀ˢ N_off ≥ S − T'
    have hfloor : ∀ S : ℝ, T' ≤ S →
        S - T' ≤ ∫ t in (0:ℝ)..S, (offLineStripZeroCountMult t : ℝ) := by
      intro S hS
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        (offline_intervalIntegrable 0 T') (offline_intervalIntegrable T' S)
      have h1 : (0:ℝ) ≤ ∫ t in (0:ℝ)..T',
          (offLineStripZeroCountMult t : ℝ) :=
        intervalIntegral.integral_nonneg hT'0 (fun t _ => by positivity)
      have h2 : S - T' ≤ ∫ t in T'..S,
          (offLineStripZeroCountMult t : ℝ) := by
        have hconst : S - T' = ∫ _t in T'..S, (1:ℝ) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
        rw [hconst]
        apply intervalIntegral.integral_mono_on hS
          intervalIntegrable_const (offline_intervalIntegrable T' S)
        intro t htm
        have := offLineStripZeroCountMult_mono htm.1
        have hcast : (1:ℝ) ≤ (offLineStripZeroCountMult t : ℝ) := by
          exact_mod_cast le_trans hk1' this
        exact hcast
      linarith [hadj]
    -- choose S beating the log bound: log(1+S) ≤ 2√(1+S), quadratic choice
    set R : ℝ := 2*C + 2 + C*(1 + 2*Real.sqrt (1 + T')) with hRdef
    have hR1 : 1 ≤ R := by
      have hs0 : (0:ℝ) ≤ Real.sqrt (1 + T') := Real.sqrt_nonneg _
      nlinarith [hC0]
    set S : ℝ := T' + R^2 with hSdef
    have hRS : T' ≤ S := by
      rw [hSdef]
      nlinarith [hR1]
    have hbound := hC S (by linarith)
    have hfloorS := hfloor S hRS
    -- log(1+S) ≤ 2√(1+S) ≤ 2√(1+T') + 2R
    have hlogS : Real.log (1 + S) ≤ 2 * Real.sqrt (1 + T') + 2 * R := by
      have h1S : (0:ℝ) < 1 + S := by nlinarith [hR1]
      have hsq : Real.log (1 + S) ≤ 2 * (Real.sqrt (1 + S) - 1) := by
        have hs := Real.sqrt_pos.mpr h1S
        have hlog1 : Real.log (Real.sqrt (1 + S)) ≤ Real.sqrt (1 + S) - 1 :=
          Real.log_le_sub_one_of_pos hs
        have hhalf : Real.log (Real.sqrt (1 + S))
            = Real.log (1 + S) / 2 :=
          Real.log_sqrt (le_of_lt h1S)
        linarith [hlog1, hhalf.le, hhalf.ge]
      have hsub : Real.sqrt (1 + S) ≤ Real.sqrt (1 + T') + R := by
        rw [hSdef, show (1 + (T' + R^2)) = (1 + T') + R^2 by ring]
        have hle : (1 + T') + R^2 ≤ (Real.sqrt (1 + T') + R)^2 := by
          have hs : Real.sqrt (1 + T') ^ 2 = 1 + T' :=
            Real.sq_sqrt (by linarith)
          nlinarith [Real.sqrt_nonneg (1 + T'), hR1]
        calc Real.sqrt ((1 + T') + R^2)
            ≤ Real.sqrt ((Real.sqrt (1 + T') + R)^2) :=
              Real.sqrt_le_sqrt hle
          _ = Real.sqrt (1 + T') + R := Real.sqrt_sq
              (by nlinarith [Real.sqrt_nonneg (1 + T'), hR1])
      linarith [hsq, hsub]
    -- assemble the contradiction: R² ≤ C(1 + 2√(1+T') + 2R) < R²
    have hchain : (R:ℝ)^2 ≤ C * (1 + 2 * Real.sqrt (1 + T') + 2 * R) := by
      have h1 : S - T' = R^2 := by rw [hSdef]; ring
      have h4 : C * (1 + Real.log (1 + S))
          ≤ C * (1 + 2 * Real.sqrt (1 + T') + 2 * R) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        linarith [hlogS]
      linarith [hfloorS, h1.le, h1.ge, hbound, h4]
    have hfinal : C * (1 + 2 * Real.sqrt (1 + T') + 2 * R) < R^2 := by
      have hs0 : (0:ℝ) ≤ Real.sqrt (1 + T') := Real.sqrt_nonneg _
      have hR2C : 2*C + 2 ≤ R := by
        rw [hRdef]
        nlinarith [hC0, hs0]
      have hRC : C * (1 + 2 * Real.sqrt (1 + T')) ≤ R := by
        rw [hRdef]
        nlinarith [hC0, hs0]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ R - (2*C+2))
        (by linarith : (0:ℝ) ≤ R), hRC, hR1]
    linarith [hchain, hfinal]
  · -- vanishing count integrates to zero
    intro hzero
    refine ⟨1, ?_⟩
    intro T hT0
    have hzero_int : (∫ t in (0:ℝ)..T,
        (offLineStripZeroCountMult t : ℝ)) = 0 := by
      have hfun : (fun t : ℝ => (offLineStripZeroCountMult t : ℝ))
          = fun _ : ℝ => (0:ℝ) := by
        funext t
        rw [hzero t]
        norm_num
      rw [hfun]
      simp
    rw [hzero_int]
    have : (0:ℝ) ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
    linarith

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.offLineMassLog_iff_offLine_zero
end AxiomAudit
