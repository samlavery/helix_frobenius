import Mathlib

/-!
# Accumulated defect positivity: degree dominance from counting data

The licensed instance of the integrated-registration positivity input
(resolved 2026-08-10: "accumulated defects are always positive" — at the
accumulated scale this is Riemann–von Mangoldt counting, unconditional for
the licensed factors).  A `CountingData` packages a zero-counting function
with main term `c·T·log T` and sub-main error, the exact shape the
classical counting theorems supply for entire completed `L`-functions; the
theorem derives positivity of the accumulated defect `N_P − N_C` beyond an
explicit height whenever the numerator's density coefficient dominates —
at rung `r` the gap is the degree `r+1` of the formal symmetric power over
`2π`.  The atomic refinement (sign flips at cancellation = containment,
per the manuscript's atomic-ledger register) is deliberately NOT claimed
here: integration forgets the atom signs; this file is the DC layer only.
No `axiom`, no `sorry`.
-/

namespace CriticalLinePhasor.AccumulatedDefect

/-- Riemann–von Mangoldt-shaped counting data: a counting function with
main term `cmain·T·log T` and error sub-main in the little-o sense. -/
structure CountingData where
  N : ℝ → ℝ
  cmain : ℝ
  approx : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, 3 ≤ T₀ ∧
    ∀ T : ℝ, T₀ ≤ T → |N T - cmain * (T * Real.log T)| ≤ ε * (T * Real.log T)

/-- **Accumulated defect positivity by degree dominance**: if the
numerator's density coefficient exceeds the denominator's, the accumulated
defect is strictly positive beyond an explicit height. -/
theorem accumulated_defect_positive (P C : CountingData)
    (hgap : C.cmain < P.cmain) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → 0 < P.N T - C.N T := by
  set g : ℝ := P.cmain - C.cmain with hg
  have hgpos : 0 < g := by rw [hg]; linarith
  obtain ⟨T₁, hT₁3, hP⟩ := P.approx (g / 4) (by linarith)
  obtain ⟨T₂, hT₂3, hC⟩ := C.approx (g / 4) (by linarith)
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hTT₂ : T₂ ≤ T := le_trans (le_max_right _ _) hT
  have hT3 : (3 : ℝ) ≤ T := le_trans hT₁3 hTT₁
  have hlogpos : 0 < Real.log T := by
    apply Real.log_pos
    linarith
  have hTlogpos : 0 < T * Real.log T := by
    apply mul_pos (by linarith) hlogpos
  have h1 := hP T hTT₁
  have h2 := hC T hTT₂
  have h1' : P.cmain * (T * Real.log T) - g / 4 * (T * Real.log T) ≤ P.N T := by
    have := abs_le.mp h1
    linarith [this.1]
  have h2' : C.N T ≤ C.cmain * (T * Real.log T) + g / 4 * (T * Real.log T) := by
    have := abs_le.mp h2
    linarith [this.2]
  have hmain : P.N T - C.N T ≥ (g / 2) * (T * Real.log T) := by
    have : P.cmain * (T * Real.log T) - C.cmain * (T * Real.log T)
        = g * (T * Real.log T) := by rw [hg]; ring
    nlinarith [h1', h2', hTlogpos]
  have : (0 : ℝ) < (g / 2) * (T * Real.log T) := by positivity
  linarith

end CriticalLinePhasor.AccumulatedDefect

#print axioms CriticalLinePhasor.AccumulatedDefect.accumulated_defect_positive
