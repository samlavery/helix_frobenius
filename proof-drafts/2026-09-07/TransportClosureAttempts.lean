import RequestProject.HelixSectionTransport
import RequestProject.WeilPolynomialGrowth
import RequestProject.FrobeniusWeightCandidateAudit

/-!
Executable closure attempts with the unconditional RH target retained.
This draft is outside the library glob. Each attempt reaches its displayed
arithmetic identification target; no hypothesis is added to either example.
-/

open Complex Polynomial ConeProjection
open CriticalLinePhasor CriticalLinePhasor.CellEdgeDoor
open CriticalLinePhasor.FiniteCellSections
open CriticalLinePhasor.HelixSectionTransport
open CriticalLinePhasor.FrobeniusWeightCandidateAudit

/- Attempt A: the positive section-count weight. The explicit finite section
count gives positivity and reflection invariance. Test its similitude law. -/
example : RiemannHypothesis := by
  let P : ℂ → ℝ := fun ρ =>
    (Module.finrank ℂ (sections
      (cellDivisor (fun _ : Fin 1 => GlobalHelix.circleReadout (1, 0, ρ.im))
        (fun _ => 1)) 2) : ℝ)
  have hP (ρ : ℂ) : P ρ = 1 := by
    simp [P, finrank_cellSections]
  apply riemannHypothesis_of_frobenius_weight P
  · intro ρ _
    rw [hP]
    norm_num
  · intro ρ _
    rw [hP, hP]
  · intro ρ hρ
    rw [hP, hP, mul_one, norm_endPairFace]
    have hdet := endPair_det_one ρ
    trace_state
    nlinarith [Real.exp_pos (ρ.re - 1 / 2)]

/- Attempt B: use the 3D phase transport power theorem in the arithmetic
two-sided power-bound target. Low heights use the existing checked ladder.
At the other heights, test the power-envelope identification itself. -/
example : RiemannHypothesis := by
  apply riemannHypothesis_of_two_sided_face_power_bounds
  intro ρ hρ
  by_cases hh : |ρ.im| ≤ 1269 / 2
  · exact endPairFace_two_sided_power_bounds_below_1269o2 hρ hh
  · have hphase (k : ℕ) :
        ‖(phaseTransport (1, 0, ρ.im) ^ k) (1 : ℂ)‖ ^ 2 = 1 := by
      simpa using phaseTransport_power_norm (1, 0, ρ.im) (1 : ℂ) k
    refine ⟨1, one_pos, 1, one_pos, ?_, ?_⟩
    · intro k
      trace_state
      simpa using (hphase k).le
    · intro k
      trace_state
      simpa using (hphase k).le

#print axioms CriticalLinePhasor.CellEdgeDoor.riemannHypothesis_of_frobenius_weight
#print axioms CriticalLinePhasor.FrobeniusWeightCandidateAudit.riemannHypothesis_of_two_sided_face_power_bounds
