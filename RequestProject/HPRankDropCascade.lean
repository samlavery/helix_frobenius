import RequestProject.ShannonCascade
import RequestProject.ExportAdapter

/-!
# The rank-drop cascade door: real-staged vanishings force RH

Sam's ordering (2026-08-30): *vanishing first, then the mark — that's the
3D rank drop.*  Stages vanish at heights (finite rank drops, real by
finite self-adjointness); the chart zero is where stage vanishings
accumulate.  Compiled here: if every stage of a cascade vanishes only at
real points, the cascade is complete, and the compiled wiring theorem
forces the exact Mathlib `RiemannHypothesis`.

No `sorry`, no `axiom`.
-/

open Filter Topology Complex

noncomputable section

namespace CriticalLinePhasor.Cascade

/-- **RH from a real-staged cascade**: stages vanishing only at real
heights (the 3D rank-drop law at finite level) force completeness, hence
the Riemann Hypothesis. -/
theorem riemannHypothesis_of_real_staged_cascade
    (C : MidpointCascade)
    (hreal : ∀ n z, C.stage n z = 0 → z.im = 0) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_complete_cascade C
  intro z hacc
  by_contra him
  have hε : (0:ℝ) < |z.im| / 2 := by
    have : z.im ≠ 0 := him
    positivity
  obtain ⟨n, w, hw, hzero⟩ := (hacc (|z.im|/2) hε).exists
  have hwim : w.im = 0 := hreal n w hzero
  have hdist : dist w z < |z.im|/2 := Metric.mem_ball.mp hw
  have hbound : |z.im| ≤ dist w z := by
    have h1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
    have h2 : (z - w).im = z.im := by
      rw [Complex.sub_im, hwim, sub_zero]
    rw [h2] at h1
    rw [dist_comm, dist_eq_norm]
    exact h1
  linarith

end CriticalLinePhasor.Cascade

#print axioms CriticalLinePhasor.Cascade.riemannHypothesis_of_real_staged_cascade
