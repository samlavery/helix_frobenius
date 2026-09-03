import Mathlib
import RequestProject.ShannonCascade

/-!
# `projection_cannot_originate_events` — the no-origination theorem at its true strength (ledger 553)

An independent audit (2026-09-02) of the compiled "data processing" theorems found, correctly, that
`limit_dominance` is Hurwitz — every zero of the limit has stage-zero ancestry — and says nothing
about whether the stage zeros are sourced; that the strengthening is the field `Complete`; and it
asked for a theorem `projection_cannot_originate_events` taking a SOURCE-LABELLED cascade and
proving that every downstream vanishing has source ancestry, from which `Complete` follows as a
corollary rather than a hypothesis.

This file compiles exactly that theorem, and shows where its hypothesis lives.

* `SourceLabelled C` — every vanishing of every stage sits at a real height (its source label).
* `complete_of_sourceLabelled` — source labelling implies `Complete`: accumulation points of real
  heights are real.
* **`projection_cannot_originate_events`** — for a source-labelled cascade, every vanishing of the
  ξ-section has real-height ancestry; **`rh_of_sourceLabelled_cascade`** — hence RH.
* **`twoPhasorStage_vanishes_off_fold`** — the hypothesis FAILS for carrier-phasor stages at the
  first nontrivial one: the two-phasor η-stage `1 − 2^{−(½+iz)}` vanishes at `z = i/2` (the helix
  end, `Re s = 0`), off the fold. So "built from carrier states" does not give source labelling.
  Source labelling is real-rootedness of the approximants: by `limit_dominance` it forces RH
  (here), and classically (Pólya, Laguerre–Pólya class) it is available exactly under RH, via the
  Hadamard product over the zeros themselves — the spectral side, labelled by the zeros.

Nothing here is conditional; the structure asserts nothing. No `sorry`, no `axiom`.
-/

open Filter Topology Complex CriticalLinePhasor.XiChannel CriticalLinePhasor.LimitDominance

namespace CriticalLinePhasor.Cascade

/-- **Source labelling**: every vanishing of every stage is at a real height. -/
def SourceLabelled (C : MidpointCascade) : Prop :=
  ∀ (n : ℕ) (z : ℂ), C.stage n z = 0 → z.im = 0

/-- Source labelling implies completeness: accumulation points of real heights are real. -/
theorem complete_of_sourceLabelled (C : MidpointCascade) (h : SourceLabelled C) : Complete C := by
  intro z hacc
  by_contra hne
  have hpos : 0 < |z.im| := abs_pos.mpr hne
  obtain ⟨n, w, hw, hw0⟩ := (hacc |z.im| hpos).exists
  have hwim : w.im = 0 := h n w hw0
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h1 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im, hwim, zero_sub, abs_neg] at h1
  linarith

/-- **The no-origination theorem.**  For a source-labelled cascade, every vanishing of the
ξ-section sits at a real height: the projection cannot originate an event. -/
theorem projection_cannot_originate_events (C : MidpointCascade) (h : SourceLabelled C)
    (z : ℂ) (hz : xiSection z = 0) : z.im = 0 := by
  apply complete_of_sourceLabelled C h z
  intro ε hε
  have hconv : TendstoLocallyUniformlyOn C.stage xiSection atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr C.converges
  exact limit_dominance isOpen_univ hconv (fun n => (C.stage_entire n).differentiableOn)
    (Set.mem_univ z) hz (xiSection_not_eventually_zero z) hε

/-- A source-labelled cascade converging to the ξ-section forces the Riemann Hypothesis. -/
theorem rh_of_sourceLabelled_cascade (C : MidpointCascade) (h : SourceLabelled C) :
    RiemannHypothesis :=
  riemannHypothesis_of_complete_cascade C (complete_of_sourceLabelled C h)

/-! ## Where the hypothesis lives: carrier-phasor stages are not source-labelled -/

/-- The two-phasor η-stage in the spectral chart, `1 − 2^{−(½ + iz)}`: the first two phasors of
the conducted ζ-fiber. -/
noncomputable def twoPhasorStage (z : ℂ) : ℂ := 1 - (2 : ℂ) ^ (-((1 / 2 : ℂ) + I * z))

/-- **The first phasor-built stage already vanishes off the fold**, at `z = i/2` — the helix end
`Re s = 0`.  Source labelling is not a property of being built from carrier states. -/
theorem twoPhasorStage_vanishes_off_fold :
    twoPhasorStage (I / 2) = 0 ∧ (I / 2 : ℂ).im ≠ 0 := by
  constructor
  · unfold twoPhasorStage
    have h0 : -((1 / 2 : ℂ) + I * (I / 2)) = 0 := by
      linear_combination (-(1 / 2 : ℂ)) * I_sq
    rw [h0, Complex.cpow_zero, sub_self]
  · simp

end CriticalLinePhasor.Cascade

#print axioms CriticalLinePhasor.Cascade.projection_cannot_originate_events
#print axioms CriticalLinePhasor.Cascade.rh_of_sourceLabelled_cascade
#print axioms CriticalLinePhasor.Cascade.twoPhasorStage_vanishes_off_fold
