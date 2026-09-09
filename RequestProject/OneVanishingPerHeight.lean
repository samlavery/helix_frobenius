import RequestProject.SourceLabelledCascade

/-!
# One vanishing per height ⟺ source labelling, and RH from it (ledger 664)

In the spectral chart `z` (`xiSection z = ξ(½ + iz)`), the height of a vanishing is `Re z` and "on the
line" is `Im z = 0`.  For a stage that is real on the axis, `f(z̄) = conj f(z)`, a non-real zero `z` comes
with its conjugate `z̄` at the SAME height.  So Sam's principle — a stage has one vanishing per height —
is exactly `SourceLabelled`, and the compiled transfer theorem `rh_of_sourceLabelled_cascade` turns it
into the Riemann Hypothesis.

* `OneVanishingPerHeight C` — no two distinct zeros of any stage share a height.
* `RealStages C` — every stage is real on the axis.
* `sourceLabelled_of_oneVanishingPerHeight`, `oneVanishingPerHeight_of_sourceLabelled` — the equivalence.
* **`rh_of_oneVanishingPerHeight`** — RH from one vanishing per height on a real cascade converging to ξ.
-/

open Complex

namespace CriticalLinePhasor.Cascade

/-- **One vanishing per height:** two zeros of a stage at the same height are the same zero. -/
def OneVanishingPerHeight (C : MidpointCascade) : Prop :=
  ∀ (n : ℕ) (z w : ℂ), C.stage n z = 0 → C.stage n w = 0 → z.re = w.re → z = w

/-- Stages real on the axis: `f(z̄) = conj f(z)`. -/
def RealStages (C : MidpointCascade) : Prop :=
  ∀ (n : ℕ) (z : ℂ), C.stage n ((starRingEnd ℂ) z) = (starRingEnd ℂ) (C.stage n z)

theorem sourceLabelled_of_oneVanishingPerHeight (C : MidpointCascade) (hR : RealStages C)
    (h1 : OneVanishingPerHeight C) : SourceLabelled C := by
  intro n z hz
  have hzbar : C.stage n ((starRingEnd ℂ) z) = 0 := by rw [hR, hz, map_zero]
  have heq : z = (starRingEnd ℂ) z := h1 n z ((starRingEnd ℂ) z) hz hzbar (by simp)
  have := congrArg Complex.im heq
  simp only [Complex.conj_im] at this
  linarith

theorem oneVanishingPerHeight_of_sourceLabelled (C : MidpointCascade) (h : SourceLabelled C) :
    OneVanishingPerHeight C := by
  intro n z w hz hw hre
  exact Complex.ext hre (by rw [h n z hz, h n w hw])

theorem oneVanishingPerHeight_iff_sourceLabelled (C : MidpointCascade) (hR : RealStages C) :
    OneVanishingPerHeight C ↔ SourceLabelled C :=
  ⟨sourceLabelled_of_oneVanishingPerHeight C hR, oneVanishingPerHeight_of_sourceLabelled C⟩

/-- **RH from one vanishing per height** on a real cascade converging to the ξ-section. -/
theorem rh_of_oneVanishingPerHeight (C : MidpointCascade) (hR : RealStages C)
    (h1 : OneVanishingPerHeight C) : RiemannHypothesis :=
  rh_of_sourceLabelled_cascade C (sourceLabelled_of_oneVanishingPerHeight C hR h1)

end CriticalLinePhasor.Cascade

#print axioms CriticalLinePhasor.Cascade.oneVanishingPerHeight_iff_sourceLabelled
#print axioms CriticalLinePhasor.Cascade.rh_of_oneVanishingPerHeight
