import RequestProject.MaassPeterssonFdo

/-!
# The hyperbolic measure is positive on nonempty open sets

Infrastructure the corpus and Mathlib both lack: `(volume : Measure ℍ).IsOpenPosMeasure` is not an
instance and is not inferrable.  It is needed wherever a continuous function has to be recovered
from an almost-everywhere statement — in particular for the positivity of the Petersson norm.

The proof is the definition unwound once.  `volume` on `ℍ` is the pullback of Lebesgue measure
along the open embedding `ℍ ↪ ℂ`, weighted by `(1/y)²`.  Both factors are positive where they act:
the weight never vanishes, and the pullback of Lebesgue along an open embedding sends a nonempty
open set to a nonempty open subset of `ℂ`, which Lebesgue measures positively.

So the statement is not an estimate but a composition of two non-degeneracies — the density's and
the chart's.
-/

open MeasureTheory Measure UpperHalfPlane
open scoped NNReal ENNReal

namespace CriticalLinePhasor.Unfolding

/-- **The hyperbolic measure is positive on nonempty open sets.** -/
instance upperHalfPlane_isOpenPosMeasure :
    (volume : Measure ℍ).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  rw [UpperHalfPlane.volume_def]
  have hDnn : Continuous fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) := by
    refine Continuous.pow (Continuous.div₀ continuous_const ?_ ?_) _
    · exact UpperHalfPlane.continuous_im.subtype_mk _
    · exact fun z => NNReal.ne_iff.mp z.im_ne_zero
  have hD : Measurable fun z : ℍ =>
      (((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) : ℝ≥0∞) :=
    hDnn.measurable.coe_nnreal_ennreal
  rw [Ne, withDensity_apply_eq_zero hD]
  intro hzero
  -- the density never vanishes, so the vanishing set is all of `U`
  have hne : ∀ z : ℍ, (((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    intro z
    have hposr : (0 : ℝ) < (NNReal.mk z.im z.im_pos.le : ℝ) := z.im_pos
    have hpos : (0 : ℝ≥0) < NNReal.mk z.im z.im_pos.le := by
      rw [← NNReal.coe_lt_coe]
      simpa using hposr
    have h1 : (1 / NNReal.mk z.im z.im_pos.le) ≠ 0 := by
      simp only [ne_eq, div_eq_zero_iff, one_ne_zero, false_or]
      exact hpos.ne'
    simp only [ne_eq, ENNReal.coe_eq_zero, pow_eq_zero_iff (two_ne_zero)]
    exact h1
  have hEq : {z : ℍ | (((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ 0} ∩ U = U := by
    ext z
    exact ⟨fun h => h.2, fun h => ⟨hne z, h⟩⟩
  rw [hEq] at hzero
  -- the pullback of Lebesgue along the open embedding is positive on nonempty opens
  rw [UpperHalfPlane.measurableEmbedding_coe.comap_apply] at hzero
  have hopen : IsOpen (UpperHalfPlane.coe '' U) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU
  have hnee : (UpperHalfPlane.coe '' U).Nonempty := hUne.image _
  exact (hopen.measure_pos volume hnee).ne' hzero

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.upperHalfPlane_isOpenPosMeasure
