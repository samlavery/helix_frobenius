import RequestProject.StripDomain

/-!
# The boundary of the modular fundamental domain is null

Slice three (a) of the Rankin–Selberg unfolding chain (brick (iv)).  The closed fundamental
domain `𝒟 = ModularGroup.fd` exceeds its interior `𝒟ᵒ` only on the unit circle and the two
vertical boundary lines, and all three are null for the hyperbolic measure
(`fd_boundary_null`): the hyperbolic measure is absolutely continuous with respect to the
Lebesgue measure pulled back through the coercion, vertical lines are product-null, and the
circle is a sphere, hence Haar-null.  This is the a.e.-disjointness input for tiling the strip
by coset translates of `𝒟`.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups Pointwise

namespace CriticalLinePhasor.Unfolding

/-- Vertical lines are Lebesgue-null in the plane. -/
lemma volume_re_line (c : ℝ) : (volume : Measure ℂ) {z : ℂ | z.re = c} = 0 := by
  have h : {z : ℂ | z.re = c} =
      Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ Set.univ) := by
    ext z
    simp [Complex.measurableEquivRealProd_apply, Set.mem_prod]
  rw [h, MeasurePreserving.measure_preimage Complex.volume_preserving_equiv_real_prod
    (((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet)]
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- Null sets upstairs: a set of `ℍ` whose coercion-image is Lebesgue-null is null for the
hyperbolic measure. -/
lemma volume_null_of_coe_image_null {A : Set ℍ}
    (h : (volume : Measure ℂ) (UpperHalfPlane.coe '' A) = 0) :
    (volume : Measure ℍ) A = 0 := by
  have h1 : (volume.comap UpperHalfPlane.coe) A = 0 := by
    rw [MeasurableEmbedding.comap_apply UpperHalfPlane.measurableEmbedding_coe]
    exact h
  rw [UpperHalfPlane.volume_def]
  exact withDensity_absolutelyContinuous _ _ h1

/-- The unit-circle locus in `ℍ` is null. -/
lemma volume_normSq_one_null :
    (volume : Measure ℍ) {z : ℍ | Complex.normSq ↑z = 1} = 0 := by
  apply volume_null_of_coe_image_null
  apply measure_mono_null (t := Metric.sphere (0 : ℂ) 1)
  · rintro w ⟨z, hz, rfl⟩
    have hn : ‖(z : ℂ)‖ = 1 := by
      have h2 : ‖(z : ℂ)‖ ^ 2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq]
        exact hz
      nlinarith [norm_nonneg (z : ℂ)]
    simp [hn]
  · exact Measure.addHaar_sphere volume 0 1

/-- The vertical-line locus in `ℍ` is null. -/
lemma volume_re_eq_null (c : ℝ) :
    (volume : Measure ℍ) {z : ℍ | z.re = c} = 0 := by
  apply volume_null_of_coe_image_null
  apply measure_mono_null (t := {w : ℂ | w.re = c})
  · rintro w ⟨z, hz, rfl⟩
    exact hz
  · exact volume_re_line c

/-- **The boundary of the modular fundamental domain is null.** -/
theorem fd_boundary_null :
    (volume : Measure ℍ) (ModularGroup.fd \ ModularGroup.fdo) = 0 := by
  have hsub : ModularGroup.fd \ ModularGroup.fdo ⊆
      {z : ℍ | Complex.normSq ↑z = 1} ∪
        ({z : ℍ | z.re = 1 / 2} ∪ {z : ℍ | z.re = -(1 / 2)}) := by
    rintro z ⟨⟨h1, h2⟩, hno⟩
    rw [ModularGroup.fdo, Set.mem_setOf_eq, not_and_or] at hno
    rcases hno with h | h
    · left
      exact le_antisymm (not_lt.mp h) h1
    · right
      have habs : |z.re| = 1 / 2 := le_antisymm h2 (not_lt.mp h)
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1 / 2) |>.mp habs with h' | h'
      · left
        exact h'
      · right
        exact h'
  apply measure_mono_null hsub
  rw [measure_union_null_iff]
  refine ⟨volume_normSq_one_null, ?_⟩
  rw [measure_union_null_iff]
  exact ⟨volume_re_eq_null _, volume_re_eq_null _⟩

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.fd_boundary_null
