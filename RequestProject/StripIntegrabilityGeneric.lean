import RequestProject.RSTransport

/-!
# Strip integrability, factored out of the holomorphic case

`RSTransport.rsIntegrand_integrableOn_strip` transports integrability from the product side to the
strip in four steps: unpack the hyperbolic density, push forward to the plane along
`UpperHalfPlane.coe`, change coordinates by `Complex.measurableEquivRealProd`, and identify the
density on the window.  **None of those steps mentions the cusp form** — they are facts about the
measure on `ℍ` — and the only form-dependent line is the last, where
`rsIntegrand_product_integrable` is supplied.

This file extracts the form-independent skeleton as `integrableOn_strip_of_product`, taking the
product-side integrability as a hypothesis.  The holomorphic lemma becomes one application of it,
and so does the Maass one, whose product-side input is `maass_horizontal_energy` against the Bessel
decay.

Nothing here is new mathematics; it is the corpus's own measure plumbing made reusable, which is
what stops the Maass port from being a ninety-line duplication.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups Pointwise NNReal

namespace CriticalLinePhasor.Unfolding

/-- **Strip integrability from the product side, for an arbitrary integrand.**  The hyperbolic
measure bookkeeping is independent of what is being integrated. -/
lemma integrableOn_strip_of_product (G : ℍ → ℂ)
    (hInt : Integrable
      (fun p : ℝ × ℝ =>
        ((1 / NNReal.mk (UpperHalfPlane.ofComplex
            (Complex.measurableEquivRealProd.symm p)).im
          (UpperHalfPlane.ofComplex
            (Complex.measurableEquivRealProd.symm p)).im_pos.le) ^ 2) •
          G (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm p)))
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Ico (0:ℝ) 1 ×ˢ Set.Ioi (0:ℝ)))) :
    IntegrableOn G strip (volume : Measure ℍ) := by
  set e := Complex.measurableEquivRealProd with he
  set T : Set (ℝ × ℝ) := Set.Ico (0:ℝ) 1 ×ˢ Set.Ioi (0:ℝ) with hT
  set D : ℍ → ℝ≥0 := fun z => (1 / NNReal.mk z.im z.im_pos.le) ^ 2 with hD
  have hDcont : Continuous D := by
    refine Continuous.pow (Continuous.div₀ continuous_const ?_ ?_) _
    · exact UpperHalfPlane.continuous_im.subtype_mk _
    · exact fun z => NNReal.ne_iff.mp z.im_ne_zero
  -- step 1: unpack the density
  rw [IntegrableOn, UpperHalfPlane.volume_def, restrict_withDensity measurableSet_strip,
    integrable_withDensity_iff_integrable_smul hDcont.measurable]
  -- step 2: move to the plane
  have hmeas_img : MeasurableSet (UpperHalfPlane.coe '' strip) := by
    rw [coe_image_strip]
    exact (measurableSet_Ico.preimage Complex.measurable_re).inter
      (measurableSet_Ioi.preimage Complex.measurable_im)
  have hmap1 : ((volume.comap UpperHalfPlane.coe).restrict strip).map UpperHalfPlane.coe =
      (volume : Measure ℂ).restrict (UpperHalfPlane.coe '' strip) := by
    have hpre : strip = UpperHalfPlane.coe ⁻¹' (UpperHalfPlane.coe '' strip) :=
      (Set.preimage_image_eq strip
        UpperHalfPlane.measurableEmbedding_coe.injective).symm
    rw [show ((volume.comap UpperHalfPlane.coe).restrict strip) =
      ((volume.comap UpperHalfPlane.coe).restrict
        (UpperHalfPlane.coe ⁻¹' (UpperHalfPlane.coe '' strip))) by rw [← hpre]]
    rw [← Measure.restrict_map UpperHalfPlane.measurable_coe hmeas_img,
      UpperHalfPlane.measurableEmbedding_coe.map_comap,
      Measure.restrict_restrict hmeas_img,
      Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _)]
  have hstep2 : Integrable (fun z : ℍ => D z • G z)
      ((volume.comap UpperHalfPlane.coe).restrict strip) ↔
      Integrable (fun w : ℂ => D (UpperHalfPlane.ofComplex w) •
        G (UpperHalfPlane.ofComplex w))
        ((volume : Measure ℂ).restrict (UpperHalfPlane.coe '' strip)) := by
    rw [← hmap1, UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff]
    constructor
    · intro h
      refine h.congr (Filter.Eventually.of_forall fun z => ?_)
      rw [Function.comp_apply, ofComplex_apply]
    · intro h
      refine h.congr (Filter.Eventually.of_forall fun z => ?_)
      rw [Function.comp_apply, ofComplex_apply]
  rw [hstep2]
  -- step 3: split into coordinates
  have himg2 : UpperHalfPlane.coe '' strip = ⇑e.symm '' T := by
    rw [coe_image_strip]
    ext w
    constructor
    · rintro ⟨hre, him⟩
      refine ⟨e w, ?_, e.symm_apply_apply w⟩
      rw [he, Complex.measurableEquivRealProd_apply]
      exact ⟨hre, him⟩
    · rintro ⟨p, hp, rfl⟩
      have h := e.apply_symm_apply p
      rw [he, Complex.measurableEquivRealProd_apply] at h
      rw [← h] at hp
      exact ⟨hp.1, hp.2⟩
  have hmap2 : ((volume : Measure (ℝ × ℝ)).restrict T).map ⇑e.symm =
      (volume : Measure ℂ).restrict (UpperHalfPlane.coe '' strip) := by
    have hpre2 : T = ⇑e.symm ⁻¹' (⇑e.symm '' T) :=
      (Set.preimage_image_eq T e.symm.injective).symm
    have hmeasT' : MeasurableSet (⇑e.symm '' T) := by
      rw [← himg2]
      exact hmeas_img
    rw [show ((volume : Measure (ℝ × ℝ)).restrict T) =
      ((volume : Measure (ℝ × ℝ)).restrict (⇑e.symm ⁻¹' (⇑e.symm '' T))) by rw [← hpre2]]
    rw [← Measure.restrict_map e.symm.measurable hmeasT',
      (Complex.volume_preserving_equiv_real_prod.symm e).map_eq, himg2]
  rw [← hmap2, e.symm.measurableEmbedding.integrable_map_iff]
  exact hInt

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.integrableOn_strip_of_product
