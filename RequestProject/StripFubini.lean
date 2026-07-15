import RequestProject.RSIntegrand

/-!
# Fubini on the strip: the hyperbolic strip integral in coordinates

Slice five (b) of brick (iv).  The strip integral of any integrable function against the
hyperbolic measure unfolds into an iterated Lebesgue integral in the natural coordinates
(`strip_integral_eq_iterated`):

  `∫_{strip} G dμ_ℍ  =  ∫_{y>0} ∫_{0≤x<1}  y⁻² · G(x+iy)  dx dy`.

The chain: the hyperbolic measure is the pulled-back planar measure with density `y⁻²`
(Mathlib's `volume_def`), the coercion is measure-preserving onto its range, the plane splits
into coordinates by the measure-preserving `measurableEquivRealProd`, and Tonelli–Fubini
(`integral_prod_symm`) splits the product.  Instantiated at the RS integrand, the inner
integral is the exact energy readout (`rankin_energy_exact`) and the outer integral is the
Mellin transform — the strip side of the Rankin–Selberg method.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups Pointwise NNReal

namespace CriticalLinePhasor.Unfolding

/-- The strip in planar coordinates. -/
lemma coe_image_strip :
    UpperHalfPlane.coe '' strip = {w : ℂ | w.re ∈ Set.Ico (0:ℝ) 1 ∧ 0 < w.im} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, z.im_pos⟩
  · rintro ⟨hre, him⟩
    exact ⟨⟨w, him⟩, hre, rfl⟩

/-- **Fubini for the hyperbolic strip**: the strip integral against the hyperbolic measure is
the iterated coordinate integral with density `y⁻²`. -/
theorem strip_integral_eq_iterated (G : ℍ → ℂ)
    (hG : Integrable (fun p : ℝ × ℝ => ((p.2 ^ 2)⁻¹ : ℝ) •
        G (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm p)))
      ((volume.restrict (Set.Ico (0:ℝ) 1)).prod (volume.restrict (Set.Ioi (0:ℝ))))) :
    ∫ z in strip, G z ∂(volume : Measure ℍ) =
      ∫ y in Set.Ioi (0:ℝ), ∫ x in Set.Ico (0:ℝ) 1, ((y ^ 2)⁻¹ : ℝ) •
        G (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm (x, y)))
        ∂volume ∂volume := by
  set e := Complex.measurableEquivRealProd with he
  set T : Set (ℝ × ℝ) := Set.Ico (0:ℝ) 1 ×ˢ Set.Ioi (0:ℝ) with hT
  set D : ℍ → ℝ≥0 := fun z => (1 / NNReal.mk z.im z.im_pos.le) ^ 2 with hD
  have hDcont : Continuous D := by
    refine Continuous.pow (Continuous.div₀ continuous_const ?_ ?_) _
    · exact UpperHalfPlane.continuous_im.subtype_mk _
    · exact fun z => NNReal.ne_iff.mp z.im_ne_zero
  -- Step 1: unpack the density.
  have h1 : ∫ z in strip, G z ∂(volume : Measure ℍ) =
      ∫ z in strip, D z • G z ∂(volume.comap UpperHalfPlane.coe) := by
    rw [UpperHalfPlane.volume_def, restrict_withDensity measurableSet_strip]
    exact integral_withDensity_eq_integral_smul hDcont.measurable G
  -- Step 2: move to the plane through the coercion.
  have hmp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (Set.range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe,
      UpperHalfPlane.measurableEmbedding_coe.map_comap volume⟩
  have h2 : ∫ z in strip, D z • G z ∂(volume.comap UpperHalfPlane.coe) =
      ∫ w in UpperHalfPlane.coe '' strip,
        D (UpperHalfPlane.ofComplex w) • G (UpperHalfPlane.ofComplex w)
        ∂(volume.restrict (Set.range UpperHalfPlane.coe)) := by
    rw [hmp.setIntegral_image_emb UpperHalfPlane.measurableEmbedding_coe]
    refine setIntegral_congr_fun measurableSet_strip fun z _ => ?_
    rw [ofComplex_apply]
  -- Step 3: the image lies in the range; drop the restriction.
  have hmeas_img : MeasurableSet (UpperHalfPlane.coe '' strip) := by
    rw [coe_image_strip]
    exact (measurableSet_Ico.preimage Complex.measurable_re).inter
      (measurableSet_Ioi.preimage Complex.measurable_im)
  have h3 : ∫ w in UpperHalfPlane.coe '' strip,
      D (UpperHalfPlane.ofComplex w) • G (UpperHalfPlane.ofComplex w)
      ∂(volume.restrict (Set.range UpperHalfPlane.coe)) =
      ∫ w in UpperHalfPlane.coe '' strip,
        D (UpperHalfPlane.ofComplex w) • G (UpperHalfPlane.ofComplex w)
        ∂(volume : Measure ℂ) := by
    rw [Measure.restrict_restrict hmeas_img,
      Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _)]
  -- Step 4: split the plane into coordinates.
  have himg2 : UpperHalfPlane.coe '' strip = e.symm '' T := by
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
  have hmp2 : MeasurePreserving (⇑e.symm) (volume : Measure (ℝ × ℝ))
      (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm e
  have h4 : ∫ w in UpperHalfPlane.coe '' strip,
      D (UpperHalfPlane.ofComplex w) • G (UpperHalfPlane.ofComplex w)
      ∂(volume : Measure ℂ) =
      ∫ p in T, D (UpperHalfPlane.ofComplex (e.symm p)) •
        G (UpperHalfPlane.ofComplex (e.symm p)) ∂(volume : Measure (ℝ × ℝ)) := by
    rw [himg2, hmp2.setIntegral_image_emb e.symm.measurableEmbedding]
  -- Step 5: identify the density on the coordinate window.
  have hscalar : ∀ p ∈ T, D (UpperHalfPlane.ofComplex (e.symm p)) •
      G (UpperHalfPlane.ofComplex (e.symm p)) =
      ((p.2 ^ 2)⁻¹ : ℝ) • G (UpperHalfPlane.ofComplex (e.symm p)) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have him : (e.symm (x, y)).im = y := by
      have h := e.apply_symm_apply (x, y)
      rw [he, Complex.measurableEquivRealProd_apply] at h
      exact congrArg Prod.snd h
    have hypos : (0 : ℝ) < (e.symm (x, y)).im := him ▸ hy
    rw [NNReal.smul_def]
    congr 1
    rw [hD]
    have him2 : (UpperHalfPlane.ofComplex (e.symm (x, y))).im = y := by
      rw [ofComplex_apply_of_im_pos hypos]
      exact him
    rw [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, him2, one_div,
      inv_pow]
  have hmeasT : MeasurableSet T := measurableSet_Ico.prod measurableSet_Ioi
  have h5 : ∫ p in T, D (UpperHalfPlane.ofComplex (e.symm p)) •
      G (UpperHalfPlane.ofComplex (e.symm p)) ∂(volume : Measure (ℝ × ℝ)) =
      ∫ p in T, ((p.2 ^ 2)⁻¹ : ℝ) •
        G (UpperHalfPlane.ofComplex (e.symm p)) ∂(volume : Measure (ℝ × ℝ)) :=
    setIntegral_congr_fun hmeasT hscalar
  -- Step 6: Fubini.
  have h6 : ∫ p in T, ((p.2 ^ 2)⁻¹ : ℝ) •
      G (UpperHalfPlane.ofComplex (e.symm p)) ∂(volume : Measure (ℝ × ℝ)) =
      ∫ y in Set.Ioi (0:ℝ), ∫ x in Set.Ico (0:ℝ) 1, ((y ^ 2)⁻¹ : ℝ) •
        G (UpperHalfPlane.ofComplex (e.symm (x, y))) ∂volume ∂volume := by
    rw [hT, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integral_prod_symm _ hG
  rw [h1, h2, h3, h4, h5, h6]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.strip_integral_eq_iterated
