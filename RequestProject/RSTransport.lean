import RequestProject.RSStripUnconditional

/-!
# Transporting integrability to the tiling: the full Rankin–Selberg equation

The last measure-theoretic step of brick (iv).  The product-side integrability transports back
through the Fubini chain to the strip (`rsIntegrand_integrableOn_strip`), then across the two
compiled fundamental domains to the coset tiling (`rsIntegrand_integrableOn_fdUnion`), which
discharges the sole hypothesis of the compiled unfolding.  The payoff
(`rankin_selberg_equation`): for `Re s > 2`, with no side conditions,

  `Γ(s+k-1) · ∑' n, ‖a_n‖²/(4πn)^{s+k-1}  =  ∑'_q ∫_𝒟 P(z)·(Im (γ_q·z))^s dμ_ℍ`

— the completed Rankin–Selberg Dirichlet series IS the Petersson–Eisenstein pairing, fully
compiled.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups Pointwise NNReal

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- The strip-side integrability, transported from the product side. -/
lemma rsIntegrand_integrableOn_strip (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (rsIntegrand f s) strip (volume : Measure ℍ) := by
  set G := rsIntegrand f s with hG
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
    rw [← hmap1,
      UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff]
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
  -- step 4: identify the density on the window and finish with the product form
  have hprod : ((volume : Measure (ℝ × ℝ)).restrict T) =
      ((volume.restrict (Set.Ico (0:ℝ) 1)).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    rw [hT, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hmeasT : MeasurableSet T := measurableSet_Ico.prod measurableSet_Ioi
  have hInt := rsIntegrand_product_integrable f hk hs
  rw [← hprod] at hInt
  refine hInt.congr ?_
  filter_upwards [ae_restrict_mem hmeasT] with p hp
  obtain ⟨x, y⟩ := p
  obtain ⟨hx, hy⟩ := hp
  have hy0 : (0 : ℝ) < y := hy
  have him2 : (UpperHalfPlane.ofComplex (e.symm (x, y))).im = y := im_ofComplex_coords hy0
  rw [Function.comp_apply, NNReal.smul_def]
  congr 1
  rw [hD]
  rw [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, him2, one_div,
    inv_pow]

/-- The tiling-side integrability: across the two compiled fundamental domains. -/
lemma rsIntegrand_integrableOn_fdUnion (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (rsIntegrand f s) fdUnion (volume : Measure ℍ) := by
  have hinv : ∀ (g : gammaInfty) (z : ℍ), rsIntegrand f s (g • z) = rsIntegrand f s z := by
    rintro ⟨δ, hδ⟩ z
    obtain ⟨n, rfl⟩ := hδ
    exact rsIntegrand_periodic f s n z
  rw [isFundamentalDomain_fdUnion.integrableOn_iff isFundamentalDomain_strip hinv]
  exact rsIntegrand_integrableOn_strip f hk hs

/-- **The Rankin–Selberg equation, unconditional**: on `Re s > 2` the completed
Rankin–Selberg Dirichlet series is the Petersson–Eisenstein pairing. -/
theorem rankin_selberg_equation (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    Complex.Gamma (s + k - 1) * ∑' n : ℕ,
        ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) /
          ((4 * π * n : ℝ) : ℂ) ^ (s + k - 1) =
      ∑' q : CosetQ, ∫ z in ModularGroup.fd,
        ((P k f z : ℝ) : ℂ) * (((rep q • z).im : ℝ) : ℂ) ^ s ∂(volume : Measure ℍ) := by
  rw [← rs_strip_side_dirichlet f hk hs]
  exact rs_unfolding f s (rsIntegrand_integrableOn_fdUnion f hk (by linarith))

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.rsIntegrand_integrableOn_fdUnion
#print axioms CriticalLinePhasor.Unfolding.rankin_selberg_equation
