import RequestProject.FdTiling

/-!
# The Rankin–Selberg unfolding identity

Slice four of brick (iv) — the identity itself.  For any translation-periodic integrand, the
strip integral equals the coset sum of modular-domain integrals of its translates
(`unfolding_identity`):

  `∫_{strip} F  =  ∑'_{q : ±⟨T⟩\Γ}  ∫_{𝒟} F(γ_q · z)`.

Proof: the strip and the coset tiling are two fundamental domains of the *same* translation
subgroup (`isFundamentalDomain_strip`, `isFundamentalDomain_fdUnion`), so the integral of a
periodic function transfers between them; the tiling integral splits over its almost-disjoint
tiles, and each tile straightens by the measure-preserving Möbius change of variables.
Instantiated with `F = P·(Im)^s` — the Petersson density times the Eisenstein height, both
compiled — the right side becomes the Eisenstein-weighted Petersson integral and the left side
the Mellin transform of the exact energy readout (`rankin_energy_exact`): that is the
Rankin–Selberg method, with every measure-theoretic step now compiled.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups Pointwise

namespace CriticalLinePhasor.Unfolding

/-- The modular action is by measurable maps, hence so is every subgroup action. -/
instance : MeasurableConstSMul SL(2, ℤ) ℍ where
  measurable_const_smul := by
    intro δ
    have hc : Continuous (fun z : ℍ => δ • z) := by
      show Continuous (fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ δ) • z)
      exact continuous_const_smul _
    exact hc.measurable

instance : Countable SL(2, ℤ) := by
  have h1 : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    Countable.of_equiv (Fin 2 → Fin 2 → ℤ) Matrix.of
  exact Subtype.countable

instance : Countable gammaInfty := Subtype.countable

/-- Hyperbolic measure is invariant for the modular action and its subgroups (inherited from
the compiled `GL(2,ℝ)`-invariance). -/
instance : SMulInvariantMeasure SL(2, ℤ) ℍ (volume : Measure ℍ) where
  measure_preimage_smul := by
    intro δ s hs
    show volume ((fun z : ℍ =>
      (Matrix.SpecialLinearGroup.mapGL ℝ δ) • z) ⁻¹' s) = volume s
    exact SMulInvariantMeasure.measure_preimage_smul _ hs

instance : SMulInvariantMeasure gammaInfty ℍ (volume : Measure ℍ) where
  measure_preimage_smul := by
    rintro ⟨δ, hδ⟩ s hs
    show volume ((fun z : ℍ =>
      (Matrix.SpecialLinearGroup.mapGL ℝ δ) • z) ⁻¹' s) = volume s
    exact SMulInvariantMeasure.measure_preimage_smul _ hs

instance : MeasurableConstSMul gammaInfty ℍ where
  measurable_const_smul := by
    rintro ⟨δ, hδ⟩
    have hc : Continuous (fun z : ℍ => δ • z) := by
      show Continuous (fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ δ) • z)
      exact continuous_const_smul _
    exact hc.measurable

/-- Tiles of distinct cosets have null overlap. -/
lemma tiles_aedisjoint : Pairwise (Function.onFun
    (MeasureTheory.AEDisjoint (volume : Measure ℍ))
    fun q : CosetQ => rep q • ModularGroup.fd) := by
  intro q q' hqq
  apply fd_smul_inter_null
  · intro h
    apply hqq
    have h4 := congrArg (Quotient.mk cosetSetoid) h
    simp only [rep] at h4
    rwa [Quotient.out_eq, Quotient.out_eq] at h4
  · intro h
    apply hqq
    have hrel : cosetSetoid.r (rep q') (rep q) := by
      refine ⟨0, Or.inr ?_⟩
      rw [zpow_zero, one_mul]
      exact h
    have h4 : Quotient.mk cosetSetoid (rep q') = Quotient.mk cosetSetoid (rep q) :=
      Quotient.sound hrel
    simp only [rep] at h4
    rw [Quotient.out_eq, Quotient.out_eq] at h4
    exact h4.symm

/-- Change of variables on a tile: integrate over the translated domain by translating the
integrand. -/
lemma tile_integral_eq (δ : SL(2, ℤ)) (F : ℍ → ℂ) :
    ∫ z in δ • ModularGroup.fd, F z ∂(volume : Measure ℍ) =
      ∫ z in ModularGroup.fd, F (δ • z) ∂(volume : Measure ℍ) := by
  have hmp : MeasurePreserving (fun z : ℍ => δ • z) volume volume := by
    show MeasurePreserving (fun z : ℍ =>
      (Matrix.SpecialLinearGroup.mapGL ℝ δ) • z) volume volume
    exact measurePreserving_smul _ _
  have hme : MeasurableEmbedding (fun z : ℍ => δ • z) := by
    show MeasurableEmbedding (fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ δ) • z)
    exact measurableEmbedding_const_smul _
  have himg : δ • ModularGroup.fd = (fun z : ℍ => δ • z) '' ModularGroup.fd := rfl
  rw [himg, hmp.setIntegral_image_emb hme]

/-- **The unfolding identity**: the strip integral of a translation-periodic function is the
coset sum of modular-domain integrals of its translates. -/
theorem unfolding_identity (F : ℍ → ℂ)
    (hF : ∀ (n : ℤ) (z : ℍ), F (ModularGroup.T ^ n • z) = F z)
    (hFi : IntegrableOn F fdUnion (volume : Measure ℍ)) :
    ∫ z in strip, F z ∂(volume : Measure ℍ) =
      ∑' q : CosetQ, ∫ z in ModularGroup.fd, F (rep q • z) ∂(volume : Measure ℍ) := by
  have hinv : ∀ (g : gammaInfty) (z : ℍ), F (g • z) = F z := by
    rintro ⟨δ, hδ⟩ z
    obtain ⟨n, rfl⟩ := hδ
    exact hF n z
  calc ∫ z in strip, F z ∂(volume : Measure ℍ)
      = ∫ z in fdUnion, F z ∂(volume : Measure ℍ) :=
        isFundamentalDomain_strip.setIntegral_eq isFundamentalDomain_fdUnion hinv
    _ = ∑' q : CosetQ, ∫ z in rep q • ModularGroup.fd, F z ∂(volume : Measure ℍ) := by
        rw [fdUnion] at hFi ⊢
        exact integral_iUnion_ae
          (fun q => (measurableSet_smul_fd (rep q)).nullMeasurableSet)
          tiles_aedisjoint hFi
    _ = ∑' q : CosetQ, ∫ z in ModularGroup.fd, F (rep q • z) ∂(volume : Measure ℍ) :=
        tsum_congr fun q => tile_integral_eq (rep q) F

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.unfolding_identity
