import RequestProject.RSDominant
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The fundamental domain has finite hyperbolic measure

The measure-theoretic input for the continuation.  The modular fundamental domain sits inside
the half-strip `{|re| ≤ 1/2, im ≥ √3/2}`, whose hyperbolic measure is finite (the coordinate
integral `∫_{y ≥ √3/2} y⁻² dy` converges, the `x`-width being one), so `volume 𝒟 < ∞`
(`volume_fd_lt_top`).  Consequently every bounded height-weight is integrable over `𝒟`
(`integrableOn_fd_of_bounded`) — the finiteness that Route B's `G`-decay estimate consumes.
No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Set
open scoped Real Topology NNReal ENNReal

namespace CriticalLinePhasor.Unfolding

/-- The hyperbolic density as a height weight. -/
noncomputable def ρ (y : ℝ) : ℝ≥0∞ := (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)

/-- The half-strip containing the fundamental domain. -/
def halfStrip : Set ℍ := {z : ℍ | |z.re| ≤ 1/2 ∧ Real.sqrt 3 / 2 ≤ z.im}

/-- The fundamental domain sits inside the half-strip. -/
lemma fd_subset_halfStrip : ModularGroup.fd ⊆ halfStrip := fun z hz =>
  ⟨hz.2, CriticalLinePhasor.HeckeSupBound.fd_im_ge hz⟩

lemma measurableSet_halfStrip : MeasurableSet halfStrip := by
  apply MeasurableSet.inter
  · exact measurableSet_Iic.preimage (UpperHalfPlane.continuous_re.abs).measurable
  · exact measurableSet_Ici.preimage UpperHalfPlane.continuous_im.measurable

/-- Planar image of the half-strip. -/
lemma coe_image_halfStrip :
    UpperHalfPlane.coe '' halfStrip =
      {w : ℂ | |w.re| ≤ 1/2 ∧ Real.sqrt 3 / 2 ≤ w.im} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · rintro ⟨hre, him⟩
    have hpos : 0 < w.im := lt_of_lt_of_le (by positivity) him
    exact ⟨⟨w, hpos⟩, ⟨hre, him⟩, rfl⟩

/-- The `y⁻²` weight has finite lintegral over the height half-line. -/
lemma lintegral_ρ_Ici_lt_top :
    ∫⁻ y in Ici (Real.sqrt 3 / 2), ρ y < ∞ := by
  have h32 : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity
  have hIoi : IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹) (Ioi (Real.sqrt 3 / 2)) := by
    refine (integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) h32).congr_fun
      (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := lt_trans h32 hy
    show y ^ (-2 : ℝ) = (y ^ 2)⁻¹
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hy0.le,
      Real.rpow_natCast]
  have hint : IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹) (Ici (Real.sqrt 3 / 2)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hIoi
  have hfin : ∫⁻ y in Ici (Real.sqrt 3 / 2), ‖(y ^ 2)⁻¹‖ₑ < ∞ :=
    hint.hasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  refine setLIntegral_congr_fun measurableSet_Ici (fun y hy => ?_)
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le h32 hy
  rw [ρ, enorm_eq_nnnorm]
  congr 1
  rw [nnnorm_inv, nnnorm_pow, one_div, inv_pow]

/-- **The half-strip has finite hyperbolic measure.** -/
lemma volume_halfStrip_lt_top : volume halfStrip < ∞ := by
  set B : Set (ℝ × ℝ) := Icc (-(1/2) : ℝ) (1/2) ×ˢ Ici (Real.sqrt 3 / 2) with hB
  have hpre : Complex.measurableEquivRealProd ⁻¹' B =
      {w : ℂ | |w.re| ≤ 1/2 ∧ Real.sqrt 3 / 2 ≤ w.im} := by
    ext w
    simp only [mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod,
      mem_Icc, mem_Ici, mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨abs_le.mpr ⟨h1, h2⟩, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨abs_le.mp h1, h2⟩
  have htrans : ∫⁻ w in {w : ℂ | |w.re| ≤ 1/2 ∧ Real.sqrt 3 / 2 ≤ w.im}, ρ w.im
      ∂(volume : Measure ℂ) =
      ∫⁻ p in B, ρ p.2 ∂(volume : Measure (ℝ × ℝ)) := by
    rw [← hpre,
      ← Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
        Complex.measurableEquivRealProd.measurableEmbedding (fun p => ρ p.2) B]
    simp only [Complex.measurableEquivRealProd_apply]
  rw [UpperHalfPlane.volume_eq_lintegral, coe_image_halfStrip]
  have hρeq : ∀ w : ℂ, (((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ρ w.im := fun w => rfl
  simp only [hρeq]
  rw [htrans, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => ρ p.2)
      ((volume.restrict (Icc (-(1/2) : ℝ) (1/2))).prod
        (volume.restrict (Ici (Real.sqrt 3 / 2)))) := by
    apply Measurable.aemeasurable
    exact ((measurable_const.div measurable_snd.nnnorm).pow_const 2).coe_nnreal_ennreal
  rw [MeasureTheory.lintegral_prod _ hmeas]
  have hinner : ∀ x : ℝ, ∫⁻ y, ρ y ∂(volume.restrict (Ici (Real.sqrt 3 / 2))) =
      ∫⁻ y in Ici (Real.sqrt 3 / 2), ρ y := fun x => rfl
  simp only [hinner]
  rw [MeasureTheory.lintegral_const]
  apply ENNReal.mul_lt_top lintegral_ρ_Ici_lt_top
  rw [Measure.restrict_apply_univ]
  exact measure_Icc_lt_top

/-- **The fundamental domain has finite hyperbolic measure.** -/
lemma volume_fd_lt_top : volume ModularGroup.fd < ∞ :=
  lt_of_le_of_lt (measure_mono fd_subset_halfStrip) volume_halfStrip_lt_top

/-- **Bounded height-weights are integrable over the fundamental domain.** -/
lemma integrableOn_fd_of_bounded {g : ℍ → ℝ} (hg : Continuous g) {C : ℝ}
    (hbdd : ∀ z ∈ ModularGroup.fd, ‖g z‖ ≤ C) :
    IntegrableOn g ModularGroup.fd volume := by
  have hmeasfd : MeasurableSet ModularGroup.fd := by
    have h1 : IsClosed {z : ℍ | 1 ≤ Complex.normSq ↑z} :=
      isClosed_Ici.preimage (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
    have h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2} :=
      isClosed_Iic.preimage UpperHalfPlane.continuous_re.abs
    exact (h1.inter h2).measurableSet
  refine Integrable.mono' (g := fun _ => C)
    (integrableOn_const volume_fd_lt_top.ne) hg.aestronglyMeasurable.restrict ?_
  exact (ae_restrict_mem hmeasfd).mono hbdd

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.volume_fd_lt_top
#print axioms CriticalLinePhasor.Unfolding.integrableOn_fd_of_bounded