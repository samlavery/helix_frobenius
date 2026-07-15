import RequestProject.GlobalHelixGaussianThetaBounds
import RequestProject.CarrierMellinContinuation

/-!
# Strong Mellin pairs from finite 3D Gaussian helix banks

For a finite reciprocal-height index bank, a coefficient fixed by the Gaussian dual-amplitude
transport gives a self-reflecting 3D source.  The fixed inversion-symmetric envelope preserves that
reflection and supplies rapid decay.  Only then is the scalar projection packaged as Mathlib's
`StrongFEPair`.
-/

open Real Complex Filter Asymptotics MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

/-- Fixed-envelope completion of the primal 3D Gaussian bank. -/
noncomputable def finiteEnvelopedGaussian3DBankReadout
    {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℝ) (x : ℝ) : ℂ :=
  (CriticalLinePhasor.StrandExchange.selfDualEnvelope 0 x : ℂ) *
    indexedGaussian3DBankReadout a H x

/-- Fixed-envelope completion of the globally reflected/sheared 3D bank. -/
noncomputable def finiteEnvelopedGaussian3DTransformedReadout
    {I : Type*} [Fintype I]
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I) (x : ℝ) : ℂ :=
  (CriticalLinePhasor.StrandExchange.selfDualEnvelope 0 x : ℂ) *
    indexedGaussian3DTransformedReadout a H dual x

/-- The fixed envelope preserves the exact equality of the primal and transformed 3D banks. -/
theorem finiteEnvelopedGaussian3D_globalHelixReflection
    {I : Type*} [Fintype I]
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (hrecip : ∀ i, H (dual.symm i) = (H i)⁻¹)
    {x : ℝ} (hx : 0 < x) :
    finiteEnvelopedGaussian3DBankReadout a H x =
      ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        finiteEnvelopedGaussian3DTransformedReadout a H dual x := by
  unfold finiteEnvelopedGaussian3DBankReadout
    finiteEnvelopedGaussian3DTransformedReadout
  rw [indexedGaussian3D_globalHelixReflection a H dual hH hrecip hx]
  ring

/-- Scalar projection of the enveloped 3D source. -/
noncomputable def finiteEnvelopedGaussianTheta
    {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℝ) (x : ℝ) : ℂ :=
  (CriticalLinePhasor.StrandExchange.selfDualEnvelope 0 x : ℂ) *
    indexedTheta a H (fun t => (gaussianLatticeTheta t : ℂ)) x

/-- A dual-amplitude fixed point turns the transported bank into the same scalar theta at reciprocal
external height. -/
theorem indexedGaussianTheta_self_reflection
    {I : Type*} [Fintype I]
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (hrecip : ∀ i, H (dual.symm i) = (H i)⁻¹)
    (hfixed : ∀ i, gaussianPoissonDualAmplitude a H dual i = a i)
    {x : ℝ} (hx : 0 < x) :
    indexedTheta a H (fun t => (gaussianLatticeTheta t : ℂ)) (1 / x) =
      ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        indexedTheta a H (fun t => (gaussianLatticeTheta t : ℂ)) x := by
  have h := indexedGaussianTheta_reflection a H dual hH hrecip (one_div_pos.mpr hx)
  have hfun : gaussianPoissonDualAmplitude a H dual = a := funext hfixed
  rw [hfun] at h
  simp only [one_div, inv_inv] at h
  have hscale : 1 / x⁻¹ ^ (1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) := by
    rw [Real.inv_rpow hx.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hx _)]
  convert h using 1
  · simp only [one_div]
  · congr 1
    have hscaleC := congrArg (fun y : ℝ => (y : ℂ)) hscale.symm
    simpa only [one_div, ofReal_inv] using hscaleC

/-- The enveloped scalar projection has the weight-`1/2` Riemann--Hecke reflection. -/
theorem finiteEnvelopedGaussianTheta_one_div
    {I : Type*} [Fintype I]
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (hrecip : ∀ i, H (dual.symm i) = (H i)⁻¹)
    (hfixed : ∀ i, gaussianPoissonDualAmplitude a H dual i = a i)
    {x : ℝ} (hx : 0 < x) :
    finiteEnvelopedGaussianTheta a H (1 / x) =
      (((x ^ (1 / 2 : ℝ) : ℝ) : ℂ)) * finiteEnvelopedGaussianTheta a H x := by
  unfold finiteEnvelopedGaussianTheta
  rw [CriticalLinePhasor.StrandExchange.selfDualEnvelope_one_div 0 hx,
    indexedGaussianTheta_self_reflection a H dual hH hrecip hfixed hx]
  simp only [Real.rpow_zero, one_mul]
  ring

/-- The finite 3D Gaussian bank as an entire strong Mellin functional-equation pair. -/
noncomputable def finiteEnvelopedGaussianStrongFEPair
    {I : Type*} [Fintype I]
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (hrecip : ∀ i, H (dual.symm i) = (H i)⁻¹)
    (hfixed : ∀ i, gaussianPoissonDualAmplitude a H dual i = a i) :
    StrongFEPair ℂ where
  toWeakFEPair := {
    f := finiteEnvelopedGaussianTheta a H
    g := finiteEnvelopedGaussianTheta a H
    k := 1 / 2
    ε := 1
    f₀ := 0
    g₀ := 0
    hf_int := indexedGaussianTheta_enveloped_locallyIntegrableOn a H hH
    hg_int := indexedGaussianTheta_enveloped_locallyIntegrableOn a H hH
    hk := by norm_num
    hε := one_ne_zero
    h_feq := fun x hx => by
      rw [finiteEnvelopedGaussianTheta_one_div a H dual hH hrecip hfixed hx]
      simp [smul_eq_mul]
    hf_top := fun r => by
      simpa [finiteEnvelopedGaussianTheta] using indexedGaussianTheta_enveloped_rapid a H hH r
    hg_top := fun r => by
      simpa [finiteEnvelopedGaussianTheta] using indexedGaussianTheta_enveloped_rapid a H hH r
  }
  hf₀ := rfl
  hg₀ := rfl

/-- Entirety, vertical-strip boundedness, and the global functional equation for the finite 3D
Gaussian bank. -/
theorem finiteEnvelopedGaussian_twistedNiceness
    {I : Type*} [Fintype I]
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (hrecip : ∀ i, H (dual.symm i) = (H i)⁻¹)
    (hfixed : ∀ i, gaussianPoissonDualAmplitude a H dual i = a i) :
    let P := finiteEnvelopedGaussianStrongFEPair a H dual hH hrecip hfixed
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  dsimp only
  let P := finiteEnvelopedGaussianStrongFEPair a H dual hH hrecip hfixed
  exact ⟨P.differentiable_Λ, P.symm.differentiable_Λ,
    fun u v => CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
      P u v,
    fun u v => CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
      P.symm u v,
    P.functional_equation⟩

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.finiteEnvelopedGaussian3D_globalHelixReflection
#print axioms CriticalLinePhasor.GlobalHelix.indexedGaussianTheta_self_reflection
#print axioms CriticalLinePhasor.GlobalHelix.finiteEnvelopedGaussianTheta_one_div
#print axioms CriticalLinePhasor.GlobalHelix.finiteEnvelopedGaussianStrongFEPair
#print axioms CriticalLinePhasor.GlobalHelix.finiteEnvelopedGaussian_twistedNiceness
