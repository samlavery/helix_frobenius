import RequestProject.GlobalHelixFiniteGaussianWeakFE

/-!
# Zero-mode-free self-dual Gaussian 3D kernels

Two reciprocal Gaussian scales and one central Gaussian are combined so that the lattice zero mode
vanishes.  The combination remains fixed by Poisson reflection, decays rapidly at both reflected
ends, and therefore gives a strong Mellin functional-equation pair for every finite 3D coefficient
bank without changing its amplitudes.
-/

open Real Complex Filter Asymptotics MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

/-- A self-dual Gaussian lattice kernel with zero Fourier mode. -/
noncomputable def zeroModeGaussianKernel (c x : ℝ) : ℂ :=
  (gaussianLatticeTheta (c * x) : ℂ) +
    ((c⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (gaussianLatticeTheta (c⁻¹ * x) : ℂ) -
    ((1 + c⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (gaussianLatticeTheta x : ℂ)

/-- Poisson reflection preserves the zero-mode-free Gaussian combination. -/
theorem zeroModeGaussianKernel_reflection {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    zeroModeGaussianKernel c x =
      ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) * zeroModeGaussianKernel c (1 / x) := by
  unfold zeroModeGaussianKernel
  rw [gaussianLatticeTheta_reflection (mul_pos hc hx),
    gaussianLatticeTheta_reflection (mul_pos (inv_pos.mpr hc) hx),
    gaussianLatticeTheta_reflection hx]
  have hcroot : c⁻¹ ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) = 1 := by
    rw [Real.inv_rpow hc.le]
    exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hc _))
  have hcx : 1 / (c * x) = c⁻¹ * (1 / x) := by field_simp [hc.ne', hx.ne']
  have hcix : 1 / (c⁻¹ * x) = c * (1 / x) := by field_simp [hc.ne', hx.ne']
  have hs₁ : 1 / (c * x) ^ (1 / 2 : ℝ) =
      c⁻¹ ^ (1 / 2 : ℝ) * (1 / x ^ (1 / 2 : ℝ)) := by
    rw [Real.mul_rpow hc.le hx.le, Real.inv_rpow hc.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hc _),
      ne_of_gt (Real.rpow_pos_of_pos hx _)]
  have hs₂ : c⁻¹ ^ (1 / 2 : ℝ) * (1 / (c⁻¹ * x) ^ (1 / 2 : ℝ)) =
      1 / x ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hx.le, Real.inv_rpow hc.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hc _),
      ne_of_gt (Real.rpow_pos_of_pos hx _)]
  have hs₂C :
      ((c⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          (((c⁻¹ * x) ^ (1 / 2 : ℝ) : ℝ) : ℂ)⁻¹ =
        (((x ^ (1 / 2 : ℝ) : ℝ) : ℂ))⁻¹ := by
    have hcast := congrArg (fun y : ℝ => (y : ℂ)) hs₂
    simpa only [one_div, ofReal_mul, ofReal_inv] using hcast
  rw [hcx, hcix, hs₁]
  push_cast
  have hs₂term :
      ((c⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          (1 / (((c⁻¹ * x) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
            (gaussianLatticeTheta (c * (1 / x)) : ℂ)) =
        1 / (((x ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          (gaussianLatticeTheta (c * (1 / x)) : ℂ) := by
    have ht := congrArg
      (fun z : ℂ => z * (gaussianLatticeTheta (c * (1 / x)) : ℂ)) hs₂C
    simpa only [one_div, mul_assoc] using ht
  rw [hs₂term]
  ring

/-- The kernel is a linear combination of three Gaussian nonzero-mode tails. -/
theorem zeroModeGaussianKernel_eq_tails (c x : ℝ) :
    zeroModeGaussianKernel c x =
      ((gaussianLatticeTheta (c * x) : ℂ) - 1) +
      ((c⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        ((gaussianLatticeTheta (c⁻¹ * x) : ℂ) - 1) -
      ((1 + c⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        ((gaussianLatticeTheta x : ℂ) - 1) := by
  unfold zeroModeGaussianKernel
  push_cast
  ring

/-- The zero-mode-free self-dual kernel decays faster than every real power. -/
theorem zeroModeGaussianKernel_rapid {c : ℝ} (hc : 0 < c) (r : ℝ) :
    zeroModeGaussianKernel c =O[atTop] (fun x : ℝ => x ^ r) := by
  have h₁ := gaussianLatticeTheta_mul_sub_one_rapid hc r
  have h₂ := (gaussianLatticeTheta_mul_sub_one_rapid (inv_pos.mpr hc) r).const_mul_left
    (((c⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ))
  have h₃ := (gaussianLatticeTheta_sub_one_rapid r).const_mul_left
    (((1 + c⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ))
  exact (h₁.add h₂).sub h₃ |>.congr' (Filter.Eventually.of_forall fun x =>
    (zeroModeGaussianKernel_eq_tails c x).symm) (Filter.Eventually.of_forall fun _ => rfl)

/-- Positive external rescaling preserves rapid decay of the zero-mode-free kernel. -/
theorem zeroModeGaussianKernel_mul_rapid {c H : ℝ} (hc : 0 < c) (hH : 0 < H) (r : ℝ) :
    (fun x : ℝ => zeroModeGaussianKernel c (H * x)) =O[atTop]
      (fun x : ℝ => x ^ r) := by
  have hcomp := (zeroModeGaussianKernel_rapid hc r).comp_tendsto
    (tendsto_id.const_mul_atTop hH)
  refine hcomp.trans ?_
  have hconst : (fun x : ℝ => H ^ r * x ^ r) =O[atTop] (fun x : ℝ => x ^ r) :=
    (isBigO_refl (fun x : ℝ => x ^ r) atTop).const_mul_left (H ^ r)
  refine hconst.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact (Real.mul_rpow hH.le hx).symm

/-- A finite indexed zero-mode Gaussian bank. -/
noncomputable def indexedZeroModeGaussianTheta
    {I : Type*} (a : I → ℂ) (H : I → ℝ) (c x : ℝ) : ℂ :=
  indexedTheta a H (zeroModeGaussianKernel c) x

/-- Every finite indexed zero-mode Gaussian bank is rapidly decreasing. -/
theorem indexedZeroModeGaussianTheta_rapid
    {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℝ)
    (hH : ∀ i, 0 < H i) {c : ℝ} (hc : 0 < c) (r : ℝ) :
    indexedZeroModeGaussianTheta a H c =O[atTop] (fun x : ℝ => x ^ r) := by
  unfold indexedZeroModeGaussianTheta indexedTheta
  simp only [tsum_fintype]
  apply IsBigO.sum
  intro i _
  exact (zeroModeGaussianKernel_mul_rapid hc (hH i) r).const_mul_left (a i)

/-- The zero-mode Gaussian kernel has the same reciprocal-height transport law as the base
Gaussian clock. -/
theorem indexedZeroModeGaussianTheta_reflection
    {I : Type*}
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (hrecip : ∀ i, H (dual.symm i) = (H i)⁻¹)
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    indexedZeroModeGaussianTheta a H c x =
      ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        indexedZeroModeGaussianTheta (gaussianPoissonDualAmplitude a H dual) H c (1 / x) := by
  unfold indexedZeroModeGaussianTheta indexedTheta gaussianPoissonDualAmplitude
  calc
    (∑' i, a i * zeroModeGaussianKernel c (H i * x)) =
        ∑' i, a (dual.symm i) * zeroModeGaussianKernel c (H (dual.symm i) * x) := by
      exact (Equiv.tsum_eq dual.symm (fun i => a i * zeroModeGaussianKernel c (H i * x))).symm
    _ = ∑' i, a (dual.symm i) *
          (((H i) ^ (1 / 2 : ℝ) * (1 / x ^ (1 / 2 : ℝ)) : ℝ) : ℂ) *
            zeroModeGaussianKernel c (H i / x) := by
      apply tsum_congr
      intro i
      rw [hrecip, zeroModeGaussianKernel_reflection hc (mul_pos (inv_pos.mpr (hH i)) hx)]
      have hs := reciprocalGaussianHalfScale (hH i) hx
      rw [hs]
      have harg : 1 / ((H i)⁻¹ * x) = H i / x := by
        field_simp [(hH i).ne', hx.ne']
      rw [harg]
      push_cast
      ring
    _ = ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ∑' i, (a (dual.symm i) * ((H i) ^ (1 / 2 : ℝ) : ℝ)) *
            zeroModeGaussianKernel c (H i * (1 / x)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro i
      push_cast
      ring

/-- The zero-mode-free kernel is continuous on positive heights. -/
theorem zeroModeGaussianKernel_continuousOn {c : ℝ} (hc : 0 < c) :
    ContinuousOn (zeroModeGaussianKernel c) (Set.Ioi 0) := by
  have hscaled (d : ℝ) (hd : 0 < d) :
      ContinuousOn (fun x : ℝ => (gaussianLatticeTheta (d * x) : ℂ)) (Set.Ioi 0) := by
    have h := indexedGaussianTheta_continuousOn
      (I := Unit) (fun _ => (1 : ℂ)) (fun _ => d) (fun _ => hd)
    convert h using 1
    funext x
    simp [indexedTheta]
  unfold zeroModeGaussianKernel
  exact ((hscaled c hc).add
    (continuousOn_const.mul (hscaled c⁻¹ (inv_pos.mpr hc)))).sub
      (continuousOn_const.mul (by simpa using hscaled 1 zero_lt_one))

/-- Every finite indexed zero-mode Gaussian bank is locally integrable on positive heights. -/
theorem indexedZeroModeGaussianTheta_locallyIntegrableOn
    {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℝ)
    (hH : ∀ i, 0 < H i) {c : ℝ} (hc : 0 < c) :
    LocallyIntegrableOn (indexedZeroModeGaussianTheta a H c) (Set.Ioi 0) := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  unfold indexedZeroModeGaussianTheta indexedTheta
  simp only [tsum_fintype]
  exact continuousOn_finsetSum Finset.univ fun i _ =>
    continuousOn_const.mul ((zeroModeGaussianKernel_continuousOn hc).comp
      (continuousOn_const.mul continuousOn_id) (fun x hx => mul_pos (hH i) hx))

/-- Primal zero-mode-free Gaussian bank, defined before projection from its 3D coefficient
fibers. -/
noncomputable def indexedZeroModeGaussian3DBankReadout
    {I : Type*} (a : I → ℂ) (H : I → ℝ) (c x : ℝ) : ℂ :=
  ∑' i : I,
    fiberPhasor (indexedCoefficientFiber a H i x) *
      zeroModeGaussianKernel c
        (multiplicativeHeight (indexedCoefficientFiber a H i x))

/-- Reflected/sheared anti-helix zero-mode Gaussian bank. -/
noncomputable def indexedZeroModeGaussian3DTransformedReadout
    {I : Type*}
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I) (c x : ℝ) : ℂ :=
  ∑' i : I,
    fiberPhasor
        (indexedReciprocalCoefficientFiber
          (fun j => (starRingEnd ℂ) (gaussianPoissonDualAmplitude a H dual j)) H i x) *
      zeroModeGaussianKernel c
        (multiplicativeHeight
          (indexedReciprocalCoefficientFiber
            (fun j => (starRingEnd ℂ) (gaussianPoissonDualAmplitude a H dual j)) H i x))

/-- Projection of the primal 3D bank is the indexed zero-mode Gaussian theta. -/
theorem indexedZeroModeGaussian3DBankReadout_eq_theta
    {I : Type*} (a : I → ℂ) (H : I → ℝ)
    (hH : ∀ i, 0 < H i) (c : ℝ) {x : ℝ} (hx : 0 < x) :
    indexedZeroModeGaussian3DBankReadout a H c x =
      indexedZeroModeGaussianTheta a H c x := by
  unfold indexedZeroModeGaussian3DBankReadout indexedZeroModeGaussianTheta indexedTheta
  apply tsum_congr
  intro i
  rw [fiberPhasor_indexedCoefficientFiber,
    multiplicativeHeight_indexedCoefficientFiber a H hH i hx]

/-- Projection of the transformed 3D bank is the reciprocal external-height dual theta. -/
theorem indexedZeroModeGaussian3DTransformedReadout_eq_theta
    {I : Type*}
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (c : ℝ) {x : ℝ} (hx : 0 < x) :
    indexedZeroModeGaussian3DTransformedReadout a H dual c x =
      indexedZeroModeGaussianTheta (gaussianPoissonDualAmplitude a H dual) H c (1 / x) := by
  unfold indexedZeroModeGaussian3DTransformedReadout indexedZeroModeGaussianTheta indexedTheta
  apply tsum_congr
  intro i
  rw [fiberPhasor_indexedReciprocalCoefficientFiber_conj,
    multiplicativeHeight_indexedReciprocalCoefficientFiber _ H hH i hx]
  congr 2
  ring

/-- Exact global reflection of the zero-mode-free primal and transformed 3D banks. -/
theorem indexedZeroModeGaussian3D_globalHelixReflection
    {I : Type*}
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (hrecip : ∀ i, H (dual.symm i) = (H i)⁻¹)
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    indexedZeroModeGaussian3DBankReadout a H c x =
      ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        indexedZeroModeGaussian3DTransformedReadout a H dual c x := by
  rw [indexedZeroModeGaussian3DBankReadout_eq_theta a H hH c hx,
    indexedZeroModeGaussian3DTransformedReadout_eq_theta a H dual hH c hx]
  exact indexedZeroModeGaussianTheta_reflection a H dual hH hrecip hc hx

/-- The scalar projection of a finite zero-mode-free 3D bank and its anti-helix transform form a
strong Mellin functional-equation pair. -/
noncomputable def finiteZeroModeGaussianStrongFEPair
    {I : Type*} [Fintype I]
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (hrecip : ∀ i, H (dual.symm i) = (H i)⁻¹)
    (c : ℝ) (hc : 0 < c) : StrongFEPair ℂ where
  toWeakFEPair := {
    f := indexedZeroModeGaussianTheta a H c
    g := indexedZeroModeGaussianTheta (gaussianPoissonDualAmplitude a H dual) H c
    k := 1 / 2
    ε := 1
    f₀ := 0
    g₀ := 0
    hf_int := indexedZeroModeGaussianTheta_locallyIntegrableOn a H hH hc
    hg_int := indexedZeroModeGaussianTheta_locallyIntegrableOn
      (gaussianPoissonDualAmplitude a H dual) H hH hc
    hk := by norm_num
    hε := one_ne_zero
    h_feq := fun x hx => by
      have h := indexedZeroModeGaussianTheta_reflection a H dual hH hrecip hc
        (one_div_pos.mpr hx)
      simp only [one_div, inv_inv] at h
      have hscale : 1 / x⁻¹ ^ (1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) := by
        rw [Real.inv_rpow hx.le]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hx _)]
      rw [one_mul, smul_eq_mul]
      convert h using 1
      · simp only [one_div]
      · congr 1
        have hscaleC := congrArg (fun y : ℝ => (y : ℂ)) hscale.symm
        simpa only [one_div, ofReal_inv] using hscaleC
    hf_top := fun r => by
      simpa only [sub_zero] using indexedZeroModeGaussianTheta_rapid a H hH hc r
    hg_top := fun r => by
      simpa only [sub_zero] using indexedZeroModeGaussianTheta_rapid
        (gaussianPoissonDualAmplitude a H dual) H hH hc r
  }
  hf₀ := rfl
  hg₀ := rfl

/-- Entirety, vertical-strip boundedness, and the functional equation of every finite
zero-mode-free 3D bank. -/
theorem finiteZeroModeGaussian_twistedNiceness
    {I : Type*} [Fintype I]
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (hrecip : ∀ i, H (dual.symm i) = (H i)⁻¹)
    (c : ℝ) (hc : 0 < c) :
    let P := finiteZeroModeGaussianStrongFEPair a H dual hH hrecip c hc
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  dsimp only
  let P := finiteZeroModeGaussianStrongFEPair a H dual hH hrecip c hc
  exact ⟨P.differentiable_Λ, P.symm.differentiable_Λ,
    fun u v => CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
      P u v,
    fun u v => CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
      P.symm u v,
    P.functional_equation⟩

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.zeroModeGaussianKernel_reflection
#print axioms CriticalLinePhasor.GlobalHelix.zeroModeGaussianKernel_rapid
#print axioms CriticalLinePhasor.GlobalHelix.indexedZeroModeGaussianTheta_rapid
#print axioms CriticalLinePhasor.GlobalHelix.indexedZeroModeGaussianTheta_reflection
#print axioms CriticalLinePhasor.GlobalHelix.indexedZeroModeGaussian3D_globalHelixReflection
#print axioms CriticalLinePhasor.GlobalHelix.finiteZeroModeGaussianStrongFEPair
#print axioms CriticalLinePhasor.GlobalHelix.finiteZeroModeGaussian_twistedNiceness
