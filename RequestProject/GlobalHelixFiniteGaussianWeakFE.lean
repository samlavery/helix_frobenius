import RequestProject.GlobalHelixGaussianThetaBounds
import RequestProject.GlobalHelixGaussianPoissonLift
import RequestProject.RepresentationRankGap
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven

/-!
# Raw finite 3D Gaussian banks as weak functional-equation pairs

The zero Fourier mode is retained as the constant term of a `WeakFEPair`.  The remaining Gaussian
modes decay rapidly.  Thus an arbitrary finite coefficient bank and its reciprocal-height Poisson
transport form a Mellin functional-equation pair without altering either coefficient bank by an
external envelope.
-/

open Real Complex Filter Asymptotics MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

/-- The Gaussian lattice clock is Mathlib's zero-shift even Hurwitz kernel. -/
theorem gaussianLatticeTheta_eq_evenKernel {x : ℝ} (hx : 0 < x) :
    gaussianLatticeTheta x = HurwitzZeta.evenKernel 0 x := by
  unfold gaussianLatticeTheta
  calc
    (∑' n : ℤ, Real.exp (-Real.pi * x * (n : ℝ) ^ 2)) =
        ∑' n : ℤ, Real.exp (-Real.pi * ((n : ℝ) + 0) ^ 2 * x) := by
      apply tsum_congr
      intro n
      congr 1
      ring
    _ = HurwitzZeta.evenKernel 0 x :=
      (HurwitzZeta.hasSum_int_evenKernel 0 hx).tsum_eq

/-- After removing its zero Fourier mode, the Gaussian lattice clock decays faster than every
real power. -/
theorem gaussianLatticeTheta_sub_one_rapid (r : ℝ) :
    (fun x : ℝ => (gaussianLatticeTheta x : ℂ) - 1) =O[atTop]
      (fun x : ℝ => x ^ r) := by
  have h := (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).hf_top r
  refine h.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, if_pos]
  rw [gaussianLatticeTheta_eq_evenKernel hx]

/-- Positive rescaling preserves rapid decay of the nonzero Gaussian modes. -/
theorem gaussianLatticeTheta_mul_sub_one_rapid {H : ℝ} (hH : 0 < H) (r : ℝ) :
    (fun x : ℝ => (gaussianLatticeTheta (H * x) : ℂ) - 1) =O[atTop]
      (fun x : ℝ => x ^ r) := by
  have hcomp := (gaussianLatticeTheta_sub_one_rapid r).comp_tendsto
    (tendsto_id.const_mul_atTop hH)
  refine hcomp.trans ?_
  have hconst : (fun x : ℝ => H ^ r * x ^ r) =O[atTop] (fun x : ℝ => x ^ r) :=
    (isBigO_refl (fun x : ℝ => x ^ r) atTop).const_mul_left (H ^ r)
  refine hconst.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact (Real.mul_rpow hH.le hx).symm

/-- Every finite indexed Gaussian bank is rapidly decreasing after its total zero-mode amplitude
is removed. -/
theorem indexedGaussianTheta_sub_sum_rapid
    {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℝ)
    (hH : ∀ i, 0 < H i) (r : ℝ) :
    (fun x : ℝ =>
      indexedTheta a H (fun t => (gaussianLatticeTheta t : ℂ)) x - ∑ i, a i) =O[atTop]
      (fun x : ℝ => x ^ r) := by
  have hsum :
      (fun x : ℝ =>
        indexedTheta a H (fun t => (gaussianLatticeTheta t : ℂ)) x - ∑ i, a i) =
      (fun x : ℝ => ∑ i, a i * ((gaussianLatticeTheta (H i * x) : ℂ) - 1)) := by
    funext x
    simp only [indexedTheta, tsum_fintype, mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hsum]
  apply IsBigO.sum
  intro i _
  exact (gaussianLatticeTheta_mul_sub_one_rapid (hH i) r).const_mul_left (a i)

/-- The scalar primal projection of the raw finite 3D Gaussian bank. -/
noncomputable def finiteGaussianPrimalTheta
    {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℝ) (x : ℝ) : ℂ :=
  indexedTheta a H (fun t => (gaussianLatticeTheta t : ℂ)) x

/-- The scalar dual projection after reciprocal-height 3D Poisson transport. -/
noncomputable def finiteGaussianDualTheta
    {I : Type*} [Fintype I]
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I) (x : ℝ) : ℂ :=
  indexedTheta (gaussianPoissonDualAmplitude a H dual) H
    (fun t => (gaussianLatticeTheta t : ℂ)) x

/-- A finite raw Gaussian 3D bank and its transported anti-helix bank form a weak Mellin
functional-equation pair. -/
noncomputable def finiteGaussianWeakFEPair
    {I : Type*} [Fintype I]
    (a : I → ℂ) (H : I → ℝ) (dual : I ≃ I)
    (hH : ∀ i, 0 < H i) (hrecip : ∀ i, H (dual.symm i) = (H i)⁻¹) :
    WeakFEPair ℂ where
  f := finiteGaussianPrimalTheta a H
  g := finiteGaussianDualTheta a H dual
  k := 1 / 2
  ε := 1
  f₀ := ∑ i, a i
  g₀ := ∑ i, gaussianPoissonDualAmplitude a H dual i
  hf_int := by
    exact (indexedGaussianTheta_continuousOn a H hH).locallyIntegrableOn measurableSet_Ioi
  hg_int := by
    exact (indexedGaussianTheta_continuousOn
      (gaussianPoissonDualAmplitude a H dual) H hH).locallyIntegrableOn measurableSet_Ioi
  hk := by norm_num
  hε := one_ne_zero
  h_feq := fun x hx => by
    have h := indexedGaussianTheta_reflection a H dual hH hrecip (one_div_pos.mpr hx)
    simp only [one_div, inv_inv] at h
    have hscale : 1 / x⁻¹ ^ (1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) := by
      rw [Real.inv_rpow hx.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hx _)]
    change finiteGaussianPrimalTheta a H (1 / x) =
      ((1 : ℂ) * ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ)) • finiteGaussianDualTheta a H dual x
    unfold finiteGaussianPrimalTheta finiteGaussianDualTheta
    rw [one_mul, smul_eq_mul]
    convert h using 1
    · simp only [one_div]
    · congr 1
      have hscaleC := congrArg (fun y : ℝ => (y : ℂ)) hscale.symm
      simpa only [one_div, ofReal_inv] using hscaleC
  hf_top := fun r => by
    simpa [finiteGaussianPrimalTheta] using indexedGaussianTheta_sub_sum_rapid a H hH r
  hg_top := fun r => by
    simpa [finiteGaussianDualTheta] using indexedGaussianTheta_sub_sum_rapid
      (gaussianPoissonDualAmplitude a H dual) H hH r

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.gaussianLatticeTheta_eq_evenKernel
#print axioms CriticalLinePhasor.GlobalHelix.gaussianLatticeTheta_sub_one_rapid
#print axioms CriticalLinePhasor.GlobalHelix.gaussianLatticeTheta_mul_sub_one_rapid
#print axioms CriticalLinePhasor.GlobalHelix.indexedGaussianTheta_sub_sum_rapid
#print axioms CriticalLinePhasor.GlobalHelix.finiteGaussianWeakFEPair
