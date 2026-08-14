import RequestProject.StripIntegrabilityGeneric
import RequestProject.MaassWaveBounded
import RequestProject.MaassRankinUnfolding
import RequestProject.RSIntegrable

/-!
# The Maass Rankin--Selberg unfolding, unconditional

The last analytic obligation of the `r = 2` rung: integrability of `‖u‖²(Im)^s` on the strip.

The holomorphic case (`RSIntegrable.rsIntegrand_product_integrable`) identifies the horizontal
marginal exactly, through Parseval, and then feeds the resulting Dirichlet series to Mathlib's
Mellin convergence criterion.  That is necessary there because the density `y^k‖f‖²` **blows up**
at the boundary — the two-sided estimate `O(y^{-k})` at `0` and exponential decay at the cusp is
genuinely two different regimes, and the series is what interpolates them.

For a Maass form the density is `‖u‖²` with no weight, and `maassWave_bounded` says it is
**globally bounded**.  So the boundary regime is `O(1)`, not `O(y^{-k})`, and a single elementary
majorant covers the whole ray:

  `‖u‖² ≤ (C·e^{4π} + B²y)·e^{-4πy} =: maassPMajorant C B y`

— the first summand absorbs the bounded regime `y ≤ 1` (where `e^{-4πy} ≥ e^{-4π}`), the second is
the cusp decay `maassWave_decay_above`.  The majorant is continuous, bounded at `0`, and
exponentially small at `∞`, so Mellin convergence applies to it directly and **the Fourier series
is never needed**.  That is the whole simplification: the exact Parseval evaluation
(`maass_horizontal_energy`) is what computes the Rankin--Selberg *series*, not what proves the
integral converges.

Result: `maass_rs_unfolding_unconditional`, the Rankin--Selberg unfolding for a genuine level-one
Maass cusp form on `Re s > 1`, with no side condition.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Filter Asymptotics
open scoped Real MatrixGroups Pointwise NNReal Topology

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-! ## The strip transport in coordinate form -/

/-- `integrableOn_strip_of_product` with the density written as a plain real scalar and the window
as a product measure — the shape the Fubini argument actually produces. -/
lemma integrableOn_strip_of_product_coords (G : ℍ → ℂ)
    (hInt : Integrable
      (fun p : ℝ × ℝ => ((p.2 ^ 2)⁻¹ : ℝ) •
        G (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm p)))
      ((volume.restrict (Set.Ico (0:ℝ) 1)).prod (volume.restrict (Set.Ioi (0:ℝ))))) :
    IntegrableOn G strip (volume : Measure ℍ) := by
  refine integrableOn_strip_of_product G ?_
  have hprod : ((volume : Measure (ℝ × ℝ)).restrict
      (Set.Ico (0:ℝ) 1 ×ˢ Set.Ioi (0:ℝ))) =
      ((volume.restrict (Set.Ico (0:ℝ) 1)).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hmeasT : MeasurableSet (Set.Ico (0:ℝ) 1 ×ˢ Set.Ioi (0:ℝ)) :=
    measurableSet_Ico.prod measurableSet_Ioi
  rw [← hprod] at hInt
  refine hInt.congr ?_
  filter_upwards [ae_restrict_mem hmeasT] with p hp
  obtain ⟨x, y⟩ := p
  obtain ⟨-, hy⟩ := hp
  have hy0 : (0:ℝ) < y := hy
  have him2 : (UpperHalfPlane.ofComplex
      (Complex.measurableEquivRealProd.symm (x, y))).im = y := im_ofComplex_coords hy0
  rw [NNReal.smul_def]
  congr 1
  rw [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, him2, one_div, inv_pow]

/-! ## Pointwise identities for the Maass integrand -/

lemma maassP_nonneg (M : GenuineMaassCuspForm3D) (z : ℍ) : 0 ≤ maassP M z := by
  unfold maassP; positivity

/-- The wave on `ℍ` is its coordinate realization. -/
lemma maassWave_eq_coords (M : GenuineMaassCuspForm3D) (z : ℍ) :
    maassWave M.eigenData M.radialKernel z =
      maassWaveCoordinates M.eigenData M.radialKernel (z : ℂ).re z.im := rfl

/-- The Maass RS integrand is continuous. -/
lemma continuous_maassRsIntegrand' (M : GenuineMaassCuspForm3D) (s : ℂ) :
    Continuous (maassRsIntegrand M s) := continuous_maassRsIntegrand M s

lemma norm_maassRsIntegrand (M : GenuineMaassCuspForm3D) (s : ℂ) (z : ℍ) :
    ‖maassRsIntegrand M s z‖ = maassP M z * z.im ^ s.re := by
  rw [maassRsIntegrand, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (maassP_nonneg M z),
    Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos]

/-! ## The global majorant -/

/-- The elementary majorant of the Petersson density: bounded regime plus cusp decay, valid on the
whole positive ray. -/
noncomputable def maassPMajorant (C B : ℝ) (y : ℝ) : ℝ :=
  (C * Real.exp (4 * Real.pi) + B ^ 2 * y) * Real.exp (-(4 * Real.pi * y))

lemma maassPMajorant_nonneg {C B : ℝ} (hC : 0 ≤ C) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ maassPMajorant C B y := by
  unfold maassPMajorant; positivity

/-- **The Petersson density of a Maass form is dominated by the elementary majorant everywhere.**
Below height one the global bound `maassWave_bounded` does the work; above it, the cusp decay. -/
theorem maassP_le_majorant (M : GenuineMaassCuspForm3D) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ z : ℍ, maassP M z ≤ maassPMajorant C B z.im := by
  obtain ⟨C, hC0, hCb⟩ := maassP_bounded M
  obtain ⟨B, hB0, hBb⟩ := maassWave_decay_above M (a := 1) one_pos
  refine ⟨C, B, hC0, hB0, fun z => ?_⟩
  have hy0 : (0:ℝ) < z.im := z.im_pos
  have hexp : (0:ℝ) < Real.exp (-(4 * Real.pi * z.im)) := Real.exp_pos _
  rcases le_or_gt 1 z.im with hz | hz
  · -- cusp regime: square the decay bound
    have hb := hBb (z : ℂ).re z.im hz
    rw [← maassWave_eq_coords M z] at hb
    have hsq : maassP M z ≤ (B * Real.sqrt z.im * Real.exp (-(2 * Real.pi * z.im))) ^ 2 := by
      unfold maassP
      exact pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hval : (B * Real.sqrt z.im * Real.exp (-(2 * Real.pi * z.im))) ^ 2 =
        B ^ 2 * z.im * Real.exp (-(4 * Real.pi * z.im)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hy0.le, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    rw [hval] at hsq
    refine le_trans hsq ?_
    unfold maassPMajorant
    have : (0:ℝ) ≤ C * Real.exp (4 * Real.pi) := by positivity
    nlinarith
  · -- bounded regime: the first summand alone dominates
    refine le_trans (hCb z) ?_
    unfold maassPMajorant
    have hge : Real.exp (-(4 * Real.pi)) ≤ Real.exp (-(4 * Real.pi * z.im)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    have hkey : C = C * Real.exp (4 * Real.pi) * Real.exp (-(4 * Real.pi)) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
      rw [Real.exp_zero, mul_one]
    have hB2 : (0:ℝ) ≤ B ^ 2 * z.im := by positivity
    nlinarith [mul_nonneg hC0 (Real.exp_pos (4 * Real.pi)).le]

/-- **Mellin convergence of the majorant.**  It is continuous, `O(1)` at the boundary and
exponentially small at the cusp, so the criterion applies on `Re s > 1` with no series. -/
theorem maassPMajorant_mellin_integrable {C B : ℝ} (hC : 0 ≤ C) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => t ^ (s.re - 2) * maassPMajorant C B t) (Set.Ioi (0:ℝ)) := by
  set K : ℝ := C * Real.exp (4 * Real.pi) with hK
  have hK0 : (0:ℝ) ≤ K := by positivity
  have hcont : Continuous (maassPMajorant C B) := by
    unfold maassPMajorant; fun_prop
  have hre1 : (s - 1).re = s.re - 1 := by simp
  have hpi : (0:ℝ) < 4 * Real.pi - 1 := by nlinarith [Real.pi_gt_three]
  have hmel := mellinConvergent_of_isBigO_rpow (E := ℂ) (a := s.re) (b := (0:ℝ))
    (f := fun t : ℝ => ((maassPMajorant C B t : ℝ) : ℂ)) (s := s - 1)
    ?_ ?_ (by rw [hre1]; linarith) ?_ (by rw [hre1]; linarith)
  · -- transport the Mellin integrand to the real form
    refine (hmel.norm).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
      Real.norm_of_nonneg (maassPMajorant_nonneg hC ht0.le)]
    congr 2
    simp only [Complex.sub_re, Complex.one_re]
    ring
  · exact (Complex.continuous_ofReal.comp hcont).continuousOn.locallyIntegrableOn
      measurableSet_Ioi
  · -- cusp end: exponentially small, hence smaller than any power
    have hOexp : (fun t : ℝ => ((maassPMajorant C B t : ℝ) : ℂ)) =O[atTop]
        (fun t : ℝ => Real.exp (-(4 * Real.pi - 1) * t)) := by
      rw [isBigO_iff]
      refine ⟨K + B ^ 2, ?_⟩
      filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      have ht0 : (0:ℝ) < t := lt_of_lt_of_le one_pos ht
      rw [Complex.norm_real, Real.norm_of_nonneg (maassPMajorant_nonneg hC ht0.le),
        Real.norm_of_nonneg (Real.exp_pos _).le]
      have het : t ≤ Real.exp t := le_trans (by linarith) (Real.add_one_le_exp t)
      have he1 : (1:ℝ) ≤ Real.exp t := le_trans ht het
      have h1 : K + B ^ 2 * t ≤ (K + B ^ 2) * Real.exp t := by nlinarith [sq_nonneg B]
      calc maassPMajorant C B t
          = (K + B ^ 2 * t) * Real.exp (-(4 * Real.pi * t)) := rfl
        _ ≤ ((K + B ^ 2) * Real.exp t) * Real.exp (-(4 * Real.pi * t)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = (K + B ^ 2) * Real.exp (-(4 * Real.pi - 1) * t) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            ring
    exact hOexp.trans
      (CriticalLinePhasor.EpsteinTheta.exp_neg_isBigO_rpow hpi (-s.re))
  · -- boundary end: bounded
    rw [isBigO_iff]
    refine ⟨K + B ^ 2, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    rw [Complex.norm_real, Real.norm_of_nonneg (maassPMajorant_nonneg hC ht0.le)]
    have hle1 : Real.exp (-(4 * Real.pi * t)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [Real.pi_pos]
    have hnn : (0:ℝ) ≤ K + B ^ 2 * t := by positivity
    have : maassPMajorant C B t ≤ K + B ^ 2 * t := by
      unfold maassPMajorant
      nlinarith
    have hstep : K + B ^ 2 * t ≤ K + B ^ 2 := by nlinarith [sq_nonneg B]
    simpa using le_trans this hstep

/-! ## The Fubini assembly -/

/-- **The Maass RS integrand is product-integrable on the strip coordinates** for `Re s > 1`. -/
theorem maassRsIntegrand_product_integrable (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : 1 < s.re) :
    Integrable (fun p : ℝ × ℝ => ((p.2 ^ 2)⁻¹ : ℝ) •
        maassRsIntegrand M s
          (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm p)))
      ((volume.restrict (Set.Ico (0:ℝ) 1)).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
  obtain ⟨C, B, hC0, hB0, hmaj⟩ := maassP_le_majorant M
  obtain ⟨Cb, hCb0, hCb⟩ := maassP_bounded M
  have hmeas : Measurable (fun p : ℝ × ℝ => ((p.2 ^ 2)⁻¹ : ℝ) •
      maassRsIntegrand M s (UpperHalfPlane.ofComplex
        (Complex.measurableEquivRealProd.symm p))) :=
    Measurable.smul ((measurable_snd.pow_const 2).inv)
      ((continuous_maassRsIntegrand' M s).measurable.comp
        (measurable_ofComplex.comp Complex.measurableEquivRealProd.symm.measurable))
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · -- fibers: bounded on a window of finite measure
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0:ℝ) < y := hy
    apply Integrable.mono' (integrable_const ((y ^ 2)⁻¹ * (Cb * y ^ s.re)))
    · exact (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        norm_maassRsIntegrand, im_ofComplex_coords hy0]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hCb _) (Real.rpow_nonneg hy0.le _)) (by positivity)
  · -- marginal: dominated by the majorant, which is Mellin-integrable
    apply Integrable.mono' (maassPMajorant_mellin_integrable (C := C) (B := B) hC0 hs)
    · exact ((hmeas.stronglyMeasurable).norm.integral_prod_left').aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : (0:ℝ) < y := hy
      have hptw : ∀ x : ℝ, ‖((y ^ 2)⁻¹ : ℝ) • maassRsIntegrand M s
          (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm (x, y)))‖ ≤
          (y ^ 2)⁻¹ * (maassPMajorant C B y * y ^ s.re) := by
        intro x
        have hz := hmaj (UpperHalfPlane.ofComplex
          (Complex.measurableEquivRealProd.symm (x, y)))
        rw [im_ofComplex_coords hy0] at hz
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          norm_maassRsIntegrand, im_ofComplex_coords hy0]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hz (Real.rpow_nonneg hy0.le _)) (by positivity)
      have hle := integral_mono_of_nonneg
        (Eventually.of_forall fun x => norm_nonneg
          (((y ^ 2)⁻¹ : ℝ) • maassRsIntegrand M s
            (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm (x, y)))))
        (integrable_const ((y ^ 2)⁻¹ * (maassPMajorant C B y * y ^ s.re))
          (μ := volume.restrict (Set.Ico (0:ℝ) 1)))
        (Eventually.of_forall hptw)
      have hconst : ∫ _x : ℝ, ((y ^ 2)⁻¹ * (maassPMajorant C B y * y ^ s.re))
          ∂(volume.restrict (Set.Ico (0:ℝ) 1)) =
          (y ^ 2)⁻¹ * (maassPMajorant C B y * y ^ s.re) := by
        rw [integral_const]
        simp [MeasureTheory.measureReal_def, Measure.restrict_apply_univ, Real.volume_Ico]
      have hsc : (y ^ 2)⁻¹ * (maassPMajorant C B y * y ^ s.re) =
          y ^ (s.re - 2) * maassPMajorant C B y := by
        have h2 : y ^ ((-2 : ℝ)) = (y ^ 2)⁻¹ := by
          rw [show ((-2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg,
            zpow_two, pow_two]
        rw [show s.re - 2 = s.re + (-2 : ℝ) by ring, Real.rpow_add hy0, ← h2]
        ring
      rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _), ← hsc, ← hconst]
      exact hle

/-- **The strip integrability, discharged.** -/
theorem maassRsIntegrand_integrableOn_strip (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (maassRsIntegrand M s) strip (volume : Measure ℍ) :=
  integrableOn_strip_of_product_coords _ (maassRsIntegrand_product_integrable M hs)

/-- **The Rankin--Selberg unfolding for a genuine level-one Maass cusp form, unconditional.**
No side condition beyond the half-plane. -/
theorem maass_rs_unfolding_unconditional (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : 1 < s.re) :
    ∫ z in strip, maassRsIntegrand M s z ∂(volume : Measure ℍ) =
      ∑' q : CosetQ, ∫ z in ModularGroup.fd,
        (maassP M z : ℂ) * (((rep q • z).im : ℝ) : ℂ) ^ s ∂(volume : Measure ℍ) :=
  maass_rs_unfolding_of_strip M s (maassRsIntegrand_integrableOn_strip M hs)

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maassP_le_majorant
#print axioms CriticalLinePhasor.Unfolding.maassPMajorant_mellin_integrable
#print axioms CriticalLinePhasor.Unfolding.maassRsIntegrand_product_integrable
#print axioms CriticalLinePhasor.Unfolding.maassRsIntegrand_integrableOn_strip
#print axioms CriticalLinePhasor.Unfolding.maass_rs_unfolding_unconditional
