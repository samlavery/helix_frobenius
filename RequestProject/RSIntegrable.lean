import RequestProject.RSDecay

/-!
# Integrability of the Rankin–Selberg integrand

Slice five (d), second half: the one named side condition of the compiled unfolding chain is
discharged.  The RS integrand is product-integrable on the strip coordinates for `Re s > 1`
(`rsIntegrand_product_integrable`): the fibers are bounded by the compiled global Petersson
bound on a finite-measure window, and the norm-marginal is exactly the Mellin integrand of
the smoothed second moment, whose convergence follows from the two-sided bounds — `O(y^{-k})`
at the boundary (the compiled `rankin_smoothed_bound`) and exponential decay at the cusp
(the compiled `rankin_series_exp_bound`) — through Mathlib's Mellin convergence criterion.
Consequently `rs_strip_side` and `rs_strip_side_eq_dirichlet` hold with no hypothesis beyond
the half-plane.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Filter Asymptotics
open scoped Real MatrixGroups Pointwise NNReal Topology

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- The smoothed second moment, as a function of the height. -/
noncomputable def rankinR (f : CuspForm 𝒮ℒ k) (y : ℝ) : ℝ :=
  ∑' n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y))

lemma rankinR_nonneg (f : CuspForm 𝒮ℒ k) (y : ℝ) : 0 ≤ rankinR f y :=
  tsum_nonneg fun n => by positivity

/-- The smoothed second moment is continuous on the positive axis. -/
lemma continuousOn_rankinR (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    ContinuousOn (rankinR f) (Set.Ioi (0 : ℝ)) := by
  intro y₀ hy₀
  have hy₀' : (0 : ℝ) < y₀ := hy₀
  have hcont : ContinuousOn (rankinR f) (Set.Ioi (y₀ / 2)) := by
    unfold rankinR
    refine continuousOn_tsum (fun n => Continuous.continuousOn (by fun_prop))
      (summable_rankin_terms f hk (half_pos hy₀')) (fun n y hy => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hy' : y₀ / 2 ≤ y := le_of_lt hy
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4)
      Real.pi_pos.le) (Nat.cast_nonneg (α := ℝ) n)) (sub_nonneg.mpr hy')]
  exact (hcont.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

/-- Exponential decay of the smoothed second moment at the cusp, as a `IsBigO`. -/
lemma rankinR_isBigO_top (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    (rankinR f) =O[atTop] fun y => Real.exp (-(4 * π) * y) := by
  rw [isBigO_iff]
  refine ⟨Real.exp (4 * π) *
    ∑' n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * 1)), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  rw [Real.norm_of_nonneg (rankinR_nonneg f y), Real.norm_of_nonneg (Real.exp_pos _).le]
  exact rankin_series_exp_bound f hk hy

/-- Boundary growth of the smoothed second moment, as a `IsBigO`. -/
lemma rankinR_isBigO_bot (f : CuspForm 𝒮ℒ k) :
    (rankinR f) =O[𝓝[>] (0:ℝ)] fun y => y ^ (-(k : ℝ)) := by
  obtain ⟨M, hM0, hM⟩ := rankin_smoothed_bound f
  rw [isBigO_iff]
  refine ⟨M, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : (0 : ℝ) < y := hy
  rw [Real.norm_of_nonneg (rankinR_nonneg f y),
    Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _)]
  calc rankinR f y ≤ M * y ^ (-k : ℤ) := hM y hy0
    _ = M * y ^ (-(k : ℝ)) := by
        rw [← Real.rpow_intCast y (-k)]
        push_cast
        ring_nf

/-- **The Mellin integrand of the smoothed second moment is integrable** for `Re s > 1`. -/
lemma rankinR_mellin_integrable (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s + k - 1 - 1) • ((rankinR f t : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have hre : (s + (k : ℂ) - 1).re = s.re + (k : ℝ) - 1 := by simp
  have h := mellinConvergent_of_isBigO_rpow (E := ℂ) (a := s.re + k) (b := (k : ℝ))
    (f := fun t => ((rankinR f t : ℝ) : ℂ)) (s := s + k - 1)
    ?_ ?_ (by rw [hre]; linarith) ?_ (by rw [hre]; linarith)
  · exact h
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_rankinR f hk)).locallyIntegrableOn measurableSet_Ioi
  · have hO := (rankinR_isBigO_top f hk).trans
      (CriticalLinePhasor.EpsteinTheta.exp_neg_isBigO_rpow
        (a := 4 * π) (by positivity) (-(s.re + k)))
    rw [← isBigO_norm_left]
    simp only [Complex.norm_real]
    exact hO.norm_left
  · have hO := rankinR_isBigO_bot f
    rw [← isBigO_norm_left]
    simp only [Complex.norm_real]
    exact hO.norm_left

/-- The height of the coordinate point. -/
lemma im_ofComplex_coords {x y : ℝ} (hy : 0 < y) :
    (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm (x, y))).im = y := by
  have hmk : Complex.measurableEquivRealProd.symm (x, y) = (x : ℂ) + y * Complex.I := by
    rw [Complex.measurableEquivRealProd_symm_apply]
    exact Complex.mk_eq_add_mul_I x y
  have him : (0 : ℝ) < ((x : ℂ) + y * Complex.I).im := by simpa using hy
  rw [hmk, ofComplex_apply_of_im_pos him]
  simp [UpperHalfPlane.im]

/-- The RS integrand is continuous on `ℍ`. -/
lemma continuous_rsIntegrand (f : CuspForm 𝒮ℒ k) (s : ℂ) :
    Continuous (rsIntegrand f s) := by
  rw [show rsIntegrand f s = fun z : ℍ => ((P k f z : ℝ) : ℂ) * ((z.im : ℝ) : ℂ) ^ s
    from rfl]
  exact (Complex.continuous_ofReal.comp (continuous_P f)).mul
    (Continuous.cpow (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im)
      continuous_const fun z => Complex.ofReal_mem_slitPlane.mpr z.im_pos)

/-- **The RS integrand is product-integrable** on the strip coordinates for `Re s > 1` — the
side condition of the compiled unfolding chain, discharged. -/
theorem rsIntegrand_product_integrable (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 1 < s.re) :
    Integrable (fun p : ℝ × ℝ => ((p.2 ^ 2)⁻¹ : ℝ) •
        rsIntegrand f s (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm p)))
      ((volume.restrict (Set.Ico (0:ℝ) 1)).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => ((p.2 ^ 2)⁻¹ : ℝ) •
      rsIntegrand f s (UpperHalfPlane.ofComplex
        (Complex.measurableEquivRealProd.symm p))) := by
    exact Measurable.smul ((measurable_snd.pow_const 2).inv)
      ((continuous_rsIntegrand f s).measurable.comp
        (measurable_ofComplex.comp Complex.measurableEquivRealProd.symm.measurable))
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  obtain ⟨M, hM0, hM⟩ := P_bounded f
  constructor
  · -- the fibers: bounded on a finite window
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := hy
    apply Integrable.mono' (integrable_const ((y ^ 2)⁻¹ * (M * y ^ s.re)))
    · exact (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · apply Eventually.of_forall
      intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_rsIntegrand,
        im_ofComplex_coords hy0]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (hM _) (Real.rpow_nonneg hy0.le _)
  · -- the marginal: the norm of the Mellin integrand
    apply Integrable.congr (rankinR_mellin_integrable f hk hs).norm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := hy
    -- left side: the norm of the Mellin integrand
    have hL : ‖(y : ℂ) ^ (s + k - 1 - 1) • ((rankinR f y : ℝ) : ℂ)‖ =
        y ^ (s.re + k - 2) * rankinR f y := by
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real,
        Real.norm_of_nonneg (rankinR_nonneg f y)]
      congr 2
      simp
      ring
    -- right side: the fiber norm-integral
    have hnormpt : ∀ x : ℝ, ‖((y ^ 2)⁻¹ : ℝ) • rsIntegrand f s
        (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm (x, y)))‖ =
        ((y ^ 2)⁻¹ * y ^ s.re * y ^ k) *
          ‖f (⟨(x : ℂ) + y * Complex.I, by simpa using hy0⟩ : ℍ)‖ ^ 2 := by
      intro x
      have hmk : Complex.measurableEquivRealProd.symm (x, y) =
          (x : ℂ) + y * Complex.I := by
        rw [Complex.measurableEquivRealProd_symm_apply]
        exact Complex.mk_eq_add_mul_I x y
      have him : (0 : ℝ) < ((x : ℂ) + y * Complex.I).im := by simpa using hy0
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_rsIntegrand,
        hmk, ofComplex_apply_of_im_pos him, P]
      have him2 : (⟨(x : ℂ) + y * Complex.I, him⟩ : ℍ).im = y := by
        simp [UpperHalfPlane.im]
      rw [him2, Complex.normSq_eq_norm_sq]
      ring
    rw [hL,
      setIntegral_congr_fun measurableSet_Ico fun x _ => hnormpt x,
      MeasureTheory.integral_const_mul, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one, ← rankin_energy_exact f hk hy0]
    -- the scalar identity: y^{σ+k−2} = (y²)⁻¹·y^σ·y^k
    have hsc : y ^ (s.re + k - 2) = (y ^ 2)⁻¹ * y ^ s.re * y ^ k := by
      have h1 : y ^ ((k : ℝ)) = y ^ k := Real.rpow_intCast y k
      have h2 : y ^ ((-2 : ℝ)) = (y ^ 2)⁻¹ := by
        rw [show ((-2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg,
          zpow_two, pow_two]
      rw [show s.re + (k : ℝ) - 2 = s.re + ((k : ℝ) + (-2 : ℝ)) by ring,
        Real.rpow_add hy0, Real.rpow_add hy0, h1, h2]
      ring
    rw [hsc]
    unfold rankinR
    ring

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.rankinR_mellin_integrable
#print axioms CriticalLinePhasor.Unfolding.rsIntegrand_product_integrable
