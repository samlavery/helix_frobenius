import RequestProject.RSPoleStructure
import RequestProject.GDecay
import RequestProject.RSDecay
import RequestProject.HolomorphicUnderIntegral

/-!
# Closing gap (i): holomorphy of the entire-part Petersson integral

`RSPoleStructure` isolates two classical inputs needed to turn the compiled pole-split into the
summatory bound.  The first — **(i) holomorphy of `s ↦ ∫_𝒟 P·Λ₀_z(s) dμ`** — was named there as
"not in Mathlib".  It is discharged here, unconditionally, at the standard axiom footprint.

The analytic core (differentiation under the integral from a locally-uniform integrable bound on
`F` alone, with no derivative bound) is `HolomorphicUnderIntegral.differentiableAt_integral_of_dominated_holo`.
The two data it consumes are supplied here:

* **the dominating bound is integrable** — `‖P(z)·Λ₀_z(s)‖ ≤ P(z)·‖Λ₀_z(s)‖` is dominated,
  uniformly for `s` in any ball, by `C·e^{-2πy}·lambdaC N·(1+y²)·y^N` (`P_exp_decay_on_fd`
  times `lambda0_bound_on_fd`, choosing the strip parameter `N` a natural number `≥` the ball).
  Taking `N ∈ ℕ`, `(1+y²)·y^N·e^{-2πy} ≤ 3·N!` for every `y>0` (`pow_le_factorial_mul_exp`,
  the exponential beating every power), so the dominant is a constant on `𝒟` and integrable
  (`integrableOn_fd_of_bounded`);
* **the integrand is `z`-measurable** — `z ↦ Λ₀_z(s)` is `AEStronglyMeasurable` because the bank
  `latticeTheta z t = ∑'_p e^{-πt·gram(z,p)}` is a countable sum of **nonnegative** jointly
  continuous terms, hence jointly measurable via the `ℝ≥0∞`-`tsum` (`measurable_latticeTheta`);
  the modification `f_modif` and its Mellin transform `Λ₀ = mellin f_modif` inherit measurability
  through the parametric-integral measurability `AEStronglyMeasurable.integral_prod_right'`.

No RH/GRH.  No `axiom`, no `sorry`.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Set Filter Topology
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- The Gram form is continuous in the point (numerator polynomial over the positive height). -/
lemma continuous_gram (p : ℤ × ℤ) : Continuous (fun z : ℍ => gram z p) := by
  rw [show (fun z : ℍ => gram z p) = fun z : ℍ =>
    (((p.1 : ℝ) * z.re + (p.2 : ℝ)) ^ 2 + (p.1 : ℝ) ^ 2 * z.im ^ 2) / z.im from rfl]
  apply Continuous.div
  · fun_prop
  · exact UpperHalfPlane.continuous_im
  · exact fun z => z.im_ne_zero

/-- **The lattice bank is jointly measurable** in the point and the height.  Each phasor
`e^{-πt·gram(z,p)}` is nonnegative and jointly continuous, so the bank is the `.toReal` of a
`ℝ≥0∞`-`tsum` of measurable terms — measurable regardless of summability (both sides collapse to
`0` off the summable locus). -/
lemma measurable_latticeTheta :
    Measurable (fun p : ℍ × ℝ => latticeTheta p.1 p.2) := by
  have key : (fun p : ℍ × ℝ => latticeTheta p.1 p.2)
      = fun p => (∑' q : ℤ × ℤ,
          ENNReal.ofReal (Real.exp (-(π * p.2) * gram p.1 q))).toReal := by
    funext p
    by_cases h : Summable (fun q : ℤ × ℤ => Real.exp (-(π * p.2) * gram p.1 q))
    · rw [latticeTheta, ← ENNReal.ofReal_tsum_of_nonneg (fun q => (Real.exp_pos _).le) h,
        ENNReal.toReal_ofReal (tsum_nonneg (fun q => (Real.exp_pos _).le))]
    · rw [latticeTheta, tsum_eq_zero_of_not_summable h]
      symm
      rw [ENNReal.toReal_eq_zero_iff]
      right
      by_contra htop
      exact h ((ENNReal.summable_toReal htop).congr
        (fun q => ENNReal.toReal_ofReal (Real.exp_pos _).le))
  rw [key]
  refine Measurable.ennreal_toReal (Measurable.ennreal_tsum (fun q => ?_))
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (((measurable_const.mul measurable_snd).neg).mul
      ((continuous_gram q).measurable.comp measurable_fst)))

/-- **The modified bank `f_modif` is jointly measurable** in the point and the Mellin variable.
The two constants of `generalFEPair` are `1`, and the `Ioo 0 1` correction `x^{-1}` is the
(unconditional) inverse `x⁻¹`; both indicators are measurable sets in the height coordinate. -/
lemma measurable_prod_f_modif :
    Measurable (fun p : ℍ × ℝ => (generalFEPair p.1).f_modif p.2) := by
  have hLT : Measurable (fun p : ℍ × ℝ => (latticeThetaC p.1 p.2 : ℂ)) :=
    Complex.measurable_ofReal.comp measurable_latticeTheta
  -- expose `f_modif` as a sum of two indicators over the height coordinate (defeq to the fields)
  have hfm : (fun p : ℍ × ℝ => (generalFEPair p.1).f_modif p.2)
      = fun p => (Ioi 1).indicator (fun x => (latticeThetaC p.1 x : ℂ) - 1) p.2
          + (Ioo 0 1).indicator (fun x => (latticeThetaC p.1 x : ℂ)
              - ((1 : ℂ) * ((x ^ (-(1 : ℝ)) : ℝ) : ℂ)) • (1 : ℂ)) p.2 := by
    funext p
    rw [WeakFEPair.f_modif]
    rfl
  rw [hfm]
  apply Measurable.add
  · -- first indicator: rewrite as a preimage-indicator of a jointly measurable function
    have e1 : (fun p : ℍ × ℝ => (Ioi 1).indicator (fun x => (latticeThetaC p.1 x : ℂ) - 1) p.2)
        = (Prod.snd ⁻¹' Ioi 1).indicator (fun p => (latticeThetaC p.1 p.2 : ℂ) - 1) := by
      funext p
      by_cases hp : p.2 ∈ Ioi 1
      · simp only [Set.indicator_of_mem hp,
          Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' Ioi 1 from hp)]
      · simp only [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' Ioi 1 from hp)]
    rw [e1]
    exact (hLT.sub measurable_const).indicator (measurableSet_Ioi.preimage measurable_snd)
  · -- second indicator: the `x^{-1}` correction is the (unconditional) inverse `x⁻¹`
    have e2 : (fun p : ℍ × ℝ => (Ioo 0 1).indicator (fun x => (latticeThetaC p.1 x : ℂ)
              - ((1 : ℂ) * ((x ^ (-(1 : ℝ)) : ℝ) : ℂ)) • (1 : ℂ)) p.2)
        = (Prod.snd ⁻¹' Ioo 0 1).indicator
            (fun p => (latticeThetaC p.1 p.2 : ℂ) - (((p.2)⁻¹ : ℝ) : ℂ)) := by
      funext p
      by_cases hp : p.2 ∈ Ioo 0 1
      · simp only [Set.indicator_of_mem hp,
          Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' Ioo 0 1 from hp),
          one_mul, smul_eq_mul, mul_one, Real.rpow_neg_one]
      · simp only [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' Ioo 0 1 from hp)]
    rw [e2]
    refine Measurable.indicator ?_ (measurableSet_Ioo.preimage measurable_snd)
    exact hLT.sub (Complex.measurable_ofReal.comp (measurable_inv.comp measurable_snd))

/-- **The entire completion `Λ₀_z(s)` is `z`-measurable.**  `Λ₀_z = mellin f_modif_z`, and the
Mellin integrand `(z,t) ↦ t^{s-1}·f_modif_z(t)` is jointly measurable (`measurable_prod_f_modif`
for the bank, `ContinuousOn`-on-`Ioi 0` for the `cpow`), so the parametric integral in `z` is
`AEStronglyMeasurable` (`integral_prod_right'`). -/
lemma aestronglyMeasurable_Lambda0 (s : ℂ) :
    AEStronglyMeasurable (fun z : ℍ => (generalFEPair z).Λ₀ s) volume := by
  have hc : AEStronglyMeasurable (fun t : ℝ => ((t : ℝ) : ℂ) ^ (s - 1))
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact continuousOn_of_forall_continuousAt fun t ht =>
      continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt ht)
  have hcpow : AEStronglyMeasurable (fun p : ℍ × ℝ => ((p.2 : ℝ) : ℂ) ^ (s - 1))
      (volume.prod (volume.restrict (Ioi 0))) := hc.comp_snd
  have hint : AEStronglyMeasurable
      (fun p : ℍ × ℝ => ((p.2 : ℝ) : ℂ) ^ (s - 1) • (generalFEPair p.1).f_modif p.2)
      (volume.prod (volume.restrict (Ioi 0))) :=
    hcpow.smul measurable_prod_f_modif.aestronglyMeasurable
  have hmel : (fun z : ℍ => (generalFEPair z).Λ₀ s)
      = fun z => ∫ t, ((t : ℝ) : ℂ) ^ (s - 1) • (generalFEPair z).f_modif t
          ∂(volume.restrict (Ioi 0)) := by
    funext z
    rw [WeakFEPair.Λ₀, mellin]
  rw [hmel]
  exact hint.integral_prod_right'

/-- **Gap (i), closed.**  For every cusp form, the entire-part Petersson pairing
`s ↦ ∫_𝒟 P(z)·Λ₀_z(s) dμ` is holomorphic on all of `ℂ`.  This is the input `RSPoleStructure`
named "(i) holomorphy of `s ↦ ∫_𝒟 P·Λ₀_z(s) dμ`" and flagged "not in Mathlib".  No RH/GRH. -/
theorem rs_entirePart_differentiable (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    Differentiable ℂ (fun s => ∫ z in ModularGroup.fd,
      ((P k f z : ℝ) : ℂ) * (generalFEPair z).Λ₀ s ∂volume) := by
  obtain ⟨C, hC0, hC⟩ := P_exp_decay_on_fd f hk
  intro s₀
  obtain ⟨Nnat, hN1, hNa, hNb⟩ :
      ∃ n : ℕ, 1 ≤ n ∧ s₀.re + 1 ≤ (n : ℝ) ∧ 2 - s₀.re ≤ (n : ℝ) := by
    refine ⟨⌈s₀.re + 1⌉₊ + ⌈2 - s₀.re⌉₊ + 1, by omega, ?_, ?_⟩
    · push_cast
      linarith [Nat.le_ceil (s₀.re + 1), Nat.cast_nonneg (α := ℝ) ⌈2 - s₀.re⌉₊]
    · push_cast
      linarith [Nat.le_ceil (2 - s₀.re), Nat.cast_nonneg (α := ℝ) ⌈s₀.re + 1⌉₊]
  set N : ℝ := (Nnat : ℝ) with hN
  have hNpos : (0 : ℝ) < N := by rw [hN]; exact_mod_cast Nat.lt_of_lt_of_le zero_lt_one hN1
  -- the dominating bound
  set bound : ℍ → ℝ := fun z =>
    (C * Real.exp (-(2 * π) * z.im)) * (lambdaC N * ((1 + z.im ^ 2) * z.im ^ N)) with hbound
  set F : ℂ → ℍ → ℂ := fun s z => ((P k f z : ℝ) : ℂ) * (generalFEPair z).Λ₀ s with hF
  -- (a) measurability of the integrand
  have hFmeas : ∀ s ∈ Metric.ball s₀ 1,
      AEStronglyMeasurable (F s) (volume.restrict ModularGroup.fd) := by
    intro s _
    refine AEStronglyMeasurable.mul ?_ ((aestronglyMeasurable_Lambda0 s).restrict)
    exact (Complex.continuous_ofReal.comp (continuous_P f)).aestronglyMeasurable
  -- (b) pointwise holomorphy (the completion is entire)
  have hFholo : ∀ᵐ z ∂(volume.restrict ModularGroup.fd),
      DifferentiableOn ℂ (fun s => F s z) (Metric.ball s₀ 1) := by
    refine ae_of_all _ (fun z => ?_)
    exact (((generalFEPair z).differentiable_Λ₀).const_mul ((P k f z : ℝ) : ℂ)).differentiableOn
  -- (c) the uniform domination
  have hFbound : ∀ᵐ z ∂(volume.restrict ModularGroup.fd),
      ∀ s ∈ Metric.ball s₀ 1, ‖F s z‖ ≤ bound z := by
    refine (ae_restrict_mem measurableSet_fd).mono (fun z hz => ?_)
    intro s hs
    have hdist : |s.re - s₀.re| < 1 := by
      have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h1
      have h2 : ‖s - s₀‖ < 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hs
      linarith
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hdist
    have hs1 : s.re ≤ N := by linarith
    have hs2 : (1 - s).re ≤ N := by rw [Complex.sub_re, Complex.one_re]; linarith
    rw [hF]
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (P_nonneg f z)]
    exact mul_le_mul (hC z hz) (lambda0_bound_on_fd hz hNpos hs1 hs2) (norm_nonneg _)
      (mul_nonneg hC0 (Real.exp_pos _).le)
  -- (d) integrability of the dominant (constant on 𝒟)
  have hbound_int : Integrable bound (volume.restrict ModularGroup.fd) := by
    have him : Continuous (fun z : ℍ => z.im) := UpperHalfPlane.continuous_im
    have hcont : Continuous bound := by
      rw [hbound]
      have hrpow : Continuous (fun z : ℍ => z.im ^ N) :=
        him.rpow_const (fun z => Or.inl z.im_ne_zero)
      have hexp : Continuous (fun z : ℍ => Real.exp (-(2 * π) * z.im)) :=
        Real.continuous_exp.comp (continuous_const.mul him)
      exact (continuous_const.mul hexp).mul
        (continuous_const.mul ((continuous_const.add (him.pow 2)).mul hrpow))
    refine integrableOn_fd_of_bounded hcont
      (C := C * lambdaC N * (3 * (Nnat.factorial : ℝ))) (fun z _ => ?_)
    have hy : 0 < z.im := z.im_pos
    have hy0 : 0 ≤ z.im := hy.le
    have hbnn : 0 ≤ bound z :=
      mul_nonneg (mul_nonneg hC0 (Real.exp_pos _).le)
        (mul_nonneg (lambdaC_nonneg hNpos)
          (mul_nonneg (by positivity) (Real.rpow_nonneg hy0 N)))
    rw [Real.norm_of_nonneg hbnn]
    show (C * Real.exp (-(2 * π) * z.im)) * (lambdaC N * ((1 + z.im ^ 2) * z.im ^ N))
        ≤ C * lambdaC N * (3 * (Nnat.factorial : ℝ))
    have hyN : z.im ^ N = z.im ^ Nnat := by rw [hN, Real.rpow_natCast]
    rw [hyN]
    set y := z.im with hy_def
    have e1 : (1 + y ^ 2) ≤ 3 * Real.exp y := by
      have h2 := pow_le_factorial_mul_exp hy0 2
      have h1 : (1 : ℝ) ≤ Real.exp y := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hy0
      have hfac2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num [Nat.factorial]
      rw [hfac2] at h2
      nlinarith [Real.exp_pos y]
    have e2 : y ^ Nnat ≤ (Nnat.factorial : ℝ) * Real.exp y := pow_le_factorial_mul_exp hy0 Nnat
    have hexp1 : Real.exp y * Real.exp y * Real.exp (-(2 * π) * y) ≤ 1 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, hy])
    have step : (1 + y ^ 2) * y ^ Nnat ≤ (3 * Real.exp y) * ((Nnat.factorial : ℝ) * Real.exp y) :=
      mul_le_mul e1 e2 (by positivity) (by positivity)
    calc (C * Real.exp (-(2 * π) * y)) * (lambdaC N * ((1 + y ^ 2) * y ^ Nnat))
        = C * lambdaC N * ((1 + y ^ 2) * y ^ Nnat * Real.exp (-(2 * π) * y)) := by ring
      _ ≤ C * lambdaC N *
            ((3 * Real.exp y) * ((Nnat.factorial : ℝ) * Real.exp y) * Real.exp (-(2 * π) * y)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 (lambdaC_nonneg hNpos))
          exact mul_le_mul_of_nonneg_right step (Real.exp_pos _).le
      _ = C * lambdaC N *
            (3 * (Nnat.factorial : ℝ) * (Real.exp y * Real.exp y * Real.exp (-(2 * π) * y))) := by
          ring
      _ ≤ C * lambdaC N * (3 * (Nnat.factorial : ℝ) * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 (lambdaC_nonneg hNpos))
          exact mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ = C * lambdaC N * (3 * (Nnat.factorial : ℝ)) := by ring
  -- assemble the general holomorphy-under-integral lemma
  exact differentiableAt_integral_of_dominated_holo F bound one_pos hFmeas hFholo hFbound hbound_int

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.measurable_latticeTheta
#print axioms CriticalLinePhasor.Unfolding.aestronglyMeasurable_Lambda0
#print axioms CriticalLinePhasor.Unfolding.rs_entirePart_differentiable
