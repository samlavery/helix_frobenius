import c3b6_A8

/-!
# C3 batch 6, block A9 — obligation B, part 4: the sum/integral interchange, discharged

The last uncompiled step of obligation B.  Mathlib's
`MeasureTheory.integral_tsum_of_summable_integral_norm` needs exactly two things:

* every cross term is integrable in `p` (`crossTerm_integrable`);
* the family of `L¹` norms is summable (`summable_crossTerm_integral_norm`).

Both are supplied here from the *same* majorant `modeBound` that block A6 proved summable,
so the interchange is discharged by an explicit summable majorant and nothing else.

The `L¹` bound is sharp in form:

  `∫_ℝ |Φ_n(u+p)Φ_m(u−p)cos(2xp)| dp ≤ modeBound x u (n,m)`,

because the change of variables `w = 2p + λ` contributes `1/2`, evenness of the
`cosh`-moments contributes `2`, and the two cancel exactly.

Result (`C_tsum`):

  `∫_ℝ Φ(u+p)Φ(u−p)cos(2xp) dp
     = 16 · Σ_{(n,m)} π²a²b²e^{5u}·cos(x log(a/b))·radial(A_{nm}(u))`,

the complete theta double-sum representation of the cell density, every cross term
retained, every constant exact, and the interchange proved rather than assumed.

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B6.Theta

open C3B6.Bessel
open CriticalLinePhasor.ThetaWronskianSuzukiGram

/-! ### 1. The `cosh`-moments -/

/-- `∫_{w>0} cosh^j w · e^{−A cosh w} dw`. -/
def coshMoment (j : ℕ) (A : ℝ) : ℝ :=
  ∫ w in Ioi (0 : ℝ), Real.cosh w ^ j * Real.exp (-(A * Real.cosh w))

theorem coshMomentFun_continuous (j : ℕ) (A : ℝ) :
    Continuous (fun w : ℝ => Real.cosh w ^ j * Real.exp (-(A * Real.cosh w))) :=
  (Real.continuous_cosh.pow j).mul
    (Real.continuous_exp.comp (continuous_const.mul Real.continuous_cosh).neg)

theorem coshMomentFun_integrableOn (j : ℕ) {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun w : ℝ => Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)))
      (Ioi (0 : ℝ)) := by
  refine integrableOn_of_bound (coshMomentFun_continuous j A) (coshMaj_integrableOn j hA) ?_
  intro w hw
  have hnn : (0 : ℝ) ≤ Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) := by
    have hc : (0 : ℝ) < Real.cosh w := lt_of_lt_of_le one_pos (one_le_cosh w)
    positivity
  rw [abs_of_nonneg hnn]
  exact cosh_pow_exp_le hA le_rfl (le_of_lt hw)

theorem coshMomentFun_integrable (j : ℕ) {A : ℝ} (hA : 0 < A) :
    Integrable (fun w : ℝ => Real.cosh w ^ j * Real.exp (-(A * Real.cosh w))) := by
  refine Integrable.mono (coshMajTwo_integrable j hA)
    (coshMomentFun_continuous j A).aestronglyMeasurable ?_
  filter_upwards with w
  have hc : (0 : ℝ) < Real.cosh w := lt_of_lt_of_le one_pos (one_le_cosh w)
  have hnn : (0 : ℝ) ≤ Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) := by positivity
  have hb := cosh_pow_exp_le_two (j := j) (A := A) (δ := A) (w := w) hA (le_refl A)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
    abs_of_nonneg (le_trans hnn hb)]
  exact hb

/-- The `cosh`-moment is bounded by the block-A1 constant with the same exponential rate. -/
theorem coshMoment_le (j : ℕ) {A δ : ℝ} (hδ : 0 < δ) (hA : δ ≤ A) :
    coshMoment j A ≤ Real.exp (-(A - δ)) * kixConst j δ := by
  have hA0 : 0 < A := lt_of_lt_of_le hδ hA
  have hbnd : IntegrableOn (fun w => Real.exp (-(A - δ)) * coshMaj j δ w) (Ioi (0 : ℝ)) :=
    (coshMaj_integrableOn j hδ).const_mul _
  have hpt : ∀ w ∈ Ioi (0 : ℝ),
      Real.cosh w ^ j * Real.exp (-(A * Real.cosh w))
        ≤ Real.exp (-(A - δ)) * coshMaj j δ w := by
    intro w hw
    have hw0 : (0 : ℝ) ≤ w := le_of_lt hw
    have hc1 : (1 : ℝ) ≤ Real.cosh w := one_le_cosh w
    have hcpos : (0 : ℝ) < Real.cosh w := lt_of_lt_of_le one_pos hc1
    have hsplit : Real.exp (-(A * Real.cosh w))
        = Real.exp (-((A - δ) * Real.cosh w)) * Real.exp (-(δ * Real.cosh w)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hfac : Real.exp (-((A - δ) * Real.cosh w)) ≤ Real.exp (-(A - δ)) := by
      refine Real.exp_le_exp.mpr ?_
      have hAd : (0 : ℝ) ≤ A - δ := by linarith
      nlinarith
    have hbase : Real.cosh w ^ j * Real.exp (-(δ * Real.cosh w)) ≤ coshMaj j δ w :=
      cosh_pow_exp_le hδ le_rfl hw0
    rw [hsplit]
    calc Real.cosh w ^ j *
          (Real.exp (-((A - δ) * Real.cosh w)) * Real.exp (-(δ * Real.cosh w)))
        = Real.exp (-((A - δ) * Real.cosh w)) *
            (Real.cosh w ^ j * Real.exp (-(δ * Real.cosh w))) := by ring
      _ ≤ Real.exp (-(A - δ)) * (Real.cosh w ^ j * Real.exp (-(δ * Real.cosh w))) := by
          refine mul_le_mul_of_nonneg_right hfac ?_
          positivity
      _ ≤ Real.exp (-(A - δ)) * coshMaj j δ w :=
          mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
  calc coshMoment j A
      ≤ ∫ w in Ioi (0 : ℝ), Real.exp (-(A - δ)) * coshMaj j δ w :=
        setIntegral_mono_on (coshMomentFun_integrableOn j hA0) hbnd measurableSet_Ioi hpt
    _ = Real.exp (-(A - δ)) * kixConst j δ := by rw [kixConst, integral_const_mul]

/-- The full-line `cosh`-moment is twice the half-line one. -/
theorem coshMoment_full (j : ℕ) {A : ℝ} (hA : 0 < A) :
    (∫ w : ℝ, Real.cosh w ^ j * Real.exp (-(A * Real.cosh w))) = 2 * coshMoment j A := by
  have hint := coshMomentFun_integrable j hA
  have hsym : (∫ w in Iic (0 : ℝ), Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)))
      = ∫ w in Ioi (0 : ℝ), Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) := by
    have hneg := integral_comp_neg_Iic (0 : ℝ)
      (fun w : ℝ => Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)))
    rw [neg_zero] at hneg
    rw [← hneg]
    refine setIntegral_congr_fun measurableSet_Iic fun w _ => ?_
    rw [Real.cosh_neg]
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (f := fun w : ℝ => Real.cosh w ^ j * Real.exp (-(A * Real.cosh w))) (b := (0 : ℝ))
    hint.integrableOn hint.integrableOn
  rw [hsym] at hsplit
  rw [← hsplit, coshMoment]
  ring

/-! ### 2. Bounds on the shifted Macdonald integrands -/

theorem kixTermShift_abs_le_cosh (j : ℕ) (x A lam w : ℝ) :
    |kixTermShift j x A lam w| ≤ Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) := by
  have hcos : |Real.cos (x * (w - lam))| ≤ 1 := Real.abs_cos_le_one _
  have hc0 : (0 : ℝ) < Real.cosh w := lt_of_lt_of_le one_pos (one_le_cosh w)
  unfold kixTermShift
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg hc0.le,
    abs_of_nonneg (Real.exp_pos _).le]
  calc Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) * |Real.cos (x * (w - lam))|
      ≤ Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) * 1 :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
    _ = Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) := by ring

theorem modeIntegrandW_abs_le (n m : ℕ) (x u w : ℝ) :
    |modeIntegrandW n m x u w|
      ≤ (modeA n m u ^ 2 + 9) * (Real.cosh w ^ 0 * Real.exp (-(modeA n m u * Real.cosh w)))
        + 6 * modeA n m u
          * (Real.cosh w ^ 1 * Real.exp (-(modeA n m u * Real.cosh w))) := by
  have hA : 0 < modeA n m u := modeA_pos n m u
  unfold modeIntegrandW
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ modeA n m u ^ 2 + 9),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 6 * modeA n m u)]
  have h0 := kixTermShift_abs_le_cosh 0 x (modeA n m u) (modeLam n m) w
  have h1 := kixTermShift_abs_le_cosh 1 x (modeA n m u) (modeLam n m) w
  have hb0 : (modeA n m u ^ 2 + 9) * |kixTermShift 0 x (modeA n m u) (modeLam n m) w|
      ≤ (modeA n m u ^ 2 + 9) * (Real.cosh w ^ 0 * Real.exp (-(modeA n m u * Real.cosh w))) :=
    mul_le_mul_of_nonneg_left h0 (by positivity)
  have hb1 : 6 * modeA n m u * |kixTermShift 1 x (modeA n m u) (modeLam n m) w|
      ≤ 6 * modeA n m u
        * (Real.cosh w ^ 1 * Real.exp (-(modeA n m u * Real.cosh w))) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

theorem modeIntegrandW_integrable (n m : ℕ) (x u : ℝ) :
    Integrable (modeIntegrandW n m x u) := by
  have hA : 0 < modeA n m u := modeA_pos n m u
  unfold modeIntegrandW
  exact ((kixTermShift_integrable 0 x hA (modeLam n m)).const_mul _).add
    ((kixTermShift_integrable 1 x hA (modeLam n m)).const_mul _)

/-! ### 3. The cross term in `p`, and its `L¹` norm -/

/-- The cross term is the head constant times the `w`-integrand at `w = 2p + λ`. -/
theorem crossTerm_eq (n m : ℕ) (x u p : ℝ) :
    riemannXiKernelTerm n (u + p) * riemannXiKernelTerm m (u - p) * Real.cos (2 * x * p)
      = Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u)
        * modeIntegrandW n m x u (2 * p + modeLam n m) := by
  rw [modePair_eq n m u p, modeW_eq, modeIntegrandW_eq,
    show x * (2 * p + modeLam n m - modeLam n m) = 2 * x * p by ring]
  ring

theorem crossTerm_integrable (n m : ℕ) (x u : ℝ) :
    Integrable (fun p : ℝ => riemannXiKernelTerm n (u + p) * riemannXiKernelTerm m (u - p)
      * Real.cos (2 * x * p)) := by
  have hG := modeIntegrandW_integrable n m x u
  have hshift : Integrable (fun q : ℝ => modeIntegrandW n m x u (q + modeLam n m)) :=
    hG.comp_add_right (modeLam n m)
  have hscale : Integrable (fun p : ℝ => modeIntegrandW n m x u (2 * p + modeLam n m)) := by
    have := hshift.comp_mul_left' (R := (2 : ℝ)) two_ne_zero
    exact this
  have hfinal := hscale.const_mul
    (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u))
  refine hfinal.congr ?_
  filter_upwards with p
  exact (crossTerm_eq n m x u p).symm

/-- **THE `L¹` BOUND.**  Exactly `modeBound`: the `1/2` from the change of variables and the
`2` from evenness cancel. -/
theorem crossTerm_integral_norm_le (n m : ℕ) (x u : ℝ) :
    (∫ p : ℝ, ‖riemannXiKernelTerm n (u + p) * riemannXiKernelTerm m (u - p)
        * Real.cos (2 * x * p)‖) ≤ modeBound x u (n, m) := by
  set A : ℝ := modeA n m u with hAdef
  set A₁ : ℝ := modeA 0 0 u with hA1def
  have hA : 0 < A := modeA_pos n m u
  have hA1 : 0 < A₁ := modeA_head_pos u
  have hge : A₁ ≤ A := modeA_ge_head n m u
  set Cnm : ℝ := Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u)
    with hCdef
  have hC0 : 0 ≤ Cnm := by
    rw [hCdef]
    have := Real.pi_pos
    positivity
  -- rewrite the norm as `Cnm * |G (2p + λ)|`
  have hnorm : ∀ p : ℝ, ‖riemannXiKernelTerm n (u + p) * riemannXiKernelTerm m (u - p)
      * Real.cos (2 * x * p)‖
      = Cnm * |modeIntegrandW n m x u (2 * p + modeLam n m)| := by
    intro p
    rw [Real.norm_eq_abs, crossTerm_eq n m x u p, abs_mul, abs_of_nonneg hC0]
  have hcongr : (∫ p : ℝ, ‖riemannXiKernelTerm n (u + p) * riemannXiKernelTerm m (u - p)
        * Real.cos (2 * x * p)‖)
      = ∫ p : ℝ, Cnm * |modeIntegrandW n m x u (2 * p + modeLam n m)| :=
    integral_congr_ae (Filter.Eventually.of_forall hnorm)
  -- change of variables on the absolute value
  have hscale : (∫ p : ℝ, |modeIntegrandW n m x u (2 * p + modeLam n m)|)
      = |(2 : ℝ)⁻¹| • ∫ q : ℝ, |modeIntegrandW n m x u (q + modeLam n m)| := by
    have h := MeasureTheory.Measure.integral_comp_mul_left
      (fun q : ℝ => |modeIntegrandW n m x u (q + modeLam n m)|) 2
    simpa using h
  have hshift : (∫ q : ℝ, |modeIntegrandW n m x u (q + modeLam n m)|)
      = ∫ w : ℝ, |modeIntegrandW n m x u w| :=
    integral_add_right_eq_self (fun w => |modeIntegrandW n m x u w|) (modeLam n m)
  -- the `w`-integral of the absolute value
  have hb0 := coshMomentFun_integrable 0 hA
  have hb1 := coshMomentFun_integrable 1 hA
  have hGabs : (∫ w : ℝ, |modeIntegrandW n m x u w|)
      ≤ (A ^ 2 + 9) * (2 * coshMoment 0 A) + 6 * A * (2 * coshMoment 1 A) := by
    have hmono : (∫ w : ℝ, |modeIntegrandW n m x u w|)
        ≤ ∫ w : ℝ, ((A ^ 2 + 9) * (Real.cosh w ^ 0 * Real.exp (-(A * Real.cosh w)))
            + 6 * A * (Real.cosh w ^ 1 * Real.exp (-(A * Real.cosh w)))) := by
      refine integral_mono ((modeIntegrandW_integrable n m x u).abs) ?_ ?_
      · exact (hb0.const_mul _).add (hb1.const_mul _)
      · intro w
        exact modeIntegrandW_abs_le n m x u w
    refine hmono.trans ?_
    rw [integral_add (hb0.const_mul _) (hb1.const_mul _), integral_const_mul, integral_const_mul,
      coshMoment_full 0 hA, coshMoment_full 1 hA]
  have hm0 := coshMoment_le 0 hA1 hge
  have hm1 := coshMoment_le 1 hA1 hge
  rw [hcongr, integral_const_mul, hscale, hshift,
    show |(2 : ℝ)⁻¹| = 2⁻¹ from abs_of_nonneg (by norm_num)]
  simp only [smul_eq_mul]
  unfold modeBound
  simp only []
  have hrw : Real.pi ^ 2 * (((n : ℝ) + 1) * ((m : ℝ) + 1)) ^ 2 * Real.exp (5 * u) = Cnm := by
    rw [hCdef]; ring
  rw [hrw]
  have hstep : 2⁻¹ * ∫ w : ℝ, |modeIntegrandW n m x u w|
      ≤ ((A ^ 2 + 9) * kixConst 0 A₁ + 6 * A * kixConst 1 A₁) * Real.exp (-(A - A₁)) := by
    have h2 : 2⁻¹ * ∫ w : ℝ, |modeIntegrandW n m x u w|
        ≤ 2⁻¹ * ((A ^ 2 + 9) * (2 * coshMoment 0 A) + 6 * A * (2 * coshMoment 1 A)) :=
      mul_le_mul_of_nonneg_left hGabs (by norm_num)
    refine h2.trans ?_
    have e0 : (A ^ 2 + 9) * coshMoment 0 A
        ≤ (A ^ 2 + 9) * (Real.exp (-(A - A₁)) * kixConst 0 A₁) :=
      mul_le_mul_of_nonneg_left hm0 (by positivity)
    have e1 : 6 * A * coshMoment 1 A
        ≤ 6 * A * (Real.exp (-(A - A₁)) * kixConst 1 A₁) :=
      mul_le_mul_of_nonneg_left hm1 (by positivity)
    nlinarith [e0, e1]
  have hfin := mul_le_mul_of_nonneg_left hstep hC0
  have hassoc : Cnm
        * (((A ^ 2 + 9) * kixConst 0 A₁ + 6 * A * kixConst 1 A₁) * Real.exp (-(A - A₁)))
      = Cnm * ((A ^ 2 + 9) * kixConst 0 A₁ + 6 * A * kixConst 1 A₁)
        * Real.exp (-(A - A₁)) := by ring
  rw [hassoc] at hfin
  exact hfin

/-! ### 4. The interchange -/

theorem summable_crossTerm_integral_norm (x u : ℝ) :
    Summable (fun z : ℕ × ℕ => ∫ p : ℝ,
      ‖riemannXiKernelTerm z.1 (u + p) * riemannXiKernelTerm z.2 (u - p)
        * Real.cos (2 * x * p)‖) := by
  refine Summable.of_nonneg_of_le ?_ ?_ (summable_modeBound x u)
  · intro z
    exact integral_nonneg fun p => norm_nonneg _
  · intro z
    obtain ⟨n, m⟩ := z
    exact crossTerm_integral_norm_le n m x u

/-- **THE COMPLETE THETA DOUBLE-SUM REPRESENTATION OF THE CELL DENSITY.**

`∫_ℝ Φ(u+p)Φ(u−p)cos(2xp) dp
   = 16 · Σ_{(n,m)} π²(n+1)²(m+1)²·e^{5u}·cos(x·log((n+1)/(m+1)))·radial(A_{nm}(u))`.

Every `(n,m)` cross term retained, every constant exact, the interchange discharged by the
summable majorant `modeBound` of block A6. -/
theorem C_tsum (x u : ℝ) :
    (∫ p : ℝ, riemannXiKernel (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p))
      = 16 * ∑' z : ℕ × ℕ,
          (Real.pi ^ 2 * ((z.1 : ℝ) + 1) ^ 2 * ((z.2 : ℝ) + 1) ^ 2 * Real.exp (5 * u)
            * Real.cos (x * modeLam z.1 z.2)
            * C3B5.A2.radial (modeA z.1 z.2 u) (kix 0 x (modeA z.1 z.2 u))
                (kix 1 x (modeA z.1 z.2 u))) := by
  have hswap := integral_tsum_of_summable_integral_norm
    (F := fun z : ℕ × ℕ => fun p : ℝ =>
      riemannXiKernelTerm z.1 (u + p) * riemannXiKernelTerm z.2 (u - p)
        * Real.cos (2 * x * p))
    (fun z => crossTerm_integrable z.1 z.2 x u)
    (summable_crossTerm_integral_norm x u)
  have hpt : ∀ p : ℝ,
      riemannXiKernel (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
      = 16 * ∑' z : ℕ × ℕ,
          (riemannXiKernelTerm z.1 (u + p) * riemannXiKernelTerm z.2 (u - p)
            * Real.cos (2 * x * p)) := kernel_product_cos_tsum x u
  have hL : (∫ p : ℝ, riemannXiKernel (u + p) * riemannXiKernel (u - p)
        * Real.cos (2 * x * p))
      = 16 * ∫ p : ℝ, ∑' z : ℕ × ℕ,
          (riemannXiKernelTerm z.1 (u + p) * riemannXiKernelTerm z.2 (u - p)
            * Real.cos (2 * x * p)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hL, ← hswap]
  congr 1
  refine tsum_congr fun z => ?_
  exact modePair_integral z.1 z.2 x u

end C3B6.Theta

section AxiomAudit
#print axioms C3B6.Theta.coshMoment_le
#print axioms C3B6.Theta.coshMoment_full
#print axioms C3B6.Theta.kixTermShift_abs_le_cosh
#print axioms C3B6.Theta.modeIntegrandW_abs_le
#print axioms C3B6.Theta.crossTerm_eq
#print axioms C3B6.Theta.crossTerm_integrable
#print axioms C3B6.Theta.crossTerm_integral_norm_le
#print axioms C3B6.Theta.summable_crossTerm_integral_norm
#print axioms C3B6.Theta.C_tsum
end AxiomAudit
