import RequestProject.SmoothedPrimeSignalInput

/-!
# The θ-dial: a one-sided bound with error `C e^{θy}` confines the strip zeros to `|Re ρ − ½| ≤ θ`

`LowerBoundTheta θ`: `W(y) ≥ D e^{y/2} − C e^{θy}` for all `y ≥ 0`.  Landau's argument of `SmoothedPrimeSignal`
runs with `C/z` replaced by `C/(z − θ)`, the transform of `C e^{θy}` on `[0, ∞)`.

* `no_zero_of_lowerBoundTheta`: no zero of `ζ` with `½ + θ < Re ρ < 1`;
* `abs_re_sub_half_le_of_lowerBoundTheta`: every zero with `0 < Re ρ < 1` has `|Re ρ − ½| ≤ θ`;
* `riemannHypothesis_of_forall_lowerBoundTheta`: the bound for every `θ > 0` suffices;
* `lowerBoundTheta_half`: the dial's end `θ = ½` holds unconditionally (`W ≥ 0`);
* `LowerBoundTheta.mono`, `lowerBound_iff_lowerBoundTheta_zero`: the dial is monotone and starts at `LowerBound`;
* `lowerBoundTheta_iff_psiK`: in the multiplicative chart the input reads `ψ_K(x) ≥ D x − C x^{½+θ}`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

namespace SmoothedPrimeSignal

/-- **The θ-dial input.** -/
def LowerBoundTheta (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ y : ℝ, 0 ≤ y → D * Real.exp (y / 2) - C * Real.exp (θ * y) ≤ W y

/-- The θ-dial weight `W(y) − D e^{y/2} + C e^{θy}`. -/
noncomputable def gTheta (θ C : ℝ) (y : ℝ) : ℝ := W y - D * Real.exp (y / 2) + C * Real.exp (θ * y)

/-- **The transform of the θ-dial weight on `[0, ∞)`**, for `Re z > ½` and `Re z > θ`. -/
theorem laplace_gTheta_eq (θ C : ℝ) {z : ℂ} (hz : 1 / 2 < z.re) (hθz : θ < z.re) :
    LandauLaplace.laplace (Ici 0) (gTheta θ C) z
      = Kt z * LSeries (fun m => (Λ m : ℂ)) (1 / 2 + z) - E z - (D : ℂ) / (z - 1 / 2)
        + (C : ℂ) / (z - θ) := by
  have hW := integrable_W_mul_cexp hz
  have h1 : IntegrableOn (fun y : ℝ => (W y : ℂ) * cexp (-z * y)) (Ici 0) := hW.integrableOn
  have h2 : IntegrableOn (fun y : ℝ => cexp ((1 / 2 - z) * y)) (Ici 0) :=
    integrableOn_Ici_cexp (by simp; linarith)
  have h3 : IntegrableOn (fun y : ℝ => cexp (((θ : ℂ) - z) * y)) (Ici 0) :=
    integrableOn_Ici_cexp (by simp; linarith)
  have hpt : ∀ y : ℝ, ((gTheta θ C y : ℝ) : ℂ) * cexp (-z * y)
      = (W y : ℂ) * cexp (-z * y) - (D : ℂ) * cexp ((1 / 2 - z) * y)
        + (C : ℂ) * cexp (((θ : ℂ) - z) * y) := by
    intro y
    rw [gTheta]
    push_cast
    rw [show (1 / 2 - z) * (y : ℂ) = (y : ℂ) / 2 + -z * y by ring,
      show ((θ : ℂ) - z) * (y : ℂ) = (θ : ℂ) * y + -z * y by ring, Complex.exp_add, Complex.exp_add]
    ring
  have hA : IntegrableOn (fun y : ℝ => (W y : ℂ) * cexp (-z * y) - (D : ℂ) * cexp ((1 / 2 - z) * y))
      (Ici 0) := h1.sub (h2.const_mul _)
  have hB : IntegrableOn (fun y : ℝ => (D : ℂ) * cexp ((1 / 2 - z) * y)) (Ici 0) := h2.const_mul _
  have hC : IntegrableOn (fun y : ℝ => (C : ℂ) * cexp (((θ : ℂ) - z) * y)) (Ici 0) := h3.const_mul _
  rw [LandauLaplace.laplace, integral_congr_ae (Eventually.of_forall hpt), integral_add hA hC,
    integral_sub h1 hB, integral_const_mul, integral_const_mul, integral_Ici_cexp (by simp; linarith),
    integral_Ici_cexp (by simp; linarith)]
  have hsplit := integral_add_compl (measurableSet_Ici (a := (0 : ℝ))) hW
  rw [compl_Ici, integral_W_mul_cexp hz] at hsplit
  have hE : ∫ y in Iio (0 : ℝ), (W y : ℂ) * cexp (-z * y) = E z := rfl
  rw [hE] at hsplit
  rw [show (∫ y in Ici (0 : ℝ), (W y : ℂ) * cexp (-z * y)) =
      Kt z * LSeries (fun m => (Λ m : ℂ)) (1 / 2 + z) - E z by rw [← hsplit]; ring]
  rw [show -1 / (1 / 2 - z) = 1 / (z - 1 / 2) by
      rw [show (1 / 2 : ℂ) - z = -(z - 1 / 2) by ring, div_neg, neg_div, neg_neg],
    show -1 / ((θ : ℂ) - z) = 1 / (z - θ) by
      rw [show (θ : ℂ) - z = -(z - θ) by ring, div_neg, neg_div, neg_neg]]
  ring

/-- The continuation for the θ-dial. -/
noncomputable def FTheta (θ C : ℝ) (z : ℂ) : ℂ :=
  Kt z * (-deriv Zfun (1 / 2 + z) / Zfun (1 / 2 + z)) + dslope (fun w => Kt w - (D : ℂ)) (1 / 2) z
    - E z + (C : ℂ) / (z - θ)

theorem FTheta_eq_laplace (θ C : ℝ) (hθ : θ < 1) {z : ℂ} (hz : 1 < z.re) :
    FTheta θ C z = LandauLaplace.laplace (Ici 0) (gTheta θ C) z := by
  rw [laplace_gTheta_eq θ C (by linarith) (by linarith)]
  have hs : 1 < ((1 / 2 : ℂ) + z).re := by rw [re_half_add]; linarith
  have hs1 : (1 / 2 : ℂ) + z ≠ 1 := half_add_ne_one (by linarith)
  have hzeta : riemannZeta ((1 / 2 : ℂ) + z) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_logDeriv_zeta_eq hs1 hzeta]
  have hz12 : z ≠ 1 / 2 := by
    intro h
    rw [h] at hz
    norm_num at hz
  rw [FTheta, dslope_of_ne _ hz12, slope_def_field, Kt_half,
    show (1 / 2 : ℂ) + z - 1 = z - 1 / 2 by ring]
  ring

theorem differentiableOn_FTheta (θ C : ℝ) {σ₀ r : ℝ} (h0 : 0 < σ₀) (hθ : θ ≤ σ₀) (h01 : σ₀ < 1)
    (hr : ∀ z : ℂ, σ₀ < z.re → |z.im| < r → Zfun (1 / 2 + z) ≠ 0) :
    DifferentiableOn ℂ (FTheta θ C) (LandauLaplace.domain σ₀ 1 r) := by
  intro z hz
  have hre : σ₀ < z.re := by
    rcases hz with ⟨h, _⟩ | h
    · exact h
    · have h' : (1 : ℝ) < z.re := h
      linarith
  have hZ : Zfun (1 / 2 + z) ≠ 0 := by
    rcases hz with ⟨h1, h2⟩ | h
    · exact hr z h1 h2
    · have h' : (1 : ℝ) < z.re := h
      rw [Ne, Zfun_eq_zero_iff (half_add_ne_one (by linarith))]
      exact riemannZeta_ne_zero_of_one_le_re (by rw [re_half_add]; linarith)
  have hzθ : z - θ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  apply DifferentiableAt.differentiableWithinAt
  have hshift : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) z :=
    (differentiableAt_const _).add differentiableAt_id
  have hZd : DifferentiableAt ℂ (fun w => Zfun (1 / 2 + w)) z :=
    (differentiable_Zfun _).comp z hshift
  have hdZd : DifferentiableAt ℂ (fun w => deriv Zfun (1 / 2 + w)) z :=
    ((differentiable_Zfun.analyticAt _).deriv.differentiableAt).comp z hshift
  have hdsl : DifferentiableAt ℂ (dslope (fun w => Kt w - (D : ℂ)) (1 / 2)) z := by
    have h := (differentiableOn_dslope (s := univ) (c := (1 / 2 : ℂ)) (f := fun w => Kt w - (D : ℂ))
      Filter.univ_mem).2 (differentiable_Kt.sub_const _).differentiableOn
    exact h.differentiableAt Filter.univ_mem
  unfold FTheta
  exact ((((differentiable_Kt z).mul (hdZd.neg.div hZd hZ)).add hdsl).sub (differentiable_E z)).add
    ((differentiableAt_const _).div (differentiableAt_id.sub_const _) hzθ)

theorem integrableOn_gTheta_Ici (θ C : ℝ) {σ : ℝ} (hσ : 1 / 2 < σ) (hθσ : θ < σ) :
    IntegrableOn (fun y => gTheta θ C y * Real.exp (-σ * y)) (Ici 0) := by
  have hW : IntegrableOn (fun y => W y * Real.exp (-σ * y)) (Ici 0) :=
    (integrable_W_mul_exp hσ).integrableOn
  have hD : IntegrableOn (fun y : ℝ => D * Real.exp (-(σ - 1 / 2) * y)) (Ici 0) :=
    ((exp_neg_integrableOn_Ioi 0 (by linarith)).congr_set_ae Ioi_ae_eq_Ici.symm).const_mul D
  have hC : IntegrableOn (fun y : ℝ => C * Real.exp (-(σ - θ) * y)) (Ici 0) :=
    ((exp_neg_integrableOn_Ioi 0 (by linarith)).congr_set_ae Ioi_ae_eq_Ici.symm).const_mul C
  refine ((hW.sub hD).add hC).congr_fun (fun y _ => ?_) measurableSet_Ici
  simp only [gTheta, Pi.add_apply, Pi.sub_apply]
  rw [show -(σ - 1 / 2) * y = y / 2 + -σ * y by ring, show -(σ - θ) * y = θ * y + -σ * y by ring,
    Real.exp_add, Real.exp_add]
  ring

/-- **Landau applied to the θ-dial weight.** -/
theorem integrableOn_gTheta_of_lowerBound (θ C : ℝ)
    (hC : ∀ y, 0 ≤ y → D * Real.exp (y / 2) - C * Real.exp (θ * y) ≤ W y)
    {σ₀ : ℝ} (h0 : 0 < σ₀) (hθ : θ ≤ σ₀) (h01 : σ₀ < 1) :
    ∀ σ, σ₀ < σ → IntegrableOn (fun y => gTheta θ C y * Real.exp (-σ * y)) (Ici 0) := by
  obtain ⟨r, hr, hrZ⟩ := exists_zeroFree_strip h0
  refine LandauLaplace.landau (gTheta θ C) 0 le_rfl (fun y hy => ?_) h01 hr
    (fun σ hσ => integrableOn_gTheta_Ici θ C (by linarith) (by linarith)) (FTheta θ C)
    (differentiableOn_FTheta θ C h0 hθ h01 hrZ) (fun z hz => FTheta_eq_laplace θ C (by linarith) hz)
  have := hC y hy
  unfold gTheta
  linarith

/-- **The θ-dial excludes zeros with `Re ρ > ½ + θ`.** -/
theorem no_zero_of_lowerBoundTheta (θ C : ℝ) (hθ : 0 ≤ θ)
    (hC : ∀ y, 0 ≤ y → D * Real.exp (y / 2) - C * Real.exp (θ * y) ≤ W y)
    (ρ : ℂ) (hρ : riemannZeta ρ = 0) (h1 : 1 / 2 + θ < ρ.re) (h2 : ρ.re < 1) : False := by
  set p : ℂ := ρ - 1 / 2 with hp
  have hpre : p.re = ρ.re - 1 / 2 := by simp [hp]
  set σ₀ : ℝ := (p.re + θ) / 2 with hσ₀
  have h0 : 0 < σ₀ := by rw [hσ₀, hpre]; linarith
  have hθσ : θ ≤ σ₀ := by rw [hσ₀, hpre]; linarith
  have h01 : σ₀ < 1 := by rw [hσ₀, hpre]; linarith
  have hLd := LandauLaplace.differentiableOn_laplace (Ici 0) (gTheta θ C) σ₀
    (integrableOn_gTheta_of_lowerBound θ C hC h0 hθσ h01)
  set U : Set ℂ := {z | σ₀ < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdsl : Differentiable ℂ (dslope (fun w => Kt w - (D : ℂ)) (1 / 2)) := by
    have h := (differentiableOn_dslope (s := univ) (c := (1 / 2 : ℂ)) (f := fun w => Kt w - (D : ℂ))
      Filter.univ_mem).2 (differentiable_Kt.sub_const _).differentiableOn
    exact fun z => h.differentiableAt Filter.univ_mem
  set Q : ℂ → ℂ := fun z => LandauLaplace.laplace (Ici 0) (gTheta θ C) z + E z - (C : ℂ) / (z - θ)
    - dslope (fun w => Kt w - (D : ℂ)) (1 / 2) z with hQ
  set ψ : ℂ → ℂ := fun z => Zfun (1 / 2 + z) with hψ
  have hψd : Differentiable ℂ ψ := fun z =>
    (differentiable_Zfun _).comp z ((differentiableAt_const _).add differentiableAt_id)
  have hQd : DifferentiableOn ℂ Q U := by
    intro z hz
    have hz' : σ₀ < z.re := hz
    have hzθ : z - θ ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    apply DifferentiableAt.differentiableWithinAt
    exact (((hLd.differentiableAt (hUo.mem_nhds hz)).add (differentiable_E z)).sub
      ((differentiableAt_const _).div (differentiableAt_id.sub_const _) hzθ)).sub (hdsl z)
  have hderiv : ∀ z, deriv ψ z = deriv Zfun (1 / 2 + z) := fun z => deriv_comp_const_add Zfun (1 / 2) z
  have hG1 : AnalyticOnNhd ℂ (fun z => ψ z * Q z) U :=
    (hψd.differentiableOn.mul hQd).analyticOnNhd hUo
  have hG2 : AnalyticOnNhd ℂ (fun z => -(Kt z * deriv ψ z)) U := by
    have hd : Differentiable ℂ (fun z => -(Kt z * deriv ψ z)) := by
      intro z
      simp_rw [hderiv]
      exact ((differentiable_Kt z).mul (((differentiable_Zfun.analyticAt _).deriv.differentiableAt).comp z
        ((differentiableAt_const _).add differentiableAt_id))).neg
    exact hd.differentiableOn.analyticOnNhd hUo
  have hUc : IsPreconnected U := (convex_halfSpace_gt Complex.reLm.isLinear σ₀).isPreconnected
  have h2U : (2 : ℂ) ∈ U := by
    show σ₀ < (2 : ℂ).re
    rw [show (2 : ℂ).re = 2 by norm_num]
    linarith
  have hEq : EqOn (fun z => ψ z * Q z) (fun z => -(Kt z * deriv ψ z)) U := by
    refine hG1.eqOn_of_preconnected_of_eventuallyEq hG2 hUc h2U ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    have hF := FTheta_eq_laplace θ C (by linarith) hz'
    have hZ : Zfun (1 / 2 + z) ≠ 0 := by
      rw [Ne, Zfun_eq_zero_iff (half_add_ne_one (by linarith))]
      exact riemannZeta_ne_zero_of_one_le_re (by rw [re_half_add]; linarith)
    have hQz : Q z = Kt z * (-deriv Zfun (1 / 2 + z) / Zfun (1 / 2 + z)) := by
      show LandauLaplace.laplace (Ici 0) (gTheta θ C) z + E z - (C : ℂ) / (z - θ)
        - dslope (fun w => Kt w - (D : ℂ)) (1 / 2) z = _
      rw [← hF]
      unfold FTheta
      ring
    show ψ z * Q z = -(Kt z * deriv ψ z)
    rw [hQz, hderiv z]
    show Zfun (1 / 2 + z) * (Kt z * (-deriv Zfun (1 / 2 + z) / Zfun (1 / 2 + z)))
      = -(Kt z * deriv Zfun (1 / 2 + z))
    rw [mul_div_assoc', mul_div_assoc', div_eq_iff hZ]
    ring
  have hpU : p ∈ U := by
    show σ₀ < p.re
    rw [hσ₀, hpre]
    linarith
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at h2
    exact lt_irrefl _ h2
  have hψp : ψ p = 0 := by
    simp only [hψ, hp]
    rw [show (1 / 2 : ℂ) + (ρ - 1 / 2) = ρ by ring, Zfun_eq_zero_iff hρ1]
    exact hρ
  have hψne : ∃ w, ψ w ≠ 0 := ⟨1 / 2, by
    simp only [hψ]
    rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Zfun_one]
    exact one_ne_zero⟩
  exact no_zero_of_multiplied_identity hψd hψne hψp
    (hQd.analyticAt (hUo.mem_nhds hpU)) (differentiable_Kt.analyticAt p) (Kt_ne_zero p)
    (by filter_upwards [hUo.mem_nhds hpU] with z hz using hEq hz)

/-- **The dial confines the strip zeros**: under `LowerBoundTheta θ` every zero of `ζ` with `0 < Re ρ < 1` has
`|Re ρ − ½| ≤ θ`.  The left half is the reflection `ρ ↦ 1 − ρ`. -/
theorem abs_re_sub_half_le_of_lowerBoundTheta {θ : ℝ} (hθ : 0 ≤ θ) (h : LowerBoundTheta θ)
    (ρ : ℂ) (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : |ρ.re - 1 / 2| ≤ θ := by
  obtain ⟨C, hC⟩ := h
  rw [abs_le]
  constructor
  · by_contra hlt
    have hlt' := not_le.mp hlt
    have hn : ∀ n : ℕ, ρ ≠ -n := by
      intro n hn
      have hre := congrArg Complex.re hn
      rw [Complex.neg_re, Complex.natCast_re] at hre
      have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have hne1 : ρ ≠ 1 := by
      intro h'
      rw [h', Complex.one_re] at h1
      exact lt_irrefl _ h1
    have hz : riemannZeta (1 - ρ) = 0 := by
      rw [riemannZeta_one_sub hn hne1, hρ, mul_zero]
    exact no_zero_of_lowerBoundTheta θ C hθ hC (1 - ρ) hz
      (by rw [Complex.sub_re, Complex.one_re]; linarith) (by rw [Complex.sub_re, Complex.one_re]; linarith)
  · by_contra hlt
    have hlt' := not_le.mp hlt
    exact no_zero_of_lowerBoundTheta θ C hθ hC ρ hρ (by linarith) h1

theorem re_eq_half_of_forall_lowerBoundTheta (h : ∀ θ : ℝ, 0 < θ → LowerBoundTheta θ)
    (ρ : ℂ) (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ.re = 1 / 2 := by
  have key : ∀ θ : ℝ, 0 < θ → |ρ.re - 1 / 2| ≤ θ := fun θ hθ =>
    abs_re_sub_half_le_of_lowerBoundTheta hθ.le (h θ hθ) ρ hρ h0 h1
  have habs : |ρ.re - 1 / 2| = 0 := by
    by_contra hne
    have hpos : 0 < |ρ.re - 1 / 2| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    have := key (|ρ.re - 1 / 2| / 2) (by linarith)
    linarith
  have := abs_eq_zero.mp habs
  linarith

/-- **Every `θ > 0` together suffices.** -/
theorem riemannHypothesis_of_forall_lowerBoundTheta (h : ∀ θ : ℝ, 0 < θ → LowerBoundTheta θ) :
    RiemannHypothesis :=
  VMEFStandalone.NontrivialZeros_implies_RiemannHypothesis fun ρ hρ =>
    re_eq_half_of_forall_lowerBoundTheta h ρ hρ.2.2 hρ.1 hρ.2.1

/-! ## The dial itself -/

/-- The dial's end: `θ = ½` holds unconditionally, because `W ≥ 0`. -/
theorem lowerBoundTheta_half : LowerBoundTheta (1 / 2) :=
  ⟨D, fun y _ => by
    rw [show (1 / 2 : ℝ) * y = y / 2 by ring, sub_self]
    exact W_nonneg y⟩

/-- The dial is monotone in `θ`. -/
theorem LowerBoundTheta.mono {θ θ' : ℝ} (hθ : θ ≤ θ') (h : LowerBoundTheta θ) : LowerBoundTheta θ' := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, fun y hy => ?_⟩
  have h1 := hC y hy
  have h2 : C * Real.exp (θ * y) ≤ max C 0 * Real.exp (θ' * y) := by
    calc C * Real.exp (θ * y) ≤ max C 0 * Real.exp (θ * y) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max C 0 * Real.exp (θ' * y) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hθ hy))
            (le_max_right _ _)
  linarith

theorem lowerBound_iff_lowerBoundTheta_zero : LowerBound ↔ LowerBoundTheta 0 := by
  simp only [LowerBound, LowerBoundTheta, zero_mul, Real.exp_zero, mul_one]

/-- **The θ-dial in the multiplicative chart**: `ψ_K(x) ≥ D x − C x^{½+θ}` for every `x ≥ 1`. -/
theorem lowerBoundTheta_iff_psiK (θ : ℝ) :
    LowerBoundTheta θ ↔ ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → D * x - C * x ^ (1 / 2 + θ) ≤ psiK x := by
  have key : ∀ y : ℝ, Real.exp y ^ (1 / 2 + θ) = Real.exp (y / 2) * Real.exp (θ * y) := by
    intro y
    rw [← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith
    have h := hC (Real.log x) (Real.log_nonneg hx)
    rw [exp_half_log hx0] at h
    rw [psiK_eq hx0]
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hxθ : x ^ (1 / 2 + θ) = Real.sqrt x * Real.exp (θ * Real.log x) := by
      have := key (Real.log x)
      rw [Real.exp_log hx0, exp_half_log hx0] at this
      exact this
    have hm := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg x)
    calc D * x - C * x ^ (1 / 2 + θ)
        = Real.sqrt x * (D * Real.sqrt x - C * Real.exp (θ * Real.log x)) := by
          rw [hxθ]
          linear_combination (-D) * hxx
      _ ≤ Real.sqrt x * W (Real.log x) := hm
  · rintro ⟨C, hC⟩
    refine ⟨C, fun y hy => ?_⟩
    have hx : 1 ≤ Real.exp y := by simpa using Real.exp_le_exp.mpr hy
    have h := hC (Real.exp y) hx
    have hsq : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
      rw [← exp_half_log (Real.exp_pos y), Real.log_exp]
    rw [psiK_eq (Real.exp_pos y), Real.log_exp, hsq, key y] at h
    have hpos : 0 < Real.exp (y / 2) := Real.exp_pos _
    have hexp : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hexp] at h
    have h' : Real.exp (y / 2) * (D * Real.exp (y / 2) - C * Real.exp (θ * y))
        ≤ Real.exp (y / 2) * W y := by
      calc Real.exp (y / 2) * (D * Real.exp (y / 2) - C * Real.exp (θ * y))
          = D * (Real.exp (y / 2) * Real.exp (y / 2)) - C * (Real.exp (y / 2) * Real.exp (θ * y)) := by
            ring
        _ ≤ Real.exp (y / 2) * W y := h
    exact le_of_mul_le_mul_left h' hpos

end SmoothedPrimeSignal
