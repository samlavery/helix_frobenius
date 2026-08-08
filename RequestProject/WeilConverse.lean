import RequestProject.RamifiedMechanism
import RequestProject.ArgumentPrincipleRectangle
import RequestProject.CPSMellinFEDischarge
import Mathlib.Analysis.MellinInversion

/-!
# The converse mechanism: the package forces the theta reflection

`mechanismK` compiles one arrow: a pointwise theta identity of the prescribed readouts
yields the complete analytic package.  This file compiles the **converse arrow** — the
Hecke/Weil converse in the carrier register: an entire continuation with the functional
equation, the chart identification, and the classical strip data (line integrability
and horizontal decay — the Phragmén–Lindelöf consequences of bounded vertical strips)
**forces** the pointwise theta reflection.

* `vertical_line_shift` — the contour shift: an entire integrand with line
  integrability on two vertical lines and vanishing horizontal integrals has equal
  line integrals (rectangle Cauchy–Goursat + limits — the one analytic step of the
  classical converse);
* `horizontal_tendsto_zero_of_bound` — integral-form horizontal decay from a
  sup-form bound;
* `mellinInv_line_shift` — the shift for the inverse-Mellin readout of an entire `Λ`;
* `mellinInv_reflect` — the functional equation exchanges the two inversion lines:
  `mellinInv (1-σ) Λ y = ε·y⁻¹·mellinInv σ Λ (1/y)`;
* `mellin_theta_eq_lam_on` — on the chart half-plane the bank's Mellin transform *is*
  the package's `lam` (compiled identification + chart);
* `weil_converse_reflection` / `weil_converse` — **the converse**: package + strip
  data ⟹ the theta reflection, in exactly the shape `mechanismK` consumes;
* `weil_converse_ring` — the ring closed: the package built by `mechanismK` from the
  derived reflection has the same `lam` (uniqueness) — identity and package are the
  same data.

Register.  The statement is per-object at every rank and every packaged chart kernel —
this subsumes the GL(2) case classically named Weil; quantifying it over a twist
family is `∀`-introduction.  The classical *identification* step — that finitely many
twisted functional equations suffice to name the object automorphic on `Γ₀(N)` — is
the cited converse-theorem layer (`AutomorphicCandidate.candidate_wellformed`,
`allRank_converseInput`), consumed at typed fields, not reproven here.  The engine
`theta_reflection_of_mellin_functionalEquation` (compiled earlier) covers two-sided
rapidly decaying profiles; this file supplies the genuinely one-sided case by the
contour shift, which is where entirety and the strip data enter.  No `axiom`, no
`sorry`.
-/

open Real Complex Set Filter Topology MeasureTheory Asymptotics

namespace CriticalLinePhasor.WeilConverse

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.TransportClosure
open CriticalLinePhasor.ThetaMechanism CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.RamifiedMechanism CriticalLinePhasor.ContourArgument

/-! ## The contour shift -/

/-- **The vertical-line shift.**  An entire integrand, integrable on two vertical
lines, whose horizontal integrals vanish at `±∞`, has equal line integrals. -/
theorem vertical_line_shift (F : ℂ → ℂ) (hF : Differentiable ℂ F) (σ₁ σ₂ : ℝ)
    (h12 : σ₁ ≤ σ₂)
    (hInt₁ : Integrable (fun y : ℝ => F ((σ₁ : ℂ) + y * I)))
    (hInt₂ : Integrable (fun y : ℝ => F ((σ₂ : ℂ) + y * I)))
    (hTop : Tendsto (fun T : ℝ => ∫ u in σ₁..σ₂, F ((u : ℂ) + T * I)) atTop (𝓝 0))
    (hBot : Tendsto (fun T : ℝ => ∫ u in σ₁..σ₂, F ((u : ℂ) + (-T) * I)) atTop (𝓝 0)) :
    (∫ y : ℝ, F ((σ₁ : ℂ) + y * I)) = ∫ y : ℝ, F ((σ₂ : ℂ) + y * I) := by
  have hv₁ : Tendsto (fun T : ℝ => ∫ y in (-T)..T, F ((σ₁ : ℂ) + y * I)) atTop
      (𝓝 (∫ y : ℝ, F ((σ₁ : ℂ) + y * I))) :=
    intervalIntegral_tendsto_integral hInt₁ tendsto_neg_atTop_atBot tendsto_id
  have hv₂ : Tendsto (fun T : ℝ => ∫ y in (-T)..T, F ((σ₂ : ℂ) + y * I)) atTop
      (𝓝 (∫ y : ℝ, F ((σ₂ : ℂ) + y * I))) :=
    intervalIntegral_tendsto_integral hInt₂ tendsto_neg_atTop_atBot tendsto_id
  have hkey : ∀ᶠ T : ℝ in atTop,
      I * (∫ y in (-T)..T, F ((σ₂ : ℂ) + y * I))
          - I * (∫ y in (-T)..T, F ((σ₁ : ℂ) + y * I))
        = (∫ u in σ₁..σ₂, F ((u : ℂ) + T * I))
          - (∫ u in σ₁..σ₂, F ((u : ℂ) + (-T) * I)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have h0 := rectangleBoundaryIntegral_eq_zero_of_differentiableOn F σ₁ σ₂ (-T) T
      h12 (by linarith) hF.differentiableOn
    unfold rectangleBoundaryIntegral at h0
    simp only [Complex.ofReal_neg] at h0 ⊢
    linear_combination h0
  have hL : Tendsto (fun T : ℝ =>
      I * (∫ y in (-T)..T, F ((σ₂ : ℂ) + y * I))
        - I * (∫ y in (-T)..T, F ((σ₁ : ℂ) + y * I))) atTop
      (𝓝 (I * (∫ y : ℝ, F ((σ₂ : ℂ) + y * I))
        - I * (∫ y : ℝ, F ((σ₁ : ℂ) + y * I)))) :=
    (hv₂.const_mul I).sub (hv₁.const_mul I)
  have hR : Tendsto (fun T : ℝ =>
      (∫ u in σ₁..σ₂, F ((u : ℂ) + T * I))
        - (∫ u in σ₁..σ₂, F ((u : ℂ) + (-T) * I))) atTop (𝓝 0) := by
    simpa using hTop.sub hBot
  have hzero : I * (∫ y : ℝ, F ((σ₂ : ℂ) + y * I))
      - I * (∫ y : ℝ, F ((σ₁ : ℂ) + y * I)) = 0 :=
    tendsto_nhds_unique (hL.congr' hkey) hR
  have hmul : I * ((∫ y : ℝ, F ((σ₂ : ℂ) + y * I))
      - (∫ y : ℝ, F ((σ₁ : ℂ) + y * I))) = 0 := by
    rw [mul_sub]
    exact hzero
  have := mul_eq_zero.mp hmul
  rcases this with h | h
  · exact absurd h I_ne_zero
  · exact (sub_eq_zero.mp h).symm

/-- Integral-form horizontal decay from a sup-form bound. -/
theorem horizontal_tendsto_zero_of_bound (F : ℂ → ℂ) (σ₁ σ₂ : ℝ) (h12 : σ₁ ≤ σ₂)
    (M : ℝ → ℝ)
    (hM : ∀ T : ℝ, ∀ u ∈ Set.Icc σ₁ σ₂, ‖F ((u : ℂ) + T * I)‖ ≤ M |T|)
    (hM0 : Tendsto M atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ u in σ₁..σ₂, F ((u : ℂ) + T * I)) atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => ∫ u in σ₁..σ₂, F ((u : ℂ) + (-T) * I)) atTop (𝓝 0) := by
  have habs : Tendsto (fun T : ℝ => M |T| * |σ₂ - σ₁|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => M |T|) atTop (𝓝 0) :=
      hM0.comp tendsto_abs_atTop_atTop
    simpa using h1.mul_const |σ₂ - σ₁|
  constructor
  · refine squeeze_zero_norm (fun T => ?_) habs
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    exact hM T u (Set.mem_Icc_of_Ioc (Set.uIoc_of_le h12 ▸ hu))
  · refine squeeze_zero_norm (fun T => ?_) habs
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    have := hM (-T) u (Set.mem_Icc_of_Ioc (Set.uIoc_of_le h12 ▸ hu))
    simpa [abs_neg] using this

/-! ## The shift for the inverse-Mellin readout -/

/-- The norm of the vertical power factor: `‖x^{-(u+tI)}‖ = x^{-u}` for `x > 0`. -/
theorem norm_cpow_vline {x : ℝ} (hx : 0 < x) (u t : ℝ) :
    ‖(x : ℂ) ^ (-((u : ℂ) + t * I))‖ = x ^ (-u) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1
  simp

/-- **The inverse-Mellin line shift** for an entire `Λ` with line integrability and
horizontal decay in the strip. -/
theorem mellinInv_line_shift (lam : ℂ → ℂ) (hlam : Differentiable ℂ lam) (σ₁ σ₂ : ℝ)
    (h12 : σ₁ ≤ σ₂) {x : ℝ} (hx : 0 < x)
    (hInt₁ : Integrable (fun y : ℝ => lam ((σ₁ : ℂ) + y * I)))
    (hInt₂ : Integrable (fun y : ℝ => lam ((σ₂ : ℂ) + y * I)))
    (M : ℝ → ℝ)
    (hM : ∀ T : ℝ, ∀ u ∈ Set.Icc σ₁ σ₂, ‖lam ((u : ℂ) + T * I)‖ ≤ M |T|)
    (hM0 : Tendsto M atTop (𝓝 0)) :
    mellinInv σ₁ lam x = mellinInv σ₂ lam x := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  set F : ℂ → ℂ := fun s => (x : ℂ) ^ (-s) * lam s with hFdef
  have hFdiff : Differentiable ℂ F :=
    (differentiable_neg.const_cpow (Or.inl hxne)).mul hlam
  have hFcont : Continuous F := hFdiff.continuous
  have hFnorm : ∀ (u t : ℝ), ‖F ((u : ℂ) + t * I)‖ = x ^ (-u) * ‖lam ((u : ℂ) + t * I)‖ := by
    intro u t
    rw [hFdef]
    dsimp only
    rw [norm_mul, norm_cpow_vline hx u t]
  have hFInt : ∀ σ : ℝ, Integrable (fun y : ℝ => lam ((σ : ℂ) + y * I)) →
      Integrable (fun y : ℝ => F ((σ : ℂ) + y * I)) := by
    intro σ h
    refine (h.norm.const_mul (x ^ (-σ))).mono' ?_ ?_
    · exact (hFcont.comp (by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall fun y => le_of_eq (hFnorm σ y)
  set c : ℝ := max (x ^ (-σ₁)) (x ^ (-σ₂)) with hcdef
  have hcpos : 0 ≤ c := le_trans (Real.rpow_nonneg hx.le _) (le_max_left _ _)
  have hcbound : ∀ u ∈ Set.Icc σ₁ σ₂, x ^ (-u) ≤ c := by
    intro u hu
    rcases le_total 1 x with hx1 | hx1
    · exact le_max_of_le_left
        (Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg hu.1))
    · exact le_max_of_le_right
        (Real.rpow_le_rpow_of_exponent_ge hx hx1 (neg_le_neg hu.2))
  have hFM : ∀ T : ℝ, ∀ u ∈ Set.Icc σ₁ σ₂,
      ‖F ((u : ℂ) + T * I)‖ ≤ (fun T => c * M T) |T| := by
    intro T u hu
    rw [hFnorm u T]
    exact mul_le_mul (hcbound u hu) (hM T u hu) (norm_nonneg _) hcpos
  have hcM : Tendsto (fun T : ℝ => c * M T) atTop (𝓝 0) := by
    have h1 := hM0.const_mul c
    rwa [mul_zero] at h1
  obtain ⟨hTop, hBot⟩ :=
    horizontal_tendsto_zero_of_bound F σ₁ σ₂ h12 (fun T => c * M T) hFM hcM
  have hshift := vertical_line_shift F hFdiff σ₁ σ₂ h12
    (hFInt σ₁ hInt₁) (hFInt σ₂ hInt₂) hTop hBot
  have hmain : (∫ y : ℝ, (x : ℂ) ^ (-((σ₁ : ℂ) + y * I)) • lam ((σ₁ : ℂ) + y * I))
      = ∫ y : ℝ, (x : ℂ) ^ (-((σ₂ : ℂ) + y * I)) • lam ((σ₂ : ℂ) + y * I) := by
    calc (∫ y : ℝ, (x : ℂ) ^ (-((σ₁ : ℂ) + y * I)) • lam ((σ₁ : ℂ) + y * I))
        = ∫ y : ℝ, F ((σ₁ : ℂ) + y * I) := by
          simp [hFdef, smul_eq_mul]
      _ = ∫ y : ℝ, F ((σ₂ : ℂ) + y * I) := hshift
      _ = ∫ y : ℝ, (x : ℂ) ^ (-((σ₂ : ℂ) + y * I)) • lam ((σ₂ : ℂ) + y * I) := by
          simp [hFdef, smul_eq_mul]
  unfold mellinInv
  rw [hmain]

/-- **The functional equation exchanges the two inversion lines**:
`mellinInv (1-σ) Λ y = ε · y⁻¹ · mellinInv σ Λ (1/y)`. -/
theorem mellinInv_reflect (lam : ℂ → ℂ) (ε : ℂ)
    (hFE : ∀ s : ℂ, lam (1 - s) = ε * lam s) (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    mellinInv (1 - σ) lam y = ε * ((y : ℂ)⁻¹ * mellinInv σ lam (1 / y)) := by
  have hyne : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hyarg : Complex.arg ((y : ℝ) : ℂ) ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]
    exact Real.pi_ne_zero.symm
  have hpoint : ∀ t : ℝ,
      (y : ℂ) ^ (-(((1 - σ : ℝ) : ℂ) + (-t : ℝ) * I)) *
          lam (((1 - σ : ℝ) : ℂ) + (-t : ℝ) * I)
        = ε * ((y : ℂ)⁻¹ *
            (((1 / y : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) * lam ((σ : ℂ) + t * I))) := by
    intro t
    have hlam : lam (((1 - σ : ℝ) : ℂ) + (-t : ℝ) * I) = ε * lam ((σ : ℂ) + t * I) := by
      have h := hFE ((σ : ℂ) + t * I)
      rw [show (1 : ℂ) - ((σ : ℂ) + t * I) = ((1 - σ : ℝ) : ℂ) + (-t : ℝ) * I by
        push_cast; ring] at h
      exact h
    have hpow : (y : ℂ) ^ (-(((1 - σ : ℝ) : ℂ) + (-t : ℝ) * I))
        = (y : ℂ)⁻¹ * ((1 / y : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) := by
      have hinv : ((1 / y : ℝ) : ℂ) = ((y : ℝ) : ℂ)⁻¹ := by push_cast; ring
      rw [hinv, Complex.inv_cpow _ _ hyarg, ← Complex.cpow_neg, neg_neg]
      rw [show -(((1 - σ : ℝ) : ℂ) + (-t : ℝ) * I) = (-1 : ℂ) + ((σ : ℂ) + t * I) by
        push_cast; ring]
      rw [Complex.cpow_add _ _ hyne, Complex.cpow_neg_one]
    rw [hpow, hlam]
    ring
  calc mellinInv (1 - σ) lam y
      = (1 / (2 * π)) • ∫ t : ℝ,
          (y : ℂ) ^ (-(((1 - σ : ℝ) : ℂ) + t * I)) * lam (((1 - σ : ℝ) : ℂ) + t * I) := by
        simp only [mellinInv, smul_eq_mul]
    _ = (1 / (2 * π)) • ∫ t : ℝ,
          (y : ℂ) ^ (-(((1 - σ : ℝ) : ℂ) + (-t : ℝ) * I)) *
            lam (((1 - σ : ℝ) : ℂ) + (-t : ℝ) * I) := by
        congr 1
        exact (MeasureTheory.integral_neg_eq_self (fun t : ℝ =>
          (y : ℂ) ^ (-(((1 - σ : ℝ) : ℂ) + (t : ℝ) * I)) *
            lam (((1 - σ : ℝ) : ℂ) + (t : ℝ) * I)) volume).symm
    _ = (1 / (2 * π)) • ∫ t : ℝ,
          ε * ((y : ℂ)⁻¹ *
            (((1 / y : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) * lam ((σ : ℂ) + t * I))) := by
        congr 1
        exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun t => hpoint t)
    _ = ε * ((y : ℂ)⁻¹ * ((1 / (2 * π)) • ∫ t : ℝ,
          ((1 / y : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) * lam ((σ : ℂ) + t * I))) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
        simp only [Complex.real_smul]
        ring
    _ = ε * ((y : ℂ)⁻¹ * mellinInv σ lam (1 / y)) := by
        simp only [mellinInv, smul_eq_mul]

/-! ## The bank's Mellin transform is the package's `lam` on the chart -/

/-- On the chart half-plane, the Mellin transform of the primal theta bank equals the
package's completed readout. -/
theorem mellin_theta_eq_lam_on (P : CoefficientSurface)
    (κ : MellinKernel) {B : ℝ} {ε : ℂ}
    (pkg : KNicePackage (coefficientArithmetic P.a) κ.G B ε)
    (hB : max κ.B0 ((P.A : ℝ) + 1) ≤ B)
    (s : ℂ) (hs : B < s.re) :
    mellin (CriticalLinePhasor.CarrierTheta.theta P.a κ.K) s = pkg.lam s := by
  have hB0 : κ.B0 < s.re :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) hB) hs
  have hA : (P.A : ℝ) + 1 < s.re :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) hB) hs
  have ha : ∀ n : ℕ, ‖P.a n‖ ≤ (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ ((P.A : ℝ))) := by
    intro n
    rw [one_mul, Real.rpow_natCast]
    exact P.a_bound n
  have hg := κ.hK s hB0
  have h := CriticalLinePhasor.CarrierTheta.theta_hasMellin_of_polynomial
    P.a κ.K s 1 (P.A : ℝ) hg.1 ha hA
  rw [h.2, hg.2, pkg.chart s hs]
  have hcoeff : P.a = fun j => (coefficientArithmetic P.a) (j + 1) := by
    funext j
    simp [coefficientArithmetic]
  have hdir : CriticalLinePhasor.CarrierTheta.dirichlet P.a s
      = LSeries (⇑(coefficientArithmetic P.a)) s := by
    conv_lhs => rw [hcoeff]
    rw [dirichlet_shift_eq_LSeries _ (coeffArithmetic_summable P hA)]
  rw [hdir]
  ring

/-- The dual bank's Mellin transform also equals `lam` (self-dual coefficients). -/
theorem mellin_theta_dual_eq_lam_on (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n)
    (κ : MellinKernel) {B : ℝ} {ε : ℂ}
    (pkg : KNicePackage (coefficientArithmetic P.a) κ.G B ε)
    (hB : max κ.B0 ((P.A : ℝ) + 1) ≤ B)
    (s : ℂ) (hs : B < s.re) :
    mellin (CriticalLinePhasor.CarrierTheta.theta P.adual κ.K) s = pkg.lam s := by
  have hth : CriticalLinePhasor.CarrierTheta.theta P.adual κ.K
      = CriticalLinePhasor.CarrierTheta.theta P.a κ.K := by
    funext x
    unfold CriticalLinePhasor.CarrierTheta.theta
    exact tsum_congr fun n => by rw [hdual n]
  rw [hth]
  exact mellin_theta_eq_lam_on P κ pkg hB s hs

/-! ## The converse -/

/-- **THE CONVERSE MECHANISM (Hecke–Weil, carrier register).**  A complete analytic
package — entire `lam`, functional equation, chart identification — together with the
classical strip data (one line integrability, horizontal decay in the strip: the
Phragmén–Lindelöf consequences of bounded vertical strips) forces the pointwise theta
reflection of the prescribed readouts, at every rank and every packaged chart kernel. -/
theorem weil_converse_reflection (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n) (κ : MellinKernel)
    (hKc : ContinuousOn κ.K (Set.Ioi 0))
    (ε : ℂ)
    (pkg : KNicePackage (coefficientArithmetic P.a) κ.G (max κ.B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max κ.B0 ((P.A : ℝ) + 1) < σ)
    (hline : Integrable (fun t : ℝ => pkg.lam ((σ : ℂ) + t * I)))
    (M : ℝ → ℝ)
    (hM : ∀ T : ℝ, ∀ u ∈ Set.Icc (1 - σ) σ, ‖pkg.lam ((u : ℂ) + T * I)‖ ≤ M |T|)
    (hM0 : Tendsto M atTop (𝓝 0)) :
    ∀ y : ℝ, 0 < y →
      CriticalLinePhasor.CarrierTheta.theta P.a κ.K y
        = ε * ((y : ℂ)⁻¹ *
            CriticalLinePhasor.CarrierTheta.theta P.adual κ.K (1 / y)) := by
  intro y hy
  have hB0σ : κ.B0 < σ := lt_of_le_of_lt (le_max_left _ _) hσ
  have hAσ : (P.A : ℝ) + 1 < σ := lt_of_le_of_lt (le_max_right _ _) hσ
  have hA1 : (1 : ℝ) ≤ (P.A : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (P.A : ℝ) := Nat.cast_nonneg _
    linarith
  have hσ1 : 1 - σ ≤ σ := by
    have h1B : (1 : ℝ) ≤ max κ.B0 ((P.A : ℝ) + 1) := le_trans hA1 (le_max_right _ _)
    linarith [lt_of_le_of_lt h1B hσ]
  -- the coefficient bounds in engine form
  have haP : ∀ n : ℕ, ‖P.a n‖ ≤ (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ ((P.A : ℝ))) := by
    intro n
    rw [one_mul, Real.rpow_natCast]
    exact P.a_bound n
  have haD : ∀ n : ℕ, ‖P.adual n‖ ≤ (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ ((P.A : ℝ))) := by
    intro n
    rw [one_mul, Real.rpow_natCast]
    exact P.adual_bound n
  have hAnn : (0 : ℝ) ≤ (P.A : ℝ) := Nat.cast_nonneg _
  -- Mellin convergence of both banks on the σ-line
  have hgσ := κ.hK ((σ : ℝ) : ℂ) (by simpa using hB0σ)
  have hconvP := CriticalLinePhasor.CarrierTheta.theta_hasMellin_of_polynomial
    P.a κ.K ((σ : ℝ) : ℂ) 1 (P.A : ℝ) hgσ.1 haP (by simpa using hAσ)
  have hconvD := CriticalLinePhasor.CarrierTheta.theta_hasMellin_of_polynomial
    P.adual κ.K ((σ : ℝ) : ℂ) 1 (P.A : ℝ) hgσ.1 haD (by simpa using hAσ)
  -- continuity of both banks on the positive ray
  have hcontP : ∀ x : ℝ, 0 < x →
      ContinuousAt (CriticalLinePhasor.CarrierTheta.theta P.a κ.K) x := fun x hx =>
    CriticalLinePhasor.CarrierTheta.theta_continuousAt_of_polynomial
      P.a κ.K 1 (P.A : ℝ) zero_le_one hAnn haP hKc (κ.hrapid _) hx
  have hcontD : ∀ x : ℝ, 0 < x →
      ContinuousAt (CriticalLinePhasor.CarrierTheta.theta P.adual κ.K) x := fun x hx =>
    CriticalLinePhasor.CarrierTheta.theta_continuousAt_of_polynomial
      P.adual κ.K 1 (P.A : ℝ) zero_le_one hAnn haD hKc (κ.hrapid _) hx
  -- the σ-line values of both Mellin transforms are lam
  have hlineP : ∀ t : ℝ,
      mellin (CriticalLinePhasor.CarrierTheta.theta P.a κ.K) ((σ : ℂ) + t * I)
        = pkg.lam ((σ : ℂ) + t * I) := fun t =>
    mellin_theta_eq_lam_on P κ pkg le_rfl _ (by simpa using hσ)
  have hlineD : ∀ t : ℝ,
      mellin (CriticalLinePhasor.CarrierTheta.theta P.adual κ.K) ((σ : ℂ) + t * I)
        = pkg.lam ((σ : ℂ) + t * I) := fun t =>
    mellin_theta_dual_eq_lam_on P hdual κ pkg le_rfl _ (by simpa using hσ)
  -- vertical integrability of both Mellin transforms on the σ-line
  have hfunP : (fun t : ℝ =>
      mellin (CriticalLinePhasor.CarrierTheta.theta P.a κ.K) ((σ : ℂ) + t * I))
      = fun t : ℝ => pkg.lam ((σ : ℂ) + t * I) := funext fun t => hlineP t
  have hfunD : (fun t : ℝ =>
      mellin (CriticalLinePhasor.CarrierTheta.theta P.adual κ.K) ((σ : ℂ) + t * I))
      = fun t : ℝ => pkg.lam ((σ : ℂ) + t * I) := funext fun t => hlineD t
  have hvertP : Complex.VerticalIntegrable
      (mellin (CriticalLinePhasor.CarrierTheta.theta P.a κ.K)) σ volume := by
    show Integrable (fun t : ℝ =>
      mellin (CriticalLinePhasor.CarrierTheta.theta P.a κ.K) ((σ : ℂ) + t * I)) volume
    rw [hfunP]
    exact hline
  have hvertD : Complex.VerticalIntegrable
      (mellin (CriticalLinePhasor.CarrierTheta.theta P.adual κ.K)) σ volume := by
    show Integrable (fun t : ℝ =>
      mellin (CriticalLinePhasor.CarrierTheta.theta P.adual κ.K) ((σ : ℂ) + t * I)) volume
    rw [hfunD]
    exact hline
  -- inversion for the primal bank at y
  have hinvP : CriticalLinePhasor.CarrierTheta.theta P.a κ.K y
      = mellinInv σ (mellin (CriticalLinePhasor.CarrierTheta.theta P.a κ.K)) y :=
    (mellinInv_mellin_eq σ _ hy hconvP.1 hvertP (hcontP y hy)).symm
  -- inversion for the dual bank at 1/y
  have h1y : (0 : ℝ) < 1 / y := by positivity
  have hinvD : CriticalLinePhasor.CarrierTheta.theta P.adual κ.K (1 / y)
      = mellinInv σ (mellin (CriticalLinePhasor.CarrierTheta.theta P.adual κ.K))
          (1 / y) :=
    (mellinInv_mellin_eq σ _ h1y hconvD.1 hvertD (hcontD _ h1y)).symm
  -- replace both mellin transforms by lam inside the inversion integrals
  have hswapP : mellinInv σ (mellin (CriticalLinePhasor.CarrierTheta.theta P.a κ.K)) y
      = mellinInv σ pkg.lam y := by
    unfold mellinInv
    congr 1
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun t => by
      dsimp only
      rw [hlineP t])
  have hswapD : mellinInv σ
      (mellin (CriticalLinePhasor.CarrierTheta.theta P.adual κ.K)) (1 / y)
      = mellinInv σ pkg.lam (1 / y) := by
    unfold mellinInv
    congr 1
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun t => by
      dsimp only
      rw [hlineD t])
  -- line integrability of lam at 1 - σ, from the FE and the σ-line
  have hlineFE : Integrable (fun t : ℝ => pkg.lam (((1 - σ : ℝ) : ℂ) + t * I)) := by
    have hneg : Integrable (fun t : ℝ => pkg.lam ((σ : ℂ) + (-t : ℝ) * I)) := by
      have h1 := hline.comp_neg
      simpa [Complex.ofReal_neg] using h1
    have heq : (fun t : ℝ => pkg.lam (((1 - σ : ℝ) : ℂ) + t * I))
        = fun t : ℝ => ε * pkg.lam ((σ : ℂ) + (-t : ℝ) * I) := by
      funext t
      have h := pkg.FE ((σ : ℂ) + (-t : ℝ) * I)
      rw [show (1 : ℂ) - ((σ : ℂ) + (-t : ℝ) * I) = ((1 - σ : ℝ) : ℂ) + t * I by
        push_cast; ring] at h
      exact h
    rw [heq]
    exact hneg.const_mul ε
  -- the contour shift
  have hshift : mellinInv ((1 : ℝ) - σ) pkg.lam y = mellinInv σ pkg.lam y :=
    mellinInv_line_shift pkg.lam pkg.entire (1 - σ) σ hσ1 hy hlineFE hline M hM hM0
  -- the FE reflection of the inversion lines
  have hreflect : mellinInv (1 - σ) pkg.lam y
      = ε * ((y : ℂ)⁻¹ * mellinInv σ pkg.lam (1 / y)) :=
    mellinInv_reflect pkg.lam ε pkg.FE σ hy
  -- assemble
  calc CriticalLinePhasor.CarrierTheta.theta P.a κ.K y
      = mellinInv σ pkg.lam y := by rw [hinvP, hswapP]
    _ = mellinInv (1 - σ) pkg.lam y := hshift.symm
    _ = ε * ((y : ℂ)⁻¹ * mellinInv σ pkg.lam (1 / y)) := hreflect
    _ = ε * ((y : ℂ)⁻¹ *
          CriticalLinePhasor.CarrierTheta.theta P.adual κ.K (1 / y)) := by
        rw [← hswapD, ← hinvD]

/-- **The converse in the mechanism's own interface**: the derived reflection is
exactly the `hrefl` hypothesis `mechanismK` consumes. -/
theorem weil_converse (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n) (κ : MellinKernel)
    (hKc : ContinuousOn κ.K (Set.Ioi 0))
    (ε : ℂ)
    (pkg : KNicePackage (coefficientArithmetic P.a) κ.G (max κ.B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max κ.B0 ((P.A : ℝ) + 1) < σ)
    (hline : Integrable (fun t : ℝ => pkg.lam ((σ : ℂ) + t * I)))
    (M : ℝ → ℝ)
    (hM : ∀ T : ℝ, ∀ u ∈ Set.Icc (1 - σ) σ, ‖pkg.lam ((u : ℂ) + T * I)‖ ≤ M |T|)
    (hM0 : Tendsto M atTop (𝓝 0)) :
    ∀ x : ℝ, 0 < x →
      coeffPrimal3DBankReadout P.a κ.K (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          coeffDual3DTransformedReadout P.adual κ.K (1 / x) := by
  intro x hx
  have h1x : (0 : ℝ) < 1 / x := by positivity
  rw [coeffPrimal3DBankReadout_eq_theta P.a κ.K h1x,
    coeffDual3DTransformedReadout_eq_theta_one_div P.adual κ.K h1x, one_div_one_div]
  have h := weil_converse_reflection P hdual κ hKc ε pkg σ hσ hline M hM hM0 (1 / x) h1x
  rw [h, one_div_one_div]
  have hcast1 : (((1 / x : ℝ)) : ℂ)⁻¹ = ((x : ℝ) : ℂ) := by
    push_cast
    rw [one_div, inv_inv]
  have hcast2 : ((x ^ (1 : ℝ) : ℝ) : ℂ) = ((x : ℝ) : ℂ) := by
    rw [Real.rpow_one]
  rw [hcast1, hcast2, smul_eq_mul]
  ring

/-- **The ring closed**: the package `mechanismK` builds from the derived reflection
has the same continuation as the input package — identity and package are the same
data, in both directions. -/
theorem weil_converse_ring (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n) (κ : MellinKernel)
    (hKc : ContinuousOn κ.K (Set.Ioi 0))
    (ε : ℂ) (hε : ε ≠ 0)
    (pkg : KNicePackage (coefficientArithmetic P.a) κ.G (max κ.B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max κ.B0 ((P.A : ℝ) + 1) < σ)
    (hline : Integrable (fun t : ℝ => pkg.lam ((σ : ℂ) + t * I)))
    (M : ℝ → ℝ)
    (hM : ∀ T : ℝ, ∀ u ∈ Set.Icc (1 - σ) σ, ‖pkg.lam ((u : ℂ) + T * I)‖ ≤ M |T|)
    (hM0 : Tendsto M atTop (𝓝 0)) :
    (mechanismK P hdual κ ε hε
      (weil_converse P hdual κ hKc ε pkg σ hσ hline M hM hM0)).lam = pkg.lam :=
  KNicePackage.unique _ pkg

end CriticalLinePhasor.WeilConverse

#print axioms CriticalLinePhasor.WeilConverse.vertical_line_shift
#print axioms CriticalLinePhasor.WeilConverse.mellinInv_line_shift
#print axioms CriticalLinePhasor.WeilConverse.mellinInv_reflect
#print axioms CriticalLinePhasor.WeilConverse.mellin_theta_eq_lam_on
#print axioms CriticalLinePhasor.WeilConverse.weil_converse_reflection
#print axioms CriticalLinePhasor.WeilConverse.weil_converse
#print axioms CriticalLinePhasor.WeilConverse.weil_converse_ring
