import RequestProject.MaassIdentification

/-!
# Obstruction detection at the ring: the pointwise identity is a pole detector

The compiled ring (mechanism ⟺ converse) turns the pointwise theta identity into an
obstruction detector, both directions typed:

* `reflection_failure_obstructs_gammaC` — **soundness** (converse contrapositive): a
  single pointwise failure of the theta identity obstructs *every* BV-package at
  every root number — no entire continuation with the functional equation and
  bounded strips exists;
* `unitSurface` / `zeta_no_package` — **the pole obstruction, compiled**: the unit
  (`ζ`-) surface admits no entire package at any `Γℂ` chart — the `ζ`-pole collides
  with entirety along the ray (the `PoleDetection` ray-limit argument at the
  surface ring);
* `zeta_reflection_fails` — **detection** (mechanism contrapositive): therefore the
  unit surface's theta identity *fails pointwise* — the pole is detected by the
  carrier readouts alone, with no L-function evaluated;
* `detection_dichotomy` — every self-dual surface at the `Γℂ` chart either
  satisfies the pointwise identity, or admits no BV-package: the detector is
  complete.

This upgrades the beyond-endoscopy demo from the representation bank to the
coefficient surface: the trivial channel's pole is equivalent to a pointwise
failure of the reflection, at the level where every compiled bank lives.  No
`axiom`, no `sorry`.
-/

open Real Complex Filter Topology MeasureTheory

namespace CriticalLinePhasor.ObstructionDetection

open CriticalLinePhasor.RamifiedMechanism CriticalLinePhasor.PhragmenBV
open CriticalLinePhasor.WeilConverse CriticalLinePhasor.CarrierTheta

/-! ## The unit surface and its `ζ`-identification -/

/-- The unit surface: the `ζ`-bank. -/
noncomputable def unitSurface : CoefficientSurface where
  a := fun _ => 1
  adual := fun _ => 1
  A := 0
  a_bound := fun n => by simp
  adual_bound := fun n => by simp

theorem unitSurface_dual : ∀ n : ℕ, unitSurface.adual n = unitSurface.a n :=
  fun _ => rfl

/-- The unit surface's Dirichlet readout is `ζ` on the chart half-plane. -/
theorem unitSurface_LSeries {s : ℂ} (hs : 1 < s.re) :
    LSeries (⇑(coefficientArithmetic unitSurface.a)) s = riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs]
  apply LSeries_congr
  intro n hn
  simp [coefficientArithmetic, unitSurface, hn]

/-- `Γℂ` is nonvanishing on the right half-plane. -/
theorem gammaC_ne_zero {s : ℂ} (hs : 0 < s.re) : Complex.Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_
  · rw [Complex.cpow_def_of_ne_zero h2pi]
    exact Complex.exp_ne_zero _
  · exact Complex.Gamma_ne_zero_of_re_pos hs

/-- The `Γℂ` chart multiplier evaluated. -/
theorem gammaCKernel_G_eq (μ : ℂ) (hμ : 0 ≤ μ.re) (s : ℂ) :
    (gammaCKernel μ hμ).G s = Complex.Gammaℂ (s + μ) := by
  show ((List.map (fun dlt => Complex.Gammaℝ (s + dlt)) []).prod) *
    ((List.map (fun m => Complex.Gammaℂ (s + m)) [μ]).prod)
    = Complex.Gammaℂ (s + μ)
  simp

/-! ## The pole obstruction -/

/-- **The pole obstructs the package**: the unit surface admits no entire package at
any `Γℂ` chart — the `ζ`-pole collides with entirety along the ray. -/
theorem zeta_no_package (μ : ℂ) (hμ : 0 ≤ μ.re) (ε : ℂ)
    (pkg : KNicePackage (coefficientArithmetic unitSurface.a) (gammaCKernel μ hμ).G
      (max (gammaCKernel μ hμ).B0 ((unitSurface.A : ℝ) + 1)) ε) : False := by
  have hbar : max (gammaCKernel μ hμ).B0 ((unitSurface.A : ℝ) + 1) = 1 := by
    show max (0 : ℝ) (((0 : ℕ) : ℝ) + 1) = 1
    norm_num
  -- the ray `s = 1 + t`, `t → 0⁺`
  have hA : Tendsto (fun t : ℝ => ((1 + t : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h1 : Tendsto (fun t : ℝ => (1 + t : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hc : Continuous (fun t : ℝ => (1 + t : ℝ)) := by continuity
      have h2 : Tendsto (fun t : ℝ => (1 + t : ℝ)) (𝓝 (0 : ℝ)) (𝓝 1) := by
        simpa using hc.tendsto 0
      exact h2.mono_left nhdsWithin_le_nhds
    have h3 := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp h1
    simpa [Function.comp_def] using h3
  have hAne : Tendsto (fun t : ℝ => ((1 + t : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hA ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcontra
    have := congrArg Complex.re hcontra
    simp only [Complex.ofReal_re, Complex.one_re] at this
    linarith
  -- the identification on the ray
  have hEq : ∀ t : ℝ, 0 < t →
      pkg.lam ((1 + t : ℝ) : ℂ) = Complex.Gammaℂ (((1 + t : ℝ) : ℂ) + μ) *
        riemannZeta ((1 + t : ℝ) : ℂ) := by
    intro t ht
    have hre : (((1 + t : ℝ) : ℂ)).re = 1 + t := by
      simp
    have hgt : max (gammaCKernel μ hμ).B0 ((unitSurface.A : ℝ) + 1)
        < (((1 + t : ℝ) : ℂ)).re := by
      rw [hbar, hre]
      linarith
    rw [pkg.chart _ hgt, gammaCKernel_G_eq,
      unitSurface_LSeries (by rw [hre]; linarith)]
  -- limit one: entirety kills `(s-1)·Λ`
  have hL1 : Tendsto (fun t : ℝ => ((((1 + t : ℝ) : ℂ)) - 1) *
      pkg.lam ((1 + t : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h₁ : Tendsto (fun t : ℝ => ((((1 + t : ℝ) : ℂ)) - 1)) (𝓝[>] (0 : ℝ))
        (𝓝 0) := by
      have := hA.sub_const 1
      simpa using this
    have h₂ : Tendsto (fun t : ℝ => pkg.lam ((1 + t : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
        (𝓝 (pkg.lam 1)) := (pkg.entire.continuous.tendsto 1).comp hA
    simpa using h₁.mul h₂
  -- limit two: the residue keeps `(s-1)·Γℂ·ζ` away from zero
  have hres : Tendsto (fun t : ℝ =>
      ((((1 + t : ℝ) : ℂ)) - 1) * riemannZeta ((1 + t : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := riemannZeta_residue_one.comp hAne
  have hGcont : Tendsto (fun t : ℝ => Complex.Gammaℂ (((1 + t : ℝ) : ℂ) + μ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Complex.Gammaℂ (1 + μ))) := by
    have hGC : ContinuousAt Complex.Gammaℂ (1 + μ) := by
      have hfun : Complex.Gammaℂ = fun s : ℂ =>
          2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s :=
        funext fun s => Complex.Gammaℂ_def s
      rw [hfun]
      have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
        simp [Real.pi_ne_zero]
      refine ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) ?_
      · exact ((differentiable_neg.const_cpow (Or.inl h2pi)).continuous).continuousAt
      · refine (Complex.differentiableAt_Gamma _ fun m => ?_).continuousAt
        intro hcontra
        have := congrArg Complex.re hcontra
        simp only [Complex.add_re, Complex.one_re, Complex.neg_re,
          Complex.natCast_re] at this
        have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
    have harg : Tendsto (fun t : ℝ => ((1 + t : ℝ) : ℂ) + μ) (𝓝[>] (0 : ℝ))
        (𝓝 (1 + μ)) := by
      have := hA.add_const μ
      simpa using this
    exact hGC.tendsto.comp harg
  have hL2 : Tendsto (fun t : ℝ => ((((1 + t : ℝ) : ℂ)) - 1) *
      pkg.lam ((1 + t : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.Gammaℂ (1 + μ))) := by
    have hmul := hGcont.mul hres
    have hmul' : Tendsto (fun t : ℝ =>
        Complex.Gammaℂ (((1 + t : ℝ) : ℂ) + μ) *
          (((((1 + t : ℝ) : ℂ)) - 1) * riemannZeta ((1 + t : ℝ) : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (Complex.Gammaℂ (1 + μ))) := by
      simpa using hmul
    refine hmul'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [hEq t ht0]
    ring
  have hzero : Complex.Gammaℂ (1 + μ) = 0 :=
    (tendsto_nhds_unique hL2 hL1)
  exact gammaC_ne_zero (by
    simp only [Complex.add_re, Complex.one_re]
    linarith) hzero

/-! ## The detector, both directions -/

/-- **Detection** (mechanism contrapositive): the `ζ`-pole is detected by the
carrier readouts alone — the unit surface's pointwise theta identity fails, at
every `Γℂ` chart and every root number, with no L-function evaluated. -/
theorem zeta_reflection_fails (μ : ℂ) (hμ : 0 ≤ μ.re) (ε : ℂ) (hε : ε ≠ 0) :
    ¬(∀ x : ℝ, 0 < x →
      coeffPrimal3DBankReadout unitSurface.a (gammaCKernel μ hμ).K (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          coeffDual3DTransformedReadout unitSurface.adual (gammaCKernel μ hμ).K
            (1 / x)) :=
  fun hrefl => zeta_no_package μ hμ ε
    (mechanismK unitSurface unitSurface_dual (gammaCKernel μ hμ) ε hε hrefl)

/-- **Soundness** (converse contrapositive): one pointwise failure of the theta
identity obstructs every BV-package at the `Γℂ` chart. -/
theorem reflection_failure_obstructs_gammaC (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n) (μ : ℂ) (hμ : 0 ≤ μ.re) (ε : ℂ)
    (x₀ : ℝ) (hx₀ : 0 < x₀)
    (hfail : ¬(coeffPrimal3DBankReadout P.a (gammaCKernel μ hμ).K (1 / x₀) =
      (ε * ((x₀ ^ (1 : ℝ) : ℝ) : ℂ)) •
        coeffDual3DTransformedReadout P.adual (gammaCKernel μ hμ).K (1 / x₀))) :
    ∀ (pkg : KNicePackage (coefficientArithmetic P.a) (gammaCKernel μ hμ).G
        (max (gammaCKernel μ hμ).B0 ((P.A : ℝ) + 1)) ε)
      (σ : ℝ), max (gammaCKernel μ hμ).B0 ((P.A : ℝ) + 1) < σ → ∀ C : ℝ,
      ¬(∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C) :=
  fun pkg σ hσ C hBV => hfail
    (weil_converse_of_BV_gammaC P hdual μ hμ ε pkg σ hσ C hBV x₀ hx₀)


/-- **The dichotomy — the detector is complete**: every self-dual surface at the
`Γℂ` chart either satisfies the pointwise theta identity everywhere, or admits no
BV-package. -/
theorem detection_dichotomy (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n) (μ : ℂ) (hμ : 0 ≤ μ.re) (ε : ℂ) :
    (∀ x : ℝ, 0 < x →
      coeffPrimal3DBankReadout P.a (gammaCKernel μ hμ).K (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          coeffDual3DTransformedReadout P.adual (gammaCKernel μ hμ).K (1 / x)) ∨
    (∀ (pkg : KNicePackage (coefficientArithmetic P.a) (gammaCKernel μ hμ).G
        (max (gammaCKernel μ hμ).B0 ((P.A : ℝ) + 1)) ε)
      (σ : ℝ), max (gammaCKernel μ hμ).B0 ((P.A : ℝ) + 1) < σ → ∀ C : ℝ,
      ¬(∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C)) := by
  by_cases h : ∀ x : ℝ, 0 < x →
      coeffPrimal3DBankReadout P.a (gammaCKernel μ hμ).K (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          coeffDual3DTransformedReadout P.adual (gammaCKernel μ hμ).K (1 / x)
  · exact Or.inl h
  · refine Or.inr fun pkg σ hσ C hBV => ?_
    exact h (weil_converse_of_BV_gammaC P hdual μ hμ ε pkg σ hσ C hBV)

end CriticalLinePhasor.ObstructionDetection

#print axioms CriticalLinePhasor.ObstructionDetection.zeta_no_package
#print axioms CriticalLinePhasor.ObstructionDetection.zeta_reflection_fails
#print axioms CriticalLinePhasor.ObstructionDetection.reflection_failure_obstructs_gammaC
#print axioms CriticalLinePhasor.ObstructionDetection.detection_dichotomy
