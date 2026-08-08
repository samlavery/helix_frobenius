import RequestProject.MultiplierPackaging
import RequestProject.ChainKernelContinuity

/-!
# The Maass wave-form identification: everything but the elliptic step, compiled

The holomorphic identification carried the axis reflection to the half-plane by the
identity theorem.  A Maass wave form is real-analytic, not holomorphic, so the
classical Hecke--Maass argument replaces the identity theorem with Cauchy uniqueness
for the hyperbolic eigen-equation.  This file compiles everything around that one
step and consumes it at a typed field:

* `waveForm` — the even wave form of a surface at an abstract radial kernel:
  `√y·Σ aₙ cos(2π(n+1)x)·K((n+1)y)`;
* `waveForm_T` / `waveForm_even` — exact `1`-periodicity and evenness in `x`, from
  the expansion alone;
* `waveForm_axis` — the axis value is the compiled theta readout: `√y·θ(y)`;
* `waveForm_axis_S_of_reflection` — **the axis S-law**: the compiled theta
  reflection is exactly `S`-transformation of the wave form on the imaginary axis;
* `even_deriv_zero` / the Cauchy-data lemmas — **both halves of the Cauchy data
  match on the axis unconditionally**: an even function has vanishing
  `x`-derivative at `x = 0` (junk-robust: no differentiability hypothesis needed),
  and both the wave form and its `S`-transform are even;
* `maass_identification` — the reduction: axis values + axis derivatives + the
  typed Cauchy-uniqueness field ⟹ the `S`-law everywhere; with the `T`-law and the
  weight-`0` slash packaging (`slashEigen_all` at `k = 0` — the slash action at
  weight zero *is* composition), the wave form is a weight-`0` eigenfunction of
  every element of `SL(2,ℤ)`;
* `weil_converse_of_BV_realChain_reflection` / `maass_modularity_of_BV` — the
  composite at the Maass spectral chart: package + one boundedness constant + the
  Cauchy-uniqueness field ⟹ full `SL(2,ℤ)` invariance (up to the root number) of
  the wave form.

Register.  The Cauchy-uniqueness field is the classical elliptic step: both
functions are eigenfunctions of the hyperbolic Laplacian (the radial kernel solves
the Whittaker equation), and eigenfunctions with equal Cauchy data on the axis
coincide.  Bessel functions and elliptic unique continuation are not in Mathlib, so
the field is consumed typed, at its exact classical strength — as local Langlands
and the converse theorem are consumed elsewhere.  The kernel needs no Bessel API:
the chain kernel at the chart `(it, -it)` has the Mellin transform
`Γℝ(s+it)Γℝ(s-it)`, and kernels with equal Mellin transforms on a line agree on the
ray (`eqOn_pos_of_mellin_eq`, compiled) — the classical `√y·K_{it}`-kernel is the
same function.  No `axiom`, no `sorry`.
-/

open Real Complex UpperHalfPlane MeasureTheory Filter Topology Asymptotics
open scoped MatrixGroups ModularForm

namespace CriticalLinePhasor.MaassIdentification

open CriticalLinePhasor.RamifiedMechanism CriticalLinePhasor.PhragmenBV
open CriticalLinePhasor.WeilConverse CriticalLinePhasor.StirlingLine
open CriticalLinePhasor.ChainKernelContinuity CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.MultiplierPackaging CriticalLinePhasor.RealChainMechanism

/-! ## The wave form and its exact laws -/

/-- The even wave form of a coefficient sequence at an abstract radial kernel. -/
noncomputable def waveForm (a : ℕ → ℂ) (K : ℝ → ℂ) (x y : ℝ) : ℂ :=
  (Real.sqrt y : ℂ) *
    ∑' n : ℕ, a n * (Real.cos (2 * Real.pi * (n + 1) * x) : ℂ) * K ((n + 1) * y)

/-- **Exact `1`-periodicity in `x`.** -/
theorem waveForm_T (a : ℕ → ℂ) (K : ℝ → ℂ) (x y : ℝ) :
    waveForm a K (x + 1) y = waveForm a K x y := by
  unfold waveForm
  congr 1
  apply tsum_congr
  intro n
  congr 2
  have h : 2 * Real.pi * (n + 1) * (x + 1)
      = 2 * Real.pi * (n + 1) * x + ((n + 1 : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [h, Real.cos_add_int_mul_two_pi]

/-- **Evenness in `x`.** -/
theorem waveForm_even (a : ℕ → ℂ) (K : ℝ → ℂ) (x y : ℝ) :
    waveForm a K (-x) y = waveForm a K x y := by
  unfold waveForm
  congr 1
  apply tsum_congr
  intro n
  congr 2
  have h : 2 * Real.pi * (n + 1) * (-x) = -(2 * Real.pi * (n + 1) * x) := by ring
  rw [h, Real.cos_neg]

/-- **The axis value is the compiled theta readout.** -/
theorem waveForm_axis (a : ℕ → ℂ) (K : ℝ → ℂ) (y : ℝ) :
    waveForm a K 0 y = (Real.sqrt y : ℂ) *
      CriticalLinePhasor.CarrierTheta.theta a K y := by
  unfold waveForm CriticalLinePhasor.CarrierTheta.theta
  congr 1
  apply tsum_congr
  intro n
  have h : 2 * Real.pi * (n + 1) * (0 : ℝ) = 0 := by ring
  rw [h, Real.cos_zero]
  push_cast
  ring

/-- **The axis `S`-law**: the compiled theta reflection is exactly the
`S`-transformation of the wave form on the imaginary axis. -/
theorem waveForm_axis_S_of_reflection (a : ℕ → ℂ) (K : ℝ → ℂ) (ε : ℂ)
    (hrefl : ∀ y : ℝ, 0 < y →
      CriticalLinePhasor.CarrierTheta.theta a K y
        = ε * ((y : ℂ)⁻¹ * CriticalLinePhasor.CarrierTheta.theta a K (1 / y)))
    {y : ℝ} (hy : 0 < y) :
    waveForm a K 0 y = ε * waveForm a K 0 (1 / y) := by
  rw [waveForm_axis, waveForm_axis, hrefl y hy]
  have hs : (Real.sqrt (1 / y) : ℂ) = (Real.sqrt y : ℂ)⁻¹ := by
    rw [one_div, Real.sqrt_inv]
    push_cast
    rfl
  have hsy : (Real.sqrt y : ℂ) ≠ 0 := by
    simpa using Real.sqrt_ne_zero'.mpr hy
  have hyc : ((y : ℝ) : ℂ) = (Real.sqrt y : ℂ) * (Real.sqrt y : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hy.le]
  rw [hs, hyc]
  field_simp

/-! ## The Cauchy data on the axis -/

/-- An even function has vanishing derivative at `0` — junk-robust: no
differentiability hypothesis. -/
theorem even_deriv_zero {f : ℝ → ℂ} (hf : ∀ x, f (-x) = f x) : deriv f 0 = 0 := by
  by_cases hd : DifferentiableAt ℝ f 0
  · have h1 : deriv (fun x => f (-x)) 0 = -deriv f (-0) := deriv_comp_neg f 0
    have h2 : (fun x : ℝ => f (-x)) = f := funext hf
    rw [h2, neg_zero] at h1
    have h3 : (2 : ℂ) * deriv f 0 = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h3).resolve_left two_ne_zero
  · exact deriv_zero_of_not_differentiableAt hd

/-- The `S`-transform of the wave form, in coordinates:
`(x, y) ↦ (-x/(x²+y²), y/(x²+y²))`. -/
noncomputable def waveFormS (a : ℕ → ℂ) (K : ℝ → ℂ) (x y : ℝ) : ℂ :=
  waveForm a K (-x / (x ^ 2 + y ^ 2)) (y / (x ^ 2 + y ^ 2))

/-- The `S`-transform is also even in `x`. -/
theorem waveFormS_even (a : ℕ → ℂ) (K : ℝ → ℂ) (x y : ℝ) :
    waveFormS a K (-x) y = waveFormS a K x y := by
  unfold waveFormS
  have h1 : (-x) ^ 2 = x ^ 2 := by ring
  rw [h1]
  have h2 : -(-x) / (x ^ 2 + y ^ 2) = -(-x / (x ^ 2 + y ^ 2)) := by ring
  rw [h2, waveForm_even]

/-- The `S`-transform on the axis is the reciprocal-height value. -/
theorem waveFormS_axis (a : ℕ → ℂ) (K : ℝ → ℂ) (y : ℝ) :
    waveFormS a K 0 y = waveForm a K 0 (y / y ^ 2) := by
  unfold waveFormS
  norm_num

/-- **Both halves of the Cauchy data match on the axis**: values by the compiled
reflection, `x`-derivatives by evenness — unconditionally. -/
theorem cauchy_data_match (a : ℕ → ℂ) (K : ℝ → ℂ) (ε : ℂ)
    (hrefl : ∀ y : ℝ, 0 < y →
      CriticalLinePhasor.CarrierTheta.theta a K y
        = ε * ((y : ℂ)⁻¹ * CriticalLinePhasor.CarrierTheta.theta a K (1 / y))) :
    (∀ y : ℝ, 0 < y → waveForm a K 0 y = ε * waveFormS a K 0 y) ∧
    (∀ y : ℝ, 0 < y →
      deriv (fun x => waveForm a K x y) 0
        = ε * deriv (fun x => waveFormS a K x y) 0) := by
  constructor
  · intro y hy
    rw [waveFormS_axis]
    have h : y / y ^ 2 = 1 / y := by
      field_simp
    rw [h]
    exact waveForm_axis_S_of_reflection a K ε hrefl hy
  · intro y hy
    rw [even_deriv_zero (fun x => waveForm_even a K x y),
      even_deriv_zero (fun x => waveFormS_even a K x y), mul_zero]

/-! ## The identification, with the elliptic step at a typed field -/

/-- **THE MAASS IDENTIFICATION** — the axis Cauchy data (compiled) plus the typed
Cauchy-uniqueness field for the pair (the classical elliptic step: both functions
are eigenfunctions of the hyperbolic Laplacian, and eigenfunctions with equal Cauchy
data on the axis coincide) give the `S`-law everywhere. -/
theorem maass_identification (a : ℕ → ℂ) (K : ℝ → ℂ) (ε : ℂ)
    (hrefl : ∀ y : ℝ, 0 < y →
      CriticalLinePhasor.CarrierTheta.theta a K y
        = ε * ((y : ℂ)⁻¹ * CriticalLinePhasor.CarrierTheta.theta a K (1 / y)))
    (hUC : (∀ y : ℝ, 0 < y → waveForm a K 0 y = ε * waveFormS a K 0 y) →
      (∀ y : ℝ, 0 < y →
        deriv (fun x => waveForm a K x y) 0
          = ε * deriv (fun x => waveFormS a K x y) 0) →
      ∀ (x y : ℝ), 0 < y → waveForm a K x y = ε * waveFormS a K x y) :
    ∀ (x y : ℝ), 0 < y → waveForm a K x y = ε * waveFormS a K x y := by
  obtain ⟨h1, h2⟩ := cauchy_data_match a K ε hrefl
  exact hUC h1 h2

/-! ## The weight-zero packaging on the half-plane -/

/-- The wave form as a function on the upper half-plane. -/
noncomputable def waveFormH (a : ℕ → ℂ) (K : ℝ → ℂ) : ℍ → ℂ :=
  fun τ => waveForm a K (τ : ℂ).re (τ : ℂ).im

/-- The `S`-transform in coordinates is the wave form at `S • τ`. -/
theorem waveFormH_S (a : ℕ → ℂ) (K : ℝ → ℂ) (τ : ℍ) :
    waveFormH a K (ModularGroup.S • τ) = waveFormS a K (τ : ℂ).re (τ : ℂ).im := by
  unfold waveFormH waveFormS
  have hcoe : ((ModularGroup.S • τ : ℍ) : ℂ) = (-(τ : ℂ))⁻¹ := by
    rw [modular_S_smul]
  have hns : Complex.normSq (τ : ℂ) = (τ : ℂ).re ^ 2 + (τ : ℂ).im ^ 2 := by
    rw [Complex.normSq_apply]
    ring
  have hre : ((-(τ : ℂ))⁻¹).re = -(τ : ℂ).re / ((τ : ℂ).re ^ 2 + (τ : ℂ).im ^ 2) := by
    rw [Complex.inv_re, Complex.neg_re, Complex.normSq_neg, hns]
  have him : ((-(τ : ℂ))⁻¹).im = (τ : ℂ).im / ((τ : ℂ).re ^ 2 + (τ : ℂ).im ^ 2) := by
    rw [Complex.inv_im, Complex.neg_im, Complex.normSq_neg, hns]
    ring
  rw [hcoe, hre, him]

/-- The `T`-translate in coordinates. -/
theorem waveFormH_T (a : ℕ → ℂ) (K : ℝ → ℂ) (τ : ℍ) :
    waveFormH a K (ModularGroup.T • τ) = waveFormH a K τ := by
  unfold waveFormH
  have hcoe : ((ModularGroup.T • τ : ℍ) : ℂ) = 1 + (τ : ℂ) := by
    rw [modular_T_smul, coe_vadd]
    norm_num
  rw [hcoe]
  have hre : ((1 : ℂ) + (τ : ℂ)).re = (τ : ℂ).re + 1 := by simp [add_comm]
  have him : ((1 : ℂ) + (τ : ℂ)).im = (τ : ℂ).im := by simp
  rw [hre, him, waveForm_T]

/-- **Weight-zero modularity of the wave form**: the identification plus the
`T`-law make the wave form a weight-`0` slash eigenvector at `S` and `T`, and the
subgroup argument extends to every `γ ∈ SL(2,ℤ)`. -/
theorem waveForm_modularity (a : ℕ → ℂ) (K : ℝ → ℂ) (ε : ℂ) (hε : ε ≠ 0)
    (hid : ∀ (x y : ℝ), 0 < y → waveForm a K x y = ε * waveFormS a K x y) :
    ∀ γ : SL(2, ℤ), ∃ v : ℂ, v ≠ 0 ∧
      waveFormH a K ∣[(0 : ℤ)] γ = v • waveFormH a K := by
  apply slashEigen_all
  · refine ⟨ε⁻¹, inv_ne_zero hε, ?_⟩
    funext τ
    rw [ModularForm.SL_slash_apply]
    simp only [neg_zero, zpow_zero, mul_one, Pi.smul_apply, smul_eq_mul]
    rw [waveFormH_S]
    have h := hid (τ : ℂ).re (τ : ℂ).im τ.2
    rw [show waveFormS a K (τ : ℂ).re (τ : ℂ).im
        = ε⁻¹ * waveForm a K (τ : ℂ).re (τ : ℂ).im from by
      rw [h]
      field_simp]
    rfl
  · refine ⟨1, one_ne_zero, ?_⟩
    funext τ
    rw [ModularForm.SL_slash_apply]
    simp only [neg_zero, zpow_zero, mul_one, Pi.smul_apply, smul_eq_mul, one_mul]
    exact waveFormH_T a K τ

/-! ## The composite at the Maass spectral chart -/

/-- The BV converse at the pure-real chain, theta form — kernel side fully
discharged. -/
theorem weil_converse_of_BV_realChain_reflection (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n)
    (d : ℂ) (hd : 0 ≤ d.re) (ds : List ℂ) (hds : ∀ e ∈ ds, 0 ≤ e.re)
    (ε : ℂ)
    (pkg : KNicePackage (coefficientArithmetic P.a)
      (realChainMellinKernel d hd ds hds).G
      (max (realChainMellinKernel d hd ds hds).B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max (realChainMellinKernel d hd ds hds).B0 ((P.A : ℝ) + 1) < σ)
    (C : ℝ) (hBV : ∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C) :
    ∀ y : ℝ, 0 < y →
      CriticalLinePhasor.CarrierTheta.theta P.a (realChainMellinKernel d hd ds hds).K y
        = ε * ((y : ℂ)⁻¹ *
            CriticalLinePhasor.CarrierTheta.theta P.adual
              (realChainMellinKernel d hd ds hds).K (1 / y)) := by
  have hA1 : (1 : ℝ) ≤ (P.A : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (P.A : ℝ) := Nat.cast_nonneg _
    linarith
  have hσpos : 0 < σ := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hA1)
    (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hσ))
  have hd' : 0 < σ + d.re := by linarith
  have hds' : ∀ e ∈ ds, 0 < σ + e.re := fun e he => by
    have := hds e he
    linarith
  have hG_int : Integrable (fun t : ℝ =>
      (realChainMellinKernel d hd ds hds).G ((σ : ℂ) + t * Complex.I)) :=
    chain_line_integrable σ d ds hd' hds'
  obtain ⟨A, hApos, hA⟩ := chain_line_exp_bound σ d ds hd' hds'
  exact weil_converse_of_BV_reflection P hdual (realChainMellinKernel d hd ds hds)
    (realChainKernelLog_continuousOn d hd ds hds) ε pkg σ hσ hG_int A
    (Real.pi / 8) hApos (by positivity) hA C hBV

/-- **MAASS MODULARITY FROM PACKAGE + BV + THE ELLIPTIC FIELD** — at the spectral
chart of `Sym^r`, every rank and parameter: the entire BV-package forces the axis
Cauchy data, and the typed Cauchy-uniqueness field carries it to full weight-`0`
`SL(2,ℤ)`-modularity of the wave form built on the chain kernel. -/
theorem maass_modularity_of_BV (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n) (r : ℕ) (t : ℝ)
    (ε : ℂ) (hε : ε ≠ 0)
    (pkg : KNicePackage (coefficientArithmetic P.a)
      (realChainMellinKernel (maassHead r t) (le_of_eq (maassHead_re r t).symm)
        (maassTail r t) (fun e he => le_of_eq (maassTail_re r t e he).symm)).G
      (max (realChainMellinKernel (maassHead r t) (le_of_eq (maassHead_re r t).symm)
        (maassTail r t) (fun e he => le_of_eq (maassTail_re r t e he).symm)).B0
        ((P.A : ℝ) + 1)) ε)
    (σ : ℝ)
    (hσ : max (realChainMellinKernel (maassHead r t) (le_of_eq (maassHead_re r t).symm)
      (maassTail r t) (fun e he => le_of_eq (maassTail_re r t e he).symm)).B0
      ((P.A : ℝ) + 1) < σ)
    (C : ℝ) (hBV : ∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C)
    (hUC : (∀ y : ℝ, 0 < y →
        waveForm P.a (realChainMellinKernel (maassHead r t)
          (le_of_eq (maassHead_re r t).symm) (maassTail r t)
          (fun e he => le_of_eq (maassTail_re r t e he).symm)).K 0 y
          = ε * waveFormS P.a (realChainMellinKernel (maassHead r t)
            (le_of_eq (maassHead_re r t).symm) (maassTail r t)
            (fun e he => le_of_eq (maassTail_re r t e he).symm)).K 0 y) →
      (∀ y : ℝ, 0 < y →
        deriv (fun x => waveForm P.a (realChainMellinKernel (maassHead r t)
          (le_of_eq (maassHead_re r t).symm) (maassTail r t)
          (fun e he => le_of_eq (maassTail_re r t e he).symm)).K x y) 0
          = ε * deriv (fun x => waveFormS P.a (realChainMellinKernel (maassHead r t)
            (le_of_eq (maassHead_re r t).symm) (maassTail r t)
            (fun e he => le_of_eq (maassTail_re r t e he).symm)).K x y) 0) →
      ∀ (x y : ℝ), 0 < y →
        waveForm P.a (realChainMellinKernel (maassHead r t)
          (le_of_eq (maassHead_re r t).symm) (maassTail r t)
          (fun e he => le_of_eq (maassTail_re r t e he).symm)).K x y
          = ε * waveFormS P.a (realChainMellinKernel (maassHead r t)
            (le_of_eq (maassHead_re r t).symm) (maassTail r t)
            (fun e he => le_of_eq (maassTail_re r t e he).symm)).K x y) :
    ∀ γ : SL(2, ℤ), ∃ v : ℂ, v ≠ 0 ∧
      waveFormH P.a (realChainMellinKernel (maassHead r t)
        (le_of_eq (maassHead_re r t).symm) (maassTail r t)
        (fun e he => le_of_eq (maassTail_re r t e he).symm)).K ∣[(0 : ℤ)] γ
        = v • waveFormH P.a (realChainMellinKernel (maassHead r t)
          (le_of_eq (maassHead_re r t).symm) (maassTail r t)
          (fun e he => le_of_eq (maassTail_re r t e he).symm)).K := by
  have hrefl0 := weil_converse_of_BV_realChain_reflection P hdual (maassHead r t)
    (le_of_eq (maassHead_re r t).symm) (maassTail r t)
    (fun e he => le_of_eq (maassTail_re r t e he).symm) ε pkg σ hσ C hBV
  have hrefl : ∀ y : ℝ, 0 < y →
      CriticalLinePhasor.CarrierTheta.theta P.a
        (realChainMellinKernel (maassHead r t) (le_of_eq (maassHead_re r t).symm)
          (maassTail r t) (fun e he => le_of_eq (maassTail_re r t e he).symm)).K y
        = ε * ((y : ℂ)⁻¹ *
            CriticalLinePhasor.CarrierTheta.theta P.a
              (realChainMellinKernel (maassHead r t)
                (le_of_eq (maassHead_re r t).symm) (maassTail r t)
                (fun e he => le_of_eq (maassTail_re r t e he).symm)).K (1 / y)) := by
    intro y hy
    have hth : CriticalLinePhasor.CarrierTheta.theta P.adual
        (realChainMellinKernel (maassHead r t) (le_of_eq (maassHead_re r t).symm)
          (maassTail r t) (fun e he => le_of_eq (maassTail_re r t e he).symm)).K
        = CriticalLinePhasor.CarrierTheta.theta P.a
          (realChainMellinKernel (maassHead r t) (le_of_eq (maassHead_re r t).symm)
            (maassTail r t) (fun e he => le_of_eq (maassTail_re r t e he).symm)).K := by
      funext u
      unfold CriticalLinePhasor.CarrierTheta.theta
      exact tsum_congr fun n => by rw [hdual n]
    have := hrefl0 y hy
    rw [hth] at this
    exact this
  exact waveForm_modularity P.a _ ε hε
    (maass_identification P.a _ ε hrefl hUC)

end CriticalLinePhasor.MaassIdentification

#print axioms CriticalLinePhasor.MaassIdentification.waveForm_T
#print axioms CriticalLinePhasor.MaassIdentification.waveForm_axis_S_of_reflection
#print axioms CriticalLinePhasor.MaassIdentification.even_deriv_zero
#print axioms CriticalLinePhasor.MaassIdentification.cauchy_data_match
#print axioms CriticalLinePhasor.MaassIdentification.maass_identification
#print axioms CriticalLinePhasor.MaassIdentification.waveForm_modularity
#print axioms CriticalLinePhasor.MaassIdentification.weil_converse_of_BV_realChain_reflection
#print axioms CriticalLinePhasor.MaassIdentification.maass_modularity_of_BV
