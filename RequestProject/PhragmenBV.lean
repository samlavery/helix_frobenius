import RequestProject.StirlingLineDischarge
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Phragmén–Lindelöf: the converse from boundedness alone

`weil_converse` consumes a strip-decay field.  Classically the converse theorem's
hypothesis is *boundedness in vertical strips*; the interior decay is a
Phragmén–Lindelöf consequence of boundedness plus the exponential decay on the two
boundary lines (which the Stirling discharge supplies).  This file compiles that step
and assembles the composite:

* `strip_exp_decay` — **the PL interpolation**: an entire function bounded on a
  closed vertical strip and exponentially decaying on its two boundary lines decays
  with the *same* constants throughout the strip (two multiplier applications of
  Mathlib's `PhragmenLindelof.vertical_strip`, one per half-plane of heights);
* `weil_converse_of_BV` — **the converse with the classical hypothesis set**: package
  + kernel line data + one boundedness constant on the strip ⟹ the theta
  reflection.  The decay field of `weil_converse` is derived, not assumed;
* `gammaCKernel` / `gammaClock_continuousOn` — the singleton-`Γℂ` chart kernel with
  its continuity compiled;
* `weil_converse_of_BV_realChain` / `weil_converse_of_BV_gammaC` — the composite at
  the two compiled kernel families, all kernel-side line data discharged from the
  house Stirling bound.  For the `Γℂ` kernel the remaining analytic inputs are
  exactly: the package and one `BV` constant — the classical Hecke hypothesis set.

No `axiom`, no `sorry`.
-/

open Real Complex Set Filter Topology MeasureTheory Asymptotics

namespace CriticalLinePhasor.PhragmenBV

open CriticalLinePhasor.GammaVertical CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.RamifiedMechanism CriticalLinePhasor.WeilConverse
open CriticalLinePhasor.StirlingLine CriticalLinePhasor.GlobalHelix

/-! ## The PL interpolation: boundary decay + boundedness ⟹ interior decay -/

/-- Norm of the vertical multiplier: `‖exp(∓k·I·z)‖ = e^{±k·im z}`. -/
theorem norm_exp_mul_I (k : ℝ) (z : ℂ) :
    ‖Complex.exp (-(k : ℂ) * I * z)‖ = Real.exp (k * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem norm_exp_mul_I' (k : ℝ) (z : ℂ) :
    ‖Complex.exp ((k : ℂ) * I * z)‖ = Real.exp (-(k * z.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- **The Phragmén–Lindelöf interpolation with decay.**  An entire function bounded
by `C` on the closed strip `a ≤ re ≤ b` and bounded by `A·e^{-k|t|}` on both
boundary lines satisfies the same decaying bound throughout the strip. -/
theorem strip_exp_decay (F : ℂ → ℂ) (hF : Differentiable ℂ F) (a b : ℝ) (hab : a < b)
    (C : ℝ) (hC : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖F z‖ ≤ C)
    (A k : ℝ) (hApos : 0 < A) (hk : 0 < k)
    (hla : ∀ t : ℝ, ‖F ((a : ℂ) + t * I)‖ ≤ A * Real.exp (-k * |t|))
    (hlb : ∀ t : ℝ, ‖F ((b : ℂ) + t * I)‖ ≤ A * Real.exp (-k * |t|)) :
    ∀ u ∈ Set.Icc a b, ∀ t : ℝ,
      ‖F ((u : ℂ) + t * I)‖ ≤ A * Real.exp (-k * |t|) := by
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC ((a : ℂ)) (by simp) (by simp; linarith))
  set c : ℝ := Real.pi / (2 * (b - a)) with hcdef
  have hcpos : 0 < c := by
    have := Real.pi_pos
    have hba : 0 < b - a := by linarith
    positivity
  have hclt : c < Real.pi / (b - a) := by
    have hba : 0 < b - a := by linarith
    rw [hcdef, div_lt_div_iff₀ (by positivity) hba]
    have := Real.pi_pos
    nlinarith
  -- the growth certificate, shared by both multipliers
  have hgrowth : ∀ (g : ℂ → ℂ),
      (∀ z : ℂ, a < z.re → z.re < b → ‖g z‖ ≤ C * Real.exp (k * |z.im|)) →
      ∃ c' < Real.pi / (b - a), ∃ B, g =O[Filter.comap (_root_.abs ∘ Complex.im) atTop ⊓
        Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (B * Real.exp (c' * |z.im|)) := by
    intro g hg
    refine ⟨c, hclt, k / c, ?_⟩
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    rw [Filter.eventually_inf_principal]
    refine Eventually.of_forall fun z hz => ?_
    simp only [Set.mem_preimage, Set.mem_Ioo] at hz
    have h1 : ‖g z‖ ≤ C * Real.exp (k * |z.im|) := hg z hz.1 hz.2
    have h2 : k * |z.im| ≤ (k / c) * Real.exp (c * |z.im|) := by
      have hx : c * |z.im| ≤ Real.exp (c * |z.im|) :=
        le_trans (by linarith [Real.add_one_le_exp (c * |z.im|)]) le_rfl
      calc k * |z.im| = (k / c) * (c * |z.im|) := by
            field_simp
        _ ≤ (k / c) * Real.exp (c * |z.im|) := by
            apply mul_le_mul_of_nonneg_left hx
            positivity
    calc ‖g z‖ ≤ C * Real.exp (k * |z.im|) := h1
      _ ≤ C * Real.exp ((k / c) * Real.exp (c * |z.im|)) := by
          apply mul_le_mul_of_nonneg_left _ hCnn
          exact Real.exp_le_exp.mpr h2
      _ ≤ C * ‖Real.exp ((k / c) * Real.exp (c * |z.im|))‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  intro u hu t
  -- multiplier for the upper heights
  have hup : ∀ t : ℝ, ‖F ((u : ℂ) + t * I)‖ ≤ A * Real.exp (-k * t) := by
    intro t'
    set g : ℂ → ℂ := fun z => F z * Complex.exp (-(k : ℂ) * I * z) with hgdef
    have hgz : ∀ z : ℂ, ‖g z‖ = ‖F z‖ * Real.exp (k * z.im) := by
      intro z
      rw [hgdef]
      dsimp only
      rw [norm_mul, norm_exp_mul_I]
    have hgd : Differentiable ℂ g :=
      hF.mul ((differentiable_const _).mul differentiable_id).cexp
    have hga : ∀ z : ℂ, z.re = a → ‖g z‖ ≤ A := by
      intro z hz
      rw [hgz]
      have hzeq : z = (a : ℂ) + z.im * I := by
        rw [← hz]
        exact (Complex.re_add_im z).symm
      have h1 : ‖F z‖ ≤ A * Real.exp (-k * |z.im|) := by
        have := hla z.im
        rwa [← hzeq] at this
      calc ‖F z‖ * Real.exp (k * z.im)
          ≤ (A * Real.exp (-k * |z.im|)) * Real.exp (k * z.im) := by
            exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = A * Real.exp (-k * |z.im| + k * z.im) := by
            rw [mul_assoc, ← Real.exp_add]
        _ ≤ A := by
            have : -k * |z.im| + k * z.im ≤ 0 := by
              have h2 : z.im ≤ |z.im| := le_abs_self _
              nlinarith
            calc A * Real.exp (-k * |z.im| + k * z.im)
                ≤ A * Real.exp 0 :=
                  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) hApos.le
              _ = A := by rw [Real.exp_zero, mul_one]
    have hgb : ∀ z : ℂ, z.re = b → ‖g z‖ ≤ A := by
      intro z hz
      rw [hgz]
      have hzeq : z = (b : ℂ) + z.im * I := by
        rw [← hz]
        exact (Complex.re_add_im z).symm
      have h1 : ‖F z‖ ≤ A * Real.exp (-k * |z.im|) := by
        have := hlb z.im
        rwa [← hzeq] at this
      calc ‖F z‖ * Real.exp (k * z.im)
          ≤ (A * Real.exp (-k * |z.im|)) * Real.exp (k * z.im) := by
            exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = A * Real.exp (-k * |z.im| + k * z.im) := by
            rw [mul_assoc, ← Real.exp_add]
        _ ≤ A := by
            have : -k * |z.im| + k * z.im ≤ 0 := by
              have h2 : z.im ≤ |z.im| := le_abs_self _
              nlinarith
            calc A * Real.exp (-k * |z.im| + k * z.im)
                ≤ A * Real.exp 0 :=
                  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) hApos.le
              _ = A := by rw [Real.exp_zero, mul_one]
    have hgC : ∀ z : ℂ, a < z.re → z.re < b → ‖g z‖ ≤ C * Real.exp (k * |z.im|) := by
      intro z h1 h2
      rw [hgz]
      have h3 : k * z.im ≤ k * |z.im| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hk.le
      exact mul_le_mul (hC z h1.le h2.le) (Real.exp_le_exp.mpr h3) (Real.exp_pos _).le
        hCnn
    have hPL := PhragmenLindelof.vertical_strip hgd.diffContOnCl
      (hgrowth g hgC) hga hgb
      (z := (u : ℂ) + t' * I) (by simpa using hu.1) (by simpa using hu.2)
    have him : ((u : ℂ) + t' * I).im = t' := by simp
    have hgnorm := hgz ((u : ℂ) + t' * I)
    rw [him] at hgnorm
    have hF' : ‖F ((u : ℂ) + t' * I)‖
        = ‖g ((u : ℂ) + t' * I)‖ * Real.exp (-(k * t')) := by
      rw [hgnorm, mul_assoc, ← Real.exp_add]
      simp
    rw [hF']
    calc ‖g ((u : ℂ) + t' * I)‖ * Real.exp (-(k * t'))
        ≤ A * Real.exp (-(k * t')) :=
          mul_le_mul_of_nonneg_right hPL (Real.exp_pos _).le
      _ = A * Real.exp (-k * t') := by ring_nf
  -- multiplier for the lower heights
  have hdown : ∀ t : ℝ, ‖F ((u : ℂ) + t * I)‖ ≤ A * Real.exp (k * t) := by
    intro t'
    set g : ℂ → ℂ := fun z => F z * Complex.exp ((k : ℂ) * I * z) with hgdef
    have hgz : ∀ z : ℂ, ‖g z‖ = ‖F z‖ * Real.exp (-(k * z.im)) := by
      intro z
      rw [hgdef]
      dsimp only
      rw [norm_mul, norm_exp_mul_I']
    have hgd : Differentiable ℂ g :=
      hF.mul ((differentiable_const _).mul differentiable_id).cexp
    have hedge : ∀ (v : ℝ), (∀ s : ℝ, ‖F ((v : ℂ) + s * I)‖ ≤ A * Real.exp (-k * |s|)) →
        ∀ z : ℂ, z.re = v → ‖g z‖ ≤ A := by
      intro v hv z hz
      rw [hgz]
      have hzeq : z = (v : ℂ) + z.im * I := by
        rw [← hz]
        exact (Complex.re_add_im z).symm
      have h1 : ‖F z‖ ≤ A * Real.exp (-k * |z.im|) := by
        have := hv z.im
        rwa [← hzeq] at this
      calc ‖F z‖ * Real.exp (-(k * z.im))
          ≤ (A * Real.exp (-k * |z.im|)) * Real.exp (-(k * z.im)) := by
            exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = A * Real.exp (-k * |z.im| + -(k * z.im)) := by
            rw [mul_assoc, ← Real.exp_add]
        _ ≤ A := by
            have : -k * |z.im| + -(k * z.im) ≤ 0 := by
              have h2 : -z.im ≤ |z.im| := neg_le_abs _
              nlinarith
            calc A * Real.exp (-k * |z.im| + -(k * z.im))
                ≤ A * Real.exp 0 :=
                  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) hApos.le
              _ = A := by rw [Real.exp_zero, mul_one]
    have hgC : ∀ z : ℂ, a < z.re → z.re < b → ‖g z‖ ≤ C * Real.exp (k * |z.im|) := by
      intro z h1 h2
      rw [hgz]
      have h3 : -(k * z.im) ≤ k * |z.im| := by
        have := neg_le_abs z.im
        nlinarith
      exact mul_le_mul (hC z h1.le h2.le) (Real.exp_le_exp.mpr h3) (Real.exp_pos _).le
        hCnn
    have hPL := PhragmenLindelof.vertical_strip hgd.diffContOnCl
      (hgrowth g hgC) (hedge a hla) (hedge b hlb)
      (z := (u : ℂ) + t' * I) (by simpa using hu.1) (by simpa using hu.2)
    have him : ((u : ℂ) + t' * I).im = t' := by simp
    have hgnorm := hgz ((u : ℂ) + t' * I)
    rw [him] at hgnorm
    have hF' : ‖F ((u : ℂ) + t' * I)‖
        = ‖g ((u : ℂ) + t' * I)‖ * Real.exp (k * t') := by
      rw [hgnorm, mul_assoc, ← Real.exp_add]
      simp
    rw [hF']
    exact mul_le_mul_of_nonneg_right hPL (Real.exp_pos _).le
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact hup t
  · rw [abs_of_nonpos ht]
    have := hdown t
    calc ‖F ((u : ℂ) + t * I)‖ ≤ A * Real.exp (k * t) := this
      _ = A * Real.exp (-k * -t) := by ring_nf

/-! ## The converse from boundedness alone -/

/-- **The converse with the classical hypothesis set** — package, kernel line data,
and one boundedness constant on the strip: the decay field is derived by
Phragmén–Lindelöf, the line fields by the Stirling discharge. -/
theorem weil_converse_of_BV (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n) (κ : MellinKernel)
    (hKc : ContinuousOn κ.K (Set.Ioi 0))
    (ε : ℂ)
    (pkg : KNicePackage (coefficientArithmetic P.a) κ.G (max κ.B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max κ.B0 ((P.A : ℝ) + 1) < σ)
    (hG_int : Integrable (fun t : ℝ => κ.G ((σ : ℂ) + t * I)))
    (A k : ℝ) (hApos : 0 < A) (hk : 0 < k)
    (hGexp : ∀ t : ℝ, ‖κ.G ((σ : ℂ) + t * I)‖ ≤ A * Real.exp (-k * |t|))
    (C : ℝ) (hBV : ∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C) :
    ∀ x : ℝ, 0 < x →
      coeffPrimal3DBankReadout P.a κ.K (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          coeffDual3DTransformedReadout P.adual κ.K (1 / x) := by
  have hA1 : (1 : ℝ) ≤ (P.A : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (P.A : ℝ) := Nat.cast_nonneg _
    linarith
  have hσ1 : 1 < σ := lt_of_le_of_lt (le_trans hA1 (le_max_right _ _)) hσ
  have hab : 1 - σ < σ := by linarith
  have hline := lam_line_integrable_of_G P κ pkg σ hσ hG_int
  obtain ⟨A', hA'pos, hA'⟩ := lam_line_exp_bound_of_G P κ pkg σ hσ A k hApos hGexp
  set A'' : ℝ := max A' (‖ε‖ * A' + 1) with hA''def
  have hA''pos : 0 < A'' := lt_of_lt_of_le hA'pos (le_max_left _ _)
  have hlb : ∀ t : ℝ, ‖pkg.lam ((σ : ℂ) + t * I)‖ ≤ A'' * Real.exp (-k * |t|) := by
    intro t
    calc ‖pkg.lam ((σ : ℂ) + t * I)‖ ≤ A' * Real.exp (-k * |t|) := hA' t
      _ ≤ A'' * Real.exp (-k * |t|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  have hla : ∀ t : ℝ, ‖pkg.lam (((1 - σ : ℝ) : ℂ) + t * I)‖
      ≤ A'' * Real.exp (-k * |t|) := by
    intro t
    have hFE := pkg.FE ((σ : ℂ) + (-t : ℝ) * I)
    rw [show (1 : ℂ) - ((σ : ℂ) + (-t : ℝ) * I) = ((1 - σ : ℝ) : ℂ) + t * I by
      push_cast; ring] at hFE
    rw [hFE, norm_mul]
    have h1 : ‖pkg.lam ((σ : ℂ) + (-t : ℝ) * I)‖ ≤ A' * Real.exp (-k * |t|) := by
      have := hA' (-t)
      simpa [abs_neg] using this
    calc ‖ε‖ * ‖pkg.lam ((σ : ℂ) + (-t : ℝ) * I)‖
        ≤ ‖ε‖ * (A' * Real.exp (-k * |t|)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (‖ε‖ * A') * Real.exp (-k * |t|) := by ring
      _ ≤ A'' * Real.exp (-k * |t|) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          calc ‖ε‖ * A' ≤ ‖ε‖ * A' + 1 := by linarith
            _ ≤ A'' := le_max_right _ _
  have hdecay := strip_exp_decay pkg.lam pkg.entire (1 - σ) σ hab C
    (fun z h1 h2 => hBV z h1 h2) A'' k hA''pos hk hla hlb
  refine weil_converse P hdual κ hKc ε pkg σ hσ hline
    (fun T => A'' * Real.exp (-k * T)) (fun T u hu => ?_) ?_ 
  · exact hdecay u hu T
  · have h1 : Tendsto (fun T : ℝ => -k * T) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hk)).mpr tendsto_id
    have h2 : Tendsto (fun T : ℝ => Real.exp (-k * T)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h1
    have := h2.const_mul A''
    rwa [mul_zero] at this

/-! ## The two compiled kernel families -/

/-- The singleton-`Γℂ` chart kernel (the holomorphic-eigenform chart type). -/
noncomputable def gammaCKernel (μ : ℂ) (hμ : 0 ≤ μ.re) : MellinKernel :=
  generalMellinKernel [] (by simp) [μ]
    (by simp) (fun x hx => by
      rw [List.mem_singleton] at hx
      rw [hx]
      exact hμ)

/-- Continuity of the `Γℂ` clock on the positive ray. -/
theorem gammaClock_continuousOn (μ : ℂ) :
    ContinuousOn (gammaClock μ) (Set.Ioi 0) := by
  have h1 : ContinuousOn (fun x : ℝ => ((x : ℂ)) ^ μ) (Set.Ioi 0) := by
    intro x hx
    have hxpos : (0 : ℝ) < x := Set.mem_Ioi.mp hx
    refine ContinuousAt.continuousWithinAt ?_
    exact Complex.continuousAt_ofReal_cpow_const x μ (Or.inr hxpos.ne')
  have h2 : Continuous (fun x : ℝ => Complex.exp (-(2 * Real.pi : ℂ) * x)) := by
    fun_prop
  have : ContinuousOn (fun x : ℝ =>
      2 * (x : ℂ) ^ μ * Complex.exp (-(2 * Real.pi : ℂ) * x)) (Set.Ioi 0) :=
    ((continuousOn_const.mul h1).mul h2.continuousOn)
  exact this

/-- **The BV converse at the pure-real chain kernel** — the Maass chart type.  All
kernel line data discharged; kernel continuity remains the one named input. -/
theorem weil_converse_of_BV_realChain (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n)
    (d : ℂ) (hd : 0 ≤ d.re) (ds : List ℂ) (hds : ∀ e ∈ ds, 0 ≤ e.re)
    (hKc : ContinuousOn (realChainKernelLog d ds) (Set.Ioi 0))
    (ε : ℂ)
    (pkg : KNicePackage (coefficientArithmetic P.a)
      (realChainMellinKernel d hd ds hds).G
      (max (realChainMellinKernel d hd ds hds).B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max (realChainMellinKernel d hd ds hds).B0 ((P.A : ℝ) + 1) < σ)
    (C : ℝ) (hBV : ∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C) :
    ∀ x : ℝ, 0 < x →
      coeffPrimal3DBankReadout P.a (realChainMellinKernel d hd ds hds).K (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          coeffDual3DTransformedReadout P.adual
            (realChainMellinKernel d hd ds hds).K (1 / x) := by
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
      (realChainMellinKernel d hd ds hds).G ((σ : ℂ) + t * I)) :=
    chain_line_integrable σ d ds hd' hds'
  obtain ⟨A, hApos, hA⟩ := chain_line_exp_bound σ d ds hd' hds'
  exact weil_converse_of_BV P hdual (realChainMellinKernel d hd ds hds) hKc ε pkg σ hσ
    hG_int A (Real.pi / 8) hApos (by positivity) hA C hBV

/-- **The BV converse at the singleton-`Γℂ` kernel — the classical Hecke hypothesis
set in full**: package + one boundedness constant; every other analytic input
(kernel continuity, line integrability, line decay, strip decay) is compiled. -/
theorem weil_converse_of_BV_gammaC (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n)
    (μ : ℂ) (hμ : 0 ≤ μ.re)
    (ε : ℂ)
    (pkg : KNicePackage (coefficientArithmetic P.a) (gammaCKernel μ hμ).G
      (max (gammaCKernel μ hμ).B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max (gammaCKernel μ hμ).B0 ((P.A : ℝ) + 1) < σ)
    (C : ℝ) (hBV : ∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C) :
    ∀ x : ℝ, 0 < x →
      coeffPrimal3DBankReadout P.a (gammaCKernel μ hμ).K (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          coeffDual3DTransformedReadout P.adual (gammaCKernel μ hμ).K (1 / x) := by
  have hA1 : (1 : ℝ) ≤ (P.A : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (P.A : ℝ) := Nat.cast_nonneg _
    linarith
  have hσpos : 0 < σ := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hA1)
    (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hσ))
  have hμσ : 0 < σ + μ.re := by linarith
  have hKc : ContinuousOn (gammaCKernel μ hμ).K (Set.Ioi 0) := by
    show ContinuousOn (gammaClock μ) (Set.Ioi 0)
    exact gammaClock_continuousOn μ
  have hGeq : ∀ t : ℝ, (gammaCKernel μ hμ).G ((σ : ℂ) + t * I)
      = Complex.Gammaℂ ((σ : ℂ) + t * I + μ) := by
    intro t
    show ((List.map (fun dlt => Complex.Gammaℝ ((σ : ℂ) + t * I + dlt)) []).prod) *
      ((List.map (fun m => Complex.Gammaℂ ((σ : ℂ) + t * I + m)) [μ]).prod)
      = Complex.Gammaℂ ((σ : ℂ) + t * I + μ)
    simp
  have hG_int : Integrable (fun t : ℝ =>
      (gammaCKernel μ hμ).G ((σ : ℂ) + t * I)) := by
    have h := gammaC_single_line_integrable σ μ hμσ
    exact h.congr (Eventually.of_forall fun t => (hGeq t).symm)
  obtain ⟨A, hApos, hA⟩ := gammaC_single_line_exp_bound σ μ hμσ
  have hA' : ∀ t : ℝ, ‖(gammaCKernel μ hμ).G ((σ : ℂ) + t * I)‖
      ≤ A * Real.exp (-(Real.pi / 4) * |t|) := by
    intro t
    rw [hGeq t]
    exact hA t
  exact weil_converse_of_BV P hdual (gammaCKernel μ hμ) hKc ε pkg σ hσ
    hG_int A (Real.pi / 4) hApos (by positivity) hA' C hBV

/-- **The BV converse in theta form** — same hypotheses, conclusion stated on the
banks themselves. -/
theorem weil_converse_of_BV_reflection (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n) (κ : MellinKernel)
    (hKc : ContinuousOn κ.K (Set.Ioi 0))
    (ε : ℂ)
    (pkg : KNicePackage (coefficientArithmetic P.a) κ.G (max κ.B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max κ.B0 ((P.A : ℝ) + 1) < σ)
    (hG_int : Integrable (fun t : ℝ => κ.G ((σ : ℂ) + t * I)))
    (A k : ℝ) (hApos : 0 < A) (hk : 0 < k)
    (hGexp : ∀ t : ℝ, ‖κ.G ((σ : ℂ) + t * I)‖ ≤ A * Real.exp (-k * |t|))
    (C : ℝ) (hBV : ∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C) :
    ∀ y : ℝ, 0 < y →
      CriticalLinePhasor.CarrierTheta.theta P.a κ.K y
        = ε * ((y : ℂ)⁻¹ *
            CriticalLinePhasor.CarrierTheta.theta P.adual κ.K (1 / y)) := by
  have hA1 : (1 : ℝ) ≤ (P.A : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (P.A : ℝ) := Nat.cast_nonneg _
    linarith
  have hσ1 : 1 < σ := lt_of_le_of_lt (le_trans hA1 (le_max_right _ _)) hσ
  have hab : 1 - σ < σ := by linarith
  have hline := lam_line_integrable_of_G P κ pkg σ hσ hG_int
  obtain ⟨A', hA'pos, hA'⟩ := lam_line_exp_bound_of_G P κ pkg σ hσ A k hApos hGexp
  set A'' : ℝ := max A' (‖ε‖ * A' + 1) with hA''def
  have hA''pos : 0 < A'' := lt_of_lt_of_le hA'pos (le_max_left _ _)
  have hlb : ∀ t : ℝ, ‖pkg.lam ((σ : ℂ) + t * I)‖ ≤ A'' * Real.exp (-k * |t|) := by
    intro t
    calc ‖pkg.lam ((σ : ℂ) + t * I)‖ ≤ A' * Real.exp (-k * |t|) := hA' t
      _ ≤ A'' * Real.exp (-k * |t|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  have hla : ∀ t : ℝ, ‖pkg.lam (((1 - σ : ℝ) : ℂ) + t * I)‖
      ≤ A'' * Real.exp (-k * |t|) := by
    intro t
    have hFE := pkg.FE ((σ : ℂ) + (-t : ℝ) * I)
    rw [show (1 : ℂ) - ((σ : ℂ) + (-t : ℝ) * I) = ((1 - σ : ℝ) : ℂ) + t * I by
      push_cast; ring] at hFE
    rw [hFE, norm_mul]
    have h1 : ‖pkg.lam ((σ : ℂ) + (-t : ℝ) * I)‖ ≤ A' * Real.exp (-k * |t|) := by
      have := hA' (-t)
      simpa [abs_neg] using this
    calc ‖ε‖ * ‖pkg.lam ((σ : ℂ) + (-t : ℝ) * I)‖
        ≤ ‖ε‖ * (A' * Real.exp (-k * |t|)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (‖ε‖ * A') * Real.exp (-k * |t|) := by ring
      _ ≤ A'' * Real.exp (-k * |t|) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          calc ‖ε‖ * A' ≤ ‖ε‖ * A' + 1 := by linarith
            _ ≤ A'' := le_max_right _ _
  have hdecay := strip_exp_decay pkg.lam pkg.entire (1 - σ) σ hab C
    (fun z h1 h2 => hBV z h1 h2) A'' k hA''pos hk hla hlb
  refine weil_converse_reflection P hdual κ hKc ε pkg σ hσ hline
    (fun T => A'' * Real.exp (-k * T)) (fun T u hu => hdecay u hu T) ?_
  have h1 : Tendsto (fun T : ℝ => -k * T) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hk)).mpr tendsto_id
  have h2 : Tendsto (fun T : ℝ => Real.exp (-k * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h1
  have := h2.const_mul A''
  rwa [mul_zero] at this

/-- **The Hecke hypothesis set in theta form at the `Γℂ` chart**: package + one
boundedness constant force the reflection of the banks. -/
theorem weil_converse_of_BV_gammaC_reflection (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n)
    (μ : ℂ) (hμ : 0 ≤ μ.re)
    (ε : ℂ)
    (pkg : KNicePackage (coefficientArithmetic P.a) (gammaCKernel μ hμ).G
      (max (gammaCKernel μ hμ).B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max (gammaCKernel μ hμ).B0 ((P.A : ℝ) + 1) < σ)
    (C : ℝ) (hBV : ∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C) :
    ∀ y : ℝ, 0 < y →
      CriticalLinePhasor.CarrierTheta.theta P.a (gammaCKernel μ hμ).K y
        = ε * ((y : ℂ)⁻¹ *
            CriticalLinePhasor.CarrierTheta.theta P.adual (gammaCKernel μ hμ).K
              (1 / y)) := by
  have hA1 : (1 : ℝ) ≤ (P.A : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (P.A : ℝ) := Nat.cast_nonneg _
    linarith
  have hσpos : 0 < σ := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hA1)
    (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hσ))
  have hμσ : 0 < σ + μ.re := by linarith
  have hKc : ContinuousOn (gammaCKernel μ hμ).K (Set.Ioi 0) := by
    show ContinuousOn (gammaClock μ) (Set.Ioi 0)
    exact gammaClock_continuousOn μ
  have hGeq : ∀ t : ℝ, (gammaCKernel μ hμ).G ((σ : ℂ) + t * I)
      = Complex.Gammaℂ ((σ : ℂ) + t * I + μ) := by
    intro t
    show ((List.map (fun dlt => Complex.Gammaℝ ((σ : ℂ) + t * I + dlt)) []).prod) *
      ((List.map (fun m => Complex.Gammaℂ ((σ : ℂ) + t * I + m)) [μ]).prod)
      = Complex.Gammaℂ ((σ : ℂ) + t * I + μ)
    simp
  have hG_int : Integrable (fun t : ℝ =>
      (gammaCKernel μ hμ).G ((σ : ℂ) + t * I)) := by
    have h := gammaC_single_line_integrable σ μ hμσ
    exact h.congr (Eventually.of_forall fun t => (hGeq t).symm)
  obtain ⟨A, hApos, hA⟩ := gammaC_single_line_exp_bound σ μ hμσ
  have hA' : ∀ t : ℝ, ‖(gammaCKernel μ hμ).G ((σ : ℂ) + t * I)‖
      ≤ A * Real.exp (-(Real.pi / 4) * |t|) := by
    intro t
    rw [hGeq t]
    exact hA t
  exact weil_converse_of_BV_reflection P hdual (gammaCKernel μ hμ) hKc ε pkg σ hσ
    hG_int A (Real.pi / 4) hApos (by positivity) hA' C hBV

end CriticalLinePhasor.PhragmenBV

#print axioms CriticalLinePhasor.PhragmenBV.strip_exp_decay
#print axioms CriticalLinePhasor.PhragmenBV.weil_converse_of_BV
#print axioms CriticalLinePhasor.PhragmenBV.weil_converse_of_BV_realChain
#print axioms CriticalLinePhasor.PhragmenBV.weil_converse_of_BV_gammaC
#print axioms CriticalLinePhasor.PhragmenBV.weil_converse_of_BV_reflection
#print axioms CriticalLinePhasor.PhragmenBV.weil_converse_of_BV_gammaC_reflection
