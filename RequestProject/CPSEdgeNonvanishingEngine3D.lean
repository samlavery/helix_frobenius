import Mathlib
import RequestProject.RectResidue

/-!
# The edge-nonvanishing engine: product bound + entirety kill boundary zeros

The order-counting half of the de la Vallée Poussin argument, abstracted to
exactly what the CPS tower supplies.  Inputs: an entire candidate `C` (the
retained standard continuation at rank `r`), a continuous companion `D` (the
diagonal Rankin--Selberg readout `ζ·∏ Sym^{2k}`, entire hence continuous),
and the Mertens product bound on the real approach segment
`1 ≤ ‖ζ(σ)‖²·‖D(σ)‖·‖C(σ+iy)‖⁴·‖D(σ+2iy)‖` — the exponential of the
termwise-nonnegative `2(1 + S·cos)²` Euler-log combination supplied by the
positivity core.  Output: `C(1+iy) ≠ 0`.

The count is exact: the ζ factor carries pole order two, a hypothetical zero
carries order at least four through the fourth power, and the companion is
bounded; so the product is `O((σ−1)²) → 0`, contradicting the bound.  The
companion never needs a pole and never needs nonvanishing — entirety and
continuity suffice, so no circularity enters.  No `axiom`, no `sorry`.
-/

open Filter Topology Complex

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.RectResidue

/-- The real approach `σ → 1⁺`, pushed to the punctured complex neighborhood
of `1`. -/
theorem tendsto_ofReal_nhdsGT_one :
    Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have h1 : (1 : ℝ) < σ := hσ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have : σ = 1 := by exact_mod_cast h
    linarith

/-- Along the real approach, `(σ−1)·ζ(σ) → 1`. -/
theorem zeta_residue_real_approach :
    Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * riemannZeta σ) (𝓝[>] (1 : ℝ))
      (𝓝 1) :=
  riemannZeta_residue_one.comp tendsto_ofReal_nhdsGT_one

/-- **The edge-nonvanishing engine.**  If `C` is entire, `D` is continuous,
and the Mertens product bound holds on the real segment `σ ∈ (1, 2]`, then
`C` has no zero at `1 + iy`.  The bound is the analytic face of the
termwise positivity `2(1 + S·cosθ)² ≥ 0`; the engine converts a boundary
zero into the contradiction `1 ≤ O((σ−1)²)`. -/
theorem edge_nonvanishing_of_product_bound
    {C D : ℂ → ℂ} {y : ℝ}
    (hC : Differentiable ℂ C) (hD : Continuous D)
    (hprod : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      1 ≤ ‖riemannZeta (σ : ℂ)‖ ^ 2 * ‖D (σ : ℂ)‖
        * ‖C ((σ : ℂ) + y * I)‖ ^ 4 * ‖D ((σ : ℂ) + 2 * y * I)‖) :
    C (1 + y * I) ≠ 0 := by
  intro hzero
  set ρ : ℂ := 1 + y * I with hρ
  -- factor the zero through the entire dslope
  have hg : Differentiable ℂ (dslope C ρ) :=
    differentiable_dslope_of_entire hC ρ
  have hfac : ∀ s : ℂ, C s = (s - ρ) * dslope C ρ s := by
    intro s
    have h := sub_smul_dslope C ρ s
    rw [smul_eq_mul] at h
    rw [h, hzero, sub_zero]
  -- the assembled product as a real function of σ
  set F : ℝ → ℝ := fun σ =>
    ‖riemannZeta (σ : ℂ)‖ ^ 2 * ‖D (σ : ℂ)‖
      * ‖C ((σ : ℂ) + y * I)‖ ^ 4 * ‖D ((σ : ℂ) + 2 * y * I)‖ with hF
  -- rewrite F with the zero factored out: F σ = ‖(σ−1)ζ(σ)‖²·‖D σ‖·
  --   ‖dslope C ρ (σ+iy)‖⁴·‖D(σ+2iy)‖·(σ−1)²  for σ > 1
  have hkey : ∀ σ : ℝ, 1 < σ → F σ =
      (‖((σ : ℂ) - 1) * riemannZeta (σ : ℂ)‖ ^ 2 * ‖D (σ : ℂ)‖
        * ‖dslope C ρ ((σ : ℂ) + y * I)‖ ^ 4 * ‖D ((σ : ℂ) + 2 * y * I)‖)
        * (σ - 1) ^ 2 := by
    intro σ hσ
    have hsub : ((σ : ℂ) + y * I) - ρ = ((σ : ℝ) - 1 : ℝ) := by
      rw [hρ]
      push_cast
      ring
    have hnorm : ‖((σ : ℂ) + y * I) - ρ‖ = σ - 1 := by
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hCval : ‖C ((σ : ℂ) + y * I)‖
        = (σ - 1) * ‖dslope C ρ ((σ : ℂ) + y * I)‖ := by
      rw [hfac ((σ : ℂ) + y * I), norm_mul, hnorm]
    have hzeta : ‖((σ : ℂ) - 1) * riemannZeta (σ : ℂ)‖
        = (σ - 1) * ‖riemannZeta (σ : ℂ)‖ := by
      rw [norm_mul]
      congr 1
      rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [hF]
    simp only [hCval, hzeta]
    have h1 : (0 : ℝ) < σ - 1 := by linarith
    ring
  -- the factored product tends to 0 as σ → 1⁺
  have hlim : Tendsto F (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hζ : Tendsto (fun σ : ℝ => ‖((σ : ℂ) - 1) * riemannZeta (σ : ℂ)‖ ^ 2)
        (𝓝[>] (1 : ℝ)) (𝓝 1) := by
      have h := (zeta_residue_real_approach.norm).pow 2
      simpa using h
    have hcont1 : Tendsto (fun σ : ℝ => ‖D (σ : ℂ)‖) (𝓝[>] (1 : ℝ))
        (𝓝 ‖D (1 : ℂ)‖) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact ((hD.norm).comp Complex.continuous_ofReal).tendsto 1
    have hcont2 : Tendsto (fun σ : ℝ => ‖dslope C ρ ((σ : ℂ) + y * I)‖ ^ 4)
        (𝓝[>] (1 : ℝ)) (𝓝 (‖dslope C ρ ρ‖ ^ 4)) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      have hc : Continuous fun σ : ℝ => ‖dslope C ρ ((σ : ℂ) + y * I)‖ ^ 4 := by
        apply Continuous.pow
        apply Continuous.norm
        exact hg.continuous.comp
          ((Complex.continuous_ofReal).add continuous_const)
      have := hc.tendsto 1
      simpa [hρ] using this
    have hcont3 : Tendsto (fun σ : ℝ => ‖D ((σ : ℂ) + 2 * y * I)‖)
        (𝓝[>] (1 : ℝ)) (𝓝 ‖D (1 + 2 * y * I)‖) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      have hc : Continuous fun σ : ℝ => ‖D ((σ : ℂ) + 2 * y * I)‖ :=
        (hD.norm).comp ((Complex.continuous_ofReal).add continuous_const)
      have := hc.tendsto 1
      simpa using this
    have hsq : Tendsto (fun σ : ℝ => (σ - 1) ^ 2) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      have hc : Continuous fun σ : ℝ => (σ - 1) ^ 2 := by continuity
      have := hc.tendsto 1
      simpa using this
    have hall := (((hζ.mul hcont1).mul hcont2).mul hcont3).mul hsq
    rw [mul_zero] at hall
    apply hall.congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (hkey σ hσ).symm
  -- but F ≥ 1 eventually on the approach — contradiction
  have hev : ∀ᶠ σ in 𝓝[>] (1 : ℝ), 1 ≤ F σ := by
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with σ hσ
    exact hprod σ hσ.1 hσ.2
  have hlt : ∀ᶠ σ in 𝓝[>] (1 : ℝ), F σ < 1 := by
    have := hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    exact this
  obtain ⟨σ, h1, h2⟩ := (hev.and hlt).exists
  linarith

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.edge_nonvanishing_of_product_bound
