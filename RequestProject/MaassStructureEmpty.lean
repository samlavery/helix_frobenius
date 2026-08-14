import RequestProject.MaassReducedKernel
import RequestProject.NoPositiveDecayingSolution

/-!
# The first-order-free radial equation is inconsistent

The capstone of the emptiness campaign.  `maass_empty_at_zero` handled `r = 0` by hand; this
closes **every** spectral parameter by feeding the reduced kernel to
`no_positive_decaying_solution`.

The three inputs are all already proved:

* `realReduced_equation` — `y²g'' − 4πy²g' = r²g`, i.e. `g'' − 4πg' = r²g/y²`;
* `realReduced_normalization` — `2√y·g(y) → 1`, so `g` is eventually positive;
* `realReduced_tendsto_zero` — `g(y) → 0`.

and they are contradictory.  The mathematical content: the equation

  `y²K'' = ((2πy)² + r²)K`

cannot hold alongside decay and the standard Whittaker normalization.  The Whittaker equation
satisfied by `K_{ir}(2πy)` — the function `radial_normalization` describes, and the one
`laplace_eigen` forces through the Fourier expansion — is instead

  `y²K'' + y·K' = ((2πy)² − r²)K`.

The **missing first-order term** is what makes the first equation's decaying solution behave like
`e^{−2πy}` with no power-law prefactor, while `radial_normalization` demands the prefactor
`y^{−1/2}`.

**History.**  `GenuineMaassCuspForm3D.radial_equation` once carried the first form, which made that
structure uninhabited and every theorem quantified over it vacuous.  It now carries the Whittaker
equation; `sqrt_weight_sign_flip` certifies that the repair moves the deciding constant from
`+r² ≥ 0` to `−(1/4 + r²) < 0`, out of the range this file's contradiction covers.  The bundle
`FirstOrderFreeRadialData` preserves the old hypotheses so the defect stays a theorem rather than
a changelog entry.
-/

open Filter
open scoped Real Topology

namespace CriticalLinePhasor.ThreeDConverse

lemma reducedDeriv_hasDerivAt (M : FirstOrderFreeRadialData) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (maassReducedKernel M)) (deriv (deriv (maassReducedKernel M)) y) y := by
  have hK : DifferentiableAt ℝ M.radialKernel y :=
    (radial_contDiffAt M hy).differentiableAt (by norm_num)
  have hK' : DifferentiableAt ℝ (deriv M.radialKernel) y := by
    have hd : ContDiffOn ℝ 1 (deriv M.radialKernel) (Set.Ioi (0:ℝ)) :=
      (M.radial_smooth 2).deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact (hd.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hy)
  have hE : HasDerivAt (fun u : ℝ => Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (u : ℂ)))
      (((2 * Real.pi : ℝ) : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (y : ℂ))) y := by
    have hid : HasDerivAt (fun u : ℝ => ((u : ℝ) : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
    simpa [mul_comm] using (hid.const_mul (((2 * Real.pi : ℝ) : ℂ))).cexp
  have hR2 : HasDerivAt (fun t : ℝ => Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (t : ℂ)) *
        (((2 * Real.pi : ℝ) : ℂ) * M.radialKernel t + deriv M.radialKernel t))
      (((2 * Real.pi : ℝ) : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (y : ℂ)) *
          (((2 * Real.pi : ℝ) : ℂ) * M.radialKernel y + deriv M.radialKernel y) +
        Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (y : ℂ)) *
          (((2 * Real.pi : ℝ) : ℂ) * deriv M.radialKernel y +
            deriv (deriv M.radialKernel) y)) y :=
    hE.mul ((hK.hasDerivAt.const_mul (((2 * Real.pi : ℝ) : ℂ))).add hK'.hasDerivAt)
  have hd1C : deriv (maassReducedKernel M) =ᶠ[𝓝 y]
      fun t : ℝ => Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (t : ℂ)) *
        (((2 * Real.pi : ℝ) : ℂ) * M.radialKernel t + deriv M.radialKernel t) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (reduced_hasDerivAt M ht).deriv
  have h := hR2.congr_of_eventuallyEq hd1C
  rw [hd1C.deriv_eq, hR2.deriv]
  exact h

lemma realReducedDeriv_differentiableAt (M : FirstOrderFreeRadialData) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℝ (deriv (maassRealReduced M)) y := by
  have heq : deriv (maassRealReduced M) =ᶠ[𝓝 y]
      fun t : ℝ => (deriv (maassReducedKernel M) t).re := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    rw [(realReduced_deriv M ht).deriv, (reduced_hasDerivAt M ht).deriv]
  exact ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt y
    (reducedDeriv_hasDerivAt M hy)).congr_of_eventuallyEq heq).differentiableAt

/-- **The first-order-free radial data is uninhabited.**  Every spectral parameter, no case
analysis: dropping `y·K'` from the modified Bessel equation is already inconsistent with decay plus
the standard Whittaker normalization. -/
theorem firstOrderFreeRadialData_false (M : FirstOrderFreeRadialData) : False := by
  -- the reduced kernel is eventually positive
  obtain ⟨Y, hY1, hY2⟩ : ∃ Y : ℝ, 0 < Y ∧ ∀ y : ℝ, Y ≤ y → 0 < maassRealReduced M y := by
    have h := (realReduced_normalization M).eventually_const_lt
      (by norm_num : (1:ℝ)/2 < 1)
    obtain ⟨Y₀, hY₀⟩ :=
      (h.and (eventually_gt_atTop (0:ℝ))).exists_forall_of_atTop
    refine ⟨max Y₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy => ?_⟩
    obtain ⟨h1, h2⟩ := hY₀ y (le_trans (le_max_left _ _) hy)
    nlinarith [Real.sqrt_pos.mpr h2]
  -- the equation, divided through by `y²`
  have hode : ∀ y : ℝ, 0 < y →
      deriv (deriv (maassRealReduced M)) y - 4 * Real.pi * deriv (maassRealReduced M) y
        = M.spectralParameter ^ 2 * maassRealReduced M y / y ^ 2 := by
    intro y hy
    have h := realReduced_equation M hy
    have hy2 : (y:ℝ) ^ 2 ≠ 0 := by positivity
    rw [eq_div_iff hy2]
    linear_combination h
  exact no_positive_decaying_solution (sq_nonneg M.spectralParameter) hY1
    (fun y hy => (realReduced_deriv M hy).differentiableAt)
    (fun y hy => realReducedDeriv_differentiableAt M hy)
    hode (realReduced_tendsto_zero M) hY2

instance : IsEmpty FirstOrderFreeRadialData := ⟨firstOrderFreeRadialData_false⟩

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.firstOrderFreeRadialData_false
