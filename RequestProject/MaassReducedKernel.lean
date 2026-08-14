import RequestProject.MaassRadialInconsistency

/-!
# The reduced radial kernel

`maass_empty_at_zero` closes the case `r = 0`, where the radial equation is constant-coefficient.
For general `r` the equation does not factor, so the argument has to be run on the **reduced
kernel**

  **`R(y) := e^{2πy}·K(y)`**,

which strips the exponential and leaves a first-order-dominated equation

  **`y²·R'' − 4π·y²·R' = r²·R`.**

Two facts about `R` come straight from `radial_normalization` and are recorded here:

* `reduced_normalization` — `2√y·R(y) → 1`.  Same statement, regrouped.
* `reduced_tendsto_zero` — `R(y) → 0`.  Dividing the previous limit by `2√y → ∞`.

Together they say `R` decays like `y^{-1/2}` — slowly.  The equation says the opposite: the
`−4πR'` term dominates `r²R/y²`, so a solution that stays positive and decays is forced to decay
faster than any power.  That is the general-`r` contradiction; these are its inputs.

**Scope.**  This file records the two normalization consequences and the reduced equation.
-/

open Filter Complex
open scoped Real Topology

namespace CriticalLinePhasor.ThreeDConverse

/-- **The reduced radial kernel** `R(y) = e^{2πy}·K(y)`. -/
noncomputable def maassReducedKernel (M : FirstOrderFreeRadialData) (y : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (y : ℂ)) * M.radialKernel y

lemma exp_ofReal_two_pi (y : ℝ) :
    Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (y : ℂ))
      = ((Real.exp (2 * Real.pi * y) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]

/-- **The normalization, in reduced form**: `2√y·R(y) → 1`. -/
theorem reduced_normalization (M : FirstOrderFreeRadialData) :
    Tendsto (fun y : ℝ => ((2 * Real.sqrt y : ℝ) : ℂ) * maassReducedKernel M y)
      atTop (𝓝 1) := by
  refine M.radial_normalization.congr fun y => ?_
  rw [maassReducedKernel, exp_ofReal_two_pi]
  push_cast
  ring

/-- **The reduced kernel decays**, but only like `y^{-1/2}`. -/
theorem reduced_tendsto_zero (M : FirstOrderFreeRadialData) :
    Tendsto (maassReducedKernel M) atTop (𝓝 0) := by
  have hnum : Tendsto
      (fun y : ℝ => ‖((2 * Real.sqrt y : ℝ) : ℂ) * maassReducedKernel M y‖)
      atTop (𝓝 1) := by
    simpa using (reduced_normalization M).norm
  have hden : Tendsto (fun y : ℝ => 2 * Real.sqrt y) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) Real.tendsto_sqrt_atTop
  have hdiv := hnum.div_atTop hden
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine hdiv.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  have hsy : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr hy
  rw [norm_mul]
  simp only [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt y)]
  field_simp

lemma reduced_hasDerivAt (M : FirstOrderFreeRadialData) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (maassReducedKernel M)
      (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (t : ℂ)) *
        (((2 * Real.pi : ℝ) : ℂ) * M.radialKernel t + deriv M.radialKernel t)) t := by
  have hK : DifferentiableAt ℝ M.radialKernel t :=
    (radial_contDiffAt M ht).differentiableAt (by norm_num)
  have hE : HasDerivAt (fun u : ℝ => Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (u : ℂ)))
      (((2 * Real.pi : ℝ) : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (t : ℂ))) t := by
    have hid : HasDerivAt (fun u : ℝ => ((u : ℝ) : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    simpa [mul_comm] using (hid.const_mul (((2 * Real.pi : ℝ) : ℂ))).cexp
  have h := hE.mul hK.hasDerivAt
  refine h.congr_deriv ?_
  ring

/-- **The reduced equation**: `y²·R'' − 4π·y²·R' = r²·R`.

The exponential is gone and with it the `(2πy)²` term: what is left is a first-order-dominated
equation whose right-hand side is the *spectral parameter alone*.  At `r = 0` it says `R'' = 4πR'`,
which is the factorization `maass_empty_at_zero` runs on. -/
theorem reduced_equation (M : FirstOrderFreeRadialData) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ 2 * deriv (deriv (maassReducedKernel M)) y
        - ((4 * Real.pi : ℝ) : ℂ) * (y : ℂ) ^ 2 * deriv (maassReducedKernel M) y
      = ((M.spectralParameter ^ 2 : ℝ) : ℂ) * maassReducedKernel M y := by
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
  -- the first derivative, as a function on a neighbourhood
  have hd1 : deriv (maassReducedKernel M) =ᶠ[𝓝 y]
      fun t : ℝ => Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (t : ℂ)) *
        (((2 * Real.pi : ℝ) : ℂ) * M.radialKernel t + deriv M.radialKernel t) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (reduced_hasDerivAt M ht).deriv
  have hR2 : HasDerivAt (fun t : ℝ => Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (t : ℂ)) *
        (((2 * Real.pi : ℝ) : ℂ) * M.radialKernel t + deriv M.radialKernel t))
      (((2 * Real.pi : ℝ) : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (y : ℂ)) *
          (((2 * Real.pi : ℝ) : ℂ) * M.radialKernel y + deriv M.radialKernel y) +
        Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (y : ℂ)) *
          (((2 * Real.pi : ℝ) : ℂ) * deriv M.radialKernel y +
            deriv (deriv M.radialKernel) y)) y :=
    hE.mul ((hK.hasDerivAt.const_mul (((2 * Real.pi : ℝ) : ℂ))).add hK'.hasDerivAt)
  rw [hd1.deriv_eq, hR2.deriv, (reduced_hasDerivAt M hy).deriv, maassReducedKernel]
  -- the structure's equation, with `iteratedDeriv` unfolded
  have heq := M.radial_equation y hy
  rw [iteratedDeriv_succ, iteratedDeriv_one] at heq
  push_cast at heq ⊢
  linear_combination Complex.exp ((2 * (Real.pi : ℂ)) * (y : ℂ)) * heq

/-- **The real reduced kernel** `g(y) = Re(e^{2πy}·K(y))`.  The reduced equation has real
coefficients, so the real part satisfies it too — and the normalization is a statement about the
real part alone. -/
noncomputable def maassRealReduced (M : FirstOrderFreeRadialData) (y : ℝ) : ℝ :=
  (maassReducedKernel M y).re

theorem realReduced_normalization (M : FirstOrderFreeRadialData) :
    Tendsto (fun y : ℝ => 2 * Real.sqrt y * maassRealReduced M y) atTop (𝓝 1) := by
  have h := (Complex.continuous_re.tendsto (1 : ℂ)).comp (reduced_normalization M)
  simpa [Function.comp_def, maassRealReduced, Complex.mul_re] using h

theorem realReduced_tendsto_zero (M : FirstOrderFreeRadialData) :
    Tendsto (maassRealReduced M) atTop (𝓝 0) := by
  have h := (Complex.continuous_re.tendsto (0 : ℂ)).comp (reduced_tendsto_zero M)
  show Tendsto (fun y : ℝ => (maassReducedKernel M y).re) atTop (𝓝 0)
  simpa [Function.comp_def] using h

lemma realReduced_deriv (M : FirstOrderFreeRadialData) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (maassRealReduced M)
      (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (t : ℂ)) *
        (((2 * Real.pi : ℝ) : ℂ) * M.radialKernel t + deriv M.radialKernel t)).re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (reduced_hasDerivAt M ht)

/-- **The real reduced equation**: `y²·g'' − 4π·y²·g' = r²·g`.

This is the object the general-`r` contradiction runs on: `g > 0` and `g → 0` by the
normalization, while integrating this equation forces `g' > 0` for large `y`. -/
theorem realReduced_equation (M : FirstOrderFreeRadialData) {y : ℝ} (hy : 0 < y) :
    y ^ 2 * deriv (deriv (maassRealReduced M)) y
        - 4 * Real.pi * y ^ 2 * deriv (maassRealReduced M) y
      = M.spectralParameter ^ 2 * maassRealReduced M y := by
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
  -- transport the two derivatives of `R` to the real part
  have hd1C : deriv (maassReducedKernel M) =ᶠ[𝓝 y]
      fun t : ℝ => Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (t : ℂ)) *
        (((2 * Real.pi : ℝ) : ℂ) * M.radialKernel t + deriv M.radialKernel t) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (reduced_hasDerivAt M ht).deriv
  have hRderiv : HasDerivAt (deriv (maassReducedKernel M))
      (deriv (deriv (maassReducedKernel M)) y) y := by
    have := hR2.congr_of_eventuallyEq hd1C
    rw [hd1C.deriv_eq, hR2.deriv]
    exact this
  have hg1 : deriv (maassRealReduced M) y = (deriv (maassReducedKernel M) y).re := by
    rw [(realReduced_deriv M hy).deriv, (reduced_hasDerivAt M hy).deriv]
  have hg1' : deriv (maassRealReduced M) =ᶠ[𝓝 y]
      fun t : ℝ => (deriv (maassReducedKernel M) t).re := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    rw [(realReduced_deriv M ht).deriv, (reduced_hasDerivAt M ht).deriv]
  have hg2 : deriv (deriv (maassRealReduced M)) y
      = (deriv (deriv (maassReducedKernel M)) y).re := by
    rw [hg1'.deriv_eq]
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hRderiv).deriv
  -- take the real part of the complex reduced equation
  have h := congrArg Complex.re (reduced_equation M hy)
  rw [hg1, hg2, maassRealReduced]
  simpa [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    pow_two] using h

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.realReduced_equation
#print axioms CriticalLinePhasor.ThreeDConverse.realReduced_normalization
#print axioms CriticalLinePhasor.ThreeDConverse.realReduced_tendsto_zero
#print axioms CriticalLinePhasor.ThreeDConverse.reduced_equation
#print axioms CriticalLinePhasor.ThreeDConverse.reduced_normalization
#print axioms CriticalLinePhasor.ThreeDConverse.reduced_tendsto_zero
