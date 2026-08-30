import c3b9_A3
import c3b10_A1

/-!
# C3 batch 10, block A2 — the cell density's exponential pairing, evaluated exactly

`c3b10_A1` evaluated the autocorrelation pairing of an arbitrary integrable weight.  Here it
is instantiated at the Riemann theta kernel, tilted by `e^{λt}`.  The tilt is exactly what
the carrier geometry wants: the two phasor legs of the cell are `u+p` and `u−p`, and

  `e^{λ(u+p)} · e^{λ(u−p)} = e^{2λu}`

**identically** — the tilt factorizes across the cell and reassembles as a pure function of
the cell centre.  So the whole exponential family of weights is evaluated in one stroke.

## What is new here relative to batches 6–9

Batches 6–9 bounded `cellDensity` by `modeBndS` and compared head against tail.  That is
worst-case analysis and the batch-9 numerics showed it cannot close on the window (the
negative lobe is within a factor ~6 of the positive one at `x = 14.134725`).  This block
instead computes the common mode **exactly**, for every `λ` at once, and the answer is a sum
of two squares.  Nothing is estimated.

## The new analytic input: a Gaussian majorant for `Φ`

The compiled `riemannXiKernel_le_majorant` gives only `Φ(u) ≤ K e^{−3u/2}`, which admits the
tilt only for `|λ| < 3/2`.  The true decay is doubly exponential, and `xiKernel_abs_gauss`
extracts a Gaussian from it — `|Φ(u)| ≤ K e^{−2πu²}` on **all** of `ℝ` — using batch 8's
`modeA_head_quad_lower` (`e^{2u} ≥ 1 + 2u + 2u²`) and `π > 3`.  That admits every `λ`.

SCOPE: this file proves an identity and a nonnegativity.  It says nothing about zeros.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B10

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open C3B6.Theta
open C3B8

/-! ### 1. A Gaussian majorant for the Riemann theta kernel -/

/-- `e^{2u} ≥ 1 + 2u + 2u²` on `u ≥ 0`, read off batch 8's head bound. -/
theorem exp_two_quad_lower {u : ℝ} (hu : 0 ≤ u) : 1 + 2 * u + 2 * u ^ 2 ≤ Real.exp (2 * u) := by
  have hpi := Real.pi_pos
  have hq := modeA_head_quad_lower hu
  rw [modeA_head] at hq
  nlinarith [hq, hpi]

theorem xiKernelTerm_gauss_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    riemannXiKernelTerm n u
      ≤ xiKernelMajorantCoeff n
        * Real.exp (9 * u / 2 - 2 * Real.pi * u - 2 * Real.pi * u ^ 2) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hr1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hrr : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [hr1]
  have hexp2 := exp_two_quad_lower hu
  -- the exponent comparison
  have hkey : 3 * ((n : ℝ) + 1) + 2 * Real.pi * u + 2 * Real.pi * u ^ 2
      ≤ Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u) := by
    have h1 : Real.pi * ((n : ℝ) + 1) ^ 2 * (1 + 2 * u + 2 * u ^ 2)
        ≤ Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u) :=
      mul_le_mul_of_nonneg_left hexp2 (by positivity)
    have h2 : 3 * ((n : ℝ) + 1) ≤ Real.pi * ((n : ℝ) + 1) ^ 2 := by nlinarith [hr1, hpi3]
    have h3 : 2 * Real.pi * u ≤ 2 * Real.pi * ((n : ℝ) + 1) ^ 2 * u := by
      have hz : (0 : ℝ) ≤ 2 * Real.pi * u * (((n : ℝ) + 1) ^ 2 - 1) :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith [hz]
    have h4 : 2 * Real.pi * u ^ 2 ≤ 2 * Real.pi * ((n : ℝ) + 1) ^ 2 * u ^ 2 := by
      have hz : (0 : ℝ) ≤ 2 * Real.pi * u ^ 2 * (((n : ℝ) + 1) ^ 2 - 1) :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith [hz]
    nlinarith [h1, h2, h3, h4]
  have hE : Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u))
      ≤ Real.exp (-(3 * ((n : ℝ) + 1))) * Real.exp (-(2 * Real.pi * u) - 2 * Real.pi * u ^ 2) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hkey]
  have hpos : (0 : ℝ) < Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)) :=
    Real.exp_pos _
  have hdrop : (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u / 2)
      - 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u / 2))
      ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u / 2) := by
    have hB : (0 : ℝ) ≤ 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u / 2) := by positivity
    linarith
  have hbig : (0 : ℝ) ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u / 2) := by
    positivity
  simp only [riemannXiKernelTerm, xiKernelMajorantCoeff]
  have hsplit : Real.exp (9 * u / 2 - 2 * Real.pi * u - 2 * Real.pi * u ^ 2)
      = Real.exp (9 * u / 2) * Real.exp (-(2 * Real.pi * u) - 2 * Real.pi * u ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  have hstep : (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u / 2)
      - 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u / 2))
      * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u))
      ≤ (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u / 2))
      * (Real.exp (-(3 * ((n : ℝ) + 1)))
          * Real.exp (-(2 * Real.pi * u) - 2 * Real.pi * u ^ 2)) := by
    refine mul_le_mul hdrop hE hpos.le hbig
  refine hstep.trans ?_
  have : Real.exp (-3 * ((n : ℝ) + 1)) = Real.exp (-(3 * ((n : ℝ) + 1))) := by
    congr 1; ring
  rw [this]
  ring_nf
  exact le_of_eq rfl

theorem xiKernel_gauss_half {u : ℝ} (hu : 0 ≤ u) :
    riemannXiKernel u
      ≤ xiKernelMajorantConstant
        * Real.exp (9 * u / 2 - 2 * Real.pi * u - 2 * Real.pi * u ^ 2) := by
  have hsum : (∑' n : ℕ, riemannXiKernelTerm n u)
      ≤ ∑' n : ℕ, xiKernelMajorantCoeff n
          * Real.exp (9 * u / 2 - 2 * Real.pi * u - 2 * Real.pi * u ^ 2) :=
    Summable.tsum_le_tsum (fun n => xiKernelTerm_gauss_le n hu)
      (riemannXiKernelTerm_summable u) (xiKernelMajorantCoeff_summable.mul_right _)
  rw [xiKernelMajorantCoeff_summable.tsum_mul_right] at hsum
  unfold riemannXiKernel xiKernelMajorantConstant
  calc 4 * ∑' n : ℕ, riemannXiKernelTerm n u
      ≤ 4 * ((∑' n : ℕ, xiKernelMajorantCoeff n)
          * Real.exp (9 * u / 2 - 2 * Real.pi * u - 2 * Real.pi * u ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (4 * ∑' n : ℕ, xiKernelMajorantCoeff n)
          * Real.exp (9 * u / 2 - 2 * Real.pi * u - 2 * Real.pi * u ^ 2) := by ring

/-- **THE GAUSSIAN MAJORANT, ON ALL OF `ℝ`.**  `|Φ(u)| ≤ K·e^{−2πu²}`.  The linear part of
the half-line exponent is absorbed because `2π > 9/2`; the reflection is
`riemannXiKernel_neg`. -/
theorem xiKernel_abs_gauss (u : ℝ) :
    |riemannXiKernel u|
      ≤ xiKernelMajorantConstant * Real.exp (-(2 * Real.pi * u ^ 2)) := by
  have hpi3 := Real.pi_gt_three
  have habs : riemannXiKernel u = riemannXiKernel |u| := by
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, riemannXiKernel_neg]
  have hnn : 0 ≤ riemannXiKernel u := (C3B5.A1.riemannXiKernel_pos_all u).le
  rw [abs_of_nonneg hnn, habs]
  refine (xiKernel_gauss_half (abs_nonneg u)).trans ?_
  have hK : (0 : ℝ) ≤ xiKernelMajorantConstant := xiKernelMajorantConstant_nonneg
  refine mul_le_mul_of_nonneg_left ?_ hK
  refine Real.exp_le_exp.mpr ?_
  have hsq : |u| ^ 2 = u ^ 2 := sq_abs u
  have hu0 : (0 : ℝ) ≤ |u| := abs_nonneg u
  nlinarith [hsq, hu0, hpi3]

/-! ### 2. The tilted weight -/

/-- The carrier weight: the theta kernel tilted by `e^{λt}`.  The tilt factorizes across the
cell — `e^{λ(u+p)}·e^{λ(u−p)} = e^{2λu}` — which is why the whole family evaluates at once. -/
def xiWeight (lam : ℝ) (t : ℝ) : ℝ := Real.exp (lam * t) * riemannXiKernel t

theorem xiWeight_measurable (lam : ℝ) : Measurable (xiWeight lam) := by
  unfold xiWeight
  exact (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).mul
    riemannXiKernel_measurable

theorem xiWeight_integrable (lam : ℝ) : Integrable (xiWeight lam) := by
  have hpi := Real.pi_pos
  have hmaj : Integrable (fun t : ℝ => xiKernelMajorantConstant
      * Real.exp (lam * t - 2 * Real.pi * t ^ 2)) :=
    (integrable_exp_lin_quad (b := 2 * Real.pi) (c := lam) (by linarith)).const_mul _
  refine Integrable.mono hmaj (xiWeight_measurable lam).aestronglyMeasurable ?_
  filter_upwards with t
  have hK : (0 : ℝ) ≤ xiKernelMajorantConstant := xiKernelMajorantConstant_nonneg
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ xiKernelMajorantConstant * Real.exp (lam * t - 2 * Real.pi * t ^ 2))]
  unfold xiWeight
  rw [abs_mul, abs_of_nonneg (Real.exp_pos (lam * t)).le]
  have hsplit : Real.exp (lam * t - 2 * Real.pi * t ^ 2)
      = Real.exp (lam * t) * Real.exp (-(2 * Real.pi * t ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
  rw [hsplit]
  have := xiKernel_abs_gauss t
  nlinarith [this, Real.exp_pos (lam * t), hK, abs_nonneg (riemannXiKernel t)]

/-! ### 3. THE EXACT EVALUATION OF THE CELL-DENSITY PAIRING -/

/-- **THE PAIRING OF THE CELL DENSITY AGAINST THE WHOLE EXPONENTIAL FAMILY, EXACTLY.**
For every real `x` and every real `λ`, one closed form, a sum of two squares. -/
theorem cellDensity_exp_pairing (x lam : ℝ) :
    (∫ u : ℝ, Real.exp (2 * lam * u) * cellDensity x u)
      = 2⁻¹ * (cosMom (xiWeight lam) x ^ 2 + sinMom (xiWeight lam) x ^ 2) := by
  have hkey : ∀ u : ℝ, Real.exp (2 * lam * u) * cellDensity x u
      = ∫ p : ℝ, xiWeight lam (u + p) * xiWeight lam (u - p) * Real.cos (2 * x * p) := by
    intro u
    unfold cellDensity
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    have hfac : Real.exp (lam * (u + p)) * Real.exp (lam * (u - p)) = Real.exp (2 * lam * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold xiWeight
    rw [← hfac]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hkey)]
  exact autocorrelation_pairing (xiWeight_integrable lam) (xiWeight_measurable lam) x

/-- **THE POSITIVITY, UNCONDITIONALLY, FOR EVERY `x` AND EVERY `λ`.**  No threshold on `x`,
no window, no head-versus-tail comparison. -/
theorem cellDensity_exp_pairing_nonneg (x lam : ℝ) :
    0 ≤ ∫ u : ℝ, Real.exp (2 * lam * u) * cellDensity x u := by
  rw [cellDensity_exp_pairing x lam]
  positivity

/-- The cell density is even in the cell centre — a pointwise consequence of the kernel's
reflection law, with no change of variables. -/
theorem cellDensity_even (x u : ℝ) : cellDensity x (-u) = cellDensity x u := by
  unfold cellDensity
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show riemannXiKernel (-u + p) * riemannXiKernel (-u - p) * Real.cos (2 * x * p)
      = riemannXiKernel (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
  have h1 : riemannXiKernel (-u + p) = riemannXiKernel (u - p) := by
    rw [show -u + p = -(u - p) by ring, riemannXiKernel_neg]
  have h2 : riemannXiKernel (-u - p) = riemannXiKernel (u + p) := by
    rw [show -u - p = -(u + p) by ring, riemannXiKernel_neg]
  rw [h1, h2]
  ring

/-- The tilted pairing integrand is integrable — inherited from the product integrability of
the carrier bilinear form, so nothing new has to be estimated. -/
theorem cellDensity_exp_integrable (x lam : ℝ) :
    Integrable (fun u : ℝ => Real.exp (2 * lam * u) * cellDensity x u) := by
  have hprod := carrierBilin_prod_integrable
    (xiWeight_integrable lam) (xiWeight_measurable lam) x
  have hleft := hprod.integral_prod_left
  refine hleft.congr ?_
  filter_upwards with u
  unfold cellDensity carrierBilin
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have hfac : Real.exp (lam * (u + p)) * Real.exp (lam * (u - p)) = Real.exp (2 * lam * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold xiWeight
  rw [← hfac]
  ring

end C3B10

section AxiomAudit
#print axioms C3B10.exp_two_quad_lower
#print axioms C3B10.xiKernelTerm_gauss_le
#print axioms C3B10.xiKernel_gauss_half
#print axioms C3B10.xiKernel_abs_gauss
#print axioms C3B10.xiWeight_measurable
#print axioms C3B10.xiWeight_integrable
#print axioms C3B10.cellDensity_exp_pairing
#print axioms C3B10.cellDensity_exp_pairing_nonneg
#print axioms C3B10.cellDensity_even
#print axioms C3B10.cellDensity_exp_integrable
end AxiomAudit
