import c3b10_A2

/-!
# C3 batch 10, block A3 — the half-line `cosh` pairing, and where the target actually sits

`c3b10_A2` evaluated `∫_ℝ e^{2λu}C(x,u)du` exactly, for every `x` and `λ`.  Since `C(x,·)` is
even (`cellDensity_even`), averaging `λ` against `−λ` and folding to the half line gives the
**unconditional** family

  `0 ≤ ∫_{(0,∞)} cosh(2λu)·C(x,u) du`     for every real `x` and every real `λ`,

together with its exact value.  At `λ = 0` this is `∫_{(0,∞)}C(x,u)du = ¼(Ξc² + Ξs²)` — the
first tail of the cell density at the left endpoint of the batch-9 window, evaluated in
closed form rather than estimated.

## Where the open target sits, exactly

The batch-9 chain ends on `0 ≤ ∫_{(0,∞)} gY y u · C(x,u) du` with `gY y u = u·sinh(2yu)`, and

  `∂/∂λ [ cosh(2λu) ] = 2u·sinh(2λu) = 2·gY λ u`     (`gY_eq_cosh_deriv`)

So the compiled family and the open target are the *same one-parameter family*, one being the
`λ`-derivative of the other.  What this block delivers unconditionally is the **value** of the
family; the target asks for its **monotonicity** in `λ`.  That is a sharp and checkable
statement of the remaining gap, and it is stated here as a property of this instrument —
the exponential/`cosh` weight cone — not as a claim about the problem.

SCOPE: identities and one nonnegativity.  Nothing here mentions zeros.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B10

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open CriticalLinePhasor.WeightedTail
open C3B6.Theta

/-! ### 1. The `cosh` fold -/

theorem cosh_split (x lam u : ℝ) :
    Real.cosh (2 * lam * u) * cellDensity x u
      = 2⁻¹ * (Real.exp (2 * lam * u) * cellDensity x u
          + Real.exp (2 * (-lam) * u) * cellDensity x u) := by
  rw [Real.cosh_eq, show 2 * (-lam) * u = -(2 * lam * u) by ring]
  ring

theorem cellDensity_cosh_integrable (x lam : ℝ) :
    Integrable (fun u : ℝ => Real.cosh (2 * lam * u) * cellDensity x u) := by
  have h1 := cellDensity_exp_integrable x lam
  have h2 := cellDensity_exp_integrable x (-lam)
  refine ((h1.add h2).const_mul (2⁻¹ : ℝ)).congr ?_
  filter_upwards with u
  exact (cosh_split x lam u).symm

/-- **The `cosh` pairing on the whole line, exactly.**  Four squares. -/
theorem cellDensity_cosh_full (x lam : ℝ) :
    (∫ u : ℝ, Real.cosh (2 * lam * u) * cellDensity x u)
      = 4⁻¹ * (cosMom (xiWeight lam) x ^ 2 + sinMom (xiWeight lam) x ^ 2
          + (cosMom (xiWeight (-lam)) x ^ 2 + sinMom (xiWeight (-lam)) x ^ 2)) := by
  have h1 := cellDensity_exp_integrable x lam
  have h2 := cellDensity_exp_integrable x (-lam)
  rw [integral_congr_ae (Filter.Eventually.of_forall (cosh_split x lam)),
    integral_const_mul, integral_add h1 h2,
    cellDensity_exp_pairing x lam, cellDensity_exp_pairing x (-lam)]
  ring

/-! ### 2. Folding to the half line -/

theorem cellDensity_cosh_even (x lam u : ℝ) :
    Real.cosh (2 * lam * -u) * cellDensity x (-u)
      = Real.cosh (2 * lam * u) * cellDensity x u := by
  rw [show 2 * lam * -u = -(2 * lam * u) by ring, Real.cosh_neg, cellDensity_even]

theorem cellDensity_cosh_Ioi (x lam : ℝ) :
    (∫ u in Ioi (0 : ℝ), Real.cosh (2 * lam * u) * cellDensity x u)
      = 2⁻¹ * ∫ u : ℝ, Real.cosh (2 * lam * u) * cellDensity x u := by
  have habs := integral_comp_abs
    (f := fun u : ℝ => Real.cosh (2 * lam * u) * cellDensity x u)
  have hcongr : (∫ u : ℝ, Real.cosh (2 * lam * |u|) * cellDensity x |u|)
      = ∫ u : ℝ, Real.cosh (2 * lam * u) * cellDensity x u := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show Real.cosh (2 * lam * |u|) * cellDensity x |u|
        = Real.cosh (2 * lam * u) * cellDensity x u
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h]
      exact cellDensity_cosh_even x lam u
  rw [hcongr] at habs
  linarith [habs]

/-- **THE UNCONDITIONAL HALF-LINE FAMILY.**  For every real `x` and every real `λ`.  No
threshold on `x`, no window, no head-versus-tail comparison: the value is a sum of squares. -/
theorem cellDensity_cosh_Ioi_nonneg (x lam : ℝ) :
    0 ≤ ∫ u in Ioi (0 : ℝ), Real.cosh (2 * lam * u) * cellDensity x u := by
  rw [cellDensity_cosh_Ioi, cellDensity_cosh_full]
  positivity

/-! ### 3. The `λ = 0` member: the first tail at the window's left endpoint -/

theorem xiWeight_zero : xiWeight 0 = riemannXiKernel := by
  funext t
  unfold xiWeight
  simp

/-- **THE FIRST TAIL, EXACTLY.**  `∫_{(0,∞)} C(x,u) du = ¼(Ξc(x)² + Ξs(x)²)`.  Batch 9 could
only bound this quantity on the certified height; here it is evaluated in closed form on the
whole half line, for every real `x`. -/
theorem cellDensity_Ioi_eq (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), cellDensity x u)
      = 4⁻¹ * (cosMom riemannXiKernel x ^ 2 + sinMom riemannXiKernel x ^ 2) := by
  have hz : ∀ u : ℝ, Real.cosh (2 * (0 : ℝ) * u) * cellDensity x u = cellDensity x u := by
    intro u
    rw [show 2 * (0 : ℝ) * u = 0 by ring, Real.cosh_zero, one_mul]
  have h := cellDensity_cosh_Ioi x 0
  have h2 := cellDensity_cosh_full x 0
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hz u)] at h
  rw [integral_congr_ae (Filter.Eventually.of_forall hz)] at h2
  rw [h, integral_congr_ae (Filter.Eventually.of_forall hz), h2, neg_zero, xiWeight_zero]
  ring

theorem cellDensity_Ioi_nonneg (x : ℝ) : 0 ≤ ∫ u in Ioi (0 : ℝ), cellDensity x u := by
  rw [cellDensity_Ioi_eq]
  positivity

/-! ### 4. Where the open target sits relative to this family -/

/-- **THE EXACT RELATION.**  The batch-9 target weight `gY y u = u·sinh(2yu)` is one half the
`λ`-derivative of the compiled `cosh` family at `λ = y`.  So the open question is not the
*value* of the pairing — that is settled above — but its *monotonicity in `λ`*. -/
theorem gY_eq_cosh_deriv (y u : ℝ) :
    HasDerivAt (fun lam : ℝ => Real.cosh (2 * lam * u)) (2 * (u * Real.sinh (2 * y * u))) y := by
  have hlin : HasDerivAt (fun lam : ℝ => 2 * lam * u) (2 * u) y := by
    have h1 : HasDerivAt (fun lam : ℝ => 2 * lam) 2 y := by
      simpa using (hasDerivAt_id y).const_mul (2 : ℝ)
    simpa using h1.mul_const u
  have hcomp := (Real.hasDerivAt_cosh (2 * y * u)).comp y hlin
  refine hcomp.congr_deriv ?_
  ring

end C3B10

section AxiomAudit
#print axioms C3B10.cosh_split
#print axioms C3B10.cellDensity_cosh_integrable
#print axioms C3B10.cellDensity_cosh_full
#print axioms C3B10.cellDensity_cosh_even
#print axioms C3B10.cellDensity_cosh_Ioi
#print axioms C3B10.cellDensity_cosh_Ioi_nonneg
#print axioms C3B10.xiWeight_zero
#print axioms C3B10.cellDensity_Ioi_eq
#print axioms C3B10.cellDensity_Ioi_nonneg
#print axioms C3B10.gY_eq_cosh_deriv
end AxiomAudit
