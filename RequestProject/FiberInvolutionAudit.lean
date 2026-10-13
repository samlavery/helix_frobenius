import RequestProject.ChartKernelInformation

/-!
# Involution audit of the 3-D fiber (ledger 906 gate, upstairs only)

Two involutions act on the coordinate object `(σ, y) ↦ (phasor3D χ₂ σ y n)_n`.

* **Conjugation** `J₁ : (σ, y) ↦ (σ, −y)`.  The chart intertwines it with complex conjugation
  (`laneChart3D_neg`, termwise: `mellinSpin (−y) = conj (mellinSpin y)`), so a vanishing at `x`
  is a vanishing at `J₁x`. Its fixed signed ordinate is `y = 0`, the native origin of this
  height reversal. (`fixed_of_conjugation_iff`.)
* **The σ-reflection** `J₂ : (σ, y) ↦ (1 − σ, y)`.  Its fixed locus is `σ = ½`
  (`reflection_fixes_iff`, `partner_eq_self_iff`). Here σ is an uncentered analytic exponent:
  in the transverse coordinate `δ = σ - ½`, this is `δ ↦ -δ`, fixed at zero.
  The transverse displacement δ and the signed height y are different coordinates.
  The configuration at `J₂x` is the sitewise
  reciprocal rescaling of the configuration at `x` (`phasor3D_partner_rescale`), and its chart is
  the `(1 − 2σ)`-th radial moment of `x`'s configuration — a DIFFERENT linear functional of the same
  configuration (`laneChart3D_reflect_eq_moment`).  Geometrically nothing relates the `0`-moment
  (the chart) to the `(1−2σ)`-moment; the statement "a vanishing at `x` is a vanishing at `J₂x`" is
  the functional equation, which is not a property of the configuration.

No `sorry`, no `axiom`; no analytic input (the two identities are termwise algebra).
-/

open CriticalLinePhasor

noncomputable section

namespace CarrierReadout

/-- **The chart at the reflected state is a radial moment of the unreflected configuration**:
`laneChart3D (1−σ) y = Σ' (n+1)^{−(1−2σ)} · plane(v_n(σ, y))` (paired). -/
theorem laneChart3D_reflect_eq_moment (σ y : ℝ) :
    laneChart3D (1 - σ) y = deformationMoment σ y (1 - 2 * σ) := by
  rw [deformationMoment_eq]; congr 1; ring

/-- The conjugation involution is fixed exactly on the ordinate axis `y = 0`. -/
theorem fixed_of_conjugation_iff (y : ℝ) : (-y = y) ↔ y = 0 := by
  constructor <;> intro h <;> linarith

/-- The two involutions commute with the chart as follows: conjugation acts by `conj`;
the σ-reflection acts by passing to the `(1−2σ)`-moment. -/
theorem chart_under_involutions (σ y : ℝ) :
    laneChart3D σ (-y) = (starRingEnd ℂ) (laneChart3D σ y)
      ∧ laneChart3D (1 - σ) y = deformationMoment σ y (1 - 2 * σ) :=
  ⟨laneChart3D_neg σ y, laneChart3D_reflect_eq_moment σ y⟩

end CarrierReadout
