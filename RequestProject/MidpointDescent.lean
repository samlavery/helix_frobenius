import RequestProject.FiberIsTheFunction
import RequestProject.GeometricReadout

/-!
# The midpoint zero descends: a vanishing on the 3-D midpoint locus is a zero of ζ on the line

The question, in the form it was put: let `π : X₃ → L₁` be the dimensional reduction, `M₃` the
3-D midpoint locus and `m₁` the 1-D midpoint with `π(M₃) = m₁`; let `F₃` be the quantity that
vanishes upstairs.  Midpoint preservation alone does not carry a zero downstairs — the
projection could discard the component that defines it.  What is needed is the intertwining
`F₁(π x) = P(F₃ x)` with `P(0) = 0`; then `F₃ x = 0 ⟹ F₁(m₁) = 0`.  And the reverse implication
is harder in general, since a projection can create zeros by cancellation between fibers.

This file states and proves each step on the paper's objects.

* **The descent of a vanishing datum.**  A 3-D vanishing datum is a real height `γ`
  (the ordinate of the event); its descent is `π(γ) = ½ + iγ` (`descend`).
* **Midpoint → midpoint.**  The 3-D midpoint locus is the fixed set of the end-swap, which in
  the ordinate variable is conjugation `z ↦ z̄` (`CarrierOffLinePairing.crit_is_conj`): a real
  `γ` is fixed (`descend_fixed_by_endSwap`); after the Cayley step it lies on the unit circle,
  the 2-D midpoint (`descend_on_unit_circle`, via `Readout.cayley_real_norm_one`); and its
  abscissa is exactly `½` (`descend_re`; the house's `midpoint_projects_to_half`), the fixed
  locus of the functional-equation reflection (`descend_fixed_by_reflection`; the house's
  `reflection_fixes_iff`).
* **The vanishing upstairs.**  `F₃(γ) := laneChart3D (½) γ = 0`: the focal cancellation of the
  three-dimensional phasors at the midpoint locus, at height `e^γ`.  (The phasors themselves
  never vanish — `fiber_phasor_ne_zero`; the only 3-D vanishing is the channels closing.)
* **The intertwining map.**  `P γ v := v / (1 − 2^{1−π(γ)})`: the lane factor divided out.
  `P γ 0 = 0` (`P_zero`), and `P γ` is injective (`P_injective`), because the lane factor does
  not vanish on the line.
* **The intertwining identity** (`zeta_descend_eq_P_laneChart3D`):
  `ζ(π γ) = P γ (F₃ γ)`.  This is Theorem 17 of the paper (`fiber3D_eq_function`) read at
  carrier scale `1` and abscissa `½`.
* **The composite** (`midpoint_zero_descends`):
  `F₃ γ = 0 ⟺ ζ(½ + iγ) = 0`.  The forward implication is `P γ 0 = 0`; the converse holds
  because `P γ` is injective — here the projection creates no zeros by cancellation between
  fibers, since there is one fiber and the chart is applied after the sum: cancellation within
  the sum *is* the 3-D vanishing.

Every statement is unconditional.
-/

open CriticalLinePhasor

noncomputable section

namespace CarrierReadout

/-- **The descent of a 3-D vanishing datum.**  A real height `γ` lands at `π(γ) = ½ + iγ`. -/
def descend (γ : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I

theorem descend_eq (γ : ℝ) : descend γ = (1 : ℂ) / 2 + (γ : ℂ) * Complex.I := by
  unfold descend; push_cast; ring

/-! ### Midpoint → midpoint -/

/-- The end-swap in the ordinate variable is conjugation; a real height is fixed by it. -/
theorem descend_fixed_by_endSwap (γ : ℝ) : (starRingEnd ℂ) (γ : ℂ) = (γ : ℂ) :=
  Complex.conj_ofReal γ

/-- After the Cayley step (`3-D → 2-D`) the datum lies on the unit circle, the 2-D midpoint. -/
theorem descend_on_unit_circle (γ : ℝ) : ‖Readout.cayley (γ : ℂ)‖ = 1 :=
  Readout.cayley_real_norm_one γ

/-- **The descent lands on the 1-D midpoint**: the abscissa of `π(γ)` is exactly `½`
(the house's `midpoint_projects_to_half`). -/
theorem descend_re (γ : ℝ) : (descend γ).re = 1 / 2 := by
  rw [descend_eq]; simp [Complex.add_re, Complex.mul_re]

/-- The 1-D midpoint is the fixed locus of the functional-equation reflection `s ↦ 1 − s`
(the house's `reflection_fixes_iff`). -/
theorem descend_fixed_by_reflection (γ : ℝ) : (1 - descend γ).re = (descend γ).re := by
  rw [Complex.sub_re, Complex.one_re, descend_re]; norm_num

theorem descend_ne_one (γ : ℝ) : descend γ ≠ 1 := by
  intro h; have := congrArg Complex.re h; rw [descend_re] at this; norm_num at this

theorem descend_re_lt_one (γ : ℝ) : (descend γ).re < 1 := by rw [descend_re]; norm_num

/-! ### The vanishing upstairs, and the intertwining map -/

/-- **The 3-D vanishing on the midpoint locus**: the focal cancellation of the three-dimensional
phasors at abscissa `½` and height `e^γ`. -/
def midpointFocalZero (γ : ℝ) : Prop := laneChart3D (1 / 2) γ = 0

/-- **The intertwining map** `P`: the lane factor divided out, at the descended point. -/
def P (γ : ℝ) (v : ℂ) : ℂ := v / (1 - (2 : ℂ) ^ ((1 : ℂ) - descend γ))

theorem P_zero (γ : ℝ) : P γ 0 = 0 := by unfold P; simp

theorem laneFactor_descend_ne_zero (γ : ℝ) : (1 - (2 : ℂ) ^ ((1 : ℂ) - descend γ)) ≠ 0 :=
  lane_factor_ne_zero (descend_re_lt_one γ)

theorem P_injective (γ : ℝ) : Function.Injective (P γ) := by
  intro v w h
  unfold P at h
  exact (div_left_inj' (laneFactor_descend_ne_zero γ)).mp h

theorem P_eq_zero_iff (γ : ℝ) (v : ℂ) : P γ v = 0 ↔ v = 0 := by
  unfold P
  rw [div_eq_zero_iff]
  exact ⟨fun h => h.resolve_right (laneFactor_descend_ne_zero γ), fun h => Or.inl h⟩

/-! ### The intertwining identity and the composite -/

/-- **The intertwining identity** `F₁(π γ) = P(F₃ γ)`: `ζ(½ + iγ) = P γ (laneChart3D (½) γ)`.
Theorem 17 of the paper (`fiber3D_eq_function`) at carrier scale `1`, abscissa `½`. -/
theorem zeta_descend_eq_P_laneChart3D (γ : ℝ) :
    riemannZeta (descend γ) = P γ (laneChart3D (1 / 2) γ) := by
  have h := fiber3D_eq_function 1 one_pos (1 / 2) γ (by norm_num)
    (by rw [show ((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I = descend γ from rfl]; exact descend_ne_one γ)
  have hs : ((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I = descend γ := rfl
  rw [hs] at h
  unfold CarrierParity.carrierFiber at h
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at h
  -- h : laneChart3D (1/2) γ = (1 - 2^(1 - descend γ)) * ζ (descend γ)
  unfold P
  rw [h, mul_div_cancel_left₀ _ (laneFactor_descend_ne_zero γ)]

/-- **THE MIDPOINT ZERO DESCENDS, AND CONVERSELY.**  A vanishing of the three-dimensional fiber
on the midpoint locus, at height `e^γ`, is exactly a zero of `ζ` at `½ + iγ`.  Forward: `P(0) = 0`.
Converse: `P` is injective — the projection creates no zeros by cancellation between fibers. -/
theorem midpoint_zero_descends (γ : ℝ) :
    midpointFocalZero γ ↔ riemannZeta (descend γ) = 0 := by
  unfold midpointFocalZero
  rw [zeta_descend_eq_P_laneChart3D, P_eq_zero_iff]

/-- The forward implication alone, in the form of the question: a 3-D midpoint zero forces a
1-D zero at the midpoint abscissa `½`. -/
theorem zero_of_midpointFocalZero (γ : ℝ) (h : midpointFocalZero γ) :
    riemannZeta (descend γ) = 0 ∧ (descend γ).re = 1 / 2 :=
  ⟨(midpoint_zero_descends γ).mp h, descend_re γ⟩

end CarrierReadout
