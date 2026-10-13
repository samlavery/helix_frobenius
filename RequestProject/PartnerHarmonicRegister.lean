import RequestProject.PartnerPhasorRigidity
import RequestProject.FiberZeroMidpointWindow

/-!
# The partner law and the midpoint, written in the harmonic register

`laneChart3D σ y` carries the unit-1 abscissa: the Cayley image of the end swap, where the partner
of `σ` is `1 − σ` and the fixed point is `1/2`.  The house writes results in the harmonic register:
the analytic abscissa is scaled by a harmonic unit `U` (canonically `π/3`), and reads
`σ_c = U·σ`, the partner reads `U − σ_c`, and the fixed point reads `U/2` (`π/6` at `U = π/3`).

This is an uncentered affine register. Its centered displacement is `σ_c-U/2`,
which negates under the partner action and is fixed at zero. Neither the choice
of unit nor this affine chart changes the native signed helix midpoint from zero.

This module restates the compiled unit-chart theorems in that register.  It adds no content: every
proof is the gauge law of `UnitMidpoint` (`σ = 1/2 ↔ σ·U = U/2`) applied to a compiled statement.

* `laneChartH U σ_c y` — the lane chart read at carrier abscissa `σ_c` with unit `U`.
* `laneChartH_partner_eq` — the end swap `σ_c ↦ U − σ_c` is the registration factor times the
  conjugate chart (`laneChart3D_partner_eq`, ledger 901).
* `partnerH_vanishing_iff` — the pair `(σ_c, y), (U − σ_c, y)` carries one datum.
* `partnerH_fixed_iff`, `partnerH_fixed_pi_div_three` — the fixed point is `U/2`; at `π/3` it is `π/6`.
* `OneVanishingPerHeightH`, `oneVanishingPerHeightH_iff` — link 3 in carrier units, equivalent to
  `OneVanishingPerHeight3D` for every unit.
* `midpointH_of_zero_below`, `midpointH_pi_div_three_of_zero_below` — in the window `|y| ≤ 1269/2`
  every vanishing sits at `U/2` (`π/6`), unconditionally.
* `onCarrier_of_oneVanishingPerHeightH` — the route's door, consumed in carrier units.
-/

open CriticalLinePhasor

namespace CarrierReadout

/-- The lane chart in the uncentered harmonic register: `σ_c / U` is the analytic abscissa.
The corresponding centered displacement is `σ_c-U/2`. -/
noncomputable def laneChartH (U σc y : ℝ) : ℂ := laneChart3D (σc / U) y

/-- `(U − σ_c) / U = 1 − σ_c / U`: the end swap in carrier units is the unit-chart swap. -/
theorem sub_div_eq_one_sub_div {U σc : ℝ} (hU : 0 < U) : (U - σc) / U = 1 - σc / U := by
  field_simp

/-- **The end swap in carrier units.**  For `0 < σ_c < U`, the chart at `U − σ_c` is the
registration factor times the conjugate of the chart at `σ_c` (the functional equation,
`laneChart3D_partner_eq`). -/
theorem laneChartH_partner_eq {U σc y : ℝ} (hU : 0 < U) (h0 : 0 < σc) (h1 : σc < U) :
    laneChartH U (U - σc) y
      = (starRingEnd ℂ) (partnerFactor (((σc / U : ℝ) : ℂ) + (y : ℂ) * Complex.I)
          * laneChartH U σc y) := by
  unfold laneChartH
  rw [sub_div_eq_one_sub_div hU]
  exact laneChart3D_partner_eq (div_pos h0 hU) ((div_lt_one hU).mpr h1)

/-- **The pair `(σ_c, y), (U − σ_c, y)` carries one datum**, in carrier units. -/
theorem partnerH_vanishing_iff {U σc y : ℝ} (hU : 0 < U) (h0 : 0 < σc) (h1 : σc < U) :
    laneChartH U (U - σc) y = 0 ↔ laneChartH U σc y = 0 := by
  unfold laneChartH
  rw [sub_div_eq_one_sub_div hU]
  exact partner_vanishing_iff (div_pos h0 hU) ((div_lt_one hU).mpr h1)

/-- The fixed point of the end swap in carrier units is `U/2`. -/
theorem partnerH_fixed_iff (U σc : ℝ) : U - σc = σc ↔ σc = U / 2 :=
  CriticalLinePhasor.UnitMidpoint.affine_reflection_fixed_iff U σc

/-- At the canonical unit `π/3` the fixed point is `π/6`. -/
theorem partnerH_fixed_pi_div_three (σc : ℝ) :
    Real.pi / 3 - σc = σc ↔ σc = Real.pi / 6 := by
  rw [partnerH_fixed_iff, show Real.pi / 3 / 2 = Real.pi / 6 by ring]

/-- Link 3 in carrier units: at each height at most one carrier abscissa in `(0, U)` vanishes. -/
def OneVanishingPerHeightH (U : ℝ) : Prop :=
  ∀ (y σ₁ σ₂ : ℝ), 0 < σ₁ → σ₁ < U → 0 < σ₂ → σ₂ < U →
    laneChartH U σ₁ y = 0 → laneChartH U σ₂ y = 0 → σ₁ = σ₂

/-- The gauge is free: link 3 in carrier units is link 3 in the unit chart, for every unit. -/
theorem oneVanishingPerHeightH_iff {U : ℝ} (hU : 0 < U) :
    OneVanishingPerHeightH U ↔ OneVanishingPerHeight3D := by
  constructor
  · intro h y σ₁ σ₂ h10 h11 h20 h21 hz1 hz2
    have key := h y (U * σ₁) (U * σ₂) (mul_pos hU h10) (mul_lt_of_lt_one_right hU h11)
      (mul_pos hU h20) (mul_lt_of_lt_one_right hU h21)
      (by unfold laneChartH; rw [mul_div_cancel_left₀ _ hU.ne']; exact hz1)
      (by unfold laneChartH; rw [mul_div_cancel_left₀ _ hU.ne']; exact hz2)
    exact mul_left_cancel₀ hU.ne' key
  · intro h y σ₁ σ₂ h10 h11 h20 h21 hz1 hz2
    unfold laneChartH at hz1 hz2
    have key := h y (σ₁ / U) (σ₂ / U) (div_pos h10 hU) ((div_lt_one hU).mpr h11)
      (div_pos h20 hU) ((div_lt_one hU).mpr h21) hz1 hz2
    exact (div_left_inj' hU.ne').mp key

/-- In the window `|y| ≤ 1269/2`, every vanishing has affine chart coordinate `U/2`,
or centered displacement zero (`midpoint_of_fiber3D_zero_below`). -/
theorem midpointH_of_zero_below {U σc y : ℝ} (hU : 0 < U) (h0 : 0 < σc) (h1 : σc < U)
    (hy : |y| ≤ 1269 / 2) (hz : laneChartH U σc y = 0) : σc = U / 2 := by
  unfold laneChartH at hz
  have key := midpoint_of_fiber3D_zero_below (div_pos h0 hU) ((div_lt_one hU).mpr h1) hy hz
  rw [div_eq_iff hU.ne'] at key
  linarith

/-- At the canonical unit, the window's vanishings sit at `π/6`. -/
theorem midpointH_pi_div_three_of_zero_below {σc y : ℝ} (h0 : 0 < σc) (h1 : σc < Real.pi / 3)
    (hy : |y| ≤ 1269 / 2) (hz : laneChartH (Real.pi / 3) σc y = 0) : σc = Real.pi / 6 := by
  have key := midpointH_of_zero_below (by positivity) h0 h1 hy hz
  rw [key]; ring

/-- The route's door, consumed in carrier units: link 3 at any unit puts every nontrivial zero on
the line. -/
theorem onCarrier_of_oneVanishingPerHeightH {U : ℝ} (hU : 0 < U) (h : OneVanishingPerHeightH U) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 :=
  rh_of_oneVanishingPerHeight3D ((oneVanishingPerHeightH_iff hU).mp h)

end CarrierReadout

#print axioms CarrierReadout.laneChartH_partner_eq
#print axioms CarrierReadout.partnerH_vanishing_iff
#print axioms CarrierReadout.oneVanishingPerHeightH_iff
#print axioms CarrierReadout.midpointH_pi_div_three_of_zero_below
#print axioms CarrierReadout.onCarrier_of_oneVanishingPerHeightH
