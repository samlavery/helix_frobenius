import RequestProject.ThreeDFocalEvent
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The projection lands on the line, and on nothing else

Sam (2026-09-11): "can you project something from 3D, through 2D, to 1D and land on anything besides a
line?"  No.  This file makes that an unconditional theorem about the compiled carrier.

A carrier state is a point of the helix (`CarrierState3D`, a geometric membership certificate with no
character, L-function, zero predicate or event in it).  The projection chain is:
* 3D → 2D: `toUnitCylinder` compresses the point radially onto the unit cylinder; the radius is dropped
  (it is booked in the loss ledger, `ConeProjection.record_bijective` in `RoundTrip.lean`);
* 2D → 1D: `toHeight` drops the angle (booked likewise) and keeps the physical height `Z`;
* the chart reads the height at the area-law abscissa: `carrierPointAtHeight Z = carrierAbscissa + i log Z`,
  and `carrierAbscissa = ½` is the unique scale-balanced abscissa (`carrierAbscissa_eq_half`, from the
  arclength area law, `carrierScaleBalanced_iff`).

The abscissa is therefore not a coordinate of the projection at all: it is the same area-law output for
every state.  Hence (`range_chartReadout`) the image of the whole chain is exactly the line `Re = ½`:
every carrier state lands on it, every point of it is hit, and a point off the line is the readout of
no carrier state (`not_chartReadout_of_re_ne`).  Nothing here mentions zeros; the corollary for an
off-line zero, should one exist, is that it is not the projection of any carrier state
(`offLine_zero_not_chartReadout`).  Standard axioms only.
-/

open Complex

namespace CriticalLinePhasor.ThreeDFocal

/-- 3D → 2D: radial compression onto the unit cylinder.  The radius is dropped (booked in the ledger);
the direction on the circle and the height are kept. -/
noncomputable def toUnitCylinder (P : ℝ × ℝ × ℝ) : (ℝ × ℝ) × ℝ :=
  ((P.1 / Real.sqrt (P.1 ^ 2 + P.2.1 ^ 2), P.2.1 / Real.sqrt (P.1 ^ 2 + P.2.1 ^ 2)), P.2.2)

/-- 2D → 1D: the angle is dropped (booked in the ledger); the physical height alone remains. -/
def toHeight (Q : (ℝ × ℝ) × ℝ) : ℝ := Q.2

/-- The chain 3D → 2D → 1D returns the third spatial coordinate, the physical height. -/
theorem toHeight_toUnitCylinder (P : ℝ × ℝ × ℝ) : toHeight (toUnitCylinder P) = P.2.2 := rfl

/-- The full chain read into the chart: 3D → 2D → 1D → the ordinate `log Z` at the area-law abscissa. -/
noncomputable def CarrierState3D.chartReadout {p r : ℝ} (s : CarrierState3D p r) : ℂ :=
  carrierPointAtHeight (toHeight (toUnitCylinder s.point))

theorem CarrierState3D.chartReadout_eq {p r : ℝ} (s : CarrierState3D p r) :
    s.chartReadout = carrierPointAtHeight s.physicalHeight := rfl

/-- **Every projected carrier state lands on the line.** -/
theorem CarrierState3D.chartReadout_re {p r : ℝ} (s : CarrierState3D p r) :
    s.chartReadout.re = 1 / 2 := by
  rw [CarrierState3D.chartReadout_eq, carrierPointAtHeight_re, carrierAbscissa_eq_half]

/-- The ordinate is recovered exactly: the chart reads `log` of the height `exp ordinate`. -/
theorem CarrierState3D.chartReadout_im {p r : ℝ} (hp : p ≠ 0) (s : CarrierState3D p r) :
    s.chartReadout.im = s.ordinate := by
  rw [CarrierState3D.chartReadout_eq, carrierPointAtHeight_im, s.physicalHeight_eq_exp hp,
    Real.log_exp]

theorem CarrierState3D.chartReadout_eq_carrierPoint {p r : ℝ} (hp : p ≠ 0)
    (s : CarrierState3D p r) : s.chartReadout = carrierPoint s.ordinate := by
  rw [CarrierState3D.chartReadout_eq, s.physicalHeight_eq_exp hp, carrierPointAtHeight_exp]

/-- **Nothing off the line is the projection of any carrier state.** -/
theorem not_chartReadout_of_re_ne {p r : ℝ} (ρ : ℂ) (h : ρ.re ≠ 1 / 2)
    (s : CarrierState3D p r) : s.chartReadout ≠ ρ := by
  intro hs
  apply h
  rw [← hs]
  exact s.chartReadout_re

/-- Every point of the line is the projection of a carrier state (the state at ordinate `Im ρ`). -/
theorem exists_chartReadout_eq {p r : ℝ} (hp : p ≠ 0) (ρ : ℂ) (h : ρ.re = 1 / 2) :
    ∃ s : CarrierState3D p r, s.chartReadout = ρ := by
  refine ⟨carrierState3D p r ρ.im, ?_⟩
  rw [CarrierState3D.chartReadout_eq_carrierPoint hp]
  show carrierPoint ρ.im = ρ
  rw [carrierPoint_eq_half_add_I]
  apply Complex.ext <;> simp [h]

/-- **THE THEOREM.**  The image of the projection 3D → 2D → 1D → chart is exactly the line `Re = ½`:
you cannot land anywhere else. -/
theorem range_chartReadout {p r : ℝ} (hp : p ≠ 0) :
    Set.range (CarrierState3D.chartReadout (p := p) (r := r)) = {ρ : ℂ | ρ.re = 1 / 2} := by
  ext ρ
  constructor
  · rintro ⟨s, rfl⟩
    exact s.chartReadout_re
  · intro h
    exact exists_chartReadout_eq hp ρ h

/-- Corollary at the zero level: an off-line zero, should one exist, is the projection of no carrier
state.  The zero set enters only in the hypothesis. -/
theorem offLine_zero_not_chartReadout {p r : ℝ} (ρ : ℂ) (_hζ : riemannZeta ρ = 0)
    (_hstrip : 0 < ρ.re ∧ ρ.re < 1) (hoff : ρ.re ≠ 1 / 2) :
    ∀ s : CarrierState3D p r, s.chartReadout ≠ ρ :=
  fun s => not_chartReadout_of_re_ne ρ hoff s

/-- **Coverage gives RH.**  Because the image of the projection is exactly the line, COVERAGE — every
nontrivial zero is the chart readout of some carrier state — gives the Riemann Hypothesis. Coverage is
the seating. -/
theorem riemannHypothesis_of_zeros_covered {p r : ℝ}
    (hcov : ∀ (ρ : ℂ), riemannZeta ρ = 0 → (¬∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 →
        ∃ s : CarrierState3D p r, s.chartReadout = ρ) :
    RiemannHypothesis := by
  intro ρ hζ hnt h1
  obtain ⟨s, hs⟩ := hcov ρ hζ hnt h1
  rw [← hs]
  exact s.chartReadout_re

end CriticalLinePhasor.ThreeDFocal
