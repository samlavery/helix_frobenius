import RequestProject.FiberDetectorChain
import RequestProject.ProjectionLandsOnLine
import RequestProject.CarrierRadialDegreeAudit

/-!
# The event is projected (ledger 1154)

What the projection does to the event, on the helix itself (`Geometry.gammaY`). The transverse
coordinate is identified before its value is named. The analytic reflection `1 − s` does not occur,
and neither does `RepresentsBothEnds`.

* The event read at fiber parameter `s` sits on the helix at ordinate `Im s` (`eventState`), at
  physical height `e^{Im s}` (`eventState_height`).
* Projection (`toUnitCylinder`, then `toHeight`) keeps the height and nothing else
  (`project_event`). On the helix the dropped radius and angle are functions of that height
  (`event_point_of_height`), so the projection loses nothing about the event and separates events
  (`project_event_injective`). What the projection sees of an event is its ordinate alone
  (`eventState_eq_of_im_eq`).
* The projected event has no transverse coordinate of its own. Its chart point is the carrier point
  of its ordinate (`event_readout`). The transverse coordinate there is the carrier's: the exponent at
  which a fiber amplitude reciprocates the carrier radius with no radial drift, and the only such
  exponent (`event_transverse_balanced`). It is the same for every helix pitch and growth rate
  (`balance_gauge_free`). (Its uniqueness is proved by computing the area law.)
* Afterward, the value: `event_transverse_value`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.EventProjection

open CriticalLinePhasor CriticalLinePhasor.ThreeDFocal

/-- The event read at fiber parameter `s`, placed on the helix at its ordinate `Im s`. -/
def eventState (p r : ℝ) (s : ℂ) : CarrierState3D p r :=
  carrierState3D p r s.im

theorem eventState_height {p r : ℝ} (hp : p ≠ 0) (s : ℂ) :
    (eventState p r s).physicalHeight = Real.exp s.im :=
  (eventState p r s).physicalHeight_eq_exp hp

/-- What the projection sees of an event is its ordinate alone. -/
theorem eventState_eq_of_im_eq (p r : ℝ) {s s' : ℂ} (h : s.im = s'.im) :
    eventState p r s = eventState p r s' := by
  unfold eventState
  rw [h]

/-- **Projection keeps the height.** -/
theorem project_event {p r : ℝ} (hp : p ≠ 0) (s : ℂ) :
    toHeight (toUnitCylinder (eventState p r s).point) = Real.exp s.im := by
  rw [toHeight_toUnitCylinder]
  exact eventState_height hp s

/-- **The dropped coordinates are functions of the kept height**: the event's helix point is
recovered from its projected height `Z` as `((r/p)·Z·cos(2πZ/p), (r/p)·Z·sin(2πZ/p), Z)`. -/
theorem event_point_of_height {p r : ℝ} (hp : p ≠ 0) (s : ℂ) :
    (eventState p r s).point =
      ((r / p) * toHeight (toUnitCylinder (eventState p r s).point) *
          Real.cos (2 * Real.pi * toHeight (toUnitCylinder (eventState p r s).point) / p),
        (r / p) * toHeight (toUnitCylinder (eventState p r s).point) *
          Real.sin (2 * Real.pi * toHeight (toUnitCylinder (eventState p r s).point) / p),
        toHeight (toUnitCylinder (eventState p r s).point)) := by
  rw [project_event hp s]
  exact Geometry.gammaY_eq p r s.im hp

/-- **Projection separates events**: equal projected heights mean the same helix point and the same
ordinate. -/
theorem project_event_injective {p r : ℝ} (hp : p ≠ 0) {s s' : ℂ}
    (h : toHeight (toUnitCylinder (eventState p r s).point) =
      toHeight (toUnitCylinder (eventState p r s').point)) :
    s.im = s'.im ∧ (eventState p r s).point = (eventState p r s').point := by
  rw [project_event hp, project_event hp] at h
  have him : s.im = s'.im := Real.exp_injective h
  exact ⟨him, by rw [eventState_eq_of_im_eq p r him]⟩

/-- The chart point of the projected event is the carrier point of its ordinate. -/
theorem event_readout {p r : ℝ} (hp : p ≠ 0) (s : ℂ) :
    (eventState p r s).chartReadout = carrierPoint s.im ∧
      (eventState p r s).chartReadout.im = s.im :=
  ⟨(eventState p r s).chartReadout_eq_carrierPoint hp, (eventState p r s).chartReadout_im hp⟩

/-- **The transverse coordinate of a projected event is the carrier's balance exponent**: the
exponent at which a fiber amplitude reciprocates the carrier radius with no radial drift, and the
only one. -/
theorem event_transverse_balanced (p r : ℝ) (s : ℂ) :
    CarrierScaleBalanced (eventState p r s).chartReadout.re ∧
      ∀ σ : ℝ, CarrierScaleBalanced σ → σ = (eventState p r s).chartReadout.re := by
  have hre : (eventState p r s).chartReadout.re = carrierAbscissa := by
    rw [CarrierState3D.chartReadout_eq, carrierPointAtHeight_re]
  rw [hre]
  exact ⟨carrierAbscissa_scaleBalanced, fun σ hσ =>
    exists_unique_carrierScaleBalanced.unique hσ carrierAbscissa_scaleBalanced⟩

/-- The balance exponent does not depend on the helix's pitch or growth rate. -/
theorem balance_gauge_free (p' r' : ℝ) (hr' : 0 < r') (σ : ℝ) :
    CarrierScaleBalanced σ ↔
      ∃ L : ℝ, 0 < L ∧
        Tendsto (fun n : ℕ => (n : ℝ) ^ (-σ) * Geometry.carrierRadius p' r' n) atTop (𝓝 L) :=
  CarrierRadialDegree.scaleBalance_gauge_free 1 3 p' r' (by norm_num) hr' σ

/-- **Afterward, the value**: the balance exponent read by every projected event is `½` (the area
law, `carrierScaleBalanced_iff`). -/
theorem event_transverse_value (p r : ℝ) (s : ℂ) :
    (eventState p r s).chartReadout.re = 1 / 2 := by
  rw [CarrierState3D.chartReadout_eq, carrierPointAtHeight_re, carrierAbscissa_eq_half]

end CriticalLinePhasor.EventProjection

#print axioms CriticalLinePhasor.EventProjection.project_event
#print axioms CriticalLinePhasor.EventProjection.event_point_of_height
#print axioms CriticalLinePhasor.EventProjection.project_event_injective
#print axioms CriticalLinePhasor.EventProjection.event_readout
#print axioms CriticalLinePhasor.EventProjection.event_transverse_balanced
#print axioms CriticalLinePhasor.EventProjection.balance_gauge_free
#print axioms CriticalLinePhasor.EventProjection.event_transverse_value
