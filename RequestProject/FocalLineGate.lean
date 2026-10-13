import RequestProject.FocalFeetDatum

/-!
# The line the focal collapse lands on, and the critical-line gate (ledger 1178)

Level A (compiled here). The post-cancellation 3D phasor of every focal event lies on the standing
axis of `Vec3` (spin plane `ℂ` × mass axis `ℝ`): `standingLine = range standingMode`, which is
exactly `{p | plane p = 0}` (`standingLine_eq`) and is a copy of `ℝ` (`standingLineEquiv`). For an
event both feet land on the same point `standingMode M` (`event_on_standingLine`), whose
transverse coordinates are zero and whose coordinate is `M` (`event_standing_coords`). The
event's height `Z` is carried alongside; it is not a coordinate of this line.

Level B (what exists). The only existing chart map from the eigenstate is through its height:
`carrierPointAtHeight Z = carrierAbscissa + i log Z`. `chartOf_im` (`= log Z`, the event's `y`),
`chartOf_mass_blind` (two eigenstates with the same height have the same chart point, whatever
their masses), `chartOf_re_const` (the real part is the same for every eigenstate: it is
`carrierAbscissa`, `chartOf_re`). The standing-axis coordinate `M` is read by no analytic map.

The dependency scan at the end of the file reports, for each theorem, whether `carrierAbscissa`
is reachable from its statement and proof within the RequestProject library.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.FocalLine

open CriticalLinePhasor CriticalLinePhasor.FocalEventProjection CriticalLinePhasor.CancellationEigenstatePair
open CriticalLinePhasor.FocalCancellation CriticalLinePhasor.Phasor3D CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.FocalFeet CriticalLinePhasor.FocalFeet.PhasorConfig

/-! ## Level A: the standing axis -/

/-- The standing axis of the 3D phasor space. -/
def standingLine : Set Vec3 := Set.range standingMode

theorem standingLine_eq : standingLine = {p : Vec3 | plane p = 0} := by
  ext p
  constructor
  · rintro ⟨r, rfl⟩
    rfl
  · intro hp
    exact ⟨p.2, Prod.ext hp.symm rfl⟩

theorem standingMode_injective : Function.Injective standingMode := fun _ _ h =>
  congrArg Prod.snd h

/-- **The standing axis is a line**: a copy of `ℝ`, coordinate `massAxis`. -/
def standingLineEquiv : ℝ ≃ standingLine where
  toFun r := ⟨standingMode r, r, rfl⟩
  invFun p := massAxis p.1
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨_, r, rfl⟩ := p
    rfl

/-- **Both feet of every focal event land on the same point of the standing axis.** -/
theorem event_on_standingLine (e : FocalEvent) :
    (eventConfig e).channels.1 = standingMode (eigenMass e) ∧
      (PhasorConfig.J (eventConfig e)).channels.1 = standingMode (eigenMass e) ∧
      standingMode (eigenMass e) ∈ standingLine := by
  obtain ⟨h1, h2⟩ := event_post_state e
  exact ⟨congrArg Prod.fst h1, congrArg Prod.fst h2, ⟨_, rfl⟩⟩

/-- **On the standing axis the transverse coordinates are zero and the coordinate is `M`.** -/
theorem event_standing_coords (e : FocalEvent) :
    plane (standingMode (eigenMass e)) = 0 ∧ massAxis (standingMode (eigenMass e)) = eigenMass e ∧
      0 < massAxis (standingMode (eigenMass e)) :=
  ⟨rfl, rfl, eigenMass_pos e⟩

/-- The height travels with the standing point; it is the event's height, read off its carrier point. -/
theorem event_height_label (e : FocalEvent) :
    (eventConfig e).channels.2 = e.height ∧ (PhasorConfig.J (eventConfig e)).channels.2 = e.height :=
  ⟨rfl, rfl⟩

/-! ## Level B: the existing chart map from the eigenstate -/

/-- The existing chart map applied to the eigenstate's height. -/
def chartOf (d : FocalEigenstate) : ℂ := carrierPointAtHeight d.height

theorem chartOf_im (d : FocalEigenstate) : (chartOf d).im = Real.log d.height :=
  carrierPointAtHeight_im _

theorem chartOf_event_im (e : FocalEvent) : (chartOf (eventEigenstate e)).im = e.y := by
  rw [chartOf_im]
  show Real.log e.height = e.y
  rw [FocalEvent.height_eq, TwoEndedJState.eventHeight, Real.log_exp]

/-- **The chart does not read the mass**: same height, same chart point. -/
theorem chartOf_mass_blind {d d' : FocalEigenstate} (h : d.height = d'.height) :
    chartOf d = chartOf d' := by
  unfold chartOf
  rw [h]

/-- The chart's real part is `carrierAbscissa`. -/
theorem chartOf_re (d : FocalEigenstate) : (chartOf d).re = carrierAbscissa :=
  carrierPointAtHeight_re _

/-- **The chart's real part is the same for every eigenstate.** -/
theorem chartOf_re_const (d d' : FocalEigenstate) : (chartOf d).re = (chartOf d').re := by
  rw [chartOf_re, chartOf_re]

end CriticalLinePhasor.FocalLine

/-! ## Dependency scan: is `carrierAbscissa` reachable? -/

open Lean in
/-- Constants reachable from `todo` through types and values, restricted to the RequestProject
library (Mathlib and core constants are recorded but not expanded). -/
partial def reachRP (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reachRP env rest seen
    else
      let seen := seen.insert n
      let inRP : Bool := match env.getModuleIdxFor? n with
        | some idx => (env.header.moduleNames[idx.toNat]!).toString.startsWith "RequestProject"
        | none => true
      if !inRP then reachRP env rest seen
      else match env.find? n with
        | none => reachRP env rest seen
        | some ci =>
          let consts := ci.type.getUsedConstants ++
            ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
          reachRP env (consts.toList ++ rest) seen

open Lean Elab Command in
elab "#scan_abscissa " ids:ident* : command => do
  let env ← getEnv
  for id in ids do
    let n := id.getId
    let s := reachRP env [n] {}
    let hit := s.contains `CriticalLinePhasor.ThreeDFocal.carrierAbscissa
    logInfo m!"{n}: carrierAbscissa reachable = {hit}"

#scan_abscissa CriticalLinePhasor.FocalLine.event_on_standingLine
  CriticalLinePhasor.FocalLine.event_standing_coords
  CriticalLinePhasor.FocalLine.standingLine_eq
  CriticalLinePhasor.FocalLine.event_height_label
  CriticalLinePhasor.FocalFeet.event_post_state
  CriticalLinePhasor.FocalFeet.PhasorConfig.channels_eq_of_cancels
  CriticalLinePhasor.FocalLine.chartOf_re
  CriticalLinePhasor.FocalLine.chartOf_event_im
  CriticalLinePhasor.ThreeDFocal.CarrierState3D.chartReadout_re
  CriticalLinePhasor.FocalEventProjection.FocalEvent.readout_value

#print axioms CriticalLinePhasor.FocalLine.standingLine_eq
#print axioms CriticalLinePhasor.FocalLine.event_on_standingLine
#print axioms CriticalLinePhasor.FocalLine.event_standing_coords
#print axioms CriticalLinePhasor.FocalLine.event_height_label
#print axioms CriticalLinePhasor.FocalLine.chartOf_event_im
#print axioms CriticalLinePhasor.FocalLine.chartOf_mass_blind
#print axioms CriticalLinePhasor.FocalLine.chartOf_re_const
