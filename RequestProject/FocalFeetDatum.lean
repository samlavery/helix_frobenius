import RequestProject.CancellationEigenstatePair
import RequestProject.TwoEndedJState

/-!
# The two feet of the focal eigenstate: same weight, same height, opposite direction (ledger 1171)

Sam (2026-10-10): both feet of the eigenstate a focal cancellation produces stand at the same height
with the same cancellation weight; J reverses only the direction. The height does not flip. `Z` is the
height in the 3D state space; `y = log Z` is the chart height, a readout.

* `FootDatum` (weight, height, direction) with `J` reversing the direction only: `J_weight`,
  `J_height`, `J_direction`, `J_involutive`.
* `phasorFoot z Z`: a phasor `z` at height `Z` as (‖z‖, Z, arg z). Conjugation is `J`
  (`phasorFoot_conj`): same magnitude, same height, opposite direction.
* The construction supplies the direction phasor by phasor. The compiled anti-helix end of the
  two-ended state (`TwoEndedJState.jEndPhasor`, conjugation at the same site and the same head) is `J`
  on every site (`jEnd_foot`), and so is the anti-helix of the event's cancelling phasors
  (`antihelix_cancelling_foot`).
* The chart reading of the reversed spin (`antihelix_wave_reversed`): the conjugate of the massive wave
  at chart height `y` is the same wave run with time reversed. The `−y` of
  `CancellationEigenstatePair.massiveWave_conj` is this reversal named in the chart's spin slot; it is
  not a height.

The eigenstate itself carries no single direction in this construction: its weight is the anti-helix
weight (`CancellationEigenstatePair.antihelix_mass`), both feet cancel at the same head
(`antihelix_cancels`), and the detector is the same matrix on both feet (`antihelix_detector_eq`).

Before and after cancellation (ledger 1173; no global direction):
* `PhasorConfig` (height, phasors) with `J` conjugating each phasor at the same height. Before
  cancellation the directions are present (`phasor_polar`), J-odd phasor by phasor (`phasorFoot_J`),
  and the J-pair is two configurations exactly when some phasor is not real (`J_eq_self_iff`). The
  channels (resultant, unsigned mass) see a non-real resultant's direction (`channels_J_eq_iff`,
  `detector_J_eq_iff`).
* After cancellation the channels are the standing mode `(0, M)` at height `Z`
  (`channels_of_cancels`); both J-related configurations give the same state
  (`channels_J_of_cancels`); any two cancelling configurations with the same mass and height give the
  same state (`channels_eq_of_cancels`).
* `FocalEigenstate` = (M > 0, Z > 0), with `standing = standingMode M`. For an event:
  `eventConfig e` (resultant `headSum`, mass `eigenMass e`, cancels), `event_post_state` (both
  J-related configurations give `(eventEigenstate e).standing` at height `e.height`), and
  `event_J_ne_iff` (the two configurations differ exactly when some cancelling phasor is not real).
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.FocalFeet

open CriticalLinePhasor CriticalLinePhasor.FocalEventProjection CriticalLinePhasor.CancellationEigenstatePair
open CriticalLinePhasor.FocalCancellation CriticalLinePhasor.UnconditionalFrobenius
open CriticalLinePhasor.Phasor3D

/-- A foot: weight, height in the 3D state space, direction. -/
structure FootDatum where
  weight : ℝ
  height : ℝ
  direction : Real.Angle

/-- **J reverses the direction only.** -/
def J (d : FootDatum) : FootDatum := ⟨d.weight, d.height, -d.direction⟩

@[simp] theorem J_weight (d : FootDatum) : (J d).weight = d.weight := rfl
@[simp] theorem J_height (d : FootDatum) : (J d).height = d.height := rfl
@[simp] theorem J_direction (d : FootDatum) : (J d).direction = -d.direction := rfl

theorem J_involutive : Function.Involutive J := fun d => by
  show (⟨d.weight, d.height, - -d.direction⟩ : FootDatum) = d
  rw [neg_neg]

/-- A phasor `z` at height `Z`: magnitude, height, direction. -/
def phasorFoot (z : ℂ) (Z : ℝ) : FootDatum := ⟨‖z‖, Z, (Complex.arg z : Real.Angle)⟩

/-- **Conjugation is J**: same magnitude, same height, opposite direction. -/
theorem phasorFoot_conj (z : ℂ) (Z : ℝ) : phasorFoot ((starRingEnd ℂ) z) Z = J (phasorFoot z Z) := by
  show (⟨‖(starRingEnd ℂ) z‖, Z, (Complex.arg ((starRingEnd ℂ) z) : Real.Angle)⟩ : FootDatum) =
    ⟨‖z‖, Z, -(Complex.arg z : Real.Angle)⟩
  rw [Complex.norm_conj, Complex.arg_conj_coe_angle]

/-- **The compiled anti-helix end is J at every site**: the J-end phasor at site `k + 1` has the
helix phasor's magnitude, the same site height, and the opposite direction. -/
theorem jEnd_foot (F : TwoEndedJState.FiberData) (y : ℝ) (k : ℕ) :
    phasorFoot (TwoEndedJState.jEndPhasor F y k) (k + 1) =
      J (phasorFoot (TwoEndedJState.endPhasor F y k) (k + 1)) :=
  phasorFoot_conj _ _

/-- **The event's anti-helix phasors are J at every site.** -/
theorem antihelix_cancelling_foot (e : FocalEvent) (k : ℕ) :
    phasorFoot ((starRingEnd ℂ) (cancellingPhasor e.w e.a e.y k)) (k + 1) =
      J (phasorFoot (cancellingPhasor e.w e.a e.y k) (k + 1)) :=
  phasorFoot_conj _ _

/-- **The reversed spin, read in the chart**: the conjugate of the massive wave at chart height `y` is
the same wave with time reversed. -/
theorem antihelix_wave_reversed (M y t : ℝ) :
    (starRingEnd ℂ) (massiveWave M y t) = massiveWave M y (-t) := by
  rw [massiveWave_conj]
  unfold massiveWave spectralWave
  congr 2
  push_cast
  ring

/-! ## Before and after cancellation (ledger 1173)

Before cancellation the event is a configuration of phasors at one height `Z`, and `J` conjugates each
phasor. After cancellation the construction supplies `(M, Z)`: a zero planar resultant and the
surviving unsigned mass `M` on the mass axis, at height `Z`. The map from configurations to that state
is the pair the detector reads, (resultant, unsigned mass). -/

/-- A configuration of phasors at a common height. -/
structure PhasorConfig where
  height : ℝ
  size : ℕ
  phasor : Fin size → ℂ

namespace PhasorConfig

/-- `J`: each phasor conjugated, at the same height. -/
def J (c : PhasorConfig) : PhasorConfig := ⟨c.height, c.size, fun k => (starRingEnd ℂ) (c.phasor k)⟩

@[simp] theorem J_height (c : PhasorConfig) : (J c).height = c.height := rfl

theorem J_involutive : Function.Involutive J := fun c => by
  obtain ⟨Z, N, f⟩ := c
  simp [J]

/-- The planar resultant: the detector's signed channel. -/
def resultant (c : PhasorConfig) : ℂ := ∑ k, c.phasor k

/-- The unsigned mass: the detector's unsigned channel. -/
def mass (c : PhasorConfig) : ℝ := ∑ k, ‖c.phasor k‖

/-- The configuration cancels: its planar resultant is zero. -/
def Cancels (c : PhasorConfig) : Prop := resultant c = 0

/-- The two channels at the configuration's height: the 3D phasor with spin-plane part the resultant
and mass-axis part the unsigned mass (`helix_eigenstate`'s pair), and the height. -/
def channels (c : PhasorConfig) : Vec3 × ℝ := ((resultant c, mass c), c.height)

/-! ### Before cancellation: the directions are present and J-odd phasor by phasor -/

/-- Each phasor is its magnitude times its direction. -/
theorem phasor_polar (c : PhasorConfig) (k : Fin c.size) :
    c.phasor k = (‖c.phasor k‖ : ℂ) * Complex.exp ((Complex.arg (c.phasor k) : ℂ) * I) :=
  (Complex.norm_mul_exp_arg_mul_I _).symm

/-- **J negates each phasor's direction** and keeps its magnitude and the height. -/
theorem phasorFoot_J (c : PhasorConfig) (k : Fin c.size) :
    phasorFoot ((J c).phasor k) c.height = FocalFeet.J (phasorFoot (c.phasor k) c.height) :=
  phasorFoot_conj _ _

/-- **The two J-related configurations differ exactly when some phasor is not real.** -/
theorem J_eq_self_iff (c : PhasorConfig) : J c = c ↔ ∀ k, (c.phasor k).im = 0 := by
  obtain ⟨Z, N, f⟩ := c
  simp only [J, PhasorConfig.mk.injEq, true_and, heq_eq_eq, funext_iff, Complex.conj_eq_iff_im]

theorem mass_J (c : PhasorConfig) : mass (J c) = mass c := by
  unfold mass J
  simp only [Complex.norm_conj]

theorem resultant_J (c : PhasorConfig) : resultant (J c) = (starRingEnd ℂ) (resultant c) := by
  unfold resultant J
  rw [map_sum]

theorem cancels_J (c : PhasorConfig) : Cancels (J c) ↔ Cancels c := by
  unfold Cancels
  rw [resultant_J, map_eq_zero]

/-- **Before cancellation the channels see the resultant's direction**: J changes the channels
exactly when the resultant is not real. -/
theorem channels_J_eq_iff (c : PhasorConfig) : channels (J c) = channels c ↔ (resultant c).im = 0 := by
  unfold channels
  rw [resultant_J, mass_J, J_height]
  simp only [Prod.mk.injEq, and_true, Complex.conj_eq_iff_im]

/-- The detector sees it too: fed the J-configuration's channels, it is the same matrix exactly when
the resultant is real. -/
theorem detector_J_eq_iff (c : PhasorConfig) (μ lam : ℂ) :
    HarmonicCell.harmonicPencil ((mass (J c) : ℝ) : ℂ) (resultant (J c)) μ lam =
        HarmonicCell.harmonicPencil ((mass c : ℝ) : ℂ) (resultant c) μ lam ↔
      (resultant c).im = 0 := by
  rw [mass_J, resultant_J, ← Complex.conj_eq_iff_im]
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simpa [HarmonicCell.harmonicPencil] using h01
  · intro h
    rw [h]

/-! ### After cancellation: the directions are absent -/

/-- **At cancellation the channels are the standing mode**: zero planar resultant, the unsigned mass
on the mass axis, at the height. -/
theorem channels_of_cancels {c : PhasorConfig} (hc : Cancels c) :
    channels c = (standingMode (mass c), c.height) := by
  unfold channels
  rw [show resultant c = 0 from hc]
  rfl

/-- **Both J-related configurations give the same post-cancellation state.** -/
theorem channels_J_of_cancels {c : PhasorConfig} (hc : Cancels c) : channels (J c) = channels c :=
  (channels_J_eq_iff c).mpr (by rw [show resultant c = 0 from hc, Complex.zero_im])

/-- **No direction survives cancellation**: any two cancelling configurations with the same unsigned
mass and the same height have the same post-cancellation state. -/
theorem channels_eq_of_cancels {c c' : PhasorConfig} (hc : Cancels c) (hc' : Cancels c')
    (hm : mass c = mass c') (hZ : c.height = c'.height) : channels c = channels c' := by
  rw [channels_of_cancels hc, channels_of_cancels hc', hm, hZ]

end PhasorConfig

/-- **The focal eigenstate after cancellation**: mass `M > 0` and height `Z > 0`. Its 3D phasor is the
standing mode `(0, M)`. -/
structure FocalEigenstate where
  mass : ℝ
  mass_pos : 0 < mass
  height : ℝ
  height_pos : 0 < height

/-- The eigenstate's 3D phasor: zero planar resultant, mass `M` on the mass axis. -/
def FocalEigenstate.standing (d : FocalEigenstate) : Vec3 := standingMode d.mass

/-! ### The event -/

/-- The event's configuration: its cancelling phasors, at the event's height. -/
def eventConfig (e : FocalEvent) : PhasorConfig :=
  ⟨e.height, ⌈CarrierHeadFiniteFiber.physicalHead e.y⌉₊,
    fun k => cancellingPhasor e.w e.a e.y k⟩

theorem resultant_eventConfig (e : FocalEvent) :
    (eventConfig e).resultant = headSum e.w e.a e.y := by
  unfold PhasorConfig.resultant eventConfig
  rw [headSum_eq_sum_cancelling]
  exact Fin.sum_univ_eq_sum_range (fun k => cancellingPhasor e.w e.a e.y k) _

theorem mass_eventConfig (e : FocalEvent) : (eventConfig e).mass = eigenMass e := by
  unfold PhasorConfig.mass eventConfig
  rw [Fin.sum_univ_eq_sum_range (fun k => ‖cancellingPhasor e.w e.a e.y k‖)]
  exact cancellingMass_eq e.w e.a_pos e.y

theorem eventConfig_cancels (e : FocalEvent) : (eventConfig e).Cancels := by
  unfold PhasorConfig.Cancels
  rw [resultant_eventConfig]
  exact e.cancel

/-- The eigenstate the event produces: `(eigenMass e, e.height)`. -/
def eventEigenstate (e : FocalEvent) : FocalEigenstate :=
  ⟨eigenMass e, eigenMass_pos e, e.height, e.height_pos⟩

/-- **Both J-related configurations of the event give the same eigenstate** `(M, Z)`: zero planar
resultant, mass `M` on the mass axis, height `Z`. -/
theorem event_post_state (e : FocalEvent) :
    (eventConfig e).channels = ((eventEigenstate e).standing, (eventEigenstate e).height) ∧
      (PhasorConfig.J (eventConfig e)).channels =
        ((eventEigenstate e).standing, (eventEigenstate e).height) := by
  have h : (eventConfig e).channels = ((eventEigenstate e).standing, (eventEigenstate e).height) := by
    rw [PhasorConfig.channels_of_cancels (eventConfig_cancels e), mass_eventConfig]
    rfl
  exact ⟨h, (PhasorConfig.channels_J_of_cancels (eventConfig_cancels e)).trans h⟩

/-- **The map is two-to-one on the event's J-pair exactly when some cancelling phasor is not real.** -/
theorem event_J_ne_iff (e : FocalEvent) :
    PhasorConfig.J (eventConfig e) ≠ eventConfig e ↔
      ∃ k : Fin ⌈CarrierHeadFiniteFiber.physicalHead e.y⌉₊,
        (cancellingPhasor e.w e.a e.y k).im ≠ 0 := by
  rw [Ne, PhasorConfig.J_eq_self_iff, not_forall]
  rfl

end CriticalLinePhasor.FocalFeet

#print axioms CriticalLinePhasor.FocalFeet.PhasorConfig.J_involutive
#print axioms CriticalLinePhasor.FocalFeet.PhasorConfig.phasor_polar
#print axioms CriticalLinePhasor.FocalFeet.PhasorConfig.phasorFoot_J
#print axioms CriticalLinePhasor.FocalFeet.PhasorConfig.J_eq_self_iff
#print axioms CriticalLinePhasor.FocalFeet.PhasorConfig.mass_J
#print axioms CriticalLinePhasor.FocalFeet.PhasorConfig.resultant_J
#print axioms CriticalLinePhasor.FocalFeet.PhasorConfig.cancels_J
#print axioms CriticalLinePhasor.FocalFeet.PhasorConfig.channels_J_eq_iff
#print axioms CriticalLinePhasor.FocalFeet.PhasorConfig.detector_J_eq_iff
#print axioms CriticalLinePhasor.FocalFeet.PhasorConfig.channels_of_cancels
#print axioms CriticalLinePhasor.FocalFeet.PhasorConfig.channels_J_of_cancels
#print axioms CriticalLinePhasor.FocalFeet.PhasorConfig.channels_eq_of_cancels
#print axioms CriticalLinePhasor.FocalFeet.resultant_eventConfig
#print axioms CriticalLinePhasor.FocalFeet.mass_eventConfig
#print axioms CriticalLinePhasor.FocalFeet.eventConfig_cancels
#print axioms CriticalLinePhasor.FocalFeet.event_post_state
#print axioms CriticalLinePhasor.FocalFeet.event_J_ne_iff
#print axioms CriticalLinePhasor.FocalFeet.J_involutive
#print axioms CriticalLinePhasor.FocalFeet.phasorFoot_conj
#print axioms CriticalLinePhasor.FocalFeet.jEnd_foot
#print axioms CriticalLinePhasor.FocalFeet.antihelix_cancelling_foot
#print axioms CriticalLinePhasor.FocalFeet.antihelix_wave_reversed
