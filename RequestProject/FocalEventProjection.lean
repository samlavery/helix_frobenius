import RequestProject.EventProjection

/-!
# The focal-cancellation event, projected (ledger 1155)

The event is the fiber's own exact cancellation at the carrier's head. The detector reads it. The
event is placed on the helix and projected. No analytic parameter, reflection, or chart abscissa
appears in any statement before the last theorem.

* `FocalEvent`: a routing law `w` (neutral sites allowed, `‖w 1‖ = 1`), a positive amplitude law
  `a`, the carrier ordinate `y` of the event, the head past the first site, and the cancellation of the
  grown fiber at the carrier's own head, `headSum w a y = 0`.
* Detection (`FocalEvent.rankDrop`, `headSum_zero_iff_rankDrop`): the specified pencil
  `!![A, B; μA, λB]`, fed with the event's own channels, drops rank exactly at the cancellation.
* The events of the existing chain are instances: `FocalEvent.ofFiberData` (the two-ended
  `TwoEndedJState.FocalCancellation`) and `FocalEvent.ofChain` (FiberDetectorChain's finite detector
  at the physical head; the amplitude exponent there is that fiber's own construction parameter).
* Projection (`FocalEvent.state` on the `(1, 3)` carrier, the carrier of `physicalHead`):
  `FocalEvent.height_eq` (the projected height is the event's physical height `eventHeight y`),
  `FocalEvent.point_of_height` (the dropped radius and angle are functions of that height),
  `readout_eq_of_y_eq` (the readout sees the event's ordinate only, not its routing or amplitude law).
* The readout is `(balanceExponent, height)`. `FocalEvent.readout_balanced`: its transverse component is
  a `CarrierScaleBalanced` exponent, and the only one. Bundled: `focalEvent_projected`.
* Last, the value: `FocalEvent.readout_value`.

**Scope (cleanup, ledger 1237).** `FocalEvent` is the CANONICAL rich physical event. It cancels exactly at
the native head `physicalHead y` tied to its own height. Its configuration carries the conductor's
site-disjoint positive/negative banks (bank-level cancellation), the J two-ended structure and the
post-cancellation state `(M, Z)` downstream (`CancellationEigenstatePair`, `FocalFeetDatum`). It is not
interchangeable with the asymptotic `LimitFocalEventNS.LimitFocalEvent` or the free-cutoff
`ThreeDFocal.ThreeDZero`. No compiled theorem takes a `FocalEvent` to analytic vanishing; that arrow is
missing, not formulated. The readout's first coordinate is the constant `balanceExponent`, attached by
definition: `readout_balanced` / `readout_value` say nothing about the event's own balance, and must not
be used as a proof of native balance. `lawFiber_head_eq_headSum` is a finite identity at the native head,
not a bridge to analytic vanishing.
-/

open Complex Filter Topology Finset
open scoped Matrix

noncomputable section

namespace CriticalLinePhasor.FocalEventProjection

open CriticalLinePhasor CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.CarrierHeadFiniteFiber
open CriticalLinePhasor.GrownFiberEvolution CriticalLinePhasor.HarmonicCell

/-! ## 1. The event -/

/-- The grown fiber at the carrier's own head at ordinate `y`: site `k + 1` carries the routing
coefficient `w(k+1)`, the amplitude `a k` and the carrier spin at `y`, under the head window. -/
def headSum (w : ℕ → ℂ) (a : ℕ → ℝ) (y : ℝ) : ℂ :=
  ∑ k ∈ range ⌈physicalHead y⌉₊, ((headWindow (physicalHead y) k : ℝ) : ℂ) *
    (w (k + 1) * (a k : ℂ) * LFunctionPhasor.mellinSpin y (k + 1))

/-- Its unsigned channel `Σ window·‖w‖·a`. -/
def headUnsigned (w : ℕ → ℂ) (a : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ k ∈ range ⌈physicalHead y⌉₊, headWindow (physicalHead y) k * ‖w (k + 1)‖ * a k

/-- **A focal-cancellation event**: the fiber's grown sum cancels at the carrier's own head. -/
structure FocalEvent where
  w : ℕ → ℂ
  w_one : ‖w 1‖ = 1
  a : ℕ → ℝ
  a_pos : ∀ k, 0 < a k
  y : ℝ
  head_gt : 1 < physicalHead y
  cancel : headSum w a y = 0

theorem headUnsigned_pos {w : ℕ → ℂ} (hw : ‖w 1‖ = 1) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) {y : ℝ}
    (hhead : 1 < physicalHead y) : 0 < headUnsigned w a y := by
  unfold headUnsigned
  have hmem : 0 ∈ range ⌈physicalHead y⌉₊ :=
    Finset.mem_range.mpr (Nat.ceil_pos.mpr (by linarith))
  refine Finset.sum_pos' (fun k _ => ?_) ⟨0, hmem, ?_⟩
  · exact mul_nonneg (mul_nonneg (smoothEntry_nonneg _) (norm_nonneg _)) (ha k).le
  · have h1 : 0 < headWindow (physicalHead y) 0 := by
      unfold headWindow
      apply FiberDetectorChain.smoothEntry_pos
      rw [div_lt_one (by linarith)]
      push_cast
      linarith
    simp only [zero_add, hw, mul_one]
    exact mul_pos h1 (ha 0)

/-! ## 2. The detector reads the event -/

/-- The specified detector fed with the event's own channels. -/
def detector (w : ℕ → ℂ) (a : ℕ → ℝ) (y : ℝ) (μ lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  harmonicPencil ((headUnsigned w a y : ℝ) : ℂ) (headSum w a y) μ lam

/-- **The grown sum cancels at the head exactly when the detector drops rank.** -/
theorem headSum_zero_iff_rankDrop {w : ℕ → ℂ} (hw : ‖w 1‖ = 1) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k)
    {y : ℝ} (hhead : 1 < physicalHead y) (μ lam : ℂ) (hlam : lam ≠ μ) :
    headSum w a y = 0 ↔ ((detector w a y μ lam)ᴴ * detector w a y μ lam).det = 0 :=
  (harmonicGram_rank_drop_iff_channel_zero _ _ μ lam
    (by exact_mod_cast (headUnsigned_pos hw ha hhead).ne') hlam).symm

theorem FocalEvent.rankDrop (e : FocalEvent) (μ lam : ℂ) (hlam : lam ≠ μ) :
    ((detector e.w e.a e.y μ lam)ᴴ * detector e.w e.a e.y μ lam).det = 0 :=
  (headSum_zero_iff_rankDrop e.w_one e.a_pos e.head_gt μ lam hlam).mp e.cancel

/-! ## 3. The chain's events are instances -/

/-- The two-ended grown end is the head sum of its fiber data. -/
theorem grownEnd_eq_headSum (F : TwoEndedJState.FiberData) (y : ℝ) :
    TwoEndedJState.grownEnd F (physicalHead y) y = headSum (fun n => F.bucket (n - 1)) F.amp y := by
  unfold TwoEndedJState.grownEnd headSum TwoEndedJState.endPhasor
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Nat.add_sub_cancel]

/-- The two-ended focal cancellation is a focal event. -/
def FocalEvent.ofFiberData (F : TwoEndedJState.FiberData) (y : ℝ) (hhead : 1 < physicalHead y)
    (h : TwoEndedJState.FocalCancellation F y) : FocalEvent where
  w := fun n => F.bucket (n - 1)
  w_one := F.bucket_unit 0
  a := F.amp
  a_pos := F.amp_pos
  y := y
  head_gt := hhead
  cancel := by rw [← grownEnd_eq_headSum]; exact h

/-- At the native head `Z = physicalHead y`, the windowed grown fiber with the power law `(k+1)^{−σ}` is
`headSum`. An exact finite identity; by itself it is not a finite→completed or native→analytic bridge. -/
theorem lawFiber_head_eq_headSum (w : ℕ → ℂ) (σ y : ℝ) :
    FiberDetectorChain.lawFiber w (physicalHead y) ((σ : ℂ) + (y : ℂ) * Complex.I) =
      headSum w (fun k => ((k : ℝ) + 1) ^ (-σ)) y := by
  unfold FiberDetectorChain.lawFiber FiberDetectorChain.windowed headSum
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsplit := EisensteinWheelBank.natCast_cpow_split (k + 1) (Nat.succ_pos k) σ y
  push_cast at hsplit
  dsimp only
  rw [hsplit]
  unfold LFunctionPhasor.mellinSpin
  push_cast
  ring

/-- **FiberDetectorChain's finite detector event at the physical head is a focal event.** The
exponent `σ` is that fiber's amplitude-law parameter; it enters the event only as `a`. -/
def FocalEvent.ofChain (w : ℕ → ℂ) (hw : ‖w 1‖ = 1) (σ y : ℝ) (hy : 0 ≤ y) (μ lam : ℂ)
    (hlam : lam ≠ μ)
    (hdrop : ((FiberDetectorChain.lawDetector w (physicalHead y) ((σ : ℂ) + (y : ℂ) * Complex.I)
      μ lam)ᴴ * FiberDetectorChain.lawDetector w (physicalHead y)
        ((σ : ℂ) + (y : ℂ) * Complex.I) μ lam).det = 0) : FocalEvent where
  w := w
  w_one := hw
  a := fun k => ((k : ℝ) + 1) ^ (-σ)
  a_pos := fun k => Real.rpow_pos_of_pos (by positivity) _
  y := y
  head_gt := FiberDetectorChain.one_lt_physicalHead hy
  cancel := by
    rw [← lawFiber_head_eq_headSum]
    exact (FiberDetectorChain.finite_cancel_iff_rankDrop w (FiberDetectorChain.one_lt_physicalHead hy)
      hw _ μ lam hlam).mpr hdrop

/-! ## 4. The event, projected -/

/-- The event on the helix: the `(1, 3)` carrier state at the event's ordinate. -/
def FocalEvent.state (e : FocalEvent) : CarrierState3D 1 3 :=
  carrierState3D 1 3 e.y

/-- The event's projected height: projection drops radius, then angle, and keeps this. -/
def FocalEvent.height (e : FocalEvent) : ℝ :=
  toHeight (toUnitCylinder e.state.point)

/-- The carrier's balance exponent: the exponent at which a fiber amplitude reciprocates the carrier
radius (`carrierAbscissa` is defined as this unique choice). -/
def balanceExponent : ℝ := carrierAbscissa

/-- **The geometric readout of the event**: (balance exponent, projected height). -/
def FocalEvent.readout (e : FocalEvent) : ℝ × ℝ := (balanceExponent, e.height)

/-- The projected height is the event's physical height. -/
theorem FocalEvent.height_eq (e : FocalEvent) : e.height = TwoEndedJState.eventHeight e.y := by
  rw [FocalEvent.height, toHeight_toUnitCylinder]
  exact e.state.physicalHeight_eq_exp one_ne_zero

theorem FocalEvent.height_pos (e : FocalEvent) : 0 < e.height := by
  rw [e.height_eq]
  exact Real.exp_pos _

/-- **Projection loses nothing**: the event's helix point is recovered from its projected height. -/
theorem FocalEvent.point_of_height (e : FocalEvent) :
    e.state.point =
      ((3 : ℝ) / 1 * e.height * Real.cos (2 * Real.pi * e.height / 1),
        (3 : ℝ) / 1 * e.height * Real.sin (2 * Real.pi * e.height / 1), e.height) := by
  rw [e.height_eq]
  exact Geometry.gammaY_eq 1 3 e.y one_ne_zero

/-- The readout sees the event's ordinate only, not its routing law or amplitude law. -/
theorem readout_eq_of_y_eq {e e' : FocalEvent} (h : e.y = e'.y) : e.readout = e'.readout := by
  unfold FocalEvent.readout FocalEvent.height FocalEvent.state
  rw [h]

/-- Distinct ordinates give distinct readouts. -/
theorem y_eq_of_readout_eq {e e' : FocalEvent} (h : e.readout = e'.readout) : e.y = e'.y := by
  have h2 := congrArg Prod.snd h
  simp only [FocalEvent.readout, FocalEvent.height_eq, TwoEndedJState.eventHeight] at h2
  exact Real.exp_injective h2

/-- **The transverse readout is the carrier's balance exponent**, and the only balanced exponent.
The readout attaches this constant to every event by definition; it does not prove native balance of
the event's own amplitude law. -/
theorem FocalEvent.readout_balanced (e : FocalEvent) :
    CarrierScaleBalanced e.readout.1 ∧ ∀ σ : ℝ, CarrierScaleBalanced σ → σ = e.readout.1 :=
  ⟨carrierAbscissa_scaleBalanced, fun _ hσ =>
    exists_unique_carrierScaleBalanced.unique hσ carrierAbscissa_scaleBalanced⟩

/-- **The composition.** A focal-cancellation event is detected by the pencil; projected, it keeps its
physical height and loses nothing; its readout is (the unique balance exponent, that height). -/
theorem focalEvent_projected (e : FocalEvent) (μ lam : ℂ) (hlam : lam ≠ μ) :
    ((detector e.w e.a e.y μ lam)ᴴ * detector e.w e.a e.y μ lam).det = 0 ∧
      e.height = TwoEndedJState.eventHeight e.y ∧ 0 < e.height ∧
      e.state.point =
        ((3 : ℝ) / 1 * e.height * Real.cos (2 * Real.pi * e.height / 1),
          (3 : ℝ) / 1 * e.height * Real.sin (2 * Real.pi * e.height / 1), e.height) ∧
      e.readout.2 = e.height ∧
      CarrierScaleBalanced e.readout.1 ∧ (∀ σ : ℝ, CarrierScaleBalanced σ → σ = e.readout.1) :=
  ⟨e.rankDrop μ lam hlam, e.height_eq, e.height_pos, e.point_of_height, rfl,
    e.readout_balanced.1, e.readout_balanced.2⟩

/-! ## 5. Last: the value of the balance coordinate -/

/-- The readout's first coordinate is `½`: the observer's chosen readout value, attached by
definition, the same for every event. Not a proof of native balance. -/
theorem FocalEvent.readout_value (e : FocalEvent) : e.readout.1 = 1 / 2 :=
  carrierAbscissa_eq_half

end CriticalLinePhasor.FocalEventProjection

#print axioms CriticalLinePhasor.FocalEventProjection.headSum_zero_iff_rankDrop
#print axioms CriticalLinePhasor.FocalEventProjection.FocalEvent.ofFiberData
#print axioms CriticalLinePhasor.FocalEventProjection.FocalEvent.ofChain
#print axioms CriticalLinePhasor.FocalEventProjection.readout_eq_of_y_eq
#print axioms CriticalLinePhasor.FocalEventProjection.y_eq_of_readout_eq
#print axioms CriticalLinePhasor.FocalEventProjection.focalEvent_projected
#print axioms CriticalLinePhasor.FocalEventProjection.FocalEvent.readout_value
