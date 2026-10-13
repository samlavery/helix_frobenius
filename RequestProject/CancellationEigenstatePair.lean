import RequestProject.FocalEventProjection
import RequestProject.FocalCancellationEigenstate

/-!
# The eigenstate produced by a focal cancellation, on both feet (ledger 1163)

Sam (2026-10-10): the focal cancellation at height `e^{y}` creates an eigenstate based on the sum
of the magnitudes of all the cancelling phasors, and it does it on the anti-helix at the same height.

For a focal event (`FocalEvent`: the grown fiber cancels exactly at the carrier's head):

* `cancellingMass_eq`: the sum of the magnitudes of the cancelling phasors is the detector's unsigned
  channel `headUnsigned`. `eigenMass e` is this sum; it is positive (`eigenMass_pos`).
* The helix eigenstate (`helix_eigenstate`): the standing mode `(0, M)` carries the cancelled
  radiating sum as its zero plane part and the mass `M` on the mass axis. The massive wave
  `M·e^{iyt}` is an eigenstate of `−i d/dt` with eigenvalue the event's ordinate `y` and constant modulus
  `M`.
* The anti-helix eigenstate (`antihelix_eigenstate`): the anti-helix phasors (conjugates) have the
  same magnitudes and cancel at the same head, so the same mass `M`. Its massive wave is the conjugate
  `M·e^{−iyt}`, an eigenstate with eigenvalue `−y`. (Ledger 1171: the `−y` is the reversed spin named
  in the chart's spin slot, not a height; the foot stands at the same height, and the conjugate is the
  same wave with time reversed, `FocalFeet.antihelix_wave_reversed`.)
* The pencil (`detector_at_event`, `detector_kernel_iff`, `antihelix_detector_eq`): at the event the
  detector is `!![M, 0; μM, 0]`. Its kernel is the signed direction, its surviving entry is the
  eigenstate's mass, and the anti-helix detector is the same matrix.

The compiled two-phasor theorem `focal_cancellation_produces_eigenstate` gives each cancelling
phasor's magnitude `r` as the mass; the rule here is the sum (`2r` for that pair).
-/

open Complex Filter Topology Finset
open scoped Matrix

noncomputable section

namespace CriticalLinePhasor.CancellationEigenstatePair

open CriticalLinePhasor CriticalLinePhasor.CarrierHeadFiniteFiber CriticalLinePhasor.GrownFiberEvolution
open CriticalLinePhasor.HarmonicCell CriticalLinePhasor.FocalEventProjection
open CriticalLinePhasor.FocalCancellation CriticalLinePhasor.UnconditionalFrobenius

/-- The cancelling phasor at site `k + 1` of the grown fiber at the carrier's head. -/
def cancellingPhasor (w : ℕ → ℂ) (a : ℕ → ℝ) (y : ℝ) (k : ℕ) : ℂ :=
  ((headWindow (physicalHead y) k : ℝ) : ℂ) * (w (k + 1) * (a k : ℂ) * LFunctionPhasor.mellinSpin y (k + 1))

theorem headSum_eq_sum_cancelling (w : ℕ → ℂ) (a : ℕ → ℝ) (y : ℝ) :
    headSum w a y = ∑ k ∈ range ⌈physicalHead y⌉₊, cancellingPhasor w a y k :=
  rfl

theorem norm_cancellingPhasor (w : ℕ → ℂ) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (y : ℝ) (k : ℕ) :
    ‖cancellingPhasor w a y k‖ = headWindow (physicalHead y) k * ‖w (k + 1)‖ * a k := by
  have hwin : 0 ≤ headWindow (physicalHead y) k := smoothEntry_nonneg _
  unfold cancellingPhasor
  rw [norm_mul, norm_mul, norm_mul, LFunctionPhasor.mellinSpin_norm, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hwin, Real.norm_of_nonneg (ha k).le]
  ring

/-- **The sum of the magnitudes of the cancelling phasors is the detector's unsigned channel.** -/
theorem cancellingMass_eq (w : ℕ → ℂ) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (y : ℝ) :
    ∑ k ∈ range ⌈physicalHead y⌉₊, ‖cancellingPhasor w a y k‖ = headUnsigned w a y := by
  unfold headUnsigned
  exact Finset.sum_congr rfl fun k _ => norm_cancellingPhasor w ha y k

/-- The mass of the eigenstate produced by the event: the sum of the magnitudes of the cancelling
phasors. -/
def eigenMass (e : FocalEvent) : ℝ := headUnsigned e.w e.a e.y

theorem eigenMass_pos (e : FocalEvent) : 0 < eigenMass e :=
  headUnsigned_pos e.w_one e.a_pos e.head_gt

/-! ## The helix foot -/

/-- **The helix eigenstate.** The standing mode `(0, M)` carries the cancelled radiating sum as its
plane part and the mass `M`; the massive wave `M·e^{iyt}` is an eigenstate with eigenvalue `y` and
modulus `M`. -/
theorem helix_eigenstate (e : FocalEvent) :
    Phasor3D.plane (standingMode (eigenMass e)) = headSum e.w e.a e.y ∧
      Phasor3D.massAxis (standingMode (eigenMass e)) =
        ∑ k ∈ range ⌈physicalHead e.y⌉₊, ‖cancellingPhasor e.w e.a e.y k‖ ∧
      (∀ t : ℝ, ‖massiveWave (eigenMass e) e.y t‖ = eigenMass e) ∧
      (∀ t : ℝ, -Complex.I * deriv (massiveWave (eigenMass e) e.y) t =
        (e.y : ℂ) * massiveWave (eigenMass e) e.y t) := by
  refine ⟨?_, ?_, massiveWave_norm _ _ (eigenMass_pos e).le, massiveWave_eigen _ _⟩
  · rw [e.cancel]
    rfl
  · rw [cancellingMass_eq e.w e.a_pos]
    rfl

/-! ## The anti-helix foot, at the same height -/

/-- The anti-helix phasors are the conjugates, with the same magnitudes. -/
theorem antihelix_mass (e : FocalEvent) :
    ∑ k ∈ range ⌈physicalHead e.y⌉₊, ‖(starRingEnd ℂ) (cancellingPhasor e.w e.a e.y k)‖ =
      eigenMass e := by
  simp only [Complex.norm_conj]
  exact cancellingMass_eq e.w e.a_pos e.y

/-- The anti-helix sum cancels at the same head. -/
theorem antihelix_cancels (e : FocalEvent) :
    ∑ k ∈ range ⌈physicalHead e.y⌉₊, (starRingEnd ℂ) (cancellingPhasor e.w e.a e.y k) = 0 := by
  rw [← map_sum, ← headSum_eq_sum_cancelling, e.cancel, map_zero]

theorem massiveWave_conj (M y t : ℝ) :
    (starRingEnd ℂ) (massiveWave M y t) = massiveWave M (-y) t := by
  unfold massiveWave spectralWave
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

/-- **The anti-helix eigenstate.** Same mass `M` at the same height; its massive wave is the
conjugate, an eigenstate with eigenvalue `−y` and modulus `M`. Ledger 1171: the `−y` is the reversed
spin read in the chart, not a height (`FocalFeet.antihelix_wave_reversed`). -/
theorem antihelix_eigenstate (e : FocalEvent) :
    (∀ t : ℝ, (starRingEnd ℂ) (massiveWave (eigenMass e) e.y t) = massiveWave (eigenMass e) (-e.y) t) ∧
      (∀ t : ℝ, ‖massiveWave (eigenMass e) (-e.y) t‖ = eigenMass e) ∧
      (∀ t : ℝ, -Complex.I * deriv (massiveWave (eigenMass e) (-e.y)) t =
        ((-e.y : ℝ) : ℂ) * massiveWave (eigenMass e) (-e.y) t) :=
  ⟨massiveWave_conj _ _, massiveWave_norm _ _ (eigenMass_pos e).le, massiveWave_eigen _ _⟩

/-! ## The pencil at the event -/

/-- **At the event the detector is `!![M, 0; μM, 0]`**: the signed column is zero and the surviving
entry is the eigenstate's mass. -/
theorem detector_at_event (e : FocalEvent) (μ lam : ℂ) :
    detector e.w e.a e.y μ lam = harmonicPencil ((eigenMass e : ℝ) : ℂ) 0 μ lam := by
  rw [detector, e.cancel]
  rfl

/-- The kernel of the detector at the event is the signed direction. -/
theorem detector_kernel_iff (e : FocalEvent) (μ lam : ℂ) (v : Fin 2 → ℂ) :
    (detector e.w e.a e.y μ lam).mulVec v = 0 ↔ v 0 = 0 := by
  rw [detector_at_event]
  have hM : eigenMass e ≠ 0 := (eigenMass_pos e).ne'
  constructor
  · intro h
    have h0 := congrFun h 0
    simp [harmonicPencil, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    exact h0.resolve_left hM
  · intro h
    ext i
    fin_cases i <;> simp [harmonicPencil, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]

/-- The anti-helix detector (fed the conjugate channel) is the same matrix at the event. -/
theorem antihelix_detector_eq (e : FocalEvent) (μ lam : ℂ) :
    harmonicPencil ((headUnsigned e.w e.a e.y : ℝ) : ℂ) ((starRingEnd ℂ) (headSum e.w e.a e.y)) μ lam =
      detector e.w e.a e.y μ lam := by
  rw [detector, e.cancel, map_zero]

end CriticalLinePhasor.CancellationEigenstatePair

#print axioms CriticalLinePhasor.CancellationEigenstatePair.cancellingMass_eq
#print axioms CriticalLinePhasor.CancellationEigenstatePair.helix_eigenstate
#print axioms CriticalLinePhasor.CancellationEigenstatePair.antihelix_mass
#print axioms CriticalLinePhasor.CancellationEigenstatePair.antihelix_cancels
#print axioms CriticalLinePhasor.CancellationEigenstatePair.antihelix_eigenstate
#print axioms CriticalLinePhasor.CancellationEigenstatePair.detector_at_event
#print axioms CriticalLinePhasor.CancellationEigenstatePair.detector_kernel_iff
#print axioms CriticalLinePhasor.CancellationEigenstatePair.antihelix_detector_eq
