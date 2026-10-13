import RequestProject.FocalFeetDatum
import RequestProject.FrobeniusSimilitude

/-!
# Is the focal quotient Frobenius-invariant? (ledger 1175)

The focal quotient `Q` sends a cancelling configuration of positive mass at height `Z > 0` to its
post-cancellation eigenstate `(M, Z)` (`FocalFeet.FocalEigenstate`). The test: is the focal locus
(resultant zero) stable under the existing Frobenius actions, so that `Q ∘ F = Q`?

* The per-site Frobenius action `frob t`: the phasor at site `k + 1` is multiplied by the Frobenius
  eigenphase `mellinSpin t (k + 1)`, the first entry of `FrobeniusSimilitude.frobeniusBlock t (k + 1)`.
  It keeps the height and the mass (`frob_height`, `frob_mass`). Its resultant is
  `∑ mellinSpin t (k + 1) · c_k` (`frob_resultant`). The focal locus is NOT stable:
  `frob_not_focal_stable` exhibits a cancelling configuration whose image does not cancel. For an
  event, `frob_eventConfig_resultant`: the image's resultant is the head sum with the window frozen at
  the event's head and the spins at chart height `y + t`, so `frob t` keeps the event's cancellation
  exactly when that frozen sum vanishes at `y + t` (`frob_eventConfig_cancels_iff`). Where the image
  does cancel, `Q` is unchanged (`Q_frob_of_cancels`): stability of the locus is the only obstruction.
* The native Frobenius (`Pencil3D.nativeFrobenius`) multiplies a whole lane by one unit phase. On a
  configuration that is `rotate u` with `‖u‖ = 1`: the resultant is multiplied by `u`
  (`resultant_rotate`), cancellation is kept, and `Q_rotate`: `Q ∘ rotate u = Q`.
* J descends (`Q_J`), as in 1173.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.FocalQuotient

open CriticalLinePhasor CriticalLinePhasor.FocalEventProjection CriticalLinePhasor.CancellationEigenstatePair
open CriticalLinePhasor.CarrierHeadFiniteFiber CriticalLinePhasor.GrownFiberEvolution
open CriticalLinePhasor.FocalFeet CriticalLinePhasor.FocalFeet.PhasorConfig

/-! ## The focal quotient -/

/-- A point of the focal locus: a cancelling configuration of positive mass at positive height. -/
structure FocalConfig where
  config : PhasorConfig
  cancels : config.Cancels
  mass_pos : 0 < config.mass
  height_pos : 0 < config.height

/-- **The focal quotient** `Q`: the post-cancellation eigenstate `(M, Z)`. -/
def Q (c : FocalConfig) : FocalEigenstate :=
  ⟨c.config.mass, c.mass_pos, c.config.height, c.height_pos⟩

theorem Q_eq_iff (c c' : FocalConfig) :
    Q c = Q c' ↔ c.config.mass = c'.config.mass ∧ c.config.height = c'.config.height := by
  simp [Q, FocalEigenstate.mk.injEq]

/-- J preserves the focal locus. -/
def FocalConfig.J (c : FocalConfig) : FocalConfig :=
  ⟨PhasorConfig.J c.config, (cancels_J _).mpr c.cancels, by rw [mass_J]; exact c.mass_pos,
    c.height_pos⟩

/-- **J descends through the quotient.** -/
theorem Q_J (c : FocalConfig) : Q c.J = Q c :=
  (Q_eq_iff _ _).mpr ⟨mass_J _, rfl⟩

/-! ## The per-site Frobenius action -/

/-- The per-site Frobenius action at parameter `t`: the phasor at site `k + 1` times the Frobenius
eigenphase `mellinSpin t (k + 1)`. -/
def frob (t : ℝ) (c : PhasorConfig) : PhasorConfig :=
  ⟨c.height, c.size, fun k => LFunctionPhasor.mellinSpin t ((k : ℕ) + 1) * c.phasor k⟩

/-- The multiplier is the first entry of the existing Frobenius block. -/
theorem frob_entry (t : ℝ) (n : ℕ) :
    FrobeniusSimilitude.frobeniusBlock t n 0 0 = LFunctionPhasor.mellinSpin t n := by
  simp [FrobeniusSimilitude.frobeniusBlock]

@[simp] theorem frob_height (t : ℝ) (c : PhasorConfig) : (frob t c).height = c.height := rfl

/-- **The per-site Frobenius action keeps the mass.** -/
theorem frob_mass (t : ℝ) (c : PhasorConfig) : (frob t c).mass = c.mass := by
  unfold PhasorConfig.mass frob
  simp only [norm_mul, LFunctionPhasor.mellinSpin_norm, one_mul]

/-- **The transformed resultant.** -/
theorem frob_resultant (t : ℝ) (c : PhasorConfig) :
    (frob t c).resultant =
      ∑ k : Fin c.size, LFunctionPhasor.mellinSpin t ((k : ℕ) + 1) * c.phasor k := rfl

/-- The two-site test configuration: `1` at site 1, `−1` at site 2, height 1. -/
def testConfig : PhasorConfig := ⟨1, 2, ![1, -1]⟩

theorem testConfig_cancels : testConfig.Cancels := by
  show ∑ k : Fin 2, (![1, -1] : Fin 2 → ℂ) k = 0
  simp [Fin.sum_univ_two]

theorem testConfig_mass : testConfig.mass = 2 := by
  show ∑ k : Fin 2, ‖(![1, -1] : Fin 2 → ℂ) k‖ = 2
  simp [Fin.sum_univ_two]
  norm_num

theorem mellinSpin_one (t : ℝ) : LFunctionPhasor.mellinSpin t 1 = 1 := by
  simp [LFunctionPhasor.mellinSpin]

theorem mellinSpin_two_half_turn :
    LFunctionPhasor.mellinSpin (Real.pi / Real.log 2) 2 = -1 := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have h : Real.pi / Real.log 2 * Real.log ((2 : ℕ) : ℝ) = Real.pi := by
    push_cast
    field_simp
  rw [LFunctionPhasor.mellinSpin, ← Complex.ofReal_mul, h, neg_mul, Complex.exp_neg,
    Complex.exp_pi_mul_I]
  norm_num

/-- The test configuration's image at `t = π / log 2` has resultant `2`. -/
theorem frob_testConfig_resultant :
    (frob (Real.pi / Real.log 2) testConfig).resultant = 2 := by
  rw [frob_resultant]
  show ∑ k : Fin 2, LFunctionPhasor.mellinSpin (Real.pi / Real.log 2) ((k : ℕ) + 1) *
    (![1, -1] : Fin 2 → ℂ) k = 2
  simp [Fin.sum_univ_two, mellinSpin_one, mellinSpin_two_half_turn]
  norm_num

/-- **The focal locus is not stable under the per-site Frobenius action.** -/
theorem frob_not_focal_stable :
    ∃ (c : PhasorConfig) (t : ℝ), c.Cancels ∧ 0 < c.mass ∧ ¬ (frob t c).Cancels := by
  refine ⟨testConfig, Real.pi / Real.log 2, testConfig_cancels, by rw [testConfig_mass]; norm_num,
    ?_⟩
  unfold PhasorConfig.Cancels
  rw [frob_testConfig_resultant]
  norm_num

/-! ## The event: the Frobenius image is the frozen-window sum at chart height `y + t` -/

/-- The pre-spin amplitude of the cancelling phasor at site `k + 1`. -/
def amplitude (e : FocalEvent) (k : ℕ) : ℂ :=
  ((headWindow (physicalHead e.y) k : ℝ) : ℂ) * (e.w (k + 1) * (e.a k : ℂ))

/-- The head sum with the window frozen at the event's head and the spins at chart height `u`. -/
def frozenSum (e : FocalEvent) (u : ℝ) : ℂ :=
  ∑ k ∈ Finset.range ⌈physicalHead e.y⌉₊, amplitude e k * LFunctionPhasor.mellinSpin u (k + 1)

theorem mellinSpin_add (s t : ℝ) (n : ℕ) :
    LFunctionPhasor.mellinSpin t n * LFunctionPhasor.mellinSpin s n =
      LFunctionPhasor.mellinSpin (s + t) n := by
  unfold LFunctionPhasor.mellinSpin
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem frozenSum_event (e : FocalEvent) : frozenSum e e.y = headSum e.w e.a e.y := by
  rw [headSum_eq_sum_cancelling]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold amplitude cancellingPhasor
  ring

/-- **The Frobenius image of the event's configuration** has resultant the frozen-window sum at chart
height `y + t`. -/
theorem frob_eventConfig_resultant (e : FocalEvent) (t : ℝ) :
    (frob t (eventConfig e)).resultant = frozenSum e (e.y + t) := by
  rw [frob_resultant, frozenSum]
  rw [← Fin.sum_univ_eq_sum_range (fun k => amplitude e k * LFunctionPhasor.mellinSpin (e.y + t) (k + 1))]
  refine Finset.sum_congr rfl fun k _ => ?_
  show LFunctionPhasor.mellinSpin t ((k : ℕ) + 1) * cancellingPhasor e.w e.a e.y k = _
  rw [← mellinSpin_add]
  unfold cancellingPhasor amplitude
  ring

/-- **`frob t` keeps the event's cancellation exactly when the frozen sum vanishes at `y + t`.** -/
theorem frob_eventConfig_cancels_iff (e : FocalEvent) (t : ℝ) :
    (frob t (eventConfig e)).Cancels ↔ frozenSum e (e.y + t) = 0 := by
  unfold PhasorConfig.Cancels
  rw [frob_eventConfig_resultant]

/-- **Where the image stays in the focal locus, `Q` does not change**: the per-site action keeps mass
and height, so stability of the locus is the only obstruction to `Q ∘ frob t = Q`. -/
theorem Q_frob_of_cancels (t : ℝ) (c : FocalConfig) (h : (frob t c.config).Cancels) :
    Q ⟨frob t c.config, h, by rw [frob_mass]; exact c.mass_pos, c.height_pos⟩ = Q c :=
  (Q_eq_iff _ _).mpr ⟨frob_mass _ _, rfl⟩

/-! ## The native Frobenius: one phase per lane -/

/-- One unit phase on every phasor (the native Frobenius's action on a lane). -/
def rotate (u : ℂ) (c : PhasorConfig) : PhasorConfig := ⟨c.height, c.size, fun k => u * c.phasor k⟩

theorem resultant_rotate (u : ℂ) (c : PhasorConfig) : (rotate u c).resultant = u * c.resultant := by
  unfold PhasorConfig.resultant rotate
  rw [Finset.mul_sum]

theorem mass_rotate {u : ℂ} (hu : ‖u‖ = 1) (c : PhasorConfig) : (rotate u c).mass = c.mass := by
  unfold PhasorConfig.mass rotate
  simp only [norm_mul, hu, one_mul]

/-- The lane phase preserves the focal locus. -/
def FocalConfig.rotate {u : ℂ} (hu : ‖u‖ = 1) (c : FocalConfig) : FocalConfig :=
  ⟨FocalQuotient.rotate u c.config,
    by unfold PhasorConfig.Cancels; rw [resultant_rotate, show c.config.resultant = 0 from c.cancels,
      mul_zero],
    by rw [mass_rotate hu]; exact c.mass_pos, c.height_pos⟩

/-- **The lane phase descends: `Q ∘ rotate u = Q`.** -/
theorem Q_rotate {u : ℂ} (hu : ‖u‖ = 1) (c : FocalConfig) : Q (c.rotate hu) = Q c :=
  (Q_eq_iff _ _).mpr ⟨mass_rotate hu _, rfl⟩

/-- The native Frobenius's lane phases are unit phases. -/
theorem nativeFrobenius_lane_phase_norm (y : ℝ) (n : ℕ) :
    ‖LFunctionPhasor.mellinSpin y n‖ = 1 ∧ ‖(starRingEnd ℂ) (LFunctionPhasor.mellinSpin y n)‖ = 1 :=
  ⟨LFunctionPhasor.mellinSpin_norm y n, by rw [Complex.norm_conj, LFunctionPhasor.mellinSpin_norm]⟩

end CriticalLinePhasor.FocalQuotient

#print axioms CriticalLinePhasor.FocalQuotient.Q_J
#print axioms CriticalLinePhasor.FocalQuotient.frob_entry
#print axioms CriticalLinePhasor.FocalQuotient.frob_mass
#print axioms CriticalLinePhasor.FocalQuotient.frob_not_focal_stable
#print axioms CriticalLinePhasor.FocalQuotient.frozenSum_event
#print axioms CriticalLinePhasor.FocalQuotient.frob_eventConfig_resultant
#print axioms CriticalLinePhasor.FocalQuotient.frob_eventConfig_cancels_iff
#print axioms CriticalLinePhasor.FocalQuotient.Q_frob_of_cancels
#print axioms CriticalLinePhasor.FocalQuotient.Q_rotate
#print axioms CriticalLinePhasor.FocalQuotient.nativeFrobenius_lane_phase_norm
