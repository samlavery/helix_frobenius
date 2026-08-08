import RequestProject.HarmonizedCellWeakInputs
import RequestProject.StClockJumpLaw

/-!
# The clock-chart cell residue: exact phase combinatorics of the native ledger

The probes of 2026-07-31 (tmp/clock_phase_law.py, tmp/clock_phase_pinning.py) located
the native per-cell law in the harmonized clock chart: with `dϑ/π` as the cell measure,
the residue of every cell is exact algebra in the boundary defect and the event clock
phases, and the measured law is *phase slaving* — every cell's clock residue sits at
the event-free floor `±1/2` up to an excess that vanished on 99.66% of the first 4999
Gram cells (max excess 0.1122).  The t-chart observation `|A_n| < 1` was resolved as
this law times the cell length (chart transfer max error 0.042).

Compiled here, unconditionally:

* `smult_clock_integral_of_const` — the constancy-interval identity: between events,
  `∫ Smult·(ϑ'/π) dt` has the exact antiderivative `(m−1)·ϑ/π − ϑ²/(2π²)`.
* `clockResidue_floor` — **the floor law**: an event-free cell of clock span `π`
  starting at clock `ν·π` has residue exactly `(m − 1 − ν) − 1/2`.
* `clockResidue_one_event` — the one-event cell (85.7% of cells in range): residue
  `= s + (1 − τ) − 1/2` with `τ = ϑ(γ)/π − ν` the event's clock phase.  Cells with
  more events assemble by iterating the same adjacent-interval split; not compiled here.
* `clock_boundary_of_phaseSlaving` — what the slaving law buys at the boundary:
  `|Σ_{n<N} residue| ≤ N/2 + Σε`.  The `N/2` term is the floor ledger; its cancellation
  (probe: 175 cells at `+1/2` vs 183 at `−1/2`, forced by defect neutrality) is the
  remaining structure and is *not* claimed here.
* `cellMassBounded_of_clockMass` — chart transfer: a positive clock-rate floor converts
  the clock-measure mass bound into the landed `CellMassBounded` input.
* `globalCoordinateIdentification_of_clockInputs` — the capstone chain: rate floor +
  clock-measure mass bound + logarithmic boundary accumulation + Littlewood close the
  global coordinate identification.
* `clockMass_le` / `clockCellMassBounded_of_uniform` — **length-free mass control**: in
  the clock chart the cell-length input disappears; on a harmonized decomposition the
  clock mass is controlled by boundary ledger values and event counts alone.
-/

open Complex Set MeasureTheory Filter Asymptotics
open intervalIntegral

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor CriticalLinePhasor.CarrierScale CriticalLinePhasor.ResidueJump

/-! ## The constancy-interval identity -/

/-- **Between events the clock-weighted ledger integrates exactly.**  If the native
count is constant on the open interval, `Smult·(ϑ'/π)` has antiderivative
`(m−1)·ϑ/π − ϑ²/(2π²)`. -/
theorem smult_clock_integral_of_const {u v : ℝ} (huv : u ≤ v) (m : ℕ)
    (hconst : ∀ t ∈ Set.Ioo u v, zeroEventCountMult t = m) :
    ∫ t in u..v, Smult t * (clockRate t / Real.pi)
      = ((m : ℝ) - 1) * (theta v - theta u) / Real.pi
        - (theta v ^ 2 - theta u ^ 2) / (2 * Real.pi ^ 2) := by
  have hstep : Smult = fun t =>
      ((zeroEventCountMult t : ℝ)) - (1 + theta t / Real.pi) := by
    funext t
    unfold CriticalLinePhasor.ResidueJump.Smult
    ring
  -- replace the ledger by its constant-count form a.e. on the interval
  have hv : ∀ᵐ t : ℝ ∂volume, t ≠ v := by
    rw [ae_iff]
    have hset : {t : ℝ | ¬t ≠ v} = {v} := by
      ext t; simp
    rw [hset]
    exact measure_singleton v
  have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc u v →
      Smult t * (clockRate t / Real.pi)
        = (((m : ℝ) - 1) - theta t / Real.pi) * (clockRate t / Real.pi) := by
    filter_upwards [hv] with t htv hmem
    rw [Set.uIoc_of_le huv] at hmem
    have hIoo : t ∈ Set.Ioo u v := ⟨hmem.1, lt_of_le_of_ne hmem.2 htv⟩
    have h1 : Smult t = ((zeroEventCountMult t : ℝ)) - (1 + theta t / Real.pi) :=
      congrFun hstep t
    rw [h1, hconst t hIoo]
    ring
  rw [intervalIntegral.integral_congr_ae hae]
  -- FTC with the explicit antiderivative
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hderiv : ∀ t ∈ Set.uIcc u v,
      HasDerivAt (fun s => ((m : ℝ) - 1) * theta s / Real.pi
          - theta s * theta s / (2 * Real.pi ^ 2))
        ((((m : ℝ) - 1) - theta t / Real.pi) * (clockRate t / Real.pi)) t := by
    intro t _
    have h := theta_hasDerivAt t
    have h1 : HasDerivAt (fun s => ((m : ℝ) - 1) * theta s / Real.pi)
        (((m : ℝ) - 1) * clockRate t / Real.pi) t :=
      (h.const_mul ((m : ℝ) - 1)).div_const Real.pi
    have h2 : HasDerivAt (fun s => theta s * theta s / (2 * Real.pi ^ 2))
        ((clockRate t * theta t + theta t * clockRate t) / (2 * Real.pi ^ 2)) t :=
      (h.mul h).div_const (2 * Real.pi ^ 2)
    have h3 := h1.sub h2
    have heq : (((m : ℝ) - 1) - theta t / Real.pi) * (clockRate t / Real.pi)
        = ((m : ℝ) - 1) * clockRate t / Real.pi
          - (clockRate t * theta t + theta t * clockRate t) / (2 * Real.pi ^ 2) := by
      field_simp
      ring
    rw [heq]
    exact h3
  have hcont : Continuous fun t =>
      (((m : ℝ) - 1) - theta t / Real.pi) * (clockRate t / Real.pi) :=
    (continuous_const.sub (theta_continuous.div_const _)).mul
      (continuous_clockRate.div_const _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable u v)]
  ring

/-! ## The harmonized-cell laws -/

/-- **The floor law.**  An event-free cell of clock span `π` starting at clock `ν·π`
has clock residue exactly `(m − 1 − ν) − 1/2`: the `±1/2` floors observed by the probe
are theorems, with zero freedom. -/
theorem clockResidue_floor {a b : ℝ} (hab : a ≤ b) {ν : ℝ}
    (ha : theta a = ν * Real.pi) (hb : theta b = (ν + 1) * Real.pi)
    (m : ℕ) (hconst : ∀ t ∈ Set.Ioo a b, zeroEventCountMult t = m) :
    ∫ t in a..b, Smult t * (clockRate t / Real.pi)
      = ((m : ℝ) - 1 - ν) - 1 / 2 := by
  rw [smult_clock_integral_of_const hab m hconst, ha, hb]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **The one-event cell.**  With count `m` before the event and `m + 1` after, the
clock residue is exactly `s + (1 − τ) − 1/2`, where `s = m − 1 − ν` is the boundary
defect and `τ = ϑ(γ)/π − ν` is the event's clock phase.  The phase variable of the
probes enters the compiled corpus here. -/
theorem clockResidue_one_event {a γ b : ℝ} (haγ : a ≤ γ) (hγb : γ ≤ b) {ν : ℝ}
    (ha : theta a = ν * Real.pi) (hb : theta b = (ν + 1) * Real.pi)
    (m : ℕ)
    (hleft : ∀ t ∈ Set.Ioo a γ, zeroEventCountMult t = m)
    (hright : ∀ t ∈ Set.Ioo γ b, zeroEventCountMult t = m + 1) :
    ∫ t in a..b, Smult t * (clockRate t / Real.pi)
      = (((m : ℝ) - 1 - ν) + (1 - (theta γ / Real.pi - ν))) - 1 / 2 := by
  have hint : ∀ p q : ℝ, IntervalIntegrable
      (fun t => Smult t * (clockRate t / Real.pi)) volume p q := fun p q =>
    (smult_intervalIntegrable p q).mul_continuousOn
      (continuous_clockRate.div_const _).continuousOn
  rw [← integral_add_adjacent_intervals (hint a γ) (hint γ b),
    smult_clock_integral_of_const haγ m hleft,
    smult_clock_integral_of_const hγb (m + 1) hright, ha, hb]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-! ## The repositioned native targets -/

/-- The clock-weighted cell residue: the ledger integrated in the carrier's own
harmonized measure `dϑ/π`. -/
noncomputable def clockCellResidue (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∫ t in (c n)..(c (n + 1)), Smult t * (clockRate t / Real.pi)

/-- **The phase-slaving law** — the named native target in clock coordinates: every
cell's clock residue sits within `ε n` of the event-free floor `±1/2`, with sublinear
total excess.  (Probe 2026-07-31: `ε n = 0` on 99.66% of the first 4999 Gram cells,
max excess 0.1122, and in defect cells the event phases show hard truncation
boundaries — the phases are slaved to the ledger.) -/
def PhaseSlavingLaw (c : ℕ → ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧
    (∀ n, |clockCellResidue c n| ≤ 1 / 2 + ε n) ∧
    ((fun N => ∑ n ∈ Finset.range N, ε n) =o[atTop] fun N => (N : ℝ))

/-- Clock-measure single-cell mass control: the clock-chart form of the (L2) input. -/
def ClockCellMassBounded (c : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ,
    (∫ t in (c n)..(c (n + 1)), |Smult t| * (clockRate t / Real.pi)) ≤ C

/-- **What phase slaving buys at the boundary**: the running clock residue is bounded
by the floor ledger `N/2` plus the sublinear excess.  The floor term does not vanish
here — its cancellation (defect neutrality balances the `+1/2` and `−1/2` floor
populations) is the remaining structure of the boundary input. -/
theorem clock_boundary_of_phaseSlaving {c : ℕ → ℝ} (h : PhaseSlavingLaw c) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧
      ((fun N => ∑ n ∈ Finset.range N, ε n) =o[atTop] fun N => (N : ℝ)) ∧
      ∀ N : ℕ, |∑ n ∈ Finset.range N, clockCellResidue c n|
        ≤ (N : ℝ) / 2 + ∑ n ∈ Finset.range N, ε n := by
  obtain ⟨ε, hε0, hεb, hεo⟩ := h
  refine ⟨ε, hε0, hεo, fun N => ?_⟩
  calc |∑ n ∈ Finset.range N, clockCellResidue c n|
      ≤ ∑ n ∈ Finset.range N, |clockCellResidue c n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, (1 / 2 + ε n) :=
        Finset.sum_le_sum fun n _ => hεb n
    _ = (N : ℝ) / 2 + ∑ n ∈ Finset.range N, ε n := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        ring

/-! ## Chart transfer: clock-measure mass delivers the landed weak input -/

/-- **Chart transfer for the mass input.**  A positive clock-rate floor on the cells
converts the clock-measure mass bound into the landed `CellMassBounded` input. -/
theorem cellMassBounded_of_clockMass {c : ℕ → ℝ} (hmono : Monotone c)
    {r : ℝ} (hr : 0 < r)
    (hrate : ∀ n, ∀ t ∈ Set.Icc (c n) (c (n + 1)), r ≤ clockRate t)
    (hmass : ClockCellMassBounded c) :
    CellMassBounded c := by
  obtain ⟨C, hC⟩ := hmass
  refine ⟨Real.pi / r * C, fun n => ?_⟩
  have hab : c n ≤ c (n + 1) := hmono (Nat.le_succ n)
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hr' : r ≠ 0 := hr.ne'
  have hpt : ∀ t ∈ Set.Icc (c n) (c (n + 1)),
      |Smult t| ≤ Real.pi / r * (|Smult t| * (clockRate t / Real.pi)) := by
    intro t ht
    have h1 : r ≤ clockRate t := hrate n t ht
    have key : Real.pi / r * (|Smult t| * (clockRate t / Real.pi))
        = |Smult t| * (clockRate t / r) := by
      field_simp
    rw [key]
    have h2 : |Smult t| * 1 ≤ |Smult t| * (clockRate t / r) :=
      mul_le_mul_of_nonneg_left ((one_le_div hr).mpr h1) (abs_nonneg _)
    simpa using h2
  have hint1 : IntervalIntegrable (fun t => |Smult t|) volume (c n) (c (n + 1)) :=
    (smult_intervalIntegrable _ _).abs
  have hint2 : IntervalIntegrable
      (fun t => Real.pi / r * (|Smult t| * (clockRate t / Real.pi)))
      volume (c n) (c (n + 1)) :=
    ((smult_intervalIntegrable _ _).abs.mul_continuousOn
      (continuous_clockRate.div_const _).continuousOn).const_mul _
  calc ∫ t in (c n)..(c (n + 1)), |Smult t|
      ≤ ∫ t in (c n)..(c (n + 1)),
          Real.pi / r * (|Smult t| * (clockRate t / Real.pi)) :=
        intervalIntegral.integral_mono_on hab hint1 hint2 hpt
    _ = Real.pi / r * ∫ t in (c n)..(c (n + 1)),
          |Smult t| * (clockRate t / Real.pi) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ Real.pi / r * C :=
        mul_le_mul_of_nonneg_left (hC n) (div_nonneg Real.pi_pos.le hr.le)

/-- **The clock-chart capstone.**  Rate floor + clock-measure mass bound + logarithmic
boundary accumulation + Littlewood close the global coordinate identification at every
good height. -/
theorem globalCoordinateIdentification_of_clockInputs {c : ℕ → ℝ}
    (hmono : Monotone c) (hc0 : 0 ≤ c 0) (htop : Tendsto c atTop atTop)
    {r : ℝ} (hr : 0 < r)
    (hrate : ∀ n, ∀ t ∈ Set.Icc (c n) (c (n + 1)), r ≤ clockRate t)
    (hmass : ClockCellMassBounded c) (hbdry : BoundaryLogAccumulation c)
    (hLittlewood : (fun T => ∫ t in (0:ℝ)..T,
        (Smult t + (offLineStripZeroCountMult t : ℝ))) =o[atTop] fun T : ℝ => T) :
    ∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T :=
  globalCoordinateIdentification_of_weakInputs hmono hc0 htop
    (cellMassBounded_of_clockMass hmono hr hrate hmass) hbdry hLittlewood

/-! ## Length-free mass control in the clock chart -/

/-- **The cell length disappears in the clock chart**: the clock-measure mass of a cell
is controlled by the boundary ledger value, the event count, and the clock span alone. -/
theorem clockMass_le {a b : ℝ} (hab : a ≤ b)
    (hrate : ∀ t ∈ Set.Icc a b, 0 ≤ clockRate t)
    {D : ℝ} (hD : ∀ t ∈ Set.Icc a b, |theta t - theta a| ≤ D) :
    (∫ t in a..b, |Smult t| * (clockRate t / Real.pi))
      ≤ (|Smult a| + ((zeroEventCountMult b : ℝ) - zeroEventCountMult a)
          + D / Real.pi) * ((theta b - theta a) / Real.pi) := by
  have hint1 : IntervalIntegrable (fun t => |Smult t| * (clockRate t / Real.pi))
      volume a b :=
    (smult_intervalIntegrable a b).abs.mul_continuousOn
      (continuous_clockRate.div_const _).continuousOn
  have hint2 : IntervalIntegrable
      (fun t => (|Smult a| + ((zeroEventCountMult b : ℝ) - zeroEventCountMult a)
        + D / Real.pi) * (clockRate t / Real.pi)) volume a b :=
    (continuous_const.mul (continuous_clockRate.div_const _)).intervalIntegrable a b
  have hpt : ∀ t ∈ Set.Icc a b,
      |Smult t| * (clockRate t / Real.pi)
        ≤ (|Smult a| + ((zeroEventCountMult b : ℝ) - zeroEventCountMult a)
            + D / Real.pi) * (clockRate t / Real.pi) := fun t ht =>
    mul_le_mul_of_nonneg_right (abs_smult_le_on_cell hD ht)
      (div_nonneg (hrate t ht) Real.pi_pos.le)
  refine (intervalIntegral.integral_mono_on hab hint1 hint2 hpt).trans_eq ?_
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_div, ← theta_sub_theta]

/-- **Two quantities suffice on a harmonized decomposition.**  With clock span exactly
`π` per cell and non-negative rate, uniform boundary ledger values and event counts
alone bound the clock mass — no cell-length input. -/
theorem clockCellMassBounded_of_uniform {c : ℕ → ℝ} (hmono : Monotone c)
    (hspan : ∀ n, theta (c (n + 1)) - theta (c n) = Real.pi)
    (hrate : ∀ n, ∀ t ∈ Set.Icc (c n) (c (n + 1)), 0 ≤ clockRate t)
    {S₀ K : ℝ}
    (hbv : ∀ n, |Smult (c n)| ≤ S₀)
    (hcount : ∀ n,
      (zeroEventCountMult (c (n + 1)) : ℝ) - zeroEventCountMult (c n) ≤ K) :
    ClockCellMassBounded c := by
  refine ⟨S₀ + K + 1, fun n => ?_⟩
  have hab : c n ≤ c (n + 1) := hmono (Nat.le_succ n)
  have hD : ∀ t ∈ Set.Icc (c n) (c (n + 1)), |theta t - theta (c n)| ≤ Real.pi := by
    intro t ht
    have h2 : 0 ≤ theta t - theta (c n) := by
      rw [theta_sub_theta]
      exact intervalIntegral.integral_nonneg ht.1
        (fun u hu => hrate n u ⟨hu.1, hu.2.trans ht.2⟩)
    have h4 : 0 ≤ theta (c (n + 1)) - theta t := by
      rw [theta_sub_theta]
      exact intervalIntegral.integral_nonneg ht.2
        (fun u hu => hrate n u ⟨ht.1.trans hu.1, hu.2⟩)
    rw [abs_of_nonneg h2]
    have h5 := hspan n
    linarith
  refine (clockMass_le hab (hrate n) hD).trans ?_
  rw [hspan n, div_self Real.pi_ne_zero, mul_one]
  have h1 := hbv n
  have h2 := hcount n
  linarith

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.smult_clock_integral_of_const
#print axioms CriticalLinePhasor.ContourArgument.clockResidue_floor
#print axioms CriticalLinePhasor.ContourArgument.clockResidue_one_event
#print axioms CriticalLinePhasor.ContourArgument.clock_boundary_of_phaseSlaving
#print axioms CriticalLinePhasor.ContourArgument.cellMassBounded_of_clockMass
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_of_clockInputs
#print axioms CriticalLinePhasor.ContourArgument.clockMass_le
#print axioms CriticalLinePhasor.ContourArgument.clockCellMassBounded_of_uniform
