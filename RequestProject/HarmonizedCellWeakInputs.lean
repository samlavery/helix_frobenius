import RequestProject.HarmonizedCellTelescoping

/-!
# Weak-form local inputs for the harmonized-cell route

`globalCoordinateIdentification_of_harmonizedCells` consumes its two local statements in
`o(c n)` form.  This file compiles the *weakest sufficient* versions — the strengths the
converter probe measured (tmp/converter_cell_probe.py, 2026-07-31: boundary accumulation
flat in [−1.05, 0.37] over 5000 Gram cells; per-cell mass ≤ 1.36 with decreasing RMS):

* `CellMassBounded` — a uniform single-cell absolute-mass bound (`O(1)` against the
  required `o(c n)`);
* `BoundaryLogAccumulation` — a logarithmic boundary-accumulation bound, the native
  ledger's analogue of Littlewood's classical `∫₀ᵀ S = O(log T)`.

Each implication to the `o` form is unconditional glue, and the capstone restates the
global coordinate identification with the weak forms as the only native inputs.  The
statements are generic in the decomposition `c`; the probe's Gram/μ6 instantiation is a
choice made at attack time, not here.

Also compiled: the cell-mass reduction — on any cell, the ledger's absolute mass is
controlled by the boundary ledger value, the per-cell event count, the cell length, and
the clock span (`abs_smult_le_on_cell`, `cellMass_le`, `cellMassBounded_of_uniform`).
This localizes the (L2) target to three interpretable native quantities.

Proven in this file: everything below, unconditionally.
-/

open Complex Set MeasureTheory Filter Asymptotics
open intervalIntegral

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor CriticalLinePhasor.CarrierScale CriticalLinePhasor.ResidueJump

/-! ## The weak inputs -/

/-- Weak (L2): the single-cell absolute mass of the native ledger is uniformly bounded
over the decomposition. -/
def CellMassBounded (c : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, (∫ t in (c n)..(c (n + 1)), |Smult t|) ≤ C

/-- Weak (L1): logarithmic boundary accumulation — the native ledger's running integral
at cell boundaries grows at most like the logarithm of the height. -/
def BoundaryLogAccumulation (c : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ,
    |∫ t in (0:ℝ)..(c n), Smult t| ≤ C * (1 + Real.log (1 + c n))

/-! ## Glue: a constant is little-o of an unbounded decomposition -/

private theorem const_isLittleO_decomposition {c : ℕ → ℝ}
    (htop : Tendsto c atTop atTop) :
    (fun _ : ℕ => (1:ℝ)) =o[atTop] fun n => c n := by
  rw [Asymptotics.isLittleO_const_left]
  right
  have h := tendsto_abs_atTop_atTop.comp htop
  simpa only [Function.comp_def, Real.norm_eq_abs] using h

/-- A uniform cell-mass bound delivers the sublinear single-cell input. -/
theorem cellMass_isLittleO {c : ℕ → ℝ} (hmono : Monotone c)
    (htop : Tendsto c atTop atTop) (h : CellMassBounded c) :
    (fun n => ∫ t in (c n)..(c (n + 1)), |Smult t|) =o[atTop] fun n => c n := by
  obtain ⟨C, hC⟩ := h
  have hO : (fun n => ∫ t in (c n)..(c (n + 1)), |Smult t|)
      =O[atTop] fun _ : ℕ => (1:ℝ) := by
    rw [isBigO_iff]
    refine ⟨max C 0, Eventually.of_forall fun n => ?_⟩
    have hnn : 0 ≤ ∫ t in (c n)..(c (n + 1)), |Smult t| :=
      intervalIntegral.integral_nonneg (hmono (Nat.le_succ n)) fun t _ => abs_nonneg _
    rw [Real.norm_eq_abs, norm_one, mul_one, abs_of_nonneg hnn]
    exact (hC n).trans (le_max_left _ _)
  exact hO.trans_isLittleO (const_isLittleO_decomposition htop)

/-- A logarithmic boundary bound delivers the sublinear boundary input. -/
theorem boundaryLog_isLittleO {c : ℕ → ℝ} (hmono : Monotone c) (hc0 : 0 ≤ c 0)
    (htop : Tendsto c atTop atTop) (h : BoundaryLogAccumulation c) :
    (fun n => ∫ t in (0:ℝ)..(c n), Smult t) =o[atTop] fun n => c n := by
  obtain ⟨C, hC⟩ := h
  have hcn : ∀ n, 0 ≤ c n := fun n => hc0.trans (hmono (Nat.zero_le n))
  -- the log gauge is little-o of the decomposition
  have hgauge : (fun n => 1 + Real.log (1 + c n)) =o[atTop] fun n => c n := by
    have h1 : Tendsto (fun n => 1 + c n) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 htop
    have hlog : (fun n => Real.log (1 + c n)) =o[atTop] fun n => 1 + c n := by
      have := Real.isLittleO_log_id_atTop.comp_tendsto h1
      simpa only [Function.comp_def, id_eq] using this
    have hshift : (fun n => 1 + c n) =O[atTop] fun n => c n := by
      rw [isBigO_iff]
      refine ⟨2, ?_⟩
      filter_upwards [htop.eventually_ge_atTop 1] with n hn
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + c n),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ c n)]
      linarith
    exact (const_isLittleO_decomposition htop).add (hlog.trans_isBigO hshift)
  -- the boundary sequence is big-O of the log gauge
  have hO : (fun n => ∫ t in (0:ℝ)..(c n), Smult t)
      =O[atTop] fun n => 1 + Real.log (1 + c n) := by
    rw [isBigO_iff]
    refine ⟨max C 0, Eventually.of_forall fun n => ?_⟩
    have hlognn : 0 ≤ Real.log (1 + c n) :=
      Real.log_nonneg (by have := hcn n; linarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + Real.log (1 + c n))]
    exact (hC n).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  exact hO.trans_isLittleO hgauge

/-! ## The capstone with weak inputs -/

/-- **The weak forms suffice.**  A uniform per-cell mass bound and a logarithmic
boundary accumulation on any monotone unbounded decomposition, together with the cited
Littlewood input, close the global coordinate identification at every good height. -/
theorem globalCoordinateIdentification_of_weakInputs
    {c : ℕ → ℝ} (hmono : Monotone c) (hc0 : 0 ≤ c 0)
    (htop : Tendsto c atTop atTop)
    (hmass : CellMassBounded c) (hbdry : BoundaryLogAccumulation c)
    (hLittlewood : (fun T => ∫ t in (0:ℝ)..T,
        (Smult t + (offLineStripZeroCountMult t : ℝ))) =o[atTop] fun T : ℝ => T) :
    ∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T :=
  globalCoordinateIdentification_of_harmonizedCells hmono hc0 htop
    (boundaryLog_isLittleO hmono hc0 htop hbdry)
    (cellMass_isLittleO hmono htop hmass)
    hLittlewood

/-! ## The cell-mass reduction: three native quantities control (L2) -/

/-- Pointwise ledger bound on a cell: between two heights the native ledger moves only
by event jumps (upward, counted by the window) and clock advance (bounded by the span).
-/
theorem abs_smult_le_on_cell {a b : ℝ} {D : ℝ}
    (hD : ∀ t ∈ Set.Icc a b, |theta t - theta a| ≤ D)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    |Smult t| ≤ |Smult a|
      + ((zeroEventCountMult b : ℝ) - zeroEventCountMult a) + D / Real.pi := by
  have hstep : Smult = fun u =>
      ((zeroEventCountMult u : ℝ)) - (1 + theta u / Real.pi) := by
    funext u
    unfold CriticalLinePhasor.ResidueJump.Smult
    ring
  set X : ℝ := (zeroEventCountMult t : ℝ) - zeroEventCountMult a with hXdef
  set Y : ℝ := (theta t - theta a) / Real.pi with hYdef
  have hkey : Smult t = Smult a + (X - Y) := by
    rw [hstep, hXdef, hYdef]; ring
  have hcount_lo : (0:ℝ) ≤ X := by
    have h := zeroEventCountMult_mono ht.1
    have h' : (zeroEventCountMult a : ℝ) ≤ zeroEventCountMult t := by exact_mod_cast h
    rw [hXdef]; linarith
  have hcount_hi : X ≤ (zeroEventCountMult b : ℝ) - zeroEventCountMult a := by
    have h := zeroEventCountMult_mono ht.2
    have h' : (zeroEventCountMult t : ℝ) ≤ zeroEventCountMult b := by exact_mod_cast h
    rw [hXdef]; linarith
  have hclock : |Y| ≤ D / Real.pi := by
    rw [hYdef, abs_div, abs_of_pos Real.pi_pos]
    gcongr
    exact hD t ht
  have htri : |Smult t| ≤ |Smult a| + |X - Y| := by
    rw [hkey]; exact abs_add_le _ _
  have htri2 : |X - Y| ≤ |X| + |Y| :=
    calc |X - Y| = |X + -Y| := by rw [sub_eq_add_neg]
      _ ≤ |X| + |-Y| := abs_add_le _ _
      _ = |X| + |Y| := by rw [abs_neg]
  have hXabs : |X| = X := abs_of_nonneg hcount_lo
  linarith

/-- **Single-cell absolute mass is controlled by three native quantities**: the boundary
ledger value, the per-cell event count, and the clock span, scaled by the cell length. -/
theorem cellMass_le {a b : ℝ} (hab : a ≤ b) {D : ℝ}
    (hD : ∀ t ∈ Set.Icc a b, |theta t - theta a| ≤ D) :
    (∫ t in a..b, |Smult t|) ≤ (b - a) * (|Smult a|
      + ((zeroEventCountMult b : ℝ) - zeroEventCountMult a) + D / Real.pi) := by
  have hconst : (∫ _t in a..b, (|Smult a|
      + ((zeroEventCountMult b : ℝ) - zeroEventCountMult a) + D / Real.pi))
      = (b - a) * (|Smult a|
        + ((zeroEventCountMult b : ℝ) - zeroEventCountMult a) + D / Real.pi) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rw [← hconst]
  exact intervalIntegral.integral_mono_on hab
    ((smult_intervalIntegrable a b).abs) intervalIntegrable_const
    (fun t ht => abs_smult_le_on_cell hD ht)

/-- **The (L2) reduction.**  Uniform cell length, boundary ledger values, per-cell event
counts, and clock spans deliver the weak cell-mass input on any monotone decomposition:
the (L2) target is exactly the uniformity of three native quantities. -/
theorem cellMassBounded_of_uniform {c : ℕ → ℝ} (hmono : Monotone c)
    {L S₀ K D : ℝ}
    (hlen : ∀ n, c (n + 1) - c n ≤ L)
    (hbv : ∀ n, |Smult (c n)| ≤ S₀)
    (hcount : ∀ n,
      (zeroEventCountMult (c (n + 1)) : ℝ) - zeroEventCountMult (c n) ≤ K)
    (hclock : ∀ n, ∀ t ∈ Set.Icc (c n) (c (n + 1)),
      |theta t - theta (c n)| ≤ D) :
    CellMassBounded c := by
  refine ⟨max L 0 * (S₀ + K + max D 0 / Real.pi), fun n => ?_⟩
  have hab : c n ≤ c (n + 1) := hmono (Nat.le_succ n)
  have hD' : ∀ t ∈ Set.Icc (c n) (c (n + 1)), |theta t - theta (c n)| ≤ max D 0 :=
    fun t ht => (hclock n t ht).trans (le_max_left _ _)
  refine (cellMass_le hab hD').trans ?_
  have hlen' : c (n + 1) - c n ≤ max L 0 := (hlen n).trans (le_max_left _ _)
  have hcnn : (0:ℝ) ≤ (zeroEventCountMult (c (n + 1)) : ℝ) - zeroEventCountMult (c n) := by
    have h := zeroEventCountMult_mono hab
    have h' : (zeroEventCountMult (c n) : ℝ) ≤ zeroEventCountMult (c (n + 1)) := by
      exact_mod_cast h
    linarith
  have hdnn : (0:ℝ) ≤ max D 0 / Real.pi :=
    div_nonneg (le_max_right _ _) Real.pi_pos.le
  have hinner0 : 0 ≤ |Smult (c n)|
      + ((zeroEventCountMult (c (n + 1)) : ℝ) - zeroEventCountMult (c n))
      + max D 0 / Real.pi := by
    have := abs_nonneg (Smult (c n)); linarith
  have hinner : |Smult (c n)|
      + ((zeroEventCountMult (c (n + 1)) : ℝ) - zeroEventCountMult (c n))
      + max D 0 / Real.pi ≤ S₀ + K + max D 0 / Real.pi := by
    have h1 := hbv n; have h2 := hcount n; linarith
  exact mul_le_mul hlen' hinner hinner0 (le_max_right L 0)

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.cellMass_isLittleO
#print axioms CriticalLinePhasor.ContourArgument.boundaryLog_isLittleO
#print axioms CriticalLinePhasor.ContourArgument.globalCoordinateIdentification_of_weakInputs
#print axioms CriticalLinePhasor.ContourArgument.abs_smult_le_on_cell
#print axioms CriticalLinePhasor.ContourArgument.cellMass_le
#print axioms CriticalLinePhasor.ContourArgument.cellMassBounded_of_uniform
