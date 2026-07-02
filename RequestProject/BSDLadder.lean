import RequestProject.HingeKernel
import RequestProject.AntihelixWindow

/-!
# The BSD rank ladder: the formal skeleton

The measured arc (`tmp/bsd_weld.py`, `tmp/bsd_rank_ladder.py`, `tmp/rank4_weld.py`,
`tmp/rank5_weld.py`): ranks 0–5 (11.a, 37.a, 389.a, 5077.a, 234446.a, Brumer–McGuinness),
first live hinge jet = the BSD leading datum at measured/predicted
1.00000 / 1.00000 / 0.99998 / 0.99974 / 0.99999 / 1.00000, with parity-dead layers at
`10⁻¹³`–`10⁻¹⁶` and rank-dead layers at `10⁻⁴`–`10⁻⁹`.  This file gives the arc its
formal skeleton — everything that is algebra/analysis rather than arithmetic:

* `hingeDim` — the hinge dimension: the first live jet of the collapse wave (Sam's
  dimension principle, `d(0)` of the census).
* `hingeDim_even_of_even` / `hingeDim_odd_of_odd` — **the parity conjecture's analytic
  shadow, at the level of the dimension itself**: an even wave (`ε = +1`) has even hinge
  dimension, an odd wave (`ε = −1`) odd — inherited from the jet-parity kernels
  (`HingeKernel.even_live_jet_is_even`, `odd_live_jet_is_odd`).
* `hingeDim_pos_of_odd` — `ε = −1` forces `d(0) ≥ 1` (the forced central zero, as a
  dimension statement; the value-level kernel is `weld_minus_one_forces_zero` and its
  term-local form `weld_kills_each_phasor`).
* `Gr` — the reference ladder `G_0(x) = e^{−x}`, `G_{r+1}(x) = ∫_x^∞ G_r(t) dt/t`, whose
  sums `2·Σ (aₙ/n)·G_r(2πn/√N)` are the BSD leading data `L^{(r)}(1)/r!` (Cremona 2.13;
  validated against Gross–Zagier/BGZ to 10 digits).  `Gr_nonneg` — every rung is
  nonnegative (the positivity that makes the reference series a dissipation profile);
  `Gr_one_eq` — the first rung is the reverb kernel `E₁` (= `upperGamma 0`), tying the
  BSD rate to the reverb chapter's residue machinery.

The arithmetic content (that `d(0)` equals the Mordell–Weil rank) is BSD itself — the
measured tier, never claimed as theorem.  No `sorry`, no `axiom`, standard footprint.
-/

open Complex MeasureTheory Set

namespace CriticalLinePhasor.BSDLadder

open CriticalLinePhasor.HingeKernel CriticalLinePhasor.AntihelixWindow

/-! ## The hinge dimension and its forced parity -/

/-- The hinge dimension of a wave: the first live jet at the origin (`d(0)` of the
dimension census — Sam's dimension principle). -/
noncomputable def hingeDim (f : ℝ → ℝ) : ℕ := sInf {k | iteratedDeriv k f 0 ≠ 0}

/-- If any jet is alive, the hinge dimension is itself a live jet. -/
theorem hingeDim_mem {f : ℝ → ℝ} (h : ∃ k, iteratedDeriv k f 0 ≠ 0) :
    iteratedDeriv (hingeDim f) f 0 ≠ 0 :=
  Nat.sInf_mem h

/-- **Weld `+1` ⟹ even hinge dimension**: an even collapse wave can only die to even
depth.  (Rank ladder: 11.a `d=0`, 389.a `d=2`, 234446.a `d=4`.) -/
theorem hingeDim_even_of_even {f : ℝ → ℝ} (heven : ∀ t, f (-t) = f t)
    (h : ∃ k, iteratedDeriv k f 0 ≠ 0) : Even (hingeDim f) :=
  even_live_jet_is_even heven (hingeDim_mem h)

/-- **Weld `−1` ⟹ odd hinge dimension**: an odd collapse wave can only die to odd
depth.  (Rank ladder: 37.a `d=1`, 5077.a `d=3`, Brumer–McGuinness `d=5`.) -/
theorem hingeDim_odd_of_odd {f : ℝ → ℝ} (hodd : ∀ t, f (-t) = -f t)
    (h : ∃ k, iteratedDeriv k f 0 ≠ 0) : Odd (hingeDim f) :=
  odd_live_jet_is_odd hodd (hingeDim_mem h)

/-- **`ε = −1` forces a vanishing hinge**: an odd wave has `d(0) ≥ 1` — the forced
central zero as a dimension statement (rank parity as interference). -/
theorem hingeDim_pos_of_odd {f : ℝ → ℝ} (hodd : ∀ t, f (-t) = -f t)
    (h : ∃ k, iteratedDeriv k f 0 ≠ 0) : 1 ≤ hingeDim f := by
  rcases hingeDim_odd_of_odd hodd h with ⟨m, hm⟩
  omega

/-- **The dead layers**: everything below the hinge dimension vanishes — the tower
structure of the census (measured at `10⁻⁴`–`10⁻¹⁶` across the ladder). -/
theorem dead_layers_below {f : ℝ → ℝ} {k : ℕ} (hk : k < hingeDim f) :
    iteratedDeriv k f 0 = 0 := by
  by_contra h
  exact absurd (Nat.sInf_le h) (not_le.mpr hk)

/-- `ε = −1` kills the hinge value directly: an odd wave vanishes at the origin — the
dimension-0 layer of the forced central zero. -/
theorem hinge_value_zero_of_odd {f : ℝ → ℝ} (hodd : ∀ t, f (-t) = -f t) : f 0 = 0 := by
  have h := hodd 0
  rw [neg_zero] at h
  linarith

/-- The weld parity in one statement: for a wave of weld sign `ε` the hinge dimension
has parity `ε` — `(−1)^{d(0)} = ε`.  (Even case `ε = +1`, odd case `ε = −1`.) -/
theorem hingeDim_parity {f : ℝ → ℝ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hweld : ∀ t, f (-t) = ε * f t)
    (h : ∃ k, iteratedDeriv k f 0 ≠ 0) : (-1 : ℝ) ^ hingeDim f = ε := by
  rcases hε with h1 | h1
  · rw [h1]
    exact Even.neg_one_pow (hingeDim_even_of_even (by simpa [h1] using hweld) h)
  · rw [h1]
    exact Odd.neg_one_pow (hingeDim_odd_of_odd (by simpa [h1] using hweld) h)

/-! ## The reference ladder `G_r` -/

/-- The BSD reference ladder: `G_0(x) = e^{−x}`, `G_{r+1}(x) = ∫_x^∞ G_r(t) dt/t`.
The sums `2 Σ (aₙ/n) G_r(2πn/√N)` are `L^{(r)}(1)/r!` — the ladder of leading data. -/
noncomputable def Gr : ℕ → ℝ → ℝ
  | 0, x => Real.exp (-x)
  | r + 1, x => ∫ t in Ioi x, Gr r t / t

/-- Every rung of the ladder is nonnegative beyond a nonnegative cut: the reference
series is a dissipation profile, rung by rung. -/
theorem Gr_nonneg : ∀ (r : ℕ) {x : ℝ}, 0 ≤ x → 0 ≤ Gr r x := by
  intro r
  induction r with
  | zero => intro x _; exact (Real.exp_pos _).le
  | succ n ih =>
      intro x hx
      refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
      have h0 : 0 < t := lt_of_le_of_lt hx ht
      exact div_nonneg (ih (le_of_lt h0)) h0.le

/-- The first rung is the reverb kernel: `G_1 = Γ(0, ·)` (= `E₁`), the same
incomplete-Γ tail as the antihelix growth window at `s = 0` — the BSD rate and the
reverb residue machinery share one kernel. -/
theorem Gr_one_eq (x : ℝ) : Gr 1 x = ∫ t in Ioi x, Real.exp (-t) / t := by
  rfl

end CriticalLinePhasor.BSDLadder
