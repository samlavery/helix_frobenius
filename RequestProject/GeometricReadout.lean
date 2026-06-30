import Mathlib
import RequestProject.GeometricPhasorClosure
import RequestProject.FocalEigenheight
import RequestProject.Phasor3D
import RequestProject.DeBranges

/-!
# The geometric readout layer, log-free helix-angle cancellation, and the fiber residue

This file completes the **geometric convention**: the geometry (helix winding `n·(π/3)`, the μ6
cell, the integer heights `Z_n = n`) lives in the carrier and carries **no logarithm**; the
logarithm is isolated to an explicit **readout / projection** pipeline

```
   3-D carrier  ──[ Möbius / Cayley map ]──▶  2-D  ──[ y = log z ]──▶  1-D analytic ordinate.
```

The logarithm enters only in the last (`2-D → 1-D`) step.

## Contents

* **§1 The explicit readout map.**  `cayley` is the Möbius/Cayley transform used for the
  `3-D → 2-D` step (it sends the real readout line to the unit circle, `cayley_real_norm_one`);
  `heightReadout z = log z` is the `2-D → 1-D` step (= `Geometric.analyticHeight`, the only place a
  logarithm appears).  The identity `z = e^γ` for a zero at readout-ordinate `γ` is **derived
  through the readout** (`height_eq_exp_of_readout`: `y = log z ⟹ z = e^y`), never from a spin rate.

* **§2 Cancellation without log, via helix-angle geometry.**  `cell_antipodal_cancel` is the exact
  `π/3` antipodal cancellation `cell n + cell (n+3) = 0` — a purely geometric (log-free) cancellation
  forced by the μ6 cell.  `helix_cancellation_logfree` re-exports the no-log helix pencil closure
  `Geometric.helix_pencil_det_zero_iff`: the helix/cell feature matrix is built from the `π/3` cell
  residues and the integer heights `Z_n = n` only — **no `log n`** — and it has a cancellation
  (closure) eigenvector at geometric height `Z` exactly when the pencil determinant vanishes.  The
  logarithm appears only later, in the readout that identifies these geometric closure heights with
  the L-zeros.

* **§3 The fiber residue: no double cancellation at one height.**  Modelling the two eigenheight
  directions of a fiber as the chiral conjugate pair `(w, w̄)` (the positive/negative sides), with
  the fiber phasor unimodular `‖w‖ = 1` (e.g. `w = mellinSpin y n`, the L-function readout phasor in
  the 3-D model, or the `π/3` cell `w = cell n`), the ± pair can never both vanish: the block is
  invertible (`det = 1 ≠ 0`).  If the two eigen-phases phase-align (`w = w̄`) the fiber collapses to
  `w = ±1`, whose block is `±I ≠ 0` — still a full residue.  A unimodular phasor also has a *unique*
  cancelling partner (`cancelling_partner_unique`), so it cannot cancel against two distinct
  directions.  Hence one cannot simultaneously phase-align two eigenheights and exactly cancel the ±
  sides: there is always a residue.  This is `fiber_residue_no_double_cancellation`.

`Mathlib`-only, `sorry`/`axiom`-free.
-/

open Complex Filter Topology
open scoped BigOperators Real ComplexConjugate

namespace CriticalLinePhasor.Readout

open CriticalLinePhasor

/-! ## 1. The explicit readout map: `3-D →[Cayley]→ 2-D →[y = log z]→ 1-D` -/

/-- **The Cayley / Möbius readout map** `cayley w = (w - i)/(w + i)`.  This is the `3-D → 2-D` step
of the readout: a genuine Möbius transform identifying the readout line with the unit circle.  It
carries **no logarithm**. -/
noncomputable def cayley (w : ℂ) : ℂ := (w - I) / (w + I)

/-
The Cayley readout map sends the **real readout line to the unit circle**:
`‖cayley x‖ = 1` for real `x` (since `|x - i| = |x + i| = √(x²+1)`).
-/
theorem cayley_real_norm_one (x : ℝ) : ‖cayley (x : ℂ)‖ = 1 := by
  unfold cayley; norm_num [ Complex.normSq, Complex.norm_def ] ; ring;
  positivity

/-- **The `2-D → 1-D` readout** `y = log z`: the geometric height `z` read off as an analytic
ordinate.  This is `Geometric.analyticHeight`, and it is the **only** place the logarithm of the
whole model appears. -/
noncomputable def heightReadout (z : ℝ) : ℝ := Real.log z

/-- The `2-D → 1-D` readout is exactly `Geometric.analyticHeight`. -/
theorem heightReadout_eq_analyticHeight (z : ℝ) :
    heightReadout z = Geometric.analyticHeight z := rfl

/-- **`z = e^γ` derived through the readout.**  If the readout ordinate of a positive carrier height
`z` is `γ` (`y = log z = γ`), then `z = e^γ`.  This is the readout chain `y = log z ⟹ z = e^y`; at a
zero `y = γ ⟹ z = e^γ`.  The `e^γ` comes out of the readout (`Real.exp_log`), not from a spin rate. -/
theorem height_eq_exp_of_readout {z γ : ℝ} (hz : 0 < z) (h : heightReadout z = γ) :
    z = Real.exp γ := by
  rw [← h, heightReadout]; exact (Real.exp_log hz).symm

/-- The readout of `e^γ` recovers the ordinate `γ` (a global, single-valued inverse — no branch
cut): `heightReadout (e^γ) = γ`. -/
theorem readout_exp (γ : ℝ) : heightReadout (Real.exp γ) = γ := by
  rw [heightReadout, Real.log_exp]

/-! ## 2. Cancellation without log, via helix-angle (μ6 / π·3) geometry -/

/-
**Exact `π/3` antipodal cancellation (log-free).**  In the μ6 cell the antipode of `cell n`
(three cells along, the `π` rotation) is its negative, so `cell n + cell (n+3) = 0`.  This is the
exact harmonic/focal cancellation of the positive and negative sides, forced purely by the `π/3`
helix-angle geometry — **no logarithm** is involved.
-/
theorem cell_antipodal_cancel (n : ℕ) : Geometric.cell n + Geometric.cell (n + 3) = 0 := by
  unfold Geometric.cell; push_cast; ring;
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, mul_one_div ];
  norm_num [ Real.cos_add, Real.sin_add ]

/-- **Cancellation without log, via the helix-angle pencil.**  The helix/μ6-cell feature matrix
`Geometric.helixFeature` is built from the `π/3` cell residues and the integer heights `Z_n = n`
only — it contains **no `log n`** — yet it has a cancellation (closure) eigenvector `v ≠ 0` at the
geometric height `Z` exactly when the pencil determinant `det(Aχ,N − Z Bχ,N)` vanishes.  The
logarithm appears only later, in the analytic readout that identifies these geometric closure
heights with the L-zeros.  (This is `Geometric.helix_pencil_det_zero_iff`, re-stated to make the
log-free claim explicit.) -/
theorem helix_cancellation_logfree {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N m : ℕ)
    (Z : ℝ) :
    Geometric.helixPencilDet χ N m Z = 0
      ↔ ∃ v : Fin 6 × Fin m → ℂ, v ≠ 0 ∧
          (Geometric.helixHeightA χ N m).mulVec v
            = (Z : ℂ) • (Geometric.helixMetricB χ N m).mulVec v :=
  Geometric.helix_pencil_det_zero_iff χ N m Z

/-! ## 3. The fiber residue: no double cancellation at a single height -/

/-- A **unit-modulus fiber phasor never vanishes**: `‖w‖ = 1 ⟹ w ≠ 0`.  This is the elementary
residue — a fiber phasor cannot cancel itself. -/
theorem fiber_phasor_ne_zero {w : ℂ} (hw : ‖w‖ = 1) : w ≠ 0 := by
  intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw

/-- **A unimodular phasor has a unique cancelling partner.**  If `a` and `b` both exactly cancel
`w` (`w + a = 0` and `w + b = 0`) then `a = b`: one cannot cancel a phasor against two distinct
directions ("cannot cancel twice"). -/
theorem cancelling_partner_unique {w a b : ℂ} (ha : w + a = 0) (hb : w + b = 0) : a = b := by
  linear_combination ha - hb

/-- **The chiral ± conjugate-pair block of a unit fiber phasor is unimodular**:
`det (conjPairBlock w) = 1`.  (= `DeBranges.conjPairBlock_det_one_of_norm_one`.) -/
theorem fiber_pair_block_det_one {w : ℂ} (hw : ‖w‖ = 1) :
    (DeBranges.conjPairBlock w).det = 1 :=
  DeBranges.conjPairBlock_det_one_of_norm_one hw

/-
**The ± pair never both vanish (the matrix residue).**  For a unit fiber phasor the chiral
conjugate-pair block is invertible (`det = 1 ≠ 0`), hence it is **not** the zero matrix: the
positive and negative sides cannot both cancel at the same height.
-/
theorem fiber_pair_block_ne_zero {w : ℂ} (hw : ‖w‖ = 1) :
    DeBranges.conjPairBlock w ≠ 0 := by
  intro h; have := congr_arg ( fun m => m 0 0 ) h; norm_num [ DeBranges.conjPairBlock ] at this;
  norm_num [ this ] at hw

/-
**Phase-aligned eigenphases collapse to `±1`.**  If the two eigen-phases of a unit fiber phasor
align (`w = w̄`, i.e. `w` is real) then `w = 1` or `w = -1`.  Even then the block is `±I ≠ 0`, so the
alignment still leaves a full residue.
-/
theorem fiber_aligned_eigenphases {w : ℂ} (hw : ‖w‖ = 1) (h : w = (starRingEnd ℂ) w) :
    w = 1 ∨ w = -1 := by
  norm_num [ Complex.ext_iff ] at *;
  norm_num [ Complex.normSq, Complex.norm_def ] at *;
  cases le_or_gt 0 w.re <;> [ left; right ] <;> constructor <;> nlinarith

/-- **No double cancellation at a single height (the fiber residue).**  Model the two eigenheight
directions of a fiber as the chiral conjugate pair `(w, w̄)` — the positive / negative sides — with
the fiber phasor unimodular `‖w‖ = 1` (e.g. `w = mellinSpin y n`, the L-function readout phasor of
the 3-D model, or the `π/3` cell `w = cell n`).  Then, *unconditionally*:

* the ± pair can never both vanish — `conjPairBlock w ≠ 0`, with `det = 1` (a genuine residue);
* if the two eigen-phases phase-align (`w = w̄`) the fiber collapses to `w = ±1`, whose block is
  `±I ≠ 0` — still a full residue;
* a unimodular phasor has a *unique* cancelling partner, so it cannot cancel against two distinct
  directions.

Hence one cannot simultaneously phase-align two eigenheights and exactly cancel the ± sides at the
same height: there is always a residue.  You cannot split the unimodular phasor energy exactly down
the middle so as to cancel twice. -/
theorem fiber_residue_no_double_cancellation {w : ℂ} (hw : ‖w‖ = 1) :
    DeBranges.conjPairBlock w ≠ 0
      ∧ (DeBranges.conjPairBlock w).det = 1
      ∧ (w = (starRingEnd ℂ) w → w = 1 ∨ w = -1)
      ∧ (∀ a b : ℂ, w + a = 0 → w + b = 0 → a = b) :=
  ⟨fiber_pair_block_ne_zero hw, fiber_pair_block_det_one hw,
    fun h => fiber_aligned_eigenphases hw h, fun _ _ ha hb => cancelling_partner_unique ha hb⟩

/-! ### The fiber phasor and the `π/3` cell are concrete unit-modulus fibers -/

/-- The **L-function readout (Mellin) fiber phasor never vanishes**: `mellinSpin y n ≠ 0`. -/
theorem mellinSpin_fiber_residue (y : ℝ) (n : ℕ) :
    LFunctionPhasor.mellinSpin y n ≠ 0 :=
  fiber_phasor_ne_zero (LFunctionPhasor.mellinSpin_norm y n)

/-- The **`π/3` cell carrier phasor never vanishes**: `cell n ≠ 0`. -/
theorem cell_fiber_residue (n : ℕ) : Geometric.cell n ≠ 0 :=
  fiber_phasor_ne_zero (Geometric.cell_norm n)

/-- **The fiber residue for the L-function readout phasor.**  Instantiating the no-double-cancellation
theorem at the concrete fiber phasor `w = mellinSpin y n` of the 3-D L-function model. -/
theorem mellinSpin_residue_no_double_cancellation (y : ℝ) (n : ℕ) :
    DeBranges.conjPairBlock (LFunctionPhasor.mellinSpin y n) ≠ 0
      ∧ (DeBranges.conjPairBlock (LFunctionPhasor.mellinSpin y n)).det = 1
      ∧ (LFunctionPhasor.mellinSpin y n = (starRingEnd ℂ) (LFunctionPhasor.mellinSpin y n)
          → LFunctionPhasor.mellinSpin y n = 1 ∨ LFunctionPhasor.mellinSpin y n = -1)
      ∧ (∀ a b : ℂ, LFunctionPhasor.mellinSpin y n + a = 0
          → LFunctionPhasor.mellinSpin y n + b = 0 → a = b) :=
  fiber_residue_no_double_cancellation (LFunctionPhasor.mellinSpin_norm y n)

/-! ### The fiber as a 3-D L-function phasor, and the π/3 focal ± cancellation -/

/-- **The fiber lives in the 3-D L-function phasor.**  As the readout ordinate advances `y ↦ y + t`,
the spin-plane component of the 3-D L-function phasor `Phasor3D.phasor3D` advances by the unit fiber
phasor `mellinSpin t n` (`Phasor3D.phasor3D_charged_spin`), and that fiber phasor is the
never-vanishing residue.  So the residue is a property of the genuine 3-D phasors of the
L-function. -/
theorem phasor3D_advances_by_fiber_residue (χ : ℕ → ℂ) (σ y t : ℝ) (n : ℕ) :
    Phasor3D.plane (Phasor3D.phasor3D χ σ (y + t) n)
      = LFunctionPhasor.mellinSpin t n * Phasor3D.plane (Phasor3D.phasor3D χ σ y n)
      ∧ LFunctionPhasor.mellinSpin t n ≠ 0 :=
  ⟨Phasor3D.phasor3D_charged_spin χ σ y t n, mellinSpin_fiber_residue t n⟩

/-- **The π/3 focal ± cancellation is exact ⇔ L-zero.**  The positive minus negative scalar
channel `P − M` (the ± sides of the fiber, scaled by `π/3`) closes to `0` exactly at an L-zero
(`Focal.channel_closure_iff_L_zero`).  This is the analytic shadow, through the readout, of the
geometric `π/3` antipodal cancellation `cell_antipodal_cancel`; together with the fiber residue it
says the ± cancellation is exact at a height precisely when the L-value vanishes there, and never
"twice" off a genuine zero. -/
theorem focal_pm_cancellation_iff_L_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1)
    (hsign : ∀ n : ℕ, χ (n : ZMod q) = 1 ∨ χ (n : ZMod q) = -1 ∨ χ (n : ZMod q) = 0) (Z : ℝ) :
    Tendsto (fun N : ℕ => Focal.Pchan χ N (Real.log Z) - Focal.Mchan χ N (Real.log Z)) atTop (nhds 0)
      ↔ Geometric.Phi χ Z = 0 :=
  Focal.channel_closure_iff_L_zero χ hχ hsign Z

end CriticalLinePhasor.Readout