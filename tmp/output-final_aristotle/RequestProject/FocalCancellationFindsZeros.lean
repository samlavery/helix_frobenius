import Mathlib
import RequestProject.HarmonicPencilCell
import RequestProject.FocalEigenheight
import RequestProject.FocalResidualVanishes

/-!
# Focal cancellation finds on-line zeros at height `e^y`, replacing infinite 1-D phasors

This file proves, **unconditionally** (no GRH/RH) and at Lean/Mathlib **v4.31.0**, the requested
statement:

> For a zero **on the critical line** `Lχ(1/2 + i y) = 0`, the 3-D spectral fiber model *finds*
> its vanishing **by focal cancellation**, and it does so at the **source/geometric height
> `Z = e^y`** (the *exponential* of `y`, not `y` itself).  The focal cancellation is an **exact**
> algebraic event (no limit): it works as a **substitute for the infinite-phasor 1-D mathematics**,
> replacing the infinite partial-sum closure of the 1-D L-function by an **exact cancellation**
> built from **finite phasors** and **cell scaling**.

## The two heights (`e^y` vs `y`)

The 3-D fiber lives in the *geometric source height* `Z > 0`; the 1-D analytic readout height is
`y = log Z`.  A critical-line zero presented at analytic ordinate `y` is therefore *found* by the
fiber at the geometric height `Z = e^y`.  These are genuinely different: `Real.exp y ≠ y` for every
real `y` (`exp_height_ne_analytic_height`).  At `Z = e^y` the readout lands back exactly on the line
at ordinate `y`: `reprPoint χ (e^y) = 1/2 + i y` (`reprPoint_exp`).

## Exact cancellation vs. the infinite 1-D phasor sum

In the 1-D picture, detecting a zero is an **infinite** process: `Φχ(Z) = Lχ(1/2 + i log Z)`
vanishes **iff the infinite phasor partial sums close** (tend to `0`) — this is
`GeometricPhasorClosure.Phi_zero_iff_closure`, packaged here as `InfinitePhasorCloses`.

In the 3-D cell fiber the same zero is detected by an **exact algebraic cancellation**: the
normalized cell focal residual factors as `Dᶜχ(Z) = Vχ(Z)·Uχ(Z)·Lχ(1/2 + i log Z)` with the two
units `Vχ(Z) ≠ 0` (focal-residual unit) and `Uχ(Z) = π/3 ≠ 0` (the **cell scaling**), so it vanishes
**exactly** when the L-value does — no limit is taken (`focal_residual_eq_cell_scaled_L`).

The bridge between the two is `focal_cancellation_iff_infinite_phasor_closure`:

```
Dᶜχ(Z) = 0   ↔   the infinite 1-D phasor partial sums close.
```

i.e. the exact finite-algebra cancellation is a **faithful substitute** for the infinite 1-D phasor
computation — it fires on exactly the same heights.

## Finite phasors and cell scaling

The **finite** phasors are the truncated signed channel difference `P_N − M_N`
(`Focal.Pchan − Focal.Mchan`, finite sums over `Finset.Icc 1 N`); cell scaling enters as the exact
six-cell amplitude `π/3` and the exact six-cell carrier closure `cell (n+6) = cell n`
(`Geometric.cell_six_periodic`):

* `finite_phasor_channel_cell_scaled` — `P_N − M_N = (π/3)·Σ_{n=1}^N readoutTerm` (the finite phasor
  sum scaled by the cell amplitude `π/3`);
* `finite_phasor_channel_abel_limit` — its Abel limit is exactly the signed cell mode
  `Bᶜχ(Z) = Φχ(Z) = scalarClosure χ Z`.

## The capstone

`focal_cancellation_finds_online_zero` assembles everything: from `Lχ(1/2 + i y) = 0`, at the
source height `Z = e^y` the focal cancellation is exact (`Dᶜχ = Kᶜχ = Φχ = 0`, cell admissible
`Aᶜχ ≠ 0`), the height is genuinely `e^y ≠ y` with readout `1/2 + i y`, the cancellation is the
exact cell-scaled multiple of the L-value, and it coincides with the infinite-phasor closure — so
the 3-D fiber really does find the zero by exact focal cancellation, as a substitute for the
infinite 1-D phasor mathematics.

Everything is `Mathlib`-only and `sorry`/`axiom`-free; honest scope is unchanged from the rest of
the project (a *real* source height reads out on the critical line, so this concerns on-line zeros,
and is not RH/GRH).
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace CriticalLinePhasor.HarmonicCell

open CriticalLinePhasor CriticalLinePhasor.Geometric CriticalLinePhasor.Focal

variable {q : ℕ} [NeZero q]

/-! ## 1. The two heights: `e^y` (geometric source) vs `y` (analytic readout) -/

/-- **The cancellation height is the exponential of the ordinate, never the ordinate itself.**
For every real `y`, the geometric source height `e^y` differs from the analytic readout height `y`
(`exp y > y` always). -/
theorem exp_height_ne_analytic_height (y : ℝ) : Real.exp y ≠ y := by
  have h : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  intro he; rw [he] at h; linarith

omit [NeZero q] in
/-- **The source height `e^y` reads back to the line at ordinate `y`.**  The represented point of the
geometric height `Z = e^y` is exactly `1/2 + i y`: the cancellation happens at `e^y`, while its
1-D readout is `y`. -/
theorem reprPoint_exp (χ : DirichletCharacter ℂ q) (y : ℝ) :
    reprPoint χ (Real.exp y) = (1 / 2 : ℂ) + (y : ℂ) * I := by
  rw [reprPoint, tauChi, Real.log_exp]

/-! ## 2. The cell scaling and the exact (no-limit) factorization -/

/-- **Scalar closure vanishes iff the L-carrier vanishes** (the cell scaling unit `Uχ = π/3` is
never zero). -/
theorem scalarClosure_zero_iff_Phi_zero (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    scalarClosure χ Z = 0 ↔ Phi χ Z = 0 := by
  rw [scalarClosure, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (Ucell_ne_zero χ Z)
    · exact h
  · intro h; exact Or.inr h

/-- **The focal cancellation is an exact cell-scaled multiple of the L-value.**  The normalized cell
focal residual factors as `Dᶜχ(Z) = Vχ(Z)·Uχ(Z)·Lχ(1/2 + i log Z)` with **both** units nonzero:
the focal-residual unit `Vχ(Z) ≠ 0` and the **cell scaling** `Uχ(Z) = π/3 ≠ 0`.  This is an exact
algebraic identity — **no limit is taken** — so the residual vanishes *exactly* when the L-value
does. -/
theorem focal_residual_eq_cell_scaled_L (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    Dcell χ Z = Vcell χ Z * Ucell χ Z * DirichletCharacter.LFunction χ (reprPoint χ Z)
      ∧ Vcell χ Z ≠ 0 ∧ Ucell χ Z ≠ 0 := by
  obtain ⟨hfac, hV⟩ := normalized_cell_focal_residual_exact χ Z
  refine ⟨?_, hV, Ucell_ne_zero χ Z⟩
  rw [hfac, scalarClosure, LFunction_reprPoint, mul_assoc]

/-! ## 3. The substitute: exact cancellation ⇔ infinite 1-D phasor closure -/

/-- **The infinite 1-D phasor closure event.**  The 1-D analytic L-function is the Abel limit of
the infinite phasor partial sums `Σ_{n<N} χ(n)·n^{-(1/2 + i log Z)}`; this predicate records that
these **infinite** partial sums close (tend to `0`) — the 1-D way to detect a zero. -/
def InfinitePhasorCloses (χ : DirichletCharacter ℂ q) (Z : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      χ (n : ZMod q) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (Real.log Z : ℂ) * I)))
    atTop (nhds 0)

/-- **Exact focal cancellation is a faithful substitute for the infinite 1-D phasor sum.**  For
every source height `Z`, the *exact* (finite-algebra, cell-scaled) focal cancellation `Dᶜχ(Z) = 0`
holds **iff** the *infinite* 1-D phasor partial sums close.  The 3-D exact cancellation fires on
exactly the heights where the 1-D infinite computation does. -/
theorem focal_cancellation_iff_infinite_phasor_closure (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (Z : ℝ) :
    Dcell χ Z = 0 ↔ InfinitePhasorCloses χ Z := by
  rw [focal_residual_zero_iff_scalar_zero, scalarClosure_zero_iff_Phi_zero]
  exact Phi_zero_iff_closure χ hχ Z

/-! ## 4. Finite phasors and cell scaling -/

/-- **The finite phasor channel difference is the cell-scaled finite phasor sum.**  The truncated
signed channel difference `P_N − M_N` (finite sums over `Finset.Icc 1 N`) equals the **finite**
phasor sum scaled by the exact six-cell amplitude `π/3`. -/
theorem finite_phasor_channel_cell_scaled (χ : DirichletCharacter ℂ q) (N : ℕ) (Z : ℝ)
    (hsign : ∀ n : ℕ, χ (n : ZMod q) = 1 ∨ χ (n : ZMod q) = -1 ∨ χ (n : ZMod q) = 0) :
    Pchan χ N (Real.log Z) - Mchan χ N (Real.log Z)
      = Ucell χ Z * ∑ n ∈ Finset.Icc 1 N, readoutTerm χ Z n := by
  rw [Ucell]
  exact channel_diff χ N Z hsign

/-- **The Abel limit of the finite phasor channel difference is the signed cell mode.**  Letting the
truncation `N → ∞`, the finite phasor channel difference `P_N − M_N` tends exactly to the signed
harmonic cell mode `Bᶜχ(Z) = Φχ(Z) = scalarClosure χ Z`.  The finite phasors with cell scaling
reproduce, in the limit, the analytic closure — but the cancellation itself is read off the *exact*
cell factorization above. -/
theorem finite_phasor_channel_abel_limit (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hsign : ∀ n : ℕ, χ (n : ZMod q) = 1 ∨ χ (n : ZMod q) = -1 ∨ χ (n : ZMod q) = 0) (Z : ℝ) :
    Tendsto (fun N : ℕ => Pchan χ N (Real.log Z) - Mchan χ N (Real.log Z)) atTop
      (nhds (Bchan χ Z)) := by
  have h := channel_diff_tendsto χ hχ hsign Z
  have he : ((Real.pi / 3 : ℝ) : ℂ) * Phi χ Z = Bchan χ Z := by
    rw [Bchan, scalarClosure, Ucell]
  rwa [he] at h

/-! ## 5. The capstone: the fiber finds on-line zeros by exact focal cancellation at `e^y` -/

/--
**The 3-D spectral fiber finds an on-line zero by exact focal cancellation at height `e^y`
(the requested statement, unconditional).**

Let `Lχ(1/2 + i y) = 0` be a zero **on the critical line**.  Then at the **source/geometric height
`Z = e^y`** (the exponential of `y`, genuinely different from `y`):

1. **Height `e^y`, readout `y`.**  `e^y ≠ y`, `log(e^y) = y`, and the represented point reads back
   to the line at ordinate `y`: `reprPoint χ (e^y) = 1/2 + i y`.
2. **Exact focal cancellation.**  The scalar closure, the focal kernel and the normalized cell
   focal residual are **all exactly zero** (`Φχ = Kᶜχ = Dᶜχ = 0`), with the cell admissible
   (`Aᶜχ ≠ 0`).
3. **Exact, cell-scaled, no limit.**  The residual is the exact cell-scaled multiple
   `Dᶜχ = Vχ·Uχ·Lχ(1/2 + i y)` with the focal-residual unit `Vχ ≠ 0` and the cell scaling
   `Uχ = π/3 ≠ 0`.
4. **Substitute for the infinite 1-D phasors.**  This exact cancellation event coincides with the
   infinite 1-D phasor closure: `Dᶜχ(e^y) = 0 ↔ InfinitePhasorCloses χ (e^y)`, and the closure
   indeed holds.

So the fiber detects the on-line zero by an exact finite/cell-scaled cancellation at `e^y`, in
place of the infinite-phasor 1-D mathematics.  Honest scope: a real source height reads out on the
critical line, so this concerns on-line zeros (not RH/GRH).
-/
theorem focal_cancellation_finds_online_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (y : ℝ)
    (hzero : DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (y : ℂ) * I) = 0) :
    -- (1) the height is `e^y`, never `y`, and reads back to the line at ordinate `y`
    (Real.exp y ≠ y ∧ Real.log (Real.exp y) = y
        ∧ reprPoint χ (Real.exp y) = (1 / 2 : ℂ) + (y : ℂ) * I)
    -- (2) exact focal cancellation at the source height `e^y`
    ∧ (scalarClosure χ (Real.exp y) = 0 ∧ Kcell χ (Real.exp y) = 0
        ∧ Dcell χ (Real.exp y) = 0 ∧ Achan χ (Real.exp y) ≠ 0)
    -- (3) exact cell-scaled factorization (no limit), with both units nonzero
    ∧ (Dcell χ (Real.exp y)
          = Vcell χ (Real.exp y) * Ucell χ (Real.exp y)
              * DirichletCharacter.LFunction χ (reprPoint χ (Real.exp y))
        ∧ Vcell χ (Real.exp y) ≠ 0 ∧ Ucell χ (Real.exp y) ≠ 0)
    -- (4) it substitutes for the infinite 1-D phasor closure, which holds here
    ∧ ((Dcell χ (Real.exp y) = 0 ↔ InfinitePhasorCloses χ (Real.exp y))
        ∧ InfinitePhasorCloses χ (Real.exp y)) := by
  obtain ⟨hsc, hK, hD, hA⟩ := focal_residual_vanishes_at_represented_zero χ y hzero
  refine ⟨⟨exp_height_ne_analytic_height y, Real.log_exp y, reprPoint_exp χ y⟩,
    ⟨hsc, hK, hD, hA⟩, focal_residual_eq_cell_scaled_L χ (Real.exp y), ?_, ?_⟩
  · exact focal_cancellation_iff_infinite_phasor_closure χ hχ (Real.exp y)
  · exact (focal_cancellation_iff_infinite_phasor_closure χ hχ (Real.exp y)).mp hD

end CriticalLinePhasor.HarmonicCell
