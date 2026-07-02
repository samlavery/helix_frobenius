import Mathlib
import RequestProject.HarmonicPencilCell

/-!
# At a represented zero the focal residual is exactly zero

This file proves, **unconditionally** (no GRH/RH), the requested statement in the expanded
harmonic/spectral state space:

> At a **represented zero** of the configured L-function, the **focal residual is exactly zero** —
> no leftover scalar residue remains in the normalized cell channel.

The normalized cell focal residual is `Dᶜχ(Z)` (`HarmonicCell.Dcell`), the residual carried by the
normalized cell channel of the harmonic pencil.  The structural factorization
`normalized_cell_focal_residual_exact` records that

```
Dᶜχ(Z) = Vχ(Z) · Φχ(Z),    Vχ(Z) ≠ 0
```

i.e. the residual is a *nonzero* multiple of the scalar closure `Φχ(Z) = scalarClosure χ Z`.
Because the unit `Vχ(Z)` never vanishes, the residual carries **exactly** the scalar closure's
zero set: it vanishes iff the scalar closure vanishes (`focal_residual_zero_iff_scalar_zero`).

A **represented zero** is a critical-line zero `Lχ(1/2 + i t) = 0` realized by the admissible real
source height `Z = exp t` (the data packaged by `HarmonicCell.IsRepresentingEigenheight`).  At such
a point the scalar closure vanishes, so the focal residual is exactly `0`: there is **no leftover
scalar residue** in the normalized cell channel.

* `focal_residual_zero_iff_scalar_zero` — `Dᶜχ(Z) = 0 ↔ Φχ(Z) = 0` (the residual is governed
  solely by the scalar closure; the focal-residual unit `Vχ(Z)` is never to blame).
* `focal_residual_zero_of_representing` — at any representing eigenheight, `Dᶜχ(Z) = 0`.
* `focal_residual_vanishes_at_represented_zero` — the headline form: from a critical-line zero
  `Lχ(1/2 + i t) = 0`, at the represented height `Z = exp t` the focal residual, the focal kernel,
  and the scalar closure are **all exactly zero**.

Everything is `Mathlib`-only and `sorry`/`axiom`-free, and inherits the project's honest scope:
"represented" means realized by a real source height, whose readout always lands on the critical
line — no claim is made about off-line zeros (not RH/GRH).
-/

open Complex
open scoped BigOperators Real

namespace CriticalLinePhasor.HarmonicCell

open CriticalLinePhasor CriticalLinePhasor.Geometric

variable {q : ℕ} [NeZero q]

/-- **The focal residual is governed solely by the scalar closure.**  Because the focal-residual
unit `Vχ(Z)` is never zero and `Dᶜχ(Z) = Vχ(Z)·Φχ(Z)`, the normalized cell focal residual vanishes
iff the scalar closure vanishes. -/
theorem focal_residual_zero_iff_scalar_zero (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    Dcell χ Z = 0 ↔ scalarClosure χ Z = 0 := by
  obtain ⟨hfac, hV⟩ := normalized_cell_focal_residual_exact χ Z
  rw [hfac, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hV
    · exact h
  · intro h; exact Or.inr h

/-- **The focal residual vanishes iff the represented L-value vanishes.**  Combining with the cell
factorization, the normalized cell focal residual vanishes exactly when the configured L-function
vanishes at the represented point. -/
theorem focal_residual_zero_iff_L_zero (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    Dcell χ Z = 0 ↔ DirichletCharacter.LFunction χ (reprPoint χ Z) = 0 := by
  rw [focal_residual_zero_iff_scalar_zero, scalar_zero_iff_L_zero]

/-- **At a representing eigenheight the focal residual is exactly zero.**  If `Z` represents the
critical-line point `1/2 + i t` (a `HarmonicCell.IsRepresentingEigenheight`), then the scalar
closure vanishes there, hence the normalized cell focal residual is exactly `0`: no leftover scalar
residue remains. -/
theorem focal_residual_zero_of_representing (χ : DirichletCharacter ℂ q) (t Z : ℝ) (μ lam : ℂ)
    (h : IsRepresentingEigenheight χ t Z μ lam) :
    Dcell χ Z = 0 :=
  (focal_residual_zero_iff_scalar_zero χ Z).mpr h.2.2.2.2.1

/--
**At a represented zero, the focal residual is exactly zero (the requested statement).**

If `Lχ(1/2 + i t) = 0` is a critical-line zero of the configured L-function, then at the represented
real source height `Z = exp t` (where `Aᶜχ(Z) ≠ 0`, so the cell is admissible):

* the **scalar closure** vanishes, `Φχ(Z) = 0`;
* the **focal kernel** vanishes, `Kᶜχ(Z) = 0`;
* the **normalized cell focal residual** is exactly zero, `Dᶜχ(Z) = 0`.

So at a represented zero **no leftover scalar residue remains in the normalized cell channel.**
Unconditional (no GRH/RH).
-/
theorem focal_residual_vanishes_at_represented_zero (χ : DirichletCharacter ℂ q) (t : ℝ)
    (hzero : DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t : ℂ) * I) = 0) :
    scalarClosure χ (Real.exp t) = 0
      ∧ Kcell χ (Real.exp t) = 0
      ∧ Dcell χ (Real.exp t) = 0
      ∧ Achan χ (Real.exp t) ≠ 0 := by
  have hlog : Real.log (Real.exp t) = t := Real.log_exp t
  have hLrepr : DirichletCharacter.LFunction χ (reprPoint χ (Real.exp t)) = 0 := by
    rw [LFunction_reprPoint, Phi_eq_L, hlog]; exact hzero
  have hsc : scalarClosure χ (Real.exp t) = 0 := (scalar_zero_iff_L_zero χ _).mpr hLrepr
  exact ⟨hsc, (focal_zero_iff_scalar_zero χ _).mpr hsc,
    (focal_residual_zero_iff_scalar_zero χ _).mpr hsc, Achan_ne_zero χ _⟩

end CriticalLinePhasor.HarmonicCell
