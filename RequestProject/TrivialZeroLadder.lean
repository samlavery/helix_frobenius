import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic

/-!
# The ladder of ends: every archimedean denominator is an FE factor at a trivial zero

Measured and recorded at RH_LEDGER 755 (2026-09-13), verified numerically to `1.5e-14`; this file
puts the algebra in the machine-checked layer.

Weil's form on the pole complement carries the weight `r^2 + 1/4`, which on the critical line is
`s * (1 - s)` — the factor completing `ζ` to `ξ`, i.e. the carrier's two ends in their own
polynomial (ledger 736).  That is *not* special to the pole.  The Lemma-C series for the
archimedean symbol `d(r) = Re ψ(1/4 + i r / 2) - log π` has denominators `r^2 + α_m^2` with
`α_m = 2 m + 1/2`, and `α_m` is the parameter of the `m`-th trivial zero.  In the spectral variable
`r = (s - 1/2)/I`:

* `trivialZeroFactor` : `((s - 1/2)/I)^2 + (2*m + 1/2)^2 = (s + 2*m) * (1 - s + 2*m)`,
  **the functional-equation-symmetric factor at `s = -2m` and its partner `s = 2m+1`**;
* `poleFactor` : the `m = 0` case is `s * (1 - s)`.

So the carrier's ends are a ladder, one per trivial zero, and the pole is only its first rung.
Consequence recorded at 755: absorbing the first `M` of these factors turns those terms of the
archimedean series into a local differential operator whose leading coefficient is
`-K + Σ_{m<M} 2/α_m` with `K = log π - ψ(1/4)`; since `Σ 2/(2m+1/2)` diverges that coefficient turns
positive, at `M = 4`, and the region where the local part is negative then contracts.
-/

namespace CriticalLinePhasor.TrivialZeroLadder

open Complex

/-- The spectral variable: `r = (s - 1/2)/I`, so that `s = 1/2 + I*r`. -/
noncomputable def spec (s : ℂ) : ℂ := (s - 1 / 2) / I

theorem spec_sq (s : ℂ) : (spec s) ^ 2 = -(s - 1 / 2) ^ 2 := by
  unfold spec
  field_simp [Complex.I_ne_zero]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- **The ladder of ends.**  The `m`-th archimedean denominator is the functional-equation-symmetric
factor at the `m`-th trivial zero: its roots are `s = -2m` and its partner `s = 2m+1`. -/
theorem trivialZeroFactor (s : ℂ) (m : ℕ) :
    (spec s) ^ 2 + (2 * (m : ℂ) + 1 / 2) ^ 2 = (s + 2 * m) * (1 - s + 2 * m) := by
  rw [spec_sq]; ring

/-- The `m = 0` rung is the pole weight `s(1-s)`: the factor that completes `ζ` to `ξ`. -/
theorem poleFactor (s : ℂ) : (spec s) ^ 2 + (1 / 2) ^ 2 = s * (1 - s) := by
  have := trivialZeroFactor s 0
  simpa using this

/-- On the critical line the weight is real and nonnegative: `r^2 + 1/4` with `r` real. -/
theorem poleFactor_ofReal (r : ℝ) :
    ((1 / 2 : ℂ) + I * r) * (1 - ((1 / 2 : ℂ) + I * r)) = ((r ^ 2 + 1 / 4 : ℝ) : ℂ) := by
  have h : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  push_cast
  linear_combination (-((r : ℂ) ^ 2)) * h

/-- Each rung's roots are exactly the `m`-th trivial zero and its functional-equation partner. -/
theorem trivialZeroFactor_eq_zero_iff (s : ℂ) (m : ℕ) :
    (spec s) ^ 2 + (2 * (m : ℂ) + 1 / 2) ^ 2 = 0 ↔ s = -(2 * m) ∨ s = 1 + 2 * m := by
  rw [trivialZeroFactor, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left; linear_combination h
    · right; linear_combination -h
  · rintro (h | h)
    · left; rw [h]; ring
    · right; rw [h]; ring

end CriticalLinePhasor.TrivialZeroLadder

#print axioms CriticalLinePhasor.TrivialZeroLadder.spec_sq
#print axioms CriticalLinePhasor.TrivialZeroLadder.trivialZeroFactor
#print axioms CriticalLinePhasor.TrivialZeroLadder.poleFactor
#print axioms CriticalLinePhasor.TrivialZeroLadder.poleFactor_ofReal
#print axioms CriticalLinePhasor.TrivialZeroLadder.trivialZeroFactor_eq_zero_iff
