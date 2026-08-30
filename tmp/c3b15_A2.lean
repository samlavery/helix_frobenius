import c3b15_A1

/-!
# C3 batch 15, block A2 — the assembled **checkable sufficient inequality**, and the exact
# reason a uniform window `a = a(x)` cannot exist for this instrument

Combining `window_lower_tail` with `central_ge_quadratic` and eliminating the window mass by
`window_mass` gives a criterion in which **every quantity is an explicit integral of the
nonnegative kernel `R`** — no reference to the target, no reference to `Ξ`, no zero locations:

  `2x²·Q(a) + 4·T(a) ≤ cosMom R 0   ⟹   0 ≤ cosMom R (2x)`,

with `Q(a) := ∫_{(-a,a)} v²R(v)dv` (window second moment) and `T(a) := ∫_{(a,∞)} R(v)dv`
(tail mass).  `cosMom R 0` is the total mass, `= L₁(0)`.  Measured
(`tmp/c3b15_num1_out.txt` §X0, `tmp/c3b15_num2_out.txt` §J): optimising `a` for each `x`, the
criterion is satisfiable exactly for **|x| ≤ 6.6387** (quadratic bound; `6.8051` with the
degree-6 Taylor bound), against batch 13's best conditional reach of `2.503` and batch 12's
single point `x = 0`.

## The per-`a` cap — and what it does NOT prove

> **CORRECTED (OpenAI adjudication, 2026-08-25).**  This header previously read "Why no
> uniform `a(x)` exists — and this is proved, not asserted".  **Withdrawn.**  The two
> theorems below are `∀a ∃cap`, not `∃cap ∀a`; an adaptive `a(x)` with a cap growing in `x`
> is **not** excluded by them.  The global exclusion additionally requires `Tail` antitone,
> `Qwin` monotone on `a ≥ 0`, and a **uniform positive lower bound** for `Qwin` over
> `{a : 4·Tail a ≤ cosMom Rker 0}` — none of which is compiled in this file.  The sentence
> below beginning "Since `Q` is nondecreasing…" is **informal reasoning, not a proof**: the
> monotonicity it invokes is not formalised here.  Batch 16 supplies it.

The two compiled necessary conditions below pin the trade-off **at fixed `a`**.

* `criterion_needs_small_tail`: the criterion forces `4T(a) ≤ cosMom R 0`, i.e. **the tail
  must carry at most a quarter of the mass** — a constraint on `a` alone, independent of `x`.
  So `a` cannot be taken small.
* `criterion_forces_x_bound`: the criterion forces `2x²Q(a) ≤ cosMom R 0`, i.e.
  `x² ≤ cosMom R 0 / (2Q(a))` whenever `Q(a) > 0` — so for each fixed admissible `a` the
  criterion has a **finite `x`-cap**.

Since `Q` is nondecreasing in `a` and `T` is nonincreasing, the first condition bounds `a`
from below and the second then bounds `x` from above.  **The cap is a property of the
polynomial-central-bound instrument, not of the target**: the true `∫_{(-a,a)}R cos(2xv)dv`
decays like `e^{−πx/2}`, and no polynomial lower bound for `cos` can track exponential decay.
The cheapest experiment that would refute the cap is a *non-polynomial* central minorant with
a computable moment — none is attempted here.

SCOPE: one sufficient criterion and two necessary conditions on it.  Nothing here decides the
target, and nothing here assumes it.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B15

open C3B10
open C3B14

/-- The window second moment, `Q(a) = ∫_{(-a,a)} v²R(v)dv`. -/
def Qwin (a : ℝ) : ℝ := ∫ v in Ioo (-a) a, v ^ 2 * Rker v

/-- The tail mass, `T(a) = ∫_{(a,∞)} R(v)dv`. -/
def Tail (a : ℝ) : ℝ := ∫ v in Ioi a, Rker v

theorem Qwin_nonneg (a : ℝ) : 0 ≤ Qwin a := by
  refine integral_nonneg_of_ae ?_
  filter_upwards with v
  have := Rker_nonneg v
  positivity

theorem Tail_nonneg (a : ℝ) : 0 ≤ Tail a := by
  refine integral_nonneg_of_ae ?_
  filter_upwards with v
  exact Rker_nonneg v

/-! ### THE CHECKABLE SUFFICIENT INEQUALITY -/

/-- **THE CRITERION.**  Every quantity is an explicit integral of the nonnegative kernel `R`.
The target's sign is never mentioned in the hypothesis. -/
theorem window_criterion_quadratic {a x : ℝ} (ha : 0 ≤ a)
    (h : 2 * x ^ 2 * Qwin a + 4 * Tail a ≤ cosMom Rker 0) :
    0 ≤ cosMom Rker (2 * x) := by
  have hw := window_lower_tail a x ha
  have hc := central_ge_quadratic a x
  have hm := window_mass a ha
  have hchain : (∫ v in Ioo (-a) a, Rker v) - 2 * x ^ 2 * Qwin a - 2 * Tail a
      ≤ cosMom Rker (2 * x) := by
    unfold Qwin Tail at *
    linarith [hw, hc]
  rw [hm] at hchain
  unfold Tail at *
  linarith [hchain, h]

/-- The same with the sharper piecewise-linear central bound, on its domain of validity
`2|x|a ≤ π/2`.  `Awin a := ∫_{(-a,a)}|v|R(v)dv` is the window first absolute moment. -/
def Awin (a : ℝ) : ℝ := ∫ v in Ioo (-a) a, |v| * Rker v

theorem Awin_nonneg (a : ℝ) : 0 ≤ Awin a := by
  refine integral_nonneg_of_ae ?_
  filter_upwards with v
  have := Rker_nonneg v
  positivity

theorem window_criterion_linear {a x : ℝ} (ha : 0 ≤ a) (hax : 2 * |x| * a ≤ Real.pi / 2)
    (h : (4 * |x| / Real.pi) * Awin a + 4 * Tail a ≤ cosMom Rker 0) :
    0 ≤ cosMom Rker (2 * x) := by
  have hw := window_lower_tail a x ha
  have hc := central_ge_linear a x ha hax
  have hm := window_mass a ha
  have hchain : (∫ v in Ioo (-a) a, Rker v) - (4 * |x| / Real.pi) * Awin a - 2 * Tail a
      ≤ cosMom Rker (2 * x) := by
    unfold Awin Tail at *
    linarith [hw, hc]
  rw [hm] at hchain
  unfold Tail at *
  linarith [hchain, h]

/-! ### THE TWO NECESSARY CONDITIONS THAT PIN THE TRADE-OFF -/

/-- **The tail must carry at most a quarter of the mass.**  A constraint on `a` alone: the
window cannot be taken small.  (`x` does not appear.) -/
theorem criterion_needs_small_tail {a x : ℝ}
    (h : 2 * x ^ 2 * Qwin a + 4 * Tail a ≤ cosMom Rker 0) :
    4 * Tail a ≤ cosMom Rker 0 := by
  have h1 : 0 ≤ 2 * x ^ 2 * Qwin a := by
    have := Qwin_nonneg a
    positivity
  linarith [h, h1]

/-- **And then `x` is capped.**  For each admissible `a` with `Q(a) > 0` the criterion forces
`x² ≤ cosMom R 0 / (2 Q(a))`; beyond that no `x` satisfies it, whatever the tail does. -/
theorem criterion_forces_x_bound {a x : ℝ} (hQ : 0 < Qwin a)
    (h : 2 * x ^ 2 * Qwin a + 4 * Tail a ≤ cosMom Rker 0) :
    x ^ 2 ≤ cosMom Rker 0 / (2 * Qwin a) := by
  have hT : 0 ≤ 4 * Tail a := by
    have := Tail_nonneg a
    linarith
  have h2 : 2 * x ^ 2 * Qwin a ≤ cosMom Rker 0 := by linarith [h, hT]
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * Qwin a)]
  linarith [h2]

/-- The contrapositive: the criterion fails past its cap, **at fixed `a`**.

> **SCOPE, CORRECTED (OpenAI adjudication, 2026-08-25).**  An earlier version of this
> docstring called this "the compiled form of *no uniform window `a(x)` exists*".  **That is
> withdrawn.**  This and `criterion_forces_x_bound` are `∀a ∃cap` statements: for each
> **fixed** `a` with `Qwin a > 0` there is a cap.  They do **not** exclude an adaptive `a(x)`
> whose cap grows without bound.  The global exclusion additionally needs `Tail` antitone,
> `Qwin` monotone on `a ≥ 0`, and a **uniform positive lower bound** for `Qwin` over
> `{a : 4·Tail a ≤ cosMom Rker 0}`.  See batch 16. -/
theorem criterion_fails_past_cap {a x : ℝ} (hQ : 0 < Qwin a)
    (hx : cosMom Rker 0 / (2 * Qwin a) < x ^ 2) :
    ¬ (2 * x ^ 2 * Qwin a + 4 * Tail a ≤ cosMom Rker 0) := by
  intro h
  exact absurd (criterion_forces_x_bound hQ h) (not_le.mpr hx)

/-! ### The `x = 0` instance, as a sanity anchor -/

/-- At `x = 0` the criterion reduces to `4T(a) ≤ cosMom R 0` and therefore fires for every
`a` whose tail is at most a quarter of the mass — recovering `C3B14.cosMom_Rker_zero_nonneg`
through the criterion rather than around it. -/
theorem window_criterion_at_zero {a : ℝ} (ha : 0 ≤ a)
    (h : 4 * Tail a ≤ cosMom Rker 0) :
    0 ≤ cosMom Rker (2 * 0) := by
  refine window_criterion_quadratic ha ?_
  have hQ := Qwin_nonneg a
  nlinarith [h, hQ]

end C3B15

section AxiomAudit
#print axioms C3B15.Qwin_nonneg
#print axioms C3B15.Tail_nonneg
#print axioms C3B15.Awin_nonneg
#print axioms C3B15.window_criterion_quadratic
#print axioms C3B15.window_criterion_linear
#print axioms C3B15.criterion_needs_small_tail
#print axioms C3B15.criterion_forces_x_bound
#print axioms C3B15.criterion_fails_past_cap
#print axioms C3B15.window_criterion_at_zero
end AxiomAudit
