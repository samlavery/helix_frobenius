import c3b13_A3

/-!
# C3 batch 13, block A4 — the large-readout **criterion**

Block A1 gives a criterion keyed to a *small* readout `c₀ = Ξ(x)`.  This block gives one
keyed to a *large* readout.

> **SCOPE, CORRECTED (OpenAI adjudication, 2026-08-25).**  Both are **conditional
> criteria**: compiled implications whose hypotheses are real inequalities that are **not
> proved to hold at any `x`** anywhere in this repository.  An earlier version of this
> header called them "complementary" and "the exact complement".  **That is withdrawn.**
> The two hypotheses are **oppositely directed** but are **not logical complements** and do
> **not partition the line** — there is a wide middle band satisfying neither, measured at
> **95.59%** of a uniform grid on `[0,60]`.  `momentTwo_nonneg_of_either` below is a
> **disjunction**, not a dichotomy.

The mechanism is a **positive double-integral split with a movable centre**.  For any `a`,

  `u² = (u² − a²) + a²`,

so, integrating the cell density against each piece over the carrier half-line,

  `∫u²C(x,u)du = ∫(u²−a²)C(x,u)du + a²∫C(x,u)du`.

The second term is *already a square*: batch 12's `cellDensity_Ioi_eq_sq` evaluates it as
`¼·cosMom Φ x ²`.  The first term is bounded below using A2's domination
`|C(x,u)| ≤ C(0,u)`, which converts an unknown signed integral into a **fixed constant**

  `Jbar a := ∫_{(0,∞)} |u² − a²| · C(0,u) du`,

independent of `x`.  Hence, unconditionally and for every `a`,

  `a²·¼·cosMom Φ x ² − Jbar a ≤ ∫_{(0,∞)} u²C(x,u)du`.

So the target holds wherever the readout is large enough: `Jbar a ≤ a²·¼·Ξ(x)²`.

**The hypothesis is satisfiable (numerically — not proved here).**
`Jbar a = a²(2m₀(a) − M₀) − (2m₂(a) − M)` with
`m₀,m₂` the partial masses of `C(0,·)`; the first bracket is `≤ 0` and the second becomes
positive once `m₂(a) > M/2`, so for such `a` the criterion fires at `x = 0` outright — and
`x = 0` is exactly where §B18 of the numerics locates the *tightest* point of the target.
Measured coverage is reported in `tmp/c3b13_num4_out.txt`.

SCOPE: one split, one lower bound, one conditional criterion.  No zero location, no
arithmetic input, and **no assertion that the criterion's hypothesis holds anywhere.**
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B13

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open C3B6.Theta
open C3B10
open C3B11
open C3B12

/-- The cell density at clock `0`, as an integrable function. -/
theorem cellDensity_zero_integrable : Integrable (cellDensity 0) := by
  have h := cellDensity_exp_integrable 0 0
  refine h.congr ?_
  filter_upwards with u
  rw [show (2 : ℝ) * 0 * u = 0 by ring, Real.exp_zero, one_mul]

theorem cellDensity_zero_aesm : AEStronglyMeasurable (cellDensity 0) volume :=
  cellDensity_zero_integrable.aestronglyMeasurable

/-- The `x`-independent constant of the split. -/
def Jbar (a : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), |u ^ 2 - a ^ 2| * cellDensity 0 u

theorem Jbar_integrableOn (a : ℝ) :
    IntegrableOn (fun u : ℝ => |u ^ 2 - a ^ 2| * cellDensity 0 u) (Ioi (0 : ℝ)) := by
  have hmaj : Integrable (fun u : ℝ => u ^ 2 * cellDensity 0 u + a ^ 2 * cellDensity 0 u) :=
    (u2_cellDensity_integrable 0).add (cellDensity_zero_integrable.const_mul _)
  have hmeas : AEStronglyMeasurable (fun u : ℝ => |u ^ 2 - a ^ 2| * cellDensity 0 u) volume :=
    (((continuous_id.pow 2).sub continuous_const).abs).aestronglyMeasurable.mul
      cellDensity_zero_aesm
  refine (Integrable.mono hmaj hmeas ?_).integrableOn
  filter_upwards [cellDensity_zero_nonneg] with u hu
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hu,
    abs_of_nonneg (by nlinarith [sq_nonneg u, sq_nonneg a, hu] :
      (0 : ℝ) ≤ u ^ 2 * cellDensity 0 u + a ^ 2 * cellDensity 0 u)]
  have habs : |u ^ 2 - a ^ 2| ≤ u ^ 2 + a ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg u, sq_nonneg a]
  nlinarith [habs, hu]

theorem Jbar_nonneg (a : ℝ) : 0 ≤ Jbar a := by
  unfold Jbar
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_of_ae (μ := volume) (s := Ioi (0 : ℝ)) cellDensity_zero_nonneg]
    with u hu
  exact mul_nonneg (abs_nonneg _) hu

/-! ### The split -/

theorem shifted_moment_split (a x : ℝ) :
    (∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u)
      = (∫ u in Ioi (0 : ℝ), (u ^ 2 - a ^ 2) * cellDensity x u)
        + a ^ 2 * ∫ u in Ioi (0 : ℝ), cellDensity x u := by
  have hI2 : IntegrableOn (fun u : ℝ => u ^ 2 * cellDensity x u) (Ioi (0 : ℝ)) :=
    (u2_cellDensity_integrable x).integrableOn
  have hI0 : IntegrableOn (fun u : ℝ => cellDensity x u) (Ioi (0 : ℝ)) := by
    have h := cellDensity_exp_integrable x 0
    have h' : Integrable (cellDensity x) := by
      refine h.congr ?_
      filter_upwards with u
      rw [show (2 : ℝ) * 0 * u = 0 by ring, Real.exp_zero, one_mul]
    exact h'.integrableOn
  have hsub : IntegrableOn (fun u : ℝ => (u ^ 2 - a ^ 2) * cellDensity x u) (Ioi (0 : ℝ)) := by
    refine (hI2.sub (hI0.const_mul (a ^ 2))).congr_fun ?_ measurableSet_Ioi
    intro u _
    simp only [Pi.sub_apply]
    ring
  rw [← integral_const_mul]
  rw [← integral_add hsub (hI0.const_mul (a ^ 2))]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  ring

/-- **THE LOWER BOUND WITH A MOVABLE CENTRE.**  For every `a` and every `x`, unconditionally.
The only input is A2's domination `|C(x,u)| ≤ C(0,u)`. -/
theorem momentTwo_ge_shifted (a x : ℝ) :
    a ^ 2 * (∫ u in Ioi (0 : ℝ), cellDensity x u) - Jbar a
      ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u := by
  have hI2 : IntegrableOn (fun u : ℝ => u ^ 2 * cellDensity x u) (Ioi (0 : ℝ)) :=
    (u2_cellDensity_integrable x).integrableOn
  have hI0 : IntegrableOn (fun u : ℝ => cellDensity x u) (Ioi (0 : ℝ)) := by
    have h := cellDensity_exp_integrable x 0
    have h' : Integrable (cellDensity x) := by
      refine h.congr ?_
      filter_upwards with u
      rw [show (2 : ℝ) * 0 * u = 0 by ring, Real.exp_zero, one_mul]
    exact h'.integrableOn
  have hsub : IntegrableOn (fun u : ℝ => (u ^ 2 - a ^ 2) * cellDensity x u) (Ioi (0 : ℝ)) := by
    refine (hI2.sub (hI0.const_mul (a ^ 2))).congr_fun ?_ measurableSet_Ioi
    intro u _
    simp only [Pi.sub_apply]
    ring
  have hkey : -Jbar a ≤ ∫ u in Ioi (0 : ℝ), (u ^ 2 - a ^ 2) * cellDensity x u := by
    have habs : |∫ u in Ioi (0 : ℝ), (u ^ 2 - a ^ 2) * cellDensity x u| ≤ Jbar a := by
      have h1 : |∫ u in Ioi (0 : ℝ), (u ^ 2 - a ^ 2) * cellDensity x u|
          ≤ ∫ u in Ioi (0 : ℝ), |(u ^ 2 - a ^ 2) * cellDensity x u| :=
        abs_integral_le_integral_abs
      refine le_trans h1 (integral_mono_ae hsub.abs (Jbar_integrableOn a) ?_)
      filter_upwards [ae_restrict_of_ae (μ := volume) (s := Ioi (0 : ℝ))
        (cellDensity_abs_le_zero x)] with u hu
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    exact (abs_le.mp habs).1
  rw [shifted_moment_split a x]
  linarith [hkey]

/-- **THE LARGE-READOUT FIBRE.**  Written with the square already evaluated by batch 12's
`cellDensity_Ioi_eq_sq`: the target holds wherever `Ξ(x)²` exceeds the fixed constant
`4·Jbar a / a²` for some `a ≠ 0`. -/
theorem momentTwo_ge_readout_sq (a x : ℝ) :
    a ^ 2 * (4⁻¹ * cosMom riemannXiKernel x ^ 2) - Jbar a
      ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u := by
  have h := momentTwo_ge_shifted a x
  rwa [cellDensity_Ioi_eq_sq x] at h

/-- The fibre as a criterion.  Complementary to `momentTwo_nonneg_of_thickened`, which needs
the readout to be *small*; this one needs it to be *large*. -/
theorem momentTwo_nonneg_of_large_readout {a x : ℝ}
    (h : Jbar a ≤ a ^ 2 * (4⁻¹ * cosMom riemannXiKernel x ^ 2)) :
    0 ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u :=
  le_trans (by linarith) (momentTwo_ge_readout_sq a x)

/-- The two criteria together, as one statement: at every `x`, if *either* the readout is
small enough for A1's criterion *or* large enough for this one, the target holds at that `x`.

**This is a disjunction, not a dichotomy.**  The two hypotheses are oppositely directed but
are not logical complements and do not partition the line: there is a wide middle band
satisfying neither, measured at 95.59% of a uniform grid on `[0,60]`. -/
theorem momentTwo_nonneg_of_either {a x : ℝ}
    (h : (cosMom kM2 0 * |cosMom riemannXiKernel x| ≤ sinMom kM1 x ^ 2)
        ∨ (Jbar a ≤ a ^ 2 * (4⁻¹ * cosMom riemannXiKernel x ^ 2))) :
    0 ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u := by
  rcases h with h | h
  · exact momentTwo_nonneg_of_thickened h
  · exact momentTwo_nonneg_of_large_readout h

end C3B13

section AxiomAudit
#print axioms C3B13.cellDensity_zero_integrable
#print axioms C3B13.cellDensity_zero_aesm
#print axioms C3B13.Jbar_integrableOn
#print axioms C3B13.Jbar_nonneg
#print axioms C3B13.shifted_moment_split
#print axioms C3B13.momentTwo_ge_shifted
#print axioms C3B13.momentTwo_ge_readout_sq
#print axioms C3B13.momentTwo_nonneg_of_large_readout
#print axioms C3B13.momentTwo_nonneg_of_either
end AxiomAudit
