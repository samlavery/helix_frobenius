import c3b13_A1

/-!
# C3 batch 13, block A2 — **cell-density domination**, and the sharp two-sided Laguerre bound

The target `0 ≤ c₀c₂ + s₁² = Ξ′(x)² − Ξ(x)Ξ″(x)` is a *lower* bound.  This block proves the
matching *upper* bound, sharply, and unconditionally, and it does so from one observation
that costs nothing:

  **the carrier product is nonnegative.**  `Φ(u+p)·Φ(u−p) ≥ 0` for every `u, p`, because
  `Φ > 0` everywhere (`riemannXiKernel_pos_all`).  The chart clock `cos(2xp)` is the only
  sign in the cell density, and `|cos| ≤ 1`.  Hence

      `|cellDensity x u| ≤ cellDensity 0 u`   for a.e. `u`, for every `x`.

That is the **positive-kernel** content of the C3 engine, in the cheapest available form.
Integrating it against any nonnegative weight gives a two-sided bound on every even moment,
and at the weight `u²` it gives the headline:

      `|Ξ′(x)² − Ξ(x)Ξ″(x)| ≤ Ξ(0)·(−Ξ″(0))`   for every real `x`.

## Why this is the sharp constant, and how it was found

The same statement follows from the representation `L₁(x) = 4∫R(v)cos(2xv)dv` with
`R(v) = ∫p²Φ(v+p)Φ(v−p)dp ≥ 0` — i.e. *the first Laguerre expression is the cosine transform
of a manifestly nonnegative function*, so `|L₁(x)| ≤ 4∫R = L₁(0)`.  That route needs a Fubini
across the `(v,p)` shear which is **not** formalised here.  The cell-density route below
reaches the same constant with no Fubini at all, because `cellDensity` already *is* the
inner integral and batch 11's `slice_ae` already supplies its integrability.  Both routes
were written out before either was attempted; this is the one whose first Lean line typed.

Verified numerically (`tmp/c3b13_num2_out.txt` §B3): the identity
`cosMom R (2x) = L₁(x)` and the bound `|L₁(x)| ≤ L₁(0)` at ten ordinates.

SCOPE: one domination inequality, its weighted corollary, and two moment instances.
Nothing here decides the target's sign, which is the *lower* bound.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B13

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open C3B6.Theta
open C3B10
open C3B11
open C3B12

/-! ### 1. The carrier product is nonnegative -/

theorem carrier_product_nonneg (u p : ℝ) :
    0 ≤ riemannXiKernel (u + p) * riemannXiKernel (u - p) :=
  mul_nonneg (xiKernel_nonneg _) (xiKernel_nonneg _)

/-- The slice integrability supplied by batch 11, at the two clock values we need. -/
theorem cell_slice_ae (x : ℝ) :
    ∀ᵐ u : ℝ, Integrable
      (fun p : ℝ => riemannXiKernel (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)) :=
  slice_ae xiKernel_integrable riemannXiKernel_measurable
    xiKernel_integrable riemannXiKernel_measurable x

/-! ### 2. THE DOMINATION -/

/-- **CELL-DENSITY DOMINATION.**  For a.e. cell centre `u`, the cell density at *any* chart
clock `x` is dominated in absolute value by its value at `x = 0`.  The only inputs are
`Φ ≥ 0` and `|cos| ≤ 1`; no zero of anything is mentioned. -/
theorem cellDensity_abs_le_zero (x : ℝ) :
    ∀ᵐ u : ℝ, |cellDensity x u| ≤ cellDensity 0 u := by
  filter_upwards [cell_slice_ae x, cell_slice_ae 0] with u hx h0
  unfold cellDensity
  have h1 : |∫ p : ℝ, riemannXiKernel (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)|
      ≤ ∫ p : ℝ, |riemannXiKernel (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)| :=
    abs_integral_le_integral_abs
  have h2 : (∫ p : ℝ, |riemannXiKernel (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)|)
      ≤ ∫ p : ℝ, riemannXiKernel (u + p) * riemannXiKernel (u - p) * Real.cos (2 * 0 * p) := by
    refine integral_mono hx.abs h0 fun p => ?_
    have hcp := carrier_product_nonneg u p
    rw [abs_mul, abs_of_nonneg hcp, show (2 : ℝ) * 0 * p = 0 by ring, Real.cos_zero, mul_one]
    nlinarith [Real.abs_cos_le_one (2 * x * p), hcp, abs_nonneg (Real.cos (2 * x * p))]
  exact le_trans h1 h2

/-- The `x = 0` cell density is nonnegative (the `x = 0` case of the domination). -/
theorem cellDensity_zero_nonneg : ∀ᵐ u : ℝ, 0 ≤ cellDensity 0 u := by
  filter_upwards [cellDensity_abs_le_zero 0] with u h
  exact le_trans (abs_nonneg _) h

/-! ### 3. The weighted corollary -/

/-- **THE WEIGHTED TWO-SIDED BOUND.**  Against any nonnegative weight `w` for which both
moments exist, the cell density's moment at clock `x` is bounded by its moment at clock `0`.
Hypotheses displayed in full; `w` is arbitrary. -/
theorem weighted_moment_abs_le {w : ℝ → ℝ} (hw : ∀ u : ℝ, 0 ≤ w u) {x : ℝ}
    (hx : IntegrableOn (fun u : ℝ => w u * cellDensity x u) (Ioi (0 : ℝ)))
    (h0 : IntegrableOn (fun u : ℝ => w u * cellDensity 0 u) (Ioi (0 : ℝ))) :
    |∫ u in Ioi (0 : ℝ), w u * cellDensity x u|
      ≤ ∫ u in Ioi (0 : ℝ), w u * cellDensity 0 u := by
  have hdom : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      |w u * cellDensity x u| ≤ w u * cellDensity 0 u := by
    have := ae_restrict_of_ae (μ := volume) (s := Ioi (0 : ℝ)) (cellDensity_abs_le_zero x)
    filter_upwards [this] with u hu
    rw [abs_mul, abs_of_nonneg (hw u)]
    exact mul_le_mul_of_nonneg_left hu (hw u)
  have h1 : |∫ u in Ioi (0 : ℝ), w u * cellDensity x u|
      ≤ ∫ u in Ioi (0 : ℝ), |w u * cellDensity x u| := abs_integral_le_integral_abs
  exact le_trans h1 (integral_mono_ae hx.abs h0 hdom)

/-! ### 4. The two moment instances -/

/-- **k = 0.**  Recovers `|Ξ(x)| ≤ Ξ(0)` through the cell density. -/
theorem momentZero_abs_le (x : ℝ) :
    |∫ u in Ioi (0 : ℝ), cellDensity x u| ≤ ∫ u in Ioi (0 : ℝ), cellDensity 0 u := by
  have hbase : ∀ y : ℝ, IntegrableOn (fun u : ℝ => (1 : ℝ) * cellDensity y u) (Ioi (0 : ℝ)) := by
    intro y
    have h := cellDensity_exp_integrable y 0
    have h' : Integrable (fun u : ℝ => (1 : ℝ) * cellDensity y u) := by
      refine h.congr ?_
      filter_upwards with u
      rw [show (2 : ℝ) * 0 * u = 0 by ring, Real.exp_zero]
    exact h'.integrableOn
  have := weighted_moment_abs_le (w := fun _ : ℝ => (1 : ℝ)) (fun _ => zero_le_one)
    (hbase x) (hbase 0)
  simpa using this

/-- **THE HEADLINE, k = 1.**  The second moment of the cell density is bounded in absolute
value by its value at `x = 0`, sharply and with no hypothesis. -/
theorem momentTwo_abs_le (x : ℝ) :
    |∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u|
      ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity 0 u :=
  weighted_moment_abs_le (w := fun u : ℝ => u ^ 2) (fun u => sq_nonneg u)
    ((u2_cellDensity_integrable x).integrableOn) ((u2_cellDensity_integrable 0).integrableOn)

/-- **THE SHARP TWO-SIDED LAGUERRE BOUND, IN MOMENTS.**  Reading the dictionary
`c₀ = Ξ`, `s₁ = −Ξ′`, `c₂ = −Ξ″` this is

  `|Ξ′(x)² − Ξ(x)Ξ″(x)| ≤ Ξ(0)·(−Ξ″(0))`   for every real `x`,

i.e. the first Laguerre expression never exceeds its value at the origin, in either
direction.  The lower half is what the OPEN target strengthens to `0`. -/
theorem laguerre_abs_le_zero (x : ℝ) :
    |cosMom riemannXiKernel x * cosMom kM2 x + sinMom kM1 x ^ 2|
      ≤ cosMom riemannXiKernel 0 * cosMom kM2 0 := by
  have h := momentTwo_abs_le x
  rw [momentTwo_eq x, momentTwo_eq 0, sinMom_at_zero] at h
  have h8 : (0 : ℝ) < 8 := by norm_num
  rw [abs_le] at h ⊢
  constructor
  · nlinarith [h.1]
  · nlinarith [h.2]

/-- Restated as the pair of one-sided bounds actually used downstream. -/
theorem laguerre_ge_neg (x : ℝ) :
    -(cosMom riemannXiKernel 0 * cosMom kM2 0)
      ≤ cosMom riemannXiKernel x * cosMom kM2 x + sinMom kM1 x ^ 2 :=
  (abs_le.mp (laguerre_abs_le_zero x)).1

theorem laguerre_le_pos (x : ℝ) :
    cosMom riemannXiKernel x * cosMom kM2 x + sinMom kM1 x ^ 2
      ≤ cosMom riemannXiKernel 0 * cosMom kM2 0 :=
  (abs_le.mp (laguerre_abs_le_zero x)).2

end C3B13

section AxiomAudit
#print axioms C3B13.carrier_product_nonneg
#print axioms C3B13.cell_slice_ae
#print axioms C3B13.cellDensity_abs_le_zero
#print axioms C3B13.cellDensity_zero_nonneg
#print axioms C3B13.weighted_moment_abs_le
#print axioms C3B13.momentZero_abs_le
#print axioms C3B13.momentTwo_abs_le
#print axioms C3B13.laguerre_abs_le_zero
#print axioms C3B13.laguerre_ge_neg
#print axioms C3B13.laguerre_le_pos
end AxiomAudit
