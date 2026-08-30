import c3b13_A2
import c3b12_A3

/-!
# C3 batch 13, block A3 — the **derivation law** of the Laguerre expression, and the
# elementary-factor split with the remaining `N` factor

The first Laguerre expression `L₁(f) = f′² − f f″` is not additive and not multiplicative.
It is a **derivation on logarithms**: `L₁(f)/f² = −(log f)″`, and `log` turns products into
sums.  Hence, for any two functions,

    `L₁(f·g) = L₁(f)·g² + f²·L₁(g)`.

This is the exact algebraic skeleton of the "elementary-factor split with the remaining `N`
factor".  Applied to the Riemann readout in the form `Ξ(x) = P(x)·G(x)` with

    `P(x) = −(x² + ¼)`   (the elementary factor `s(s−1)` at `s = ½ + ix`),
    `G(x) = π^{−s/2}Γ(s/2)ζ(s)|_{s=½+ix}`   (real, because `Ξ` and `P` are),

and `L₁(P) = P′² − P P″ = 4x² − 2(x² + ¼) = 2x² − ½`, it gives the **exact identity**

    `L₁(Ξ)(x) = (2x² − ½)·G(x)² + (x² + ¼)²·L₁(G)(x)`.

Two consequences, both compiled below:

* **the elementary factor helps outside `|x| < ½` and only there** — `2x² − ½ ≥ 0 ⟺ x² ≥ ¼`,
  the same circle `|s − ½| = ½` that batch 12's `elementary_factor_split` found on the
  four-moment leaf.  So on `|x| ≥ ½` the target follows from `L₁(G) ≥ 0`;
* the split is an **exact reduction**, not an estimate: no information is lost.

## What this does NOT do, stated plainly

`L₁(G) ≥ 0` is not proved here and is not easier: the numerics of this batch
(`tmp/c3b13_num2_out.txt` §B4) show that after the further split
`G = (archimedean envelope)·(Hardy function)`, **neither factor is separately
log-concave** — the archimedean part `−(log A)″ = T_el + T_gam` and the Hardy part
`−(log|Z|)″ = T_zeta` each go negative on the scanned range, with
`min T_zeta = −0.699` at `x ≈ 0.85`.  In particular `Re (ζ′/ζ)′(½+it) ≥ 0` is **false**.
The split therefore relocates the difficulty exactly, and is recorded as such.

**ANALYTIC BRIDGE, NAMED AND NOT COMPILED.**  Everything below is an identity between real
numbers standing for a function and its first two derivatives.  Instantiating it at the
actual `Ξ` requires (i) the dictionary `c₀ = Ξ, s₁ = −Ξ′, c₂ = −Ξ″` (differentiation under
the integral sign — measured this batch to `6.7e-53`, **not** formalised) and (ii) that
`ξ(½+ix) = P(x)G(x)` with `G` real and twice differentiable.  Neither is formalised in this
repository.  Do not cite the instantiation as compiled.

SCOPE: pure two-jet algebra, in two independent spellings, plus its sign fibre; and one
genuine analytic lemma (the general-kernel domination) that does not depend on the bridge.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B13

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open C3B6.Theta
open C3B10
open C3B11
open C3B12

/-! ### 1. The derivation law — DECOMPOSITION I (two-jet product rule) -/

/-- **THE DERIVATION LAW.**  `f, f1, f2` stand for `f, f′, f″` and likewise for `g`; the
product's jet is the Leibniz jet.  Then the Laguerre expression splits with no cross term.
No hypothesis. -/
theorem laguerre_mul (f f1 f2 g g1 g2 : ℝ) :
    (f1 * g + f * g1) ^ 2 - (f * g) * (f2 * g + 2 * (f1 * g1) + f * g2)
      = (f1 ^ 2 - f * f2) * g ^ 2 + f ^ 2 * (g1 ^ 2 - g * g2) := by
  ring

/-! ### 2. The same law — DECOMPOSITION II (additivity of `−(log)″`) -/

/-- **THE SAME LAW, AS ADDITIVITY OF THE LOGARITHMIC CURVATURE.**  Written independently of
Decomposition I: `L₁(h)/h² = L₁(f)/f² + L₁(g)/g²` whenever `f, g ≠ 0`.  This is the spelling
in which the split of `ξ` into `elementary × Γ × ζ` is read (numerics §B2/§B4). -/
theorem laguerre_quotient (f f1 f2 g g1 g2 : ℝ) (hf : f ≠ 0) (hg : g ≠ 0) :
    ((f1 * g + f * g1) ^ 2 - (f * g) * (f2 * g + 2 * (f1 * g1) + f * g2)) / (f * g) ^ 2
      = (f1 ^ 2 - f * f2) / f ^ 2 + (g1 ^ 2 - g * g2) / g ^ 2 := by
  field_simp
  ring

/-! ### 3. The elementary factor `P(x) = −(x² + ¼)` -/

/-- The Laguerre expression of the elementary factor, exactly. -/
theorem laguerre_elementary_value (x : ℝ) :
    (-(2 * x)) ^ 2 - (-(x ^ 2 + 4⁻¹)) * (-2) = 2 * x ^ 2 - 2⁻¹ := by
  ring

/-- **THE ELEMENTARY-FACTOR SPLIT.**  With `P(x) = −(x²+¼)`, `P′ = −2x`, `P″ = −2`, the
Laguerre expression of `P·G` is an explicit scalar times `G²` plus `P²` times the Laguerre
expression of `G`.  Exact; no hypothesis. -/
theorem laguerre_elementary_split (x g g1 g2 : ℝ) :
    ((-(2 * x)) * g + (-(x ^ 2 + 4⁻¹)) * g1) ^ 2
        - ((-(x ^ 2 + 4⁻¹)) * g)
          * ((-2) * g + 2 * ((-(2 * x)) * g1) + (-(x ^ 2 + 4⁻¹)) * g2)
      = (2 * x ^ 2 - 2⁻¹) * g ^ 2 + (x ^ 2 + 4⁻¹) ^ 2 * (g1 ^ 2 - g * g2) := by
  ring

/-- **THE FIBRE.**  Outside the disc `|x| < ½` the elementary factor contributes a
nonnegative amount, so the sign of the whole is carried by the remaining factor. -/
theorem laguerre_elementary_fibre {x g g1 g2 : ℝ} (hx : 4⁻¹ ≤ x ^ 2)
    (hg : 0 ≤ g1 ^ 2 - g * g2) :
    0 ≤ ((-(2 * x)) * g + (-(x ^ 2 + 4⁻¹)) * g1) ^ 2
        - ((-(x ^ 2 + 4⁻¹)) * g)
          * ((-2) * g + 2 * ((-(2 * x)) * g1) + (-(x ^ 2 + 4⁻¹)) * g2) := by
  rw [laguerre_elementary_split]
  have h1 : (0 : ℝ) ≤ 2 * x ^ 2 - 2⁻¹ := by linarith
  have h2 : (0 : ℝ) ≤ (x ^ 2 + 4⁻¹) ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg g, h1, h2, hg]

/-- Inside the disc the elementary factor fights: the scalar is strictly negative there.
Compiled so the sign orientation is checked rather than asserted. -/
theorem laguerre_elementary_neg {x : ℝ} (hx : x ^ 2 < 4⁻¹) : 2 * x ^ 2 - 2⁻¹ < 0 := by
  linarith

/-- The split as an **exact reduction**: the target for `P·G` is equivalent to an explicit
inequality in `G` alone.  Nothing is lost, and nothing unproved is assumed. -/
theorem laguerre_elementary_iff (x g g1 g2 : ℝ) :
    (0 ≤ ((-(2 * x)) * g + (-(x ^ 2 + 4⁻¹)) * g1) ^ 2
        - ((-(x ^ 2 + 4⁻¹)) * g)
          * ((-2) * g + 2 * ((-(2 * x)) * g1) + (-(x ^ 2 + 4⁻¹)) * g2))
      ↔ 0 ≤ (2 * x ^ 2 - 2⁻¹) * g ^ 2 + (x ^ 2 + 4⁻¹) ^ 2 * (g1 ^ 2 - g * g2) := by
  rw [laguerre_elementary_split]

/-! ### 4. One genuine analytic lemma: the domination for an ARBITRARY nonnegative kernel

This does not use the bridge, and it is the general form of `cellDensity_abs_le_zero`.  It is
the exact statement of what the C3 engine's positivity gives: the chart clock is the only
sign, so every clock value is dominated by the clock-free one. -/

/-- **GENERAL-KERNEL CELL DOMINATION.**  For any real kernel `W` with `W ≥ 0` whose carrier
slices are integrable, the general cell density at clock `x` is dominated by its value at
clock `0`.  Hypotheses displayed in full; nothing arithmetic, nothing about zeros, and — in
contrast to `gen_target_eq` — **not even evenness** is used. -/
theorem gen_cellDensity_abs_le {W : ℝ → ℝ} (hpos : ∀ t : ℝ, 0 ≤ W t) {x u : ℝ}
    (hx : Integrable (fun p : ℝ => W (u + p) * W (u - p) * Real.cos (2 * x * p)))
    (h0 : Integrable (fun p : ℝ => W (u + p) * W (u - p) * Real.cos (2 * 0 * p))) :
    |genCell W x u| ≤ genCell W 0 u := by
  unfold genCell
  have h1 : |∫ p : ℝ, W (u + p) * W (u - p) * Real.cos (2 * x * p)|
      ≤ ∫ p : ℝ, |W (u + p) * W (u - p) * Real.cos (2 * x * p)| :=
    abs_integral_le_integral_abs
  have h2 : (∫ p : ℝ, |W (u + p) * W (u - p) * Real.cos (2 * x * p)|)
      ≤ ∫ p : ℝ, W (u + p) * W (u - p) * Real.cos (2 * 0 * p) := by
    refine integral_mono hx.abs h0 fun p => ?_
    have hcp : 0 ≤ W (u + p) * W (u - p) := mul_nonneg (hpos _) (hpos _)
    rw [abs_mul, abs_of_nonneg hcp, show (2 : ℝ) * 0 * p = 0 by ring, Real.cos_zero, mul_one]
    nlinarith [Real.abs_cos_le_one (2 * x * p), hcp, abs_nonneg (Real.cos (2 * x * p))]
  exact le_trans h1 h2

end C3B13

section AxiomAudit
#print axioms C3B13.laguerre_mul
#print axioms C3B13.laguerre_quotient
#print axioms C3B13.laguerre_elementary_value
#print axioms C3B13.laguerre_elementary_split
#print axioms C3B13.laguerre_elementary_fibre
#print axioms C3B13.laguerre_elementary_neg
#print axioms C3B13.laguerre_elementary_iff
#print axioms C3B13.gen_cellDensity_abs_le
end AxiomAudit
