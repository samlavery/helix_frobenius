import c3b13_A4

/-!
# C3 batch 13, block A5 — the **corner obstruction**, and a closed-form counterexample

This block records, in compiled form, *why* the target cannot be proved from softness alone,
and it does so with an explicit witness rather than an assertion.

## The mechanism

Let `W` be even, positive and integrable, with a **corner** at the origin — `W′(0⁺) = A/2 ≠ 0`
in the one-sided sense.  Then its cosine transform has the tail `Ξ(x) = −A/x² + O(x⁻⁴)`, and
feeding that tail into the first Laguerre expression gives

  `Ξ ~ −A x⁻²`, `Ξ′ ~ 2A x⁻³`, `Ξ″ ~ −6A x⁻⁴`,
  `L₁ = Ξ′² − Ξ Ξ″ ~ 4A²x⁻⁶ − 6A²x⁻⁶ = −2A² x⁻⁶ < 0`.

So **every even positive kernel with a corner at `0` violates the target for all large `x`**,
with no arithmetic content whatever.  `corner_tail_laguerre_neg` compiles that computation.

Riemann's `Φ` has **no** corner: `Φ′(0) = 0`, and that is precisely the Jacobi reflection —
the functional equation.  Measured (`tmp/c3b13_num5_out.txt` §C2): the truncation `Φ_N(|u|)`
has one-sided derivative `7.90e-2` at `N = 1`, `1.65e-7` at `N = 2`, `2.78e-16` at `N = 3`,
`3.5e-40` at `N ≥ 5`.  Stated neutrally: `Φ` is even as an identity (the Jacobi reflection,
compiled as `riemannXiKernel_neg`), and an even differentiable function has vanishing
derivative at `0`, so the corner mechanism below does not apply to `Φ`.  Nothing is claimed
about which ingredient of a hypothetical proof would carry the weight.

## The closed-form counterexample

`W(t) = e^{−|t|}` is even, positive, integrable, and `∫W(t)cos(xt)dt = 2/(1+x²)` exactly
(quadrature check to `1.5e-31`, `tmp/c3b13_num6_out.txt` §D1).  Its Laguerre expression is

  `L₁(x) = (8 − 8x²)/(1 + x²)⁴`,

**negative for every `|x| > 1`** — verified against numerical differentiation to `4e-31`.
This supersedes batch 12's `Φ_g` witness (a Gaussian mixture, established numerically) and
batch 3's `FAILED-5` witness (a discrete measure `cδ₀ + b(δ_a + δ_{−a})`, which is not an
integrable kernel at all): here the kernel is a genuine `L¹` function and the refutation is
in closed form.

> **WHAT IS COMPILED AND WHAT IS NOT.**  What compiles below is the **rational-function
> algebra**: the value of `f′² − f f″` for `f = 2/(1+x²)` and for the model tail `f = −A/x²`,
> and their signs.  The **transform** `∫e^{−|t|}cos(xt)dt = 2/(1+x²)` is a textbook Laplace
> computation and is **NOT** formalised here — it is checked numerically only.  Likewise the
> corner-to-tail asymptotic `Ξ(x) = −A/x² + O(x⁻⁴)` is classical and **NOT** formalised.
> Do not cite either as compiled.

SCOPE: two rational identities and their sign consequences.  No claim about `Φ` is made
here; the point is a property of the **soft-kernel instrument class**.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B13

/-! ### 1. The model corner tail -/

/-- **THE CORNER COMPUTATION.**  For the exact tail `f(x) = −A/x²` (with `f′ = 2A/x³`,
`f″ = −6A/x⁴`), the first Laguerre expression is `−2A²/x⁶`.  Exact; no hypothesis beyond
`x ≠ 0`. -/
theorem corner_tail_laguerre (A x : ℝ) (hx : x ≠ 0) :
    (2 * A / x ^ 3) ^ 2 - (-(A / x ^ 2)) * (-(6 * A / x ^ 4)) = -(2 * A ^ 2 / x ^ 6) := by
  field_simp
  ring

/-- Hence it is **strictly negative** whenever the corner is present (`A ≠ 0`).  This is the
whole obstruction: it uses nothing about the kernel except that its transform decays like
`x⁻²`, which is what a corner at the origin forces. -/
theorem corner_tail_laguerre_neg {A x : ℝ} (hA : A ≠ 0) (hx : x ≠ 0) :
    (2 * A / x ^ 3) ^ 2 - (-(A / x ^ 2)) * (-(6 * A / x ^ 4)) < 0 := by
  rw [corner_tail_laguerre A x hx]
  have h1 : 0 < A ^ 2 := by positivity
  have h2 : 0 < x ^ 6 := by positivity
  have : 0 < 2 * A ^ 2 / x ^ 6 := by positivity
  linarith

/-! ### 2. The closed-form witness `W(t) = e^{−|t|}`, transform `2/(1+x²)` -/

/-- The first Laguerre expression of `f(x) = 2/(1+x²)`, in closed form.  Here `f′` and `f″`
are the (elementary, correct) derivatives written out explicitly, so the statement is a
rational-function identity with no analysis in it. -/
theorem laguerre_two_over_one_add_sq (x : ℝ) :
    (-(4 * x) / (1 + x ^ 2) ^ 2) ^ 2
        - (2 / (1 + x ^ 2)) * ((12 * x ^ 2 - 4) / (1 + x ^ 2) ^ 3)
      = (8 - 8 * x ^ 2) / (1 + x ^ 2) ^ 4 := by
  have h : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **THE WITNESS.**  Strictly negative for every `|x| > 1`.  So evenness, positivity and
integrability of the kernel do **not** imply the first Laguerre inequality — and the
counterexample is elementary. -/
theorem laguerre_two_over_one_add_sq_neg {x : ℝ} (hx : 1 < x ^ 2) :
    (-(4 * x) / (1 + x ^ 2) ^ 2) ^ 2
        - (2 / (1 + x ^ 2)) * ((12 * x ^ 2 - 4) / (1 + x ^ 2) ^ 3) < 0 := by
  rw [laguerre_two_over_one_add_sq x]
  have h : (0 : ℝ) < (1 + x ^ 2) ^ 4 := by positivity
  have hnum : (8 : ℝ) - 8 * x ^ 2 < 0 := by linarith
  exact div_neg_of_neg_of_pos hnum h

/-- At `|x| = 1` the witness is exactly `0`: the sign change is at the edge of the disc
`|x| ≤ 1`, recorded so the boundary is checked rather than assumed. -/
theorem laguerre_two_over_one_add_sq_boundary {x : ℝ} (hx : x ^ 2 = 1) :
    (-(4 * x) / (1 + x ^ 2) ^ 2) ^ 2
        - (2 / (1 + x ^ 2)) * ((12 * x ^ 2 - 4) / (1 + x ^ 2) ^ 3) = 0 := by
  rw [laguerre_two_over_one_add_sq x, hx]
  norm_num

/-- And it is strictly **positive** inside, so the witness is not degenerate: the kernel
satisfies the target near the origin and fails it away from it, exactly as the corner
asymptotic predicts. -/
theorem laguerre_two_over_one_add_sq_pos {x : ℝ} (hx : x ^ 2 < 1) :
    0 < (-(4 * x) / (1 + x ^ 2) ^ 2) ^ 2
        - (2 / (1 + x ^ 2)) * ((12 * x ^ 2 - 4) / (1 + x ^ 2) ^ 3) := by
  rw [laguerre_two_over_one_add_sq x]
  have h : (0 : ℝ) < (1 + x ^ 2) ^ 4 := by positivity
  have hnum : (0 : ℝ) < 8 - 8 * x ^ 2 := by linarith
  exact div_pos hnum h

end C3B13

section AxiomAudit
#print axioms C3B13.corner_tail_laguerre
#print axioms C3B13.corner_tail_laguerre_neg
#print axioms C3B13.laguerre_two_over_one_add_sq
#print axioms C3B13.laguerre_two_over_one_add_sq_neg
#print axioms C3B13.laguerre_two_over_one_add_sq_boundary
#print axioms C3B13.laguerre_two_over_one_add_sq_pos
end AxiomAudit
