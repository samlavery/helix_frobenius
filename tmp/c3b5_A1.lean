import RequestProject.JKernelSignLaw

/-!
# C3 batch 5, block A1 — the `|u|` corner does not exist, and the exact mode-pair bracket

Two independent things, both purely algebraic, both feeding the full-double-sum
adjudication of batch 5.

## 1. The corner

`JKernelSignLaw.phiEven u = riemannXiKernel |u|` is an *even extension* of the
half-line kernel.  Batch 4 (§18, §22) attributed part of the small-`u` mismatch
between the Bessel mode `C₁₁` and the `Ξ`-route to "the `|u|` corner".  There is no
corner: the compiled `riemannXiKernel_neg` says the *analytic* kernel is already even
on all of `ℝ`, so `phiEven = riemannXiKernel` as functions.  Consequences:

* `riemannXiKernel` is strictly positive on the **whole line**, not just `u ≥ 0`;
* the theta double sum `Σ_{n,m} Φ_n(u+v)Φ_m(u−v)` has **no even-extension remainder**.

This is exactly the question `tmp/att544_c3b5_doublesum.py cmd_even` was written to
decide numerically.  It is decided here by a compiled theorem instead.

## 2. The mode-pair bracket

With `Φ_n(t) = 2πn²e^{5t/2}(2πn²e^{2t} − 3)e^{−πn²e^{2t}}` (so `Φ = riemannXiKernel/2`,
term by term `Φ_{n+1} = 2·riemannXiKernelTerm n`), the product of two modes at
`t = u ± v` has exponent

  `π(n²e^{2(u+v)} + m²e^{2(u−v)}) = A cosh w`,  `A = 2πnm e^{2u}`, `w = 2v + log(n/m)`

and polynomial factor `(a − 3)(b − 3) = A² − 6A cosh w + 9` with `a = Ae^w`, `b = Ae^{−w}`.
Both are proved below as real identities, which is the "verify all changes of variables"
obligation of the batch-5 adjudication discharged by the compiler rather than by a plot.

The bracket also has the exact square form `A² − 6A cosh w + 9 = (A − 3cosh w)² − 9 sinh²w`,
which specializes on the diagonal `w = 0` to batch 4's `theta_diagonal_perfect_square`.

SCOPE: nothing here mentions zeros, `Ξ`, positivity of any quadratic form, or RH.
-/

open Real

noncomputable section

namespace C3B5.A1

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open CriticalLinePhasor.JKernel

/-! ### 1. The corner elimination -/

/-- **The even extension is not an extension.**  `phiEven = riemannXiKernel` as
functions on `ℝ`, because the analytic kernel is already even (`riemannXiKernel_neg`). -/
theorem phiEven_eq_kernel (u : ℝ) : phiEven u = riemannXiKernel u := by
  show riemannXiKernel |u| = riemannXiKernel u
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, riemannXiKernel_neg]

/-- **Riemann's kernel is strictly positive on the WHOLE line**, not just on `u ≥ 0`. -/
theorem riemannXiKernel_pos_all (u : ℝ) : 0 < riemannXiKernel u := by
  rw [← phiEven_eq_kernel]
  exact riemannXiKernel_pos (abs_nonneg u)

/-- The `J`-kernel written without any absolute value. -/
theorem jKernel_eq_kernel (d s : ℝ) :
    jKernel d s
      = s * riemannXiKernel ((s + d) / 2) * riemannXiKernel ((s - d) / 2) := by
  simp only [jKernel, phiEven_eq_kernel]

/-- The `J`-weight of the sinh bridge is a product of two strictly positive kernel
values — no corner, no case split. -/
theorem jKernel_weight_pos (d u : ℝ) :
    0 < riemannXiKernel (u + d / 2) * riemannXiKernel (u - d / 2) :=
  mul_pos (riemannXiKernel_pos_all _) (riemannXiKernel_pos_all _)

/-! ### 2. The exact mode-pair change of variables -/

/-- **The two-mode exponent collapses to one hyperbolic cosine.**
`π(n²e^{2(u+v)} + m²e^{2(u−v)}) = A·cosh w` with `A = 2πnm e^{2u}` and
`w = 2v + log(n/m)`.  This is the substitution that turns the `v`-integral of a
mode pair into a Macdonald function of imaginary order. -/
theorem theta_pair_cosh {n m : ℝ} (hn : 0 < n) (hm : 0 < m) (u v : ℝ) :
    Real.pi * (n ^ 2 * Real.exp (2 * (u + v)) + m ^ 2 * Real.exp (2 * (u - v)))
      = 2 * Real.pi * n * m * Real.exp (2 * u) *
          Real.cosh (2 * v + Real.log (n / m)) := by
  have hnm : (0 : ℝ) < n / m := div_pos hn hm
  have hmn : (0 : ℝ) < m / n := div_pos hm hn
  have hlog : Real.log (m / n) = -Real.log (n / m) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  have h1 : Real.exp (2 * v + Real.log (n / m)) = Real.exp (2 * v) * (n / m) := by
    rw [Real.exp_add, Real.exp_log hnm]
  have h2 : Real.exp (-(2 * v + Real.log (n / m))) = Real.exp (-(2 * v)) * (m / n) := by
    rw [show -(2 * v + Real.log (n / m)) = -(2 * v) + Real.log (m / n) by rw [hlog]; ring,
      Real.exp_add, Real.exp_log hmn]
  have he1 : Real.exp (2 * (u + v)) = Real.exp (2 * u) * Real.exp (2 * v) := by
    rw [← Real.exp_add]; congr 1; ring
  have he2 : Real.exp (2 * (u - v)) = Real.exp (2 * u) * Real.exp (-(2 * v)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.cosh_eq, h1, h2, he1, he2]
  field_simp

/-- **The mode-pair polynomial bracket.**  `(a − 3)(b − 3) = A² − 6A cosh w + 9`
with `a = Ae^w`, `b = Ae^{−w}`.  The `3` is the pole compensator of Riemann's `Φ`. -/
theorem bracket_product (A w : ℝ) :
    (A * Real.exp w - 3) * (A * Real.exp (-w) - 3)
      = A ^ 2 - 6 * A * Real.cosh w + 9 := by
  have h : Real.exp w * Real.exp (-w) = 1 := by
    rw [← Real.exp_add]; simp
  rw [Real.cosh_eq]
  linear_combination A ^ 2 * h

/-- **The bracket as a square minus a square** — the `w`-uniform form of batch 4's
`theta_diagonal_perfect_square`. -/
theorem bracket_square (A w : ℝ) :
    A ^ 2 - 6 * A * Real.cosh w + 9
      = (A - 3 * Real.cosh w) ^ 2 - 9 * Real.sinh w ^ 2 := by
  have h : Real.cosh w ^ 2 - Real.sinh w ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq w
  linear_combination (-9 : ℝ) * h

/-- On the diagonal the bracket is a perfect square. -/
theorem bracket_diag (A : ℝ) :
    A ^ 2 - 6 * A * Real.cosh 0 + 9 = (A - 3) ^ 2 := by
  rw [Real.cosh_zero]; ring

/-- The bracket is nonnegative exactly up to the hyperbolic angle
`cosh w ≤ (A²+9)/(6A)`, and that threshold is always `≥ 1` (AM–GM), so the bracket is
nonnegative on a genuine window around the diagonal for every `A > 0`. -/
theorem bracket_threshold_ge_one {A : ℝ} (hA : 0 < A) : 6 * A ≤ A ^ 2 + 9 := by
  nlinarith [sq_nonneg (A - 3)]

/-! ### 3. The turning-point quadratic -/

/-- `A² − 6A + 6 > 0` for `A ≥ 8`.  This is the coefficient produced by the Riccati
bracketing of the radial combination in block A2. -/
theorem quad_pos_of_ge_eight {A : ℝ} (hA : 8 ≤ A) : 0 < A ^ 2 - 6 * A + 6 := by
  nlinarith [hA, sq_nonneg (A - 8)]

/-- The sharp threshold: `A² − 6A + 6 > 0` for `A > 3 + √3`. -/
theorem quad_pos_of_gt_root {A : ℝ} (hA : 3 + Real.sqrt 3 < A) :
    0 < A ^ 2 - 6 * A + 6 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  nlinarith

end C3B5.A1

section AxiomAudit
#print axioms C3B5.A1.phiEven_eq_kernel
#print axioms C3B5.A1.riemannXiKernel_pos_all
#print axioms C3B5.A1.jKernel_eq_kernel
#print axioms C3B5.A1.jKernel_weight_pos
#print axioms C3B5.A1.theta_pair_cosh
#print axioms C3B5.A1.bracket_product
#print axioms C3B5.A1.bracket_square
#print axioms C3B5.A1.bracket_diag
#print axioms C3B5.A1.bracket_threshold_ge_one
#print axioms C3B5.A1.quad_pos_of_ge_eight
#print axioms C3B5.A1.quad_pos_of_gt_root
end AxiomAudit
