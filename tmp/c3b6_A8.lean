import c3b6_A7

/-!
# C3 batch 6, block A8 — obligation B, part 3: the complete theta double sum, pointwise

The remaining structural ingredient of obligation B is the **pointwise** double-sum
representation of the product of two Riemann kernels, with every `(n,m)` cross term and no
dropped remainder:

  `Φ(u+p)·Φ(u−p) = 16 · Σ_{(n,m) ∈ ℕ×ℕ} Φ_n(u+p)·Φ_m(u−p)`   (`kernel_product_tsum`)

This needs absolute summability of `Φ_n(t)` in `n` at every real `t` — not just at `t ≥ 0`,
because `t = u ± p` runs over the whole line.  It is supplied here by an explicit
elementary majorant, derived rather than assumed:

With `q = xiKernelQ n t = π(n+1)²e^{2t}` the kernel term is *exactly*

  `Φ_n(t) = e^{t/2}·(2q² − 3q)·e^{−q}`   (`kernelTerm_q_form`)

and `q ≤ 2e^{q/2}`, `q² ≤ 8e^{q/2}` (from `1+x ≤ e^x` and `1+x+x²/2 ≤ e^x` at `x = q/2`)
give

  `|Φ_n(t)| ≤ 22·e^{t/2}·e^{−q/2} ≤ 22·e^{t/2}·e^{−(πe^{2t}/2)(n+1)}`,

a geometric majorant, uniform in the sign of `t` (`kernelTerm_abs_le_exp`,
`summable_kernelTerm_norm`).

Composed with block A5's exact evaluation of each cross term and block A6's summable
majorant `modeBound`, the only step of obligation B that is **not** compiled is the
sum/integral interchange itself; the literal next Lean statement is recorded in the batch
ledger.

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B6.Theta

open C3B6.Bessel
open CriticalLinePhasor.ThetaWronskianSuzukiGram

/-! ### 1. The kernel term in `q`-form -/

/-- **Riemann's kernel term, exactly, in the Gaussian coordinate.**
`Φ_n(t) = e^{t/2}·(2q² − 3q)·e^{−q}` with `q = π(n+1)²e^{2t}`. -/
theorem kernelTerm_q_form (n : ℕ) (t : ℝ) :
    riemannXiKernelTerm n t
      = Real.exp (t / 2) * (2 * (xiKernelQ n t) ^ 2 - 3 * xiKernelQ n t)
        * Real.exp (-(xiKernelQ n t)) := by
  unfold riemannXiKernelTerm xiKernelQ
  dsimp only
  have h1 : Real.exp (9 * t / 2) = Real.exp (t / 2) * (Real.exp (2 * t) * Real.exp (2 * t)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (5 * t / 2) = Real.exp (t / 2) * Real.exp (2 * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * t))
      = Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * t))) := by
    congr 1; ring
  rw [h1, h2, h3]
  ring

theorem xiKernelQ_pos (n : ℕ) (t : ℝ) : 0 < xiKernelQ n t := by
  unfold xiKernelQ
  dsimp only
  have h1 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  have := Real.pi_pos
  positivity

/-- `q ≥ πe^{2t}·(n+1)`: the square in `(n+1)²` is thrown away, keeping geometric decay. -/
theorem xiKernelQ_ge (n : ℕ) (t : ℝ) :
    Real.pi * Real.exp (2 * t) * ((n : ℝ) + 1) ≤ xiKernelQ n t := by
  unfold xiKernelQ
  dsimp only
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := one_le_cast_succ n
  have hpi := Real.pi_pos
  have hE : (0 : ℝ) < Real.exp (2 * t) := Real.exp_pos _
  have hsq : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hcoef : (0 : ℝ) < Real.pi * Real.exp (2 * t) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsq hcoef.le]

/-! ### 2. The elementary exponential bounds -/

theorem q_le_two_exp {q : ℝ} (hq : 0 ≤ q) : q ≤ 2 * Real.exp (q / 2) := by
  have h := Real.add_one_le_exp (q / 2)
  linarith

theorem q_sq_le_eight_exp {q : ℝ} (hq : 0 ≤ q) : q ^ 2 ≤ 8 * Real.exp (q / 2) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := q / 2) (by linarith)
  nlinarith [h, hq]

/-- **The uniform kernel-term majorant**, valid at every real `t`. -/
theorem kernelTerm_abs_le_exp (n : ℕ) (t : ℝ) :
    |riemannXiKernelTerm n t|
      ≤ 22 * Real.exp (t / 2) * Real.exp (-(xiKernelQ n t) / 2) := by
  set q : ℝ := xiKernelQ n t with hq
  have hq0 : 0 < q := xiKernelQ_pos n t
  have hEt : (0 : ℝ) < Real.exp (t / 2) := Real.exp_pos _
  have hEq : (0 : ℝ) < Real.exp (-q) := Real.exp_pos _
  have hbr : |2 * q ^ 2 - 3 * q| ≤ 22 * Real.exp (q / 2) := by
    have h1 := q_le_two_exp hq0.le
    have h2 := q_sq_le_eight_exp hq0.le
    have hE2 : (0 : ℝ) < Real.exp (q / 2) := Real.exp_pos _
    rw [abs_le]
    constructor <;> nlinarith [h1, h2, hq0, hE2, sq_nonneg q]
  have hsplit : Real.exp (q / 2) * Real.exp (-q) = Real.exp (-q / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [kernelTerm_q_form n t, ← hq, abs_mul, abs_mul, abs_of_nonneg hEt.le,
    abs_of_nonneg hEq.le]
  calc Real.exp (t / 2) * |2 * q ^ 2 - 3 * q| * Real.exp (-q)
      ≤ Real.exp (t / 2) * (22 * Real.exp (q / 2)) * Real.exp (-q) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbr hEt.le) hEq.le
    _ = 22 * Real.exp (t / 2) * (Real.exp (q / 2) * Real.exp (-q)) := by ring
    _ = 22 * Real.exp (t / 2) * Real.exp (-q / 2) := by rw [hsplit]

/-! ### 3. Absolute summability at every real height -/

theorem summable_kernelTerm_norm (t : ℝ) :
    Summable (fun n : ℕ => ‖riemannXiKernelTerm n t‖) := by
  set c : ℝ := Real.pi * Real.exp (2 * t) / 2 with hcdef
  have hc0 : 0 < c := by
    rw [hcdef]
    have := Real.pi_pos
    positivity
  have hbase : Summable (fun n : ℕ =>
      ((n : ℝ) + 1) ^ 0 * Real.exp (-c * ((n : ℝ) + 1))) :=
    summable_pow_exp_shift 0 hc0
  have hmaj : Summable (fun n : ℕ =>
      22 * Real.exp (t / 2) * Real.exp (-c * ((n : ℝ) + 1))) := by
    simp only [pow_zero, one_mul] at hbase
    exact hbase.mul_left _
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hmaj
  intro n
  rw [Real.norm_eq_abs]
  refine (kernelTerm_abs_le_exp n t).trans ?_
  have hstep : Real.exp (-(xiKernelQ n t) / 2) ≤ Real.exp (-c * ((n : ℝ) + 1)) := by
    refine Real.exp_le_exp.mpr ?_
    have hge := xiKernelQ_ge n t
    rw [hcdef]
    have h1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    nlinarith [hge, h1]
  have hpos : (0 : ℝ) ≤ 22 * Real.exp (t / 2) := by positivity
  exact mul_le_mul_of_nonneg_left hstep hpos

/-! ### 4. The complete theta double sum, pointwise -/

/-- **THE COMPLETE THETA DOUBLE SUM.**  Every `(n,m)` cross term, no remainder:

  `Φ(u+p)·Φ(u−p) = 16 · Σ_{(n,m)} Φ_n(u+p)·Φ_m(u−p)`.

The factor `16` is `4·4` from `riemannXiKernel = 4·Σ`. -/
theorem kernel_product_tsum (u p : ℝ) :
    riemannXiKernel (u + p) * riemannXiKernel (u - p)
      = 16 * ∑' z : ℕ × ℕ,
          riemannXiKernelTerm z.1 (u + p) * riemannXiKernelTerm z.2 (u - p) := by
  have hprod := tsum_mul_tsum_of_summable_norm
    (summable_kernelTerm_norm (u + p)) (summable_kernelTerm_norm (u - p))
  unfold riemannXiKernel
  rw [show (4 * ∑' n : ℕ, riemannXiKernelTerm n (u + p))
        * (4 * ∑' m : ℕ, riemannXiKernelTerm m (u - p))
      = 16 * ((∑' n : ℕ, riemannXiKernelTerm n (u + p))
        * ∑' m : ℕ, riemannXiKernelTerm m (u - p)) by ring, hprod]

/-- The same with the outer cosine carried inside, i.e. the exact pointwise integrand of
`C(u,x)` as a double sum of the cross terms evaluated in block A5. -/
theorem kernel_product_cos_tsum (x u p : ℝ) :
    riemannXiKernel (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
      = 16 * ∑' z : ℕ × ℕ,
          (riemannXiKernelTerm z.1 (u + p) * riemannXiKernelTerm z.2 (u - p)
            * Real.cos (2 * x * p)) := by
  rw [kernel_product_tsum u p, mul_assoc, tsum_mul_right]

/-! ### 5. Absolute summability of the cross-term family at fixed `p` -/

/-- The `(n,m)` cross-term family is absolutely summable at every `(u,p)` — the hypothesis
the sum/integral interchange consumes at each fixed `p`. -/
theorem summable_crossTerm_norm (u p : ℝ) :
    Summable (fun z : ℕ × ℕ =>
      ‖riemannXiKernelTerm z.1 (u + p) * riemannXiKernelTerm z.2 (u - p)‖) := by
  have h := (summable_kernelTerm_norm (u + p)).mul_of_nonneg
    (summable_kernelTerm_norm (u - p))
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine h.congr fun z => ?_
  rw [norm_mul]

end C3B6.Theta

section AxiomAudit
#print axioms C3B6.Theta.kernelTerm_q_form
#print axioms C3B6.Theta.xiKernelQ_ge
#print axioms C3B6.Theta.q_le_two_exp
#print axioms C3B6.Theta.q_sq_le_eight_exp
#print axioms C3B6.Theta.kernelTerm_abs_le_exp
#print axioms C3B6.Theta.summable_kernelTerm_norm
#print axioms C3B6.Theta.kernel_product_tsum
#print axioms C3B6.Theta.kernel_product_cos_tsum
#print axioms C3B6.Theta.summable_crossTerm_norm
end AxiomAudit
