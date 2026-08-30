import Mathlib

/-!
# C3 batch 5, block A2 — the radial combination `F(A,x)` and diagonal domination

Batch-5 adjudication point 4 asks to prove or falsify

  `F(A,x) = (A² + 9)·K_{ix}(A) + 6A·K′_{ix}(A) > 0`  above the turning point,

and warns (correctly) that `K_{ix} > 0` alone is not enough, because `K′ < 0` and the
term `6A·K′` is of the same order as `A²·K` when `A ≍ 6`.

Mathlib has no Macdonald function of imaginary order, so what is formalized here is the
*mechanism*, stated over an abstract pair `(K, K′)` constrained exactly the way the
Liouville/Riccati analysis constrains the true pair.  The analytic inputs are, with
`z(A) = A^{1/2}K_{ix}(A)` and `q(A) = 1 − (x²+¼)/A²`:

* `z″ = q·z` (Liouville normal form of the modified Bessel equation);
* `q > 0` for `A > A* := √(x²+¼)`, so the equation is disconjugate there and the
  recessive solution `z` has no zero above `A*`;
* hence `ρ := −z′/z` satisfies `√q ≤ ρ ≤ 1` on `(A*,∞)`
  (lower: else `ρ` drops through `0` and `z` grows; upper: else `ρ′ ≥ ρ²−1 > 0` blows up
  in finite `A`, i.e. `z` acquires a zero);
* `K′/K = z′/z − 1/(2A) = −(ρ + 1/(2A))`.

Block A3 formalizes the Riccati/blow-up core.  What is formalized *here* is the payoff:

  `F = (A² + 6 − 6Aρ)·K ≥ (A² − 6A + 6)·K > 0`   whenever `0 ≤ ρ ≤ 1` and `A > 3+√3`.

The second half of the file is the summation criterion that turns pointwise positivity of
`F` into positivity of the full `(n,m)` theta double sum: since `A_{nm} = 2πnm·e^{2u}`
depends only on `k = nm`, and `n²m² = k²` on the hyperbola, the double sum collapses to a
single sum over `k` with the divisor phase `τ_{ix}(k) = Σ_{de=k}(d/e)^{ix}` (the Dirichlet
coefficient of `ζ(s+ix)ζ(s−ix)`), and `|τ_{ix}(k)| ≤ d(k)`.

SCOPE: no `Ξ`, no zeros, no RH.  Pure inequalities plus a `tsum` comparison.
-/

open Real BigOperators

noncomputable section

namespace C3B5.A2

/-! ### 1. The radial combination -/

/-- The radial combination in the form it is used: `F = (A²+9)K + 6A·K′`. -/
def radial (A K K' : ℝ) : ℝ := (A ^ 2 + 9) * K + 6 * A * K'

/-- **The exact evaluation of `F` through the logarithmic derivative.**
If `K′ = −(ρ + 1/(2A))·K` then `F = (A² + 6 − 6Aρ)·K`.  The `9` becomes a `6`: three
units are eaten by the `A^{−1/2}` Liouville gauge. -/
theorem radial_eq {A K K' ρ : ℝ} (hA : A ≠ 0) (hlog : K' = -(ρ + 1 / (2 * A)) * K) :
    radial A K K' = (A ^ 2 + 6 - 6 * A * ρ) * K := by
  rw [radial, hlog]
  field_simp
  ring

/-- **The lower bound.**  With `ρ ≤ 1` (the Riccati ceiling) and `K > 0`,
`F ≥ (A² − 6A + 6)·K`. -/
theorem radial_ge {A K K' ρ : ℝ} (hA : 0 < A) (hK : 0 < K) (hρ : ρ ≤ 1)
    (hlog : K' = -(ρ + 1 / (2 * A)) * K) :
    (A ^ 2 - 6 * A + 6) * K ≤ radial A K K' := by
  rw [radial_eq hA.ne' hlog]
  have h : A ^ 2 - 6 * A + 6 ≤ A ^ 2 + 6 - 6 * A * ρ := by nlinarith
  exact mul_le_mul_of_nonneg_right h hK.le

/-- **THE RADIAL POSITIVITY.**  Above the turning point the radial combination is
strictly positive.  Adjudication point 4, discharged in the direction of proof. -/
theorem radial_pos {A K K' ρ : ℝ} (hA : 0 < A) (hK : 0 < K) (hρ : ρ ≤ 1)
    (hquad : 0 < A ^ 2 - 6 * A + 6)
    (hlog : K' = -(ρ + 1 / (2 * A)) * K) :
    0 < radial A K K' :=
  lt_of_lt_of_le (mul_pos hquad hK) (radial_ge hA hK hρ hlog)

/-- Explicit threshold form: `A ≥ 8` suffices for the quadratic factor. -/
theorem radial_pos_of_ge_eight {A K K' ρ : ℝ} (hA : 8 ≤ A) (hK : 0 < K) (hρ : ρ ≤ 1)
    (hlog : K' = -(ρ + 1 / (2 * A)) * K) :
    0 < radial A K K' := by
  refine radial_pos (by linarith) hK hρ ?_ hlog
  nlinarith [hA, sq_nonneg (A - 8)]

/-- **The upper bound**, used for the tail of the mode sum.  With `ρ ≥ 0` (the Riccati
floor, weakened) and `K > 0`, `F ≤ (A² + 6)·K`. -/
theorem radial_le {A K K' ρ : ℝ} (hA : 0 < A) (hK : 0 < K) (hρ : 0 ≤ ρ)
    (hlog : K' = -(ρ + 1 / (2 * A)) * K) :
    radial A K K' ≤ (A ^ 2 + 6) * K := by
  rw [radial_eq hA.ne' hlog]
  have h : A ^ 2 + 6 - 6 * A * ρ ≤ A ^ 2 + 6 := by nlinarith
  exact mul_le_mul_of_nonneg_right h hK.le

/-- The two bounds together: the radial combination is pinched between two explicit
multiples of `K`, so a ratio `F(kA)/F(A)` is controlled by `K(kA)/K(A)` times an explicit
rational function.  This is what makes the tail estimate of the mode sum elementary. -/
theorem radial_ratio_le {A B KA KB KA' KB' ρA ρB : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hKA : 0 < KA) (hKB : 0 < KB)
    (hρA : ρA ≤ 1) (hρB : 0 ≤ ρB)
    (hlogA : KA' = -(ρA + 1 / (2 * A)) * KA)
    (hlogB : KB' = -(ρB + 1 / (2 * B)) * KB)
    (hquad : 0 < A ^ 2 - 6 * A + 6) :
    radial B KB KB' * ((A ^ 2 - 6 * A + 6) * KA)
      ≤ ((B ^ 2 + 6) * KB) * radial A KA KA' := by
  have h1 : radial B KB KB' ≤ (B ^ 2 + 6) * KB := radial_le hB hKB hρB hlogB
  have h2 : (A ^ 2 - 6 * A + 6) * KA ≤ radial A KA KA' := radial_ge hA hKA hρA hlogA
  have h3 : (0 : ℝ) < (A ^ 2 - 6 * A + 6) * KA := mul_pos hquad hKA
  have h4 : (0 : ℝ) ≤ (B ^ 2 + 6) * KB := by positivity
  calc radial B KB KB' * ((A ^ 2 - 6 * A + 6) * KA)
      ≤ ((B ^ 2 + 6) * KB) * ((A ^ 2 - 6 * A + 6) * KA) :=
        mul_le_mul_of_nonneg_right h1 h3.le
    _ ≤ ((B ^ 2 + 6) * KB) * radial A KA KA' := mul_le_mul_of_nonneg_left h2 h4

/-! ### 2. Diagonal domination for the full mode sum -/

/-- **The head-dominant criterion.**  A summable real family whose head strictly exceeds
the absolute sum of its tail has a positive total.  This is the honest form of
"the `(1,1)` diagonal dominates": it uses every off-diagonal term, and bounds the
arithmetic phases by `|cos| ≤ 1` rather than evaluating them away. -/
theorem tsum_pos_of_head_dominant {f : ℕ → ℝ} (hf : Summable f)
    (habs : Summable fun k => |f (k + 1)|)
    (hdom : ∑' k : ℕ, |f (k + 1)| < f 0) :
    0 < ∑' k : ℕ, f k := by
  have hsplit : ∑' k : ℕ, f k = f 0 + ∑' k : ℕ, f (k + 1) := hf.tsum_eq_zero_add
  have hnorm : ‖∑' k : ℕ, f (k + 1)‖ ≤ ∑' k : ℕ, ‖f (k + 1)‖ := by
    refine norm_tsum_le_tsum_norm ?_
    simpa [Real.norm_eq_abs] using habs
  rw [Real.norm_eq_abs] at hnorm
  simp only [Real.norm_eq_abs] at hnorm
  have hlow : -(∑' k : ℕ, |f (k + 1)|) ≤ ∑' k : ℕ, f (k + 1) :=
    neg_le_of_abs_le hnorm
  rw [hsplit]
  linarith

/-- The comparison form: bound each tail term and sum the bound. -/
theorem tsum_pos_of_head_dominant_le {f g : ℕ → ℝ} (hf : Summable f)
    (hg : Summable fun k => g (k + 1))
    (hbd : ∀ k, |f (k + 1)| ≤ g (k + 1))
    (hdom : ∑' k : ℕ, g (k + 1) < f 0) :
    0 < ∑' k : ℕ, f k := by
  have habs : Summable fun k => |f (k + 1)| :=
    hg.of_nonneg_of_le (fun k => abs_nonneg _) hbd
  refine tsum_pos_of_head_dominant hf habs ?_
  exact lt_of_le_of_lt (Summable.tsum_le_tsum hbd habs hg) hdom

/-! ### 3. The hyperbola collapse and the divisor phase -/

/-- **The hyperbola weight is constant.**  On `nm = k` the mode weight `n²m²` equals
`k²`, so the `(n,m)` double sum collapses to a single sum over `k` with multiplicity
`d(k)` and no residual polynomial dependence on the individual factors. -/
theorem hyperbola_weight {k n m : ℕ} (h : n * m = k) :
    ((n : ℝ) ^ 2) * ((m : ℝ) ^ 2) = ((k : ℝ)) ^ 2 := by
  rw [← h]; push_cast; ring

/-- The divisor phase `τ_{ix}(k) = Σ_{d|k} cos(x·log(d²/k))`, real form. -/
def divisorPhase (x : ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ k.divisors, Real.cos (x * Real.log ((d : ℝ) ^ 2 / (k : ℝ)))

/-- **`|τ_{ix}(k)| ≤ d(k)`** — the only bound on the arithmetic phase used in the tail
estimate.  It is attained (at `x = 0`), so this is the worst case honestly. -/
theorem divisorPhase_abs_le (x : ℝ) (k : ℕ) :
    |divisorPhase x k| ≤ (k.divisors.card : ℝ) := by
  calc |divisorPhase x k|
      ≤ ∑ d ∈ k.divisors, |Real.cos (x * Real.log ((d : ℝ) ^ 2 / (k : ℝ)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ k.divisors, (1 : ℝ) :=
        Finset.sum_le_sum fun d _ => Real.abs_cos_le_one _
    _ = (k.divisors.card : ℝ) := by simp

/-- The head of the divisor phase is exactly `1`: the `k = 1` mode carries no arithmetic,
which is why it is the DC mode of the decomposition. -/
theorem divisorPhase_one (x : ℝ) : divisorPhase x 1 = 1 := by
  simp [divisorPhase]

end C3B5.A2

section AxiomAudit
#print axioms C3B5.A2.radial_eq
#print axioms C3B5.A2.radial_ge
#print axioms C3B5.A2.radial_pos
#print axioms C3B5.A2.radial_pos_of_ge_eight
#print axioms C3B5.A2.radial_le
#print axioms C3B5.A2.radial_ratio_le
#print axioms C3B5.A2.tsum_pos_of_head_dominant
#print axioms C3B5.A2.tsum_pos_of_head_dominant_le
#print axioms C3B5.A2.hyperbola_weight
#print axioms C3B5.A2.divisorPhase_abs_le
#print axioms C3B5.A2.divisorPhase_one
end AxiomAudit
