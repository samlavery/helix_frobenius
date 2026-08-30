import c3b18_A2

/-!
# C3 batch 18, block A3 — the exact double-sum inequality that remains for `Φ`

The open input is `xiKernel_log_concaveOn`.  In midpoint form (equivalent to `ConcaveOn` for
a continuous positive function) it reads, with `a_n(t) := riemannXiKernelTerm n t`:

  `Φ(t)² − Φ(t−h)Φ(t+h) ≥ 0`,   i.e.   `(Σ a_n(t))² − (Σ a_n(t−h))(Σ a_n(t+h)) ≥ 0`.

This block compiles the **exact algebraic decomposition** of that quantity into a diagonal
part and an off-diagonal part, so the remaining obligation is stated precisely rather than
gestured at:

  `(Σa)² − (Σb)(Σc) = Σ_n (a_n² − b_n c_n)  +  Σ_n Σ_{m ≠ n} (a_n a_m − b_n c_m)`.

* the **diagonal** `a_n² − b_n c_n` is `≥ 0` term by term — that is exactly the repository's
  compiled `riemannXiKernelTerm_log_strictConcaveOn` (per-summand log-concavity on `Ici 0`);
* the **off-diagonal** is **not** `≥ 0`: measured **33/36 violations** of the cross-pair
  inequality `2a_n a_m ≥ b_n c_m + b_m c_n` (§T4).  For log-linear terms `e^{αt}, e^{βt}` with
  `α ≠ β` the cross term is `2e^{(α+β)t}cosh((β−α)h) > 2e^{(α+β)t}`, so it is false in
  general — this is precisely why a sum of log-concave functions need not be log-concave, and
  why the per-term theorem **cannot** be used as a mixture theorem.

**So the whole remaining content is that the diagonal surplus dominates the off-diagonal
deficit.**  Measured (§T3, split verified against the direct value to `reldiff ≤ 1.5e−51`):

| `t` | `h` | DIAG | OFF | ratio `|OFF|/DIAG` |
|---|---|---|---|---|
| 0.1 | 0.3 | `2.2551e+00` | `−3.0737e−02` | `1.4e−2` |
| 0.4 | 0.3 | `1.1125e−01` | `−1.8358e−06` | `1.6e−5` |
| 0.8 | 0.3 | `2.0738e−07` | `−8.5933e−20` | `4.1e−13` |
| 1.2 | 0.05 | `6.8297e−23` | `−4.0829e−62` | `6.0e−40` |

The margin is enormous and grows with `t`; the tight region is small `t`.

**What is NOT compiled here, named:** the passage from these `Finset` identities to the
infinite sums needs summability of the double series, and the passage from midpoint
log-concavity to `ConcaveOn` needs continuity of `Φ` on the whole line (the repository has
`riemannXiKernel_continuousOn` on `Ici 0` only).  Neither is formalised.

SCOPE: two Finset identities and the assembled reduction.  No analysis, no kernel-specific
claim, and nothing target-shaped.
-/

open Finset

noncomputable section

namespace C3B18

/-! ### 1. Product of sums is the double sum -/

theorem prod_sum_sub_eq_double (s : Finset ℕ) (a b c : ℕ → ℝ) :
    (∑ n ∈ s, a n) * (∑ n ∈ s, a n) - (∑ n ∈ s, b n) * (∑ n ∈ s, c n)
      = ∑ n ∈ s, ∑ m ∈ s, (a n * a m - b n * c m) := by
  have h1 : (∑ n ∈ s, a n) * (∑ n ∈ s, a n) = ∑ n ∈ s, ∑ m ∈ s, a n * a m :=
    Finset.sum_mul_sum s s a a
  have h2 : (∑ n ∈ s, b n) * (∑ n ∈ s, c n) = ∑ n ∈ s, ∑ m ∈ s, b n * c m :=
    Finset.sum_mul_sum s s b c
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_sub_distrib]

/-! ### 2. Diagonal / off-diagonal split -/

theorem double_sum_diag_offdiag (s : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ n ∈ s, ∑ m ∈ s, f n m)
      = (∑ n ∈ s, f n n) + ∑ n ∈ s, ∑ m ∈ s.erase n, f n m := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [← Finset.add_sum_erase s (f n) hn]

/-! ### 3. THE ASSEMBLED REDUCTION -/

/-- **THE EXACT REMAINING INEQUALITY.**  The midpoint quantity is nonnegative as soon as the
diagonal surplus dominates the off-diagonal deficit.  Both sides are explicit finite sums in
the theta modes; nothing here is about `Rker`, `cosMom`, or any zero. -/
theorem midpoint_nonneg_of_diag_dominates (s : Finset ℕ) (a b c : ℕ → ℝ)
    (h : 0 ≤ (∑ n ∈ s, (a n * a n - b n * c n))
            + ∑ n ∈ s, ∑ m ∈ s.erase n, (a n * a m - b n * c m)) :
    0 ≤ (∑ n ∈ s, a n) * (∑ n ∈ s, a n) - (∑ n ∈ s, b n) * (∑ n ∈ s, c n) := by
  rw [prod_sum_sub_eq_double s a b c,
    double_sum_diag_offdiag s (fun n m => a n * a m - b n * c m)]
  exact h

/-- The same, split so the two contributions are separately visible: a nonnegative diagonal
and an off-diagonal that must not undo it. -/
theorem midpoint_nonneg_of_diag_ge_offdiag (s : Finset ℕ) (a b c : ℕ → ℝ)
    (_hdiag : ∀ n ∈ s, 0 ≤ a n * a n - b n * c n)
    (hoff : -(∑ n ∈ s, (a n * a n - b n * c n))
            ≤ ∑ n ∈ s, ∑ m ∈ s.erase n, (a n * a m - b n * c m)) :
    0 ≤ (∑ n ∈ s, a n) * (∑ n ∈ s, a n) - (∑ n ∈ s, b n) * (∑ n ∈ s, c n) := by
  refine midpoint_nonneg_of_diag_dominates s a b c ?_
  linarith [hoff]

/-- The diagonal is nonnegative exactly when each term is midpoint log-concave — which is
what `riemannXiKernelTerm_log_strictConcaveOn` delivers on `Ici 0`.  Recorded so the split's
first half is visibly already available. -/
theorem diag_nonneg_of_termwise (s : Finset ℕ) (a b c : ℕ → ℝ)
    (hterm : ∀ n ∈ s, b n * c n ≤ a n * a n) :
    0 ≤ ∑ n ∈ s, (a n * a n - b n * c n) := by
  refine Finset.sum_nonneg fun n hn => ?_
  linarith [hterm n hn]

end C3B18

section AxiomAudit
#print axioms C3B18.prod_sum_sub_eq_double
#print axioms C3B18.double_sum_diag_offdiag
#print axioms C3B18.midpoint_nonneg_of_diag_dominates
#print axioms C3B18.midpoint_nonneg_of_diag_ge_offdiag
#print axioms C3B18.diag_nonneg_of_termwise
end AxiomAudit
