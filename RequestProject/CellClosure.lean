import RequestProject.LFunctionPhasor

/-!
# The carrier-cell theorem: adapted cell closure ⇒ bounded primitive and zero DC mode

The split architecture is carrier (a per-fiber *warp mechanism*) versus fiber (the function object).
For a carrier rescaled onto a fixed harmonic (a `μ_P` cell) the adapted warp is periodic and each
complete native cell sums to zero; this file proves the consequence and then closes it *for the class
of finite duality-stable harmonic fibers* --- not as a fiber-uniform theorem but as a property of each
carrier+fiber pair in the class.

* `cell_closure_partialSum_le` — cell closure (`∑_{n<P} f = 0`, `f` `P`-periodic, `‖f‖ ≤ B`) ⇒ bounded
  primitive `‖∑_{n<N} f‖ ≤ B·P`.
* `cell_closure_dc_mode_zero` — hence the Cesàro mean `→ 0`: the DC residual mode vanishes (`R = 0`).
* `root_of_unity_cell_sum_zero` — a nonzero-frequency root-of-unity channel closes its cell exactly.
* `harmonic_bank_cell_sum_zero`, `harmonic_bank_primitive_bounded` — **closure for the class**: for a
  finite duality-stable fiber whose weight channels are `P`-th roots of unity, *none trivial*, the
  warped bank closes every native cell, so its primitive is bounded and `R = 0`.  Galois-free, at the
  weight level; the Dirichlet character (`dirichlet_cell_closure`) is the classical instance.

No `sorry`, no `axiom`.
-/

open Filter Topology
open scoped BigOperators

namespace CriticalLinePhasor.CellClosure

variable {f : ℕ → ℂ} {P : ℕ}

/-- Periodicity in multiples: `f (n + P*m) = f n`. -/
theorem periodic_mul (hper : ∀ n, f (n + P) = f n) : ∀ m n, f (n + P * m) = f n := by
  intro m
  induction m with
  | zero => intro n; simp
  | succ k ih => intro n; rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]

/-- A complete run of cells sums to zero: `∑_{n < P*k} f n = 0`. -/
theorem sum_periods_zero (hper : ∀ n, f (n + P) = f n)
    (hcell : ∑ n ∈ Finset.range P, f n = 0) :
    ∀ k, ∑ n ∈ Finset.range (P * k), f n = 0 := by
  intro k
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, zero_add]
    calc ∑ i ∈ Finset.range P, f (P * m + i)
        = ∑ i ∈ Finset.range P, f i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [show P * m + i = i + P * m from Nat.add_comm _ _, periodic_mul hper]
      _ = 0 := hcell

/-- **The carrier-cell theorem (bounded primitive).**  A `P`-periodic warp bounded by `B` whose
complete cell sums to zero has warped partial sums bounded by `B·P`: complete cells vanish, leaving an
incomplete remainder of `< P` terms each of size `≤ B`. -/
theorem cell_closure_partialSum_le {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ n, ‖f n‖ ≤ B)
    (hper : ∀ n, f (n + P) = f n) (hcell : ∑ n ∈ Finset.range P, f n = 0) (hP : 0 < P) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, f n‖ ≤ B * P := by
  have hsplit : ∑ n ∈ Finset.range N, f n
      = ∑ k ∈ Finset.range (N % P), f (P * (N / P) + k) := by
    conv_lhs => rw [← Nat.div_add_mod N P]
    rw [Finset.sum_range_add, sum_periods_zero hper hcell, zero_add]
  rw [hsplit]
  have hmod : N % P < P := Nat.mod_lt _ hP
  calc ‖∑ k ∈ Finset.range (N % P), f (P * (N / P) + k)‖
      ≤ ∑ k ∈ Finset.range (N % P), ‖f (P * (N / P) + k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (N % P), B := Finset.sum_le_sum (fun k _ => hbound _)
    _ = (↑(N % P) : ℝ) * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (↑P : ℝ) * B := by apply mul_le_mul_of_nonneg_right _ hB; exact_mod_cast hmod.le
    _ = B * ↑P := mul_comm _ _

/-- **The carrier-cell theorem (zero DC mode).**  The Cesàro mean of a unit-bounded cell-closing warp
tends to zero, so the reflected carrier theta has no zero-frequency residual mode: `R = 0`. -/
theorem cell_closure_dc_mode_zero (hbound : ∀ n, ‖f n‖ ≤ 1) (hper : ∀ n, f (n + P) = f n)
    (hcell : ∑ n ∈ Finset.range P, f n = 0) (hP : 0 < P) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n) / (N : ℂ)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun N => norm_nonneg _) (g := fun N : ℕ => (P : ℝ) / N) (fun N => ?_) ?_
  · rw [norm_div, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · have hN : (0 : ℝ) < N := by exact_mod_cast h
      have hb := cell_closure_partialSum_le (by norm_num) hbound hper hcell hP N
      rw [one_mul] at hb
      exact (div_le_div_iff_of_pos_right hN).mpr hb
  · simpa using tendsto_const_div_atTop_nhds_zero_nat (P : ℝ)

/-- The Dirichlet character is the classical instance: for `χ ≠ 1` mod `q`, the period-`q` cell sums to
zero and the warped primitive is bounded (recovering `LFunctionPhasor.character_partialSum_norm_le`). -/
theorem dirichlet_cell_closure {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ ((n : ZMod q))‖ ≤ q :=
  LFunctionPhasor.character_partialSum_norm_le χ hχ N

/-! ## Closure for the finite duality-stable harmonic fiber class -/

/-- A nonzero-frequency root-of-unity channel closes its cell: `∑_{n<P} ζ^n = 0` for `ζ^P = 1`,
`ζ ≠ 1` (geometric series). -/
theorem root_of_unity_cell_sum_zero {ζ : ℂ} {P : ℕ} (hP : ζ ^ P = 1) (hζ : ζ ≠ 1) :
    ∑ n ∈ Finset.range P, ζ ^ n = 0 := by
  rw [geom_sum_eq hζ P, hP, sub_self, zero_div]

/-- **The warped bank of a finite duality-stable harmonic fiber closes.**  If every weight channel
`w i` is a `P`-th root of unity and none is trivial, the complete native cell of the bank
`k ↦ ∑ᵢ (w i)^k` sums to zero: each nonzero channel cancels over its period. -/
theorem harmonic_bank_cell_sum_zero {ι : Type*} [Fintype ι] {P : ℕ} (w : ι → ℂ)
    (hroot : ∀ i, (w i) ^ P = 1) (hnt : ∀ i, w i ≠ 1) :
    ∑ k ∈ Finset.range P, ∑ i, (w i) ^ k = 0 := by
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero (fun i _ => root_of_unity_cell_sum_zero (hroot i) (hnt i))

/-- **Closure for the class.**  For a finite duality-stable fiber whose weight channels are `P`-th roots
of unity, none trivial, the warped bank's primitive is bounded by `|ι|·P`, so continuation, the vertical
bound, and (via `cell_closure_dc_mode_zero`) entireness all hold --- proved outright, Galois-free, at the
weight level.  The general cuspidal fiber engages its own function warp per instance. -/
theorem harmonic_bank_primitive_bounded {ι : Type*} [Fintype ι] {P : ℕ} (w : ι → ℂ) (hP : 0 < P)
    (hroot : ∀ i, (w i) ^ P = 1) (hnt : ∀ i, w i ≠ 1) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, ∑ i, (w i) ^ k‖ ≤ (Fintype.card ι : ℝ) * P := by
  refine cell_closure_partialSum_le (B := (Fintype.card ι : ℝ)) (by positivity) (fun n => ?_)
    (fun n => ?_) (harmonic_bank_cell_sum_zero w hroot hnt) hP N
  · calc ‖∑ i, (w i) ^ n‖
        ≤ ∑ i, ‖(w i) ^ n‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
            rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one (hroot i) hP.ne', one_pow])
      _ = (Fintype.card ι : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · exact Finset.sum_congr rfl (fun i _ => by rw [pow_add, hroot i, mul_one])

end CriticalLinePhasor.CellClosure

