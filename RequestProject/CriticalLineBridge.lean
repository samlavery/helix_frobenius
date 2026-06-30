import RequestProject.LFunctionPhasor

/-!
# Critical-line bridge lemmas

This file packages the already-established analytic channel (the Abel/Dirichlet strip
convergence `dirichlet_strip_tendsto_LFunction`) into the *zero-statement* form requested,
and records the elementary algebraic and geometric bridge facts that sit immediately above it
in the proof chain:

1. **Zero packaging** (`criticalLine_phasor_closure_iff_L_zero`):
   on the critical line `s = 1/2 + i t`, the value `LFunction χ (1/2 + i t)` vanishes
   **iff** the Abel/Dirichlet phasor partial sums tend to `0`.  This is a direct consequence of
   `dirichlet_strip_tendsto_LFunction` together with uniqueness of limits.

2. **Lane split** (`character_lane_split`, `quadratic_phasor_lane_split`):
   for a character taking values in `{0, +1, -1}` the weighted partial sum is the
   *positive lane* minus the *negative lane*, with the neutral (`χ n = 0`) terms contributing
   nothing.  Consequently `L`-vanishing is equivalent to the two lanes having equal Abel limits
   (`L_zero_iff_lane_limits_eq`).

3. **`π/3` exact six-cell carrier closure** (`pi_over_three_cell_periodic`,
   `pi_over_three_six_cell_closure`): the carrier phase `(π/3)·n` is exactly `2π`-periodic
   with period `6`, i.e. `6 · (π/3) = 2π`, so `exp(I·(π/3)·(n+6)) = exp(I·(π/3)·n)`.

These are the *provable* lower rungs of the requested chain.  The deeper spectral bridges
(admissible rank-drop ⇔ self-adjoint eigenheight, and reality of the eigenheight) are **not**
asserted here, because under the requested reading they would amount to a proof of the
Generalized Riemann Hypothesis; see `REVIEW.md` for the honest status discussion.

Everything below is `Mathlib`-only and `sorry`/`axiom`-free.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace CriticalLinePhasor.Bridge

open CriticalLinePhasor CriticalLinePhasor.LFunctionPhasor

/-! ## 1. Zero packaging: `L = 0` ⇔ Abel phasor closure -/

/-
**Critical-line zero packaging.**  For a non-principal Dirichlet character `χ` mod `q`, the
value of the `L`-function at the critical-line point `1/2 + i t` is zero **iff** the
Abel/Dirichlet phasor partial sums close (tend to `0`).  Immediate from the strip convergence
`dirichlet_strip_tendsto_LFunction` and uniqueness of limits.
-/
theorem criticalLine_phasor_closure_iff_L_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t : ℂ) * I) = 0
    ↔
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        χ (n : ZMod q) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I)))
      atTop (nhds 0) := by
  have h := CriticalLinePhasor.LFunctionPhasor.dirichlet_strip_tendsto_LFunction χ hχ ( show 0 < ( 1 / 2 + t * I |> Complex.re ) by norm_num ) ; simp_all +decide ;
  exact ⟨ fun h' => by simpa [ h' ] using h, fun h' => tendsto_nhds_unique h h' ⟩

/-! ## 2. Positive / negative lane split -/

/-
**Lane split for a `{0, ±1}`-valued weight.**  If `χ` only takes the values `0`, `1`, `-1`,
then any weighted finite sum splits as the *positive lane* (terms with `χ n = 1`) minus the
*negative lane* (terms with `χ n = -1`); the neutral terms (`χ n = 0`) drop out.
-/
theorem character_lane_split (χ : ℕ → ℂ) (a : ℕ → ℂ)
    (hχ : ∀ n, χ n = 0 ∨ χ n = 1 ∨ χ n = -1) (s : Finset ℕ) :
    ∑ n ∈ s, χ n * a n
      = (∑ n ∈ s.filter (fun n => χ n = 1), a n)
        - (∑ n ∈ s.filter (fun n => χ n = -1), a n) := by
  rw [ Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_sub_distrib ] ; congr ; ext x ; rcases hχ x with h | h | h <;> simp +decide [ h ] ;
  · norm_num;
  · norm_num

/-
**Phasor lane split** on the critical line `s = 1/2 + i t`: the Dirichlet partial sum equals
the positive lane minus the negative lane of the phasor terms, for a character whose values lie
in `{0, ±1}` (e.g. a real / quadratic Dirichlet character).
-/
theorem quadratic_phasor_lane_split
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : ∀ n : ℕ, (χ (n : ZMod q) : ℂ) = 0 ∨ (χ (n : ZMod q) : ℂ) = 1 ∨ (χ (n : ZMod q) : ℂ) = -1)
    (t : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        χ (n : ZMod q) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I)))
      = (∑ n ∈ (Finset.range N).filter (fun n : ℕ => (χ (n : ZMod q) : ℂ) = 1),
            (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I)))
        - (∑ n ∈ (Finset.range N).filter (fun n : ℕ => (χ (n : ZMod q) : ℂ) = -1),
            (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I))) := by
  convert character_lane_split ( fun n : ℕ => ( χ n : ℂ ) ) ( fun n : ℕ => ( n : ℂ ) ^ ( - ( 1 / 2 + t * I ) ) ) ( fun n => ?_ ) ( Finset.range N ) using 1;
  exact hχ n

/-
**`L`-vanishing ⇔ equal lane limits.**  Combining the zero packaging with the lane split:
for a `{0, ±1}`-valued character, `L(1/2 + i t) = 0` iff the positive and negative lane partial
sums have the same Abel limit.
-/
theorem L_zero_iff_lane_limits_eq
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hval : ∀ n : ℕ, (χ (n : ZMod q) : ℂ) = 0 ∨ (χ (n : ZMod q) : ℂ) = 1 ∨ (χ (n : ZMod q) : ℂ) = -1)
    (t : ℝ) (ℓ : ℂ) :
    (DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t : ℂ) * I) = 0
      ∧ Tendsto (fun N : ℕ => ∑ n ∈ (Finset.range N).filter (fun n : ℕ => (χ (n : ZMod q) : ℂ) = 1),
            (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I))) atTop (nhds ℓ))
    ↔
    (Tendsto (fun N : ℕ => ∑ n ∈ (Finset.range N).filter (fun n : ℕ => (χ (n : ZMod q) : ℂ) = 1),
            (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I))) atTop (nhds ℓ)
      ∧ Tendsto (fun N : ℕ => ∑ n ∈ (Finset.range N).filter (fun n : ℕ => (χ (n : ZMod q) : ℂ) = -1),
            (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I))) atTop (nhds ℓ)) := by
  constructor <;> intro h;
  · have h_neg : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, χ n * (n : ℂ) ^ (-(1 / 2 + t * I))) Filter.atTop (nhds 0) := by
      convert criticalLine_phasor_closure_iff_L_zero χ hχ t |>.1 h.1 using 1;
    have h_neg : Filter.Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, χ n * (n : ℂ) ^ (-(1 / 2 + t * I))) - (∑ n ∈ Finset.range N, if χ n = 1 then (n : ℂ) ^ (-(1 / 2 + t * I)) else 0)) Filter.atTop (nhds (-ℓ)) := by
      convert h_neg.sub h.2 using 2 ; norm_num [ Finset.sum_ite ];
      ring;
    have h_neg : Filter.Tendsto (fun N : ℕ => -∑ n ∈ Finset.range N, if χ n = -1 then (n : ℂ) ^ (-(1 / 2 + t * I)) else 0) Filter.atTop (nhds (-ℓ)) := by
      convert h_neg using 2 ; norm_num [ Finset.sum_ite ] ; ring;
      rw [ Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_neg_distrib ] ; rw [ ← Finset.sum_sub_distrib ] ; congr ; ext ; rcases hval ‹_› with h | h | h <;> norm_num [ h ] ;
    exact ⟨ h.2, by simpa [ Finset.sum_filter ] using h_neg.neg ⟩;
  · convert criticalLine_phasor_closure_iff_L_zero χ hχ t |>.2 _ using 1;
    · grind +qlia;
    · convert h.1.sub h.2 using 2 ; norm_num [ quadratic_phasor_lane_split ];
      · rw [ Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_sub_distrib ] ; congr ; ext ; rcases hval ‹_› with h | h | h <;> norm_num [ h ] ;
      · ring

/-! ## 3. Exact `π/3` six-cell carrier closure -/

/-
The carrier phase steps by `π/3`; after `6` cells it advances by exactly one full turn
`2π`.  Hence the carrier is `6`-periodic: `exp(I·(π/3)·(n+6)) = exp(I·(π/3)·n)`.
-/
theorem pi_over_three_cell_periodic (n : ℝ) :
    Complex.exp (I * ((Real.pi / 3) * (n + 6))) = Complex.exp (I * ((Real.pi / 3) * n)) := by
  convert Complex.exp_periodic _ using 2 ; ring

/-
Integer form of the six-cell closure.
-/
theorem pi_over_three_six_cell_closure (n : ℤ) :
    Complex.exp (I * ((Real.pi / 3) * ((n : ℝ) + 6)))
      = Complex.exp (I * ((Real.pi / 3) * (n : ℝ))) := by
  convert pi_over_three_cell_periodic ( n : ℝ ) using 1

end CriticalLinePhasor.Bridge