import Mathlib
import RequestProject.GlobalHelixClebschGordanBank

/-!
# Sym² coefficient identification — the local (prime-power) layer of the r = 2 rung

At unit-determinant Satake `diag(α, α⁻¹)` (`α ≠ 0`), the seed coefficients
`seedCoeff α k = tr Sym^k diag(α, α⁻¹) = U_k` and the Sym²-bank coefficients
`sym2Coeff α k = h_k(α², 1, α⁻²) = tr Sym^k` of the rank-3 Sym²-Satake
`diag(α², 1, α⁻²)` satisfy, exactly and for every `k`:

* `seedCoeff_rec` — the Chebyshev recurrence
  `U_{k+2} = (α + α⁻¹)·U_{k+1} − U_k`.
* `sym2Coeff_rec` — the 3-variable complete-homogeneous recurrence
  `h_{k+3} = e₁·h_{k+2} − e₂·h_{k+1} + e₃·h_k` where, at the weights
  `(α², 1, α⁻²)`, the elementary symmetric functions collapse:
  `e₁ = e₂ = α² + 1 + α⁻²` and `e₃ = 1` (`sym2_elementary_collapse`).
* `seedCoeff_sq_succ` / `seedCoeff_sq` — **the square law**:
  `U_k² = h_k + h_{k-1}` for `1 ≤ k`, and `U_0² = h_0` (`seedCoeff_sq_zero`).
* `sym2Coeff_eq_sum_peeled` — **the peel + squares-redilation form**: with
  `peeled α k := U_k² − U_{k-1}²` (`peeled α 0 := 1`), the Sym² coefficients are

    `h_k = ∑_{m ≤ k/2} peeled α (k − 2m)`.

  In local Dirichlet-polynomial language at a prime `p` this says exactly: the
  Sym² local bank coefficients ARE the squares-dilation (the `m`-sum, i.e.
  multiplication by the local `ζ(2s)`-factor `∑_m p^{-2ms}`) of the Möbius peel
  (the first difference `peeled`, i.e. multiplication by the local
  `1/ζ(2s)`-factor `1 − p^{-2s}`) of the squared seed coefficients.  The
  difference form of the peel is `sym2Coeff_localZetaPeel`:
  `h_{k+2} − h_k = U_{k+2}² − U_{k+1}²`.
* `seedCoeff_eq_clockWeight_sum` / `sym2Coeff_eq_clockWeight_homogeneous` — the
  identification with the repo's literal clock-bank weights: `seedCoeff α k` is
  the sum of the `Sym^k` clock string `GlobalHelix.symClockWeight k α ·`, and
  `sym2Coeff α k` is the complete homogeneous sum of the three rank-3 weights
  `GlobalHelix.symClockWeight 2 α {0,1,2} = (α², 1, α⁻²)`.

Everything here is an unconditional finite algebraic identity — finite-sum
telescoping, reindexing, and strong induction; no analysis, no L-function.

**Scope.** This file proves the local (prime-power, identity-class) layer of the
r = 2 coefficient identification only.  The global assembly under Hecke
multiplicativity and the analytic (Mellin-layer) wiring are not proven in this
file.
-/

open Finset

namespace CriticalLinePhasor.Sym2Identification

/-- The seed coefficient at prime-power level `k`: the trace of `Sym^k` of the
unit-determinant Satake class `diag(α, α⁻¹)` — the Chebyshev value `U_k`. -/
noncomputable def seedCoeff (α : ℂ) (k : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (k + 1), α ^ ((k : ℤ) - 2 * (i : ℤ))

/-- The Sym²-bank coefficient at prime-power level `k`: the complete homogeneous
`h_k(α², 1, α⁻²)` — the trace of `Sym^k` of the rank-3 Sym²-Satake
`diag(α², 1, α⁻²)`. -/
noncomputable def sym2Coeff (α : ℂ) (k : ℕ) : ℂ :=
  ∑ a ∈ Finset.range (k + 1), ∑ c ∈ Finset.range (k + 1 - a),
    α ^ (2 * ((a : ℤ) - (c : ℤ)))

@[simp] theorem seedCoeff_zero (α : ℂ) : seedCoeff α 0 = 1 := by
  simp [seedCoeff]

@[simp] theorem sym2Coeff_zero (α : ℂ) : sym2Coeff α 0 = 1 := by
  simp [sym2Coeff]

/-- Squares through `zpow`: `(α²)^m = α^(2m)` for every integer `m`. -/
private theorem sq_zpow (α : ℂ) (m : ℤ) : (α ^ 2) ^ m = α ^ (2 * m) := by
  rw [← zpow_natCast α 2, ← zpow_mul]
  norm_num

/-- **T0, seed layer** — the Chebyshev recurrence of the seed coefficients:
`U_{k+2} = (α + α⁻¹)·U_{k+1} − U_k`, by finite-sum telescoping. -/
theorem seedCoeff_rec (α : ℂ) (hα : α ≠ 0) (k : ℕ) :
    seedCoeff α (k + 2) = (α + α⁻¹) * seedCoeff α (k + 1) - seedCoeff α k := by
  have hmul : (α + α⁻¹) * seedCoeff α (k + 1)
      = (∑ i ∈ Finset.range (k + 2), α ^ (((k + 2 : ℕ) : ℤ) - 2 * (i : ℤ)))
        + ∑ i ∈ Finset.range (k + 2), α ^ (((k : ℕ) : ℤ) - 2 * (i : ℤ)) := by
    unfold seedCoeff
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ((k + 2 : ℕ) : ℤ) - 2 * (i : ℤ)
        = (((k + 1 : ℕ) : ℤ) - 2 * (i : ℤ)) + 1 := by push_cast; ring
    have h2 : ((k : ℕ) : ℤ) - 2 * (i : ℤ)
        = (((k + 1 : ℕ) : ℤ) - 2 * (i : ℤ)) - 1 := by push_cast; ring
    rw [h1, h2, zpow_add_one₀ hα, zpow_sub_one₀ hα]
    ring
  have htop : seedCoeff α (k + 2)
      = (∑ i ∈ Finset.range (k + 2), α ^ (((k + 2 : ℕ) : ℤ) - 2 * (i : ℤ)))
        + α ^ (((k : ℕ) : ℤ) - 2 * (((k + 1 : ℕ)) : ℤ)) := by
    unfold seedCoeff
    rw [Finset.sum_range_succ]
    congr 1
    congr 1
    push_cast
    ring
  have hbot : (∑ i ∈ Finset.range (k + 2), α ^ (((k : ℕ) : ℤ) - 2 * (i : ℤ)))
      = seedCoeff α k + α ^ (((k : ℕ) : ℤ) - 2 * (((k + 1 : ℕ)) : ℤ)) := by
    unfold seedCoeff
    rw [Finset.sum_range_succ]
  rw [htop, hmul, hbot]
  ring

/-- One rung of the triangle: `h_{k+1} = h_k + s_{k+1}` where
`s_j := seedCoeff (α²) j` is the two-variable homogeneous string
`h_j(α², α⁻²)` in the squared clock — grouping the triangle `a + c ≤ k + 1`
by total degree.  Unconditional, no `α ≠ 0` needed (pure reindexing). -/
theorem sym2Coeff_succ (α : ℂ) (k : ℕ) :
    sym2Coeff α (k + 1) = sym2Coeff α k + seedCoeff (α ^ 2) (k + 1) := by
  have hdiag : (∑ a ∈ Finset.range (k + 2),
        α ^ (2 * ((a : ℤ) - ((k + 1 - a : ℕ) : ℤ))))
      = seedCoeff (α ^ 2) (k + 1) := by
    unfold seedCoeff
    rw [← Finset.sum_range_reflect
      (fun i => (α ^ 2) ^ (((k + 1 : ℕ) : ℤ) - 2 * (i : ℤ))) (k + 2)]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : a < k + 2 := Finset.mem_range.mp ha
    rw [sq_zpow]
    congr 1
    omega
  have hstep : ∀ a ∈ Finset.range (k + 1),
      (∑ c ∈ Finset.range (k + 1 + 1 - a), α ^ (2 * ((a : ℤ) - (c : ℤ))))
        = (∑ c ∈ Finset.range (k + 1 - a), α ^ (2 * ((a : ℤ) - (c : ℤ))))
          + α ^ (2 * ((a : ℤ) - ((k + 1 - a : ℕ) : ℤ))) := by
    intro a ha
    have ha' : a < k + 1 := Finset.mem_range.mp ha
    rw [show k + 1 + 1 - a = (k + 1 - a) + 1 from by omega, Finset.sum_range_succ]
  have hjoin : (∑ a ∈ Finset.range (k + 1),
        α ^ (2 * ((a : ℤ) - ((k + 1 - a : ℕ) : ℤ))))
        + α ^ (2 * (((k + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)))
      = ∑ a ∈ Finset.range (k + 2),
        α ^ (2 * ((a : ℤ) - ((k + 1 - a : ℕ) : ℤ))) := by
    conv_rhs => rw [Finset.sum_range_succ]
    congr 2
    omega
  unfold sym2Coeff
  rw [Finset.sum_range_succ]
  rw [show k + 1 + 1 - (k + 1) = 1 from by omega, Finset.sum_range_one]
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  linear_combination hjoin + hdiag

/-- The triangle resummation: `h_k = ∑_{j ≤ k} s_j` — the Sym² coefficient is
the partial sum of the squared-clock seed strings. -/
theorem sym2Coeff_eq_sum_seedCoeff (α : ℂ) (k : ℕ) :
    sym2Coeff α k = ∑ j ∈ Finset.range (k + 1), seedCoeff (α ^ 2) j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sym2Coeff_succ, ih]
    exact (Finset.sum_range_succ _ _).symm

/-- **T0, Sym² layer** — the 3-variable complete-homogeneous recurrence at the
weights `(α², 1, α⁻²)`:

  `h_{k+3} = e₁·h_{k+2} − e₂·h_{k+1} + e₃·h_k`,

where the elementary symmetric functions collapse to `e₁ = e₂ = α² + 1 + α⁻²`
and `e₃ = 1` — both middle coefficients carry the SAME weight, and the
constant coefficient is unit (unit determinant of the Sym²-Satake). -/
theorem sym2Coeff_rec (α : ℂ) (hα : α ≠ 0) (k : ℕ) :
    sym2Coeff α (k + 3)
      = (α ^ 2 + 1 + (α⁻¹) ^ 2) * sym2Coeff α (k + 2)
        - (α ^ 2 + 1 + (α⁻¹) ^ 2) * sym2Coeff α (k + 1) + sym2Coeff α k := by
  have h2 : (α : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hα
  have hs : seedCoeff (α ^ 2) (k + 3)
      = (α ^ 2 + (α⁻¹) ^ 2) * seedCoeff (α ^ 2) (k + 2)
        - seedCoeff (α ^ 2) (k + 1) := by
    have h := seedCoeff_rec (α ^ 2) h2 (k + 1)
    rw [← inv_pow] at h
    exact h
  have e1 : sym2Coeff α (k + 1) = sym2Coeff α k + seedCoeff (α ^ 2) (k + 1) :=
    sym2Coeff_succ α k
  have e2 : sym2Coeff α (k + 2) = sym2Coeff α (k + 1) + seedCoeff (α ^ 2) (k + 2) :=
    sym2Coeff_succ α (k + 1)
  have e3 : sym2Coeff α (k + 3) = sym2Coeff α (k + 2) + seedCoeff (α ^ 2) (k + 3) :=
    sym2Coeff_succ α (k + 2)
  linear_combination e3 + hs - (α ^ 2 + (α⁻¹) ^ 2) * e2 + e1

/-- The elementary symmetric functions of the Sym²-Satake weights
`(α², 1, α⁻²)` collapse: `e₂ = e₁` and `e₃ = 1`. -/
theorem sym2_elementary_collapse (α : ℂ) (hα : α ≠ 0) :
    (α ^ 2 * 1 + α ^ 2 * (α⁻¹) ^ 2 + 1 * (α⁻¹) ^ 2
        = α ^ 2 + 1 + (α⁻¹) ^ 2)
      ∧ α ^ 2 * 1 * (α⁻¹) ^ 2 = 1 := by
  constructor
  · field_simp
  · field_simp

/-- The squared seed coefficients satisfy the SAME order-3 recurrence as the
Sym² coefficients — squares of a two-term-recurrence sequence close under the
product of the shifted characteristic roots.  Pure polynomial consequence of
two instances of `seedCoeff_rec`. -/
theorem seedCoeff_sq_rec (α : ℂ) (hα : α ≠ 0) (k : ℕ) :
    seedCoeff α (k + 3) ^ 2
      = (α ^ 2 + 1 + (α⁻¹) ^ 2) * seedCoeff α (k + 2) ^ 2
        - (α ^ 2 + 1 + (α⁻¹) ^ 2) * seedCoeff α (k + 1) ^ 2
        + seedCoeff α k ^ 2 := by
  have h1 : seedCoeff α (k + 2) = (α + α⁻¹) * seedCoeff α (k + 1) - seedCoeff α k :=
    seedCoeff_rec α hα k
  have h2 : seedCoeff α (k + 3) = (α + α⁻¹) * seedCoeff α (k + 2) - seedCoeff α (k + 1) :=
    seedCoeff_rec α hα (k + 1)
  have hinv : α * α⁻¹ = 1 := mul_inv_cancel₀ hα
  linear_combination
    (seedCoeff α (k + 3) + (α + α⁻¹) * seedCoeff α (k + 2) - seedCoeff α (k + 1)) * h2
      + (seedCoeff α (k + 2) - (α + α⁻¹) * seedCoeff α (k + 1) - seedCoeff α k) * h1
      + 2 * (seedCoeff α (k + 2) ^ 2 - seedCoeff α (k + 1) ^ 2) * hinv

/-- **T1 base**: `U_0² = h_0`. -/
theorem seedCoeff_sq_zero (α : ℂ) : seedCoeff α 0 ^ 2 = sym2Coeff α 0 := by
  simp

/-- **T1, the square law** (successor form): `U_{k+1}² = h_{k+1} + h_k` for
every `k` — the Clebsch–Gordan square `Sym^k ⊗ Sym^k = ⊕_j Sym²`-strings read
at the coefficient level.  Strong induction: both sides satisfy the same
order-3 recurrence (`seedCoeff_sq_rec`, `sym2Coeff_rec`). -/
theorem seedCoeff_sq_succ (α : ℂ) (hα : α ≠ 0) (k : ℕ) :
    seedCoeff α (k + 1) ^ 2 = sym2Coeff α (k + 1) + sym2Coeff α k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
      show seedCoeff α 1 ^ 2 = sym2Coeff α 1 + sym2Coeff α 0
      simp only [seedCoeff, sym2Coeff]
      norm_num [Finset.sum_range_succ]
      field_simp
      ring
    | 1 =>
      show seedCoeff α 2 ^ 2 = sym2Coeff α 2 + sym2Coeff α 1
      simp only [seedCoeff, sym2Coeff]
      norm_num [Finset.sum_range_succ]
      field_simp
      ring
    | 2 =>
      show seedCoeff α 3 ^ 2 = sym2Coeff α 3 + sym2Coeff α 2
      simp only [seedCoeff, sym2Coeff]
      norm_num [Finset.sum_range_succ]
      field_simp
      ring
    | (n + 3) =>
      have ih0 : seedCoeff α (n + 1) ^ 2 = sym2Coeff α (n + 1) + sym2Coeff α n :=
        ih n (by omega)
      have ih1 : seedCoeff α (n + 2) ^ 2 = sym2Coeff α (n + 2) + sym2Coeff α (n + 1) :=
        ih (n + 1) (by omega)
      have ih2 : seedCoeff α (n + 3) ^ 2 = sym2Coeff α (n + 3) + sym2Coeff α (n + 2) :=
        ih (n + 2) (by omega)
      have hsq : seedCoeff α (n + 4) ^ 2
          = (α ^ 2 + 1 + (α⁻¹) ^ 2) * seedCoeff α (n + 3) ^ 2
            - (α ^ 2 + 1 + (α⁻¹) ^ 2) * seedCoeff α (n + 2) ^ 2
            + seedCoeff α (n + 1) ^ 2 :=
        seedCoeff_sq_rec α hα (n + 1)
      have hS1 : sym2Coeff α (n + 4)
          = (α ^ 2 + 1 + (α⁻¹) ^ 2) * sym2Coeff α (n + 3)
            - (α ^ 2 + 1 + (α⁻¹) ^ 2) * sym2Coeff α (n + 2) + sym2Coeff α (n + 1) :=
        sym2Coeff_rec α hα (n + 1)
      have hS0 : sym2Coeff α (n + 3)
          = (α ^ 2 + 1 + (α⁻¹) ^ 2) * sym2Coeff α (n + 2)
            - (α ^ 2 + 1 + (α⁻¹) ^ 2) * sym2Coeff α (n + 1) + sym2Coeff α n :=
        sym2Coeff_rec α hα n
      show seedCoeff α (n + 4) ^ 2 = sym2Coeff α (n + 4) + sym2Coeff α (n + 3)
      linear_combination hsq + (α ^ 2 + 1 + (α⁻¹) ^ 2) * ih2
        - (α ^ 2 + 1 + (α⁻¹) ^ 2) * ih1 + ih0 - hS1 - hS0

/-- **T1, the square law** (`k − 1` form): `U_k² = h_k + h_{k−1}` for `1 ≤ k`. -/
theorem seedCoeff_sq (α : ℂ) (hα : α ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    seedCoeff α k ^ 2 = sym2Coeff α k + sym2Coeff α (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simpa using seedCoeff_sq_succ α hα j

/-- The Möbius peel of the squared seed coefficients at prime-power level: the
first difference `U_k² − U_{k−1}²` (with `peeled α 0 = 1 = U_0²`) — the local
`1/ζ(2s)`-peel of the squared seed Dirichlet polynomial. -/
noncomputable def peeled (α : ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => seedCoeff α (k + 1) ^ 2 - seedCoeff α k ^ 2

@[simp] theorem peeled_zero (α : ℂ) : peeled α 0 = 1 := rfl

theorem peeled_succ (α : ℂ) (k : ℕ) :
    peeled α (k + 1) = seedCoeff α (k + 1) ^ 2 - seedCoeff α k ^ 2 := rfl

/-- One peel rung: `h_{k+2} = h_k + peeled α (k+2)` — the square law telescoped
once. -/
theorem sym2Coeff_peel_step (α : ℂ) (hα : α ≠ 0) (k : ℕ) :
    sym2Coeff α (k + 2) = sym2Coeff α k + peeled α (k + 2) := by
  have h1 : seedCoeff α (k + 2) ^ 2 = sym2Coeff α (k + 2) + sym2Coeff α (k + 1) :=
    seedCoeff_sq_succ α hα (k + 1)
  have h0 : seedCoeff α (k + 1) ^ 2 = sym2Coeff α (k + 1) + sym2Coeff α k :=
    seedCoeff_sq_succ α hα k
  have hp : peeled α (k + 2) = seedCoeff α (k + 2) ^ 2 - seedCoeff α (k + 1) ^ 2 :=
    peeled_succ α (k + 1)
  linear_combination h0 - h1 - hp

/-- **T3, the local `μ/ζ(2s)` peel in difference form**: at every prime-power
level, `h_{k+2} − h_k = U_{k+2}² − U_{k+1}²`.  On local Dirichlet polynomials
at a prime `p` this is precisely: multiplying the Sym² local series by the
local `1/ζ(2s)`-factor `(1 − p^{−2s})` returns the Möbius peel `peeled` of the
squared seed series. -/
theorem sym2Coeff_localZetaPeel (α : ℂ) (hα : α ≠ 0) (k : ℕ) :
    sym2Coeff α (k + 2) - sym2Coeff α k = peeled α (k + 2) := by
  rw [sym2Coeff_peel_step α hα k]
  ring

/-- **T2, the peel + squares-redilation form of the Sym² coefficients**:

  `h_k = ∑_{m ≤ k/2} peeled α (k − 2m)`.

The Sym² local bank coefficients ARE the squares-dilation (the `m`-sum: the
local `ζ(2s)`-factor `∑_m p^{−2ms}`) of the Möbius peel (`peeled`: the local
`1/ζ(2s)`-peel) of the squared seed coefficients — exact, at every prime power,
unit-determinant Satake, identity class.  This is the local layer of the r = 2
coefficient identification. -/
theorem sym2Coeff_eq_sum_peeled (α : ℂ) (hα : α ≠ 0) (k : ℕ) :
    sym2Coeff α k = ∑ m ∈ Finset.range (k / 2 + 1), peeled α (k - 2 * m) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 =>
      rw [show (1 : ℕ) / 2 + 1 = 1 from by norm_num, Finset.sum_range_one,
        show 1 - 2 * 0 = 1 from by norm_num, peeled_succ]
      simp only [seedCoeff, sym2Coeff]
      norm_num [Finset.sum_range_succ]
      field_simp
      ring
    | (n + 2) =>
      have ihn : sym2Coeff α n = ∑ m ∈ Finset.range (n / 2 + 1), peeled α (n - 2 * m) :=
        ih n (by omega)
      have hsum : (∑ m ∈ Finset.range ((n + 2) / 2 + 1), peeled α (n + 2 - 2 * m))
          = (∑ m ∈ Finset.range (n / 2 + 1), peeled α (n - 2 * m))
            + peeled α (n + 2) := by
        rw [show (n + 2) / 2 + 1 = (n / 2 + 1) + 1 from by omega,
          Finset.sum_range_succ']
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        congr 1
        omega
      show sym2Coeff α (n + 2)
          = ∑ m ∈ Finset.range ((n + 2) / 2 + 1), peeled α (n + 2 - 2 * m)
      rw [hsum, sym2Coeff_peel_step α hα n, ihn]

/-- **T4a** — identification with the repo's literal clock-bank weights: the
seed coefficient is the sum of the `Sym^k` clock string of
`GlobalHelixClebschGordanBank`. -/
theorem seedCoeff_eq_clockWeight_sum (α : ℂ) (k : ℕ) :
    seedCoeff α k = ∑ i ∈ Finset.range (k + 1), GlobalHelix.symClockWeight k α i :=
  rfl

/-- **T4b** — the Sym² coefficient is the complete homogeneous sum of the three
rank-3 bank weights `GlobalHelix.symClockWeight 2 α {0, 1, 2} = (α², 1, α⁻²)`:
`h_k = ∑_{a + b + c = k} w₀^a · w₁^b · w₂^c` written over the triangle
`a + c ≤ k` with `b = k − a − c`. -/
theorem sym2Coeff_eq_clockWeight_homogeneous (α : ℂ) (hα : α ≠ 0) (k : ℕ) :
    sym2Coeff α k
      = ∑ a ∈ Finset.range (k + 1), ∑ c ∈ Finset.range (k + 1 - a),
          GlobalHelix.symClockWeight 2 α 0 ^ a
            * GlobalHelix.symClockWeight 2 α 1 ^ (k - a - c)
            * GlobalHelix.symClockWeight 2 α 2 ^ c := by
  unfold sym2Coeff
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => ?_
  have hw0 : GlobalHelix.symClockWeight 2 α 0 = α ^ (2 : ℤ) := by
    unfold GlobalHelix.symClockWeight
    norm_num
  have hw1 : GlobalHelix.symClockWeight 2 α 1 = 1 := by
    unfold GlobalHelix.symClockWeight
    norm_num
  have hw2 : GlobalHelix.symClockWeight 2 α 2 = α ^ (-2 : ℤ) := by
    unfold GlobalHelix.symClockWeight
    norm_num
  rw [hw0, hw1, hw2, one_pow, mul_one, ← zpow_natCast (α ^ (2 : ℤ)) a,
    ← zpow_natCast (α ^ (-2 : ℤ)) c, ← zpow_mul, ← zpow_mul,
    ← zpow_add₀ hα]
  congr 1
  ring

end CriticalLinePhasor.Sym2Identification

#print axioms CriticalLinePhasor.Sym2Identification.seedCoeff
#print axioms CriticalLinePhasor.Sym2Identification.sym2Coeff
#print axioms CriticalLinePhasor.Sym2Identification.seedCoeff_zero
#print axioms CriticalLinePhasor.Sym2Identification.sym2Coeff_zero
#print axioms CriticalLinePhasor.Sym2Identification.seedCoeff_rec
#print axioms CriticalLinePhasor.Sym2Identification.sym2Coeff_succ
#print axioms CriticalLinePhasor.Sym2Identification.sym2Coeff_eq_sum_seedCoeff
#print axioms CriticalLinePhasor.Sym2Identification.sym2Coeff_rec
#print axioms CriticalLinePhasor.Sym2Identification.sym2_elementary_collapse
#print axioms CriticalLinePhasor.Sym2Identification.seedCoeff_sq_rec
#print axioms CriticalLinePhasor.Sym2Identification.seedCoeff_sq_zero
#print axioms CriticalLinePhasor.Sym2Identification.seedCoeff_sq_succ
#print axioms CriticalLinePhasor.Sym2Identification.seedCoeff_sq
#print axioms CriticalLinePhasor.Sym2Identification.peeled
#print axioms CriticalLinePhasor.Sym2Identification.peeled_zero
#print axioms CriticalLinePhasor.Sym2Identification.peeled_succ
#print axioms CriticalLinePhasor.Sym2Identification.sym2Coeff_peel_step
#print axioms CriticalLinePhasor.Sym2Identification.sym2Coeff_localZetaPeel
#print axioms CriticalLinePhasor.Sym2Identification.sym2Coeff_eq_sum_peeled
#print axioms CriticalLinePhasor.Sym2Identification.seedCoeff_eq_clockWeight_sum
#print axioms CriticalLinePhasor.Sym2Identification.sym2Coeff_eq_clockWeight_homogeneous
