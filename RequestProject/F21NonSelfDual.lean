import Mathlib
import RequestProject.CellClosure

/-!
# A genuine non-self-dual degree-three fiber: the F₂₁ order-seven bank

`tmp/f21_gl3_multirail.py` runs the multi-rail 3D helix on a **genuinely non-self-dual** degree-three
object: the degree-three complex (irreducible, `ρ ≇ ρ^∨`) Artin representation of the Frobenius group
`F₂₁ = C₇ ⋊ C₃` (7T4), field `x^7 - 14x^5 + 56x^3 - 56x + 22`.  At an order-seven Frobenius the local
Satake bank is the three roots of unity `{ζ, ζ², ζ⁴}` (class `7A`, trace the Gauss period
`η = (-1+√-7)/2`) or its conjugate `{ζ³, ζ⁵, ζ⁶}` (class `7B`, trace `η' = (-1-√-7)/2`), `ζ` a
primitive seventh root of unity.  The object is non-self-dual because `{ζ,ζ²,ζ⁴}` is *not* closed
under conjugation, and genuinely non-abelian (`p = 13` and `p = 41` are both `≡ 6 (mod 7)` yet lie in
different classes, so no congruence fixes the trace).

This file gives that computation its Lean backing.  Over any primitive seventh root `ζ`:

* `order7A_bank_cell_closes` / `order7B_bank_cell_closes` — **exact focal closure** of the order-seven
  bank: the complete `μ₇` cell of `k ↦ ∑ᵢ (wᵢ)^k` sums to zero, *for both* non-self-dual classes
  (an instance of `CellClosure.harmonic_bank_cell_sum_zero`; matches the machine-zero closure that
  tracks `10^{-dps}`).  No DC rail is present (no unit eigenvalue), so closure is residue-free.
* `order7A_det_one` / `order7B_det_one` — `∏ rails = 1` (`ζ·ζ²·ζ⁴ = ζ⁷`), i.e. `SL(3)`: two
  independent rails carry the degree-three bank.
* `gauss_period_sum` (`η + η' = -1`), `gauss_period_prod` (`η·η' = 2`), and `eta_ne_etaPrime`
  (`η ≠ η'`): the two order-seven traces are the distinct roots of `x² + x + 2` (discriminant `-7`).

Specializing to `ζ = exp(2πi/7)` gives the **scalar-readout obstruction**, the sharp statement of why
a non-self-dual fiber needs the multi-rail carrier and cannot ride a real one-dimensional readout:

* `etaPrime_eq_conj_eta` — `η' = conj η`, hence `scalar_readout_cannot_separate`:
  `(η).re = (η').re` while `η ≠ η'`.  A real (scalar) readout gives the **same** value to both
  Frobenius classes `7A`, `7B`, so it destroys the non-abelian bit that the multi-rail bank keeps.

No `sorry`, no `axiom`; the axiom footprint of every theorem is `{propext, Classical.choice, Quot.sound}`.
-/

open Complex
open scoped BigOperators

namespace CriticalLinePhasor.F21NonSelfDual

/-- The three order-seven `7A` rails `{ζ, ζ², ζ⁴}` (trace the Gauss period `η`). -/
noncomputable def rails7A (ζ : ℂ) : Fin 3 → ℂ := ![ζ ^ 1, ζ ^ 2, ζ ^ 4]

/-- The three order-seven `7B` rails `{ζ³, ζ⁵, ζ⁶}` (trace the conjugate Gauss period `η'`). -/
noncomputable def rails7B (ζ : ℂ) : Fin 3 → ℂ := ![ζ ^ 3, ζ ^ 5, ζ ^ 6]

/-- The Gauss period `η = ζ + ζ² + ζ⁴` (the order-seven `7A` trace / character value). -/
noncomputable def eta (ζ : ℂ) : ℂ := ζ ^ 1 + ζ ^ 2 + ζ ^ 4

/-- The conjugate Gauss period `η' = ζ³ + ζ⁵ + ζ⁶` (the order-seven `7B` trace). -/
noncomputable def etaPrime (ζ : ℂ) : ℂ := ζ ^ 3 + ζ ^ 5 + ζ ^ 6

variable {ζ : ℂ}

/-- Any power of a primitive seventh root is a seventh root of unity. -/
private theorem pow_seven (hζ : IsPrimitiveRoot ζ 7) (m : ℕ) : (ζ ^ m) ^ 7 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

/-- A power `ζ^m` with `7 ∤ m` is not `1`. -/
private theorem pow_ne_one (hζ : IsPrimitiveRoot ζ 7) {m : ℕ} (hm : ¬ (7 ∣ m)) : ζ ^ m ≠ 1 :=
  fun h => hm ((hζ.pow_eq_one_iff_dvd m).mp h)

/-- Each `7A` rail is a seventh root of unity (indices reduce definitionally: `![…] i`). -/
theorem rails7A_root (hζ : IsPrimitiveRoot ζ 7) (i : Fin 3) : (rails7A ζ i) ^ 7 = 1 := by
  fin_cases i <;> exact pow_seven hζ _

/-- Each `7A` rail is nontrivial (no unit eigenvalue: `7 ∤ 1,2,4`). -/
theorem rails7A_ne_one (hζ : IsPrimitiveRoot ζ 7) (i : Fin 3) : rails7A ζ i ≠ 1 := by
  fin_cases i
  · exact pow_ne_one hζ (by decide)
  · exact pow_ne_one hζ (by decide)
  · exact pow_ne_one hζ (by decide)

theorem rails7B_root (hζ : IsPrimitiveRoot ζ 7) (i : Fin 3) : (rails7B ζ i) ^ 7 = 1 := by
  fin_cases i <;> exact pow_seven hζ _

theorem rails7B_ne_one (hζ : IsPrimitiveRoot ζ 7) (i : Fin 3) : rails7B ζ i ≠ 1 := by
  fin_cases i
  · exact pow_ne_one hζ (by decide)
  · exact pow_ne_one hζ (by decide)
  · exact pow_ne_one hζ (by decide)

/-- **Exact focal closure of the `7A` bank.**  The complete `μ₇` cell of the three-rail order-seven
bank sums to zero — the machine-zero cell closure of the genuine non-self-dual degree-three fiber,
with no DC (unit-eigenvalue) rail, so residue-free. -/
theorem order7A_bank_cell_closes (hζ : IsPrimitiveRoot ζ 7) :
    ∑ k ∈ Finset.range 7, ∑ i, (rails7A ζ i) ^ k = 0 :=
  CellClosure.harmonic_bank_cell_sum_zero (rails7A ζ) (rails7A_root hζ) (rails7A_ne_one hζ)

/-- **Exact focal closure of the `7B` bank** (the conjugate non-self-dual class closes identically). -/
theorem order7B_bank_cell_closes (hζ : IsPrimitiveRoot ζ 7) :
    ∑ k ∈ Finset.range 7, ∑ i, (rails7B ζ i) ^ k = 0 :=
  CellClosure.harmonic_bank_cell_sum_zero (rails7B ζ) (rails7B_root hζ) (rails7B_ne_one hζ)

/-- `∏ 7A rails = ζ·ζ²·ζ⁴ = ζ⁷ = 1`: the bank sits in `SL(3)` (two independent rails). -/
theorem order7A_det_one (hζ : IsPrimitiveRoot ζ 7) :
    (rails7A ζ 0) * (rails7A ζ 1) * (rails7A ζ 2) = 1 := by
  simp only [rails7A, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [← pow_add, ← pow_add]; exact hζ.pow_eq_one

/-- `∏ 7B rails = ζ³·ζ⁵·ζ⁶ = ζ^14 = 1`: `SL(3)` for the conjugate class too. -/
theorem order7B_det_one (hζ : IsPrimitiveRoot ζ 7) :
    (rails7B ζ 0) * (rails7B ζ 1) * (rails7B ζ 2) = 1 := by
  simp only [rails7B, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [← pow_add, ← pow_add, show 3 + 5 + 6 = 7 * 2 from rfl, pow_mul, hζ.pow_eq_one, one_pow]

/-- The full seventh-root cell sum, expanded: `1 + ζ + ζ² + ⋯ + ζ⁶ = 0`. -/
theorem sum_all_roots (hζ : IsPrimitiveRoot ζ 7) :
    1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6 = 0 := by
  have h := CellClosure.root_of_unity_cell_sum_zero (P := 7) hζ.pow_eq_one
    (hζ.ne_one (by norm_num))
  simpa [Finset.sum_range_succ, pow_zero, pow_one, add_comm, add_left_comm, add_assoc]
    using h

/-- **Gauss-period sum** `η + η' = -1`. -/
theorem gauss_period_sum (hζ : IsPrimitiveRoot ζ 7) : eta ζ + etaPrime ζ = -1 := by
  have h := sum_all_roots hζ
  simp only [eta, etaPrime, pow_one]
  linear_combination h

/-- **Gauss-period product** `η · η' = 2` (using `ζ⁷ = 1` to fold the high powers). -/
theorem gauss_period_prod (hζ : IsPrimitiveRoot ζ 7) : eta ζ * etaPrime ζ = 2 := by
  have h7 : ζ ^ 7 = 1 := hζ.pow_eq_one
  have hs := sum_all_roots hζ
  simp only [eta, etaPrime, pow_one]
  linear_combination (3 + ζ + ζ ^ 2 + ζ ^ 3) * h7 + hs

/-- **The two order-seven traces are distinct**: `η ≠ η'`.  With `η + η' = -1` and `η·η' = 2` they are
the two roots of `x² + x + 2` (discriminant `-7 ≠ 0`); equal would force `η = -1/2` and `η² = 2`,
i.e. `8 = 1`. -/
theorem eta_ne_etaPrime (hζ : IsPrimitiveRoot ζ 7) : eta ζ ≠ etaPrime ζ := by
  intro heq
  have hsum := gauss_period_sum hζ
  have hprod := gauss_period_prod hζ
  rw [heq] at hsum hprod
  -- `2·η' = -1` and `η'² = 2` ⇒ `4·η'² = 1` ⇒ `8 = 1`
  have h8 : (8 : ℂ) = 1 := by
    have h4 : 4 * etaPrime ζ ^ 2 = 1 := by linear_combination (2 * etaPrime ζ - 1) * hsum
    linear_combination h4 - 4 * hprod
  norm_num at h8

/-! ### The scalar-readout obstruction at `ζ = exp(2πi/7)` -/

/-- The canonical primitive seventh root `ζ₇ = exp(2πi/7)`. -/
noncomputable def z7 : ℂ := Complex.exp (2 * Real.pi * I / 7)

theorem z7_primitive : IsPrimitiveRoot z7 7 := by
  simpa [z7] using Complex.isPrimitiveRoot_exp 7 (by norm_num)

/-- Complex conjugation sends `ζ₇` to `ζ₇⁶` (its inverse), the geometric fact behind non-self-duality. -/
theorem conj_z7 : (starRingEnd ℂ) z7 = z7 ^ 6 := by
  have h7 : z7 ^ 7 = 1 := z7_primitive.pow_eq_one
  have harg : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * I / 7) = -(2 * (Real.pi : ℂ) * I / 7) := by
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  have hconj : (starRingEnd ℂ) z7 = z7⁻¹ := by
    simp only [z7, ← Complex.exp_conj, harg, Complex.exp_neg]
  rw [hconj]
  -- `z7⁻¹ = z7^6` since `z7^6 * z7 = z7^7 = 1`
  exact inv_eq_of_mul_eq_one_left (by rw [← pow_succ]; exact h7)

/-- **`η' = conj η`.**  The `7B` trace is the complex conjugate of the `7A` trace: conjugation permutes
`{ζ,ζ²,ζ⁴} ↦ {ζ⁶,ζ⁵,ζ³}`. -/
theorem etaPrime_eq_conj_eta : etaPrime z7 = (starRingEnd ℂ) (eta z7) := by
  have h7 : z7 ^ 7 = 1 := z7_primitive.pow_eq_one
  rw [eta, map_add, map_add, map_pow, map_pow, map_pow, conj_z7, pow_one, ← pow_mul, ← pow_mul]
  rw [show z7 ^ (6 * 2) = z7 ^ 5 by
        rw [show (6 * 2 : ℕ) = 7 + 5 from rfl, pow_add, h7, one_mul],
      show z7 ^ (6 * 4) = z7 ^ 3 by
        rw [show (6 * 4 : ℕ) = 7 * 3 + 3 from rfl, pow_add, pow_mul, h7, one_pow, one_mul]]
  rw [etaPrime]; ring

/-- **The scalar readout cannot separate the two Frobenius classes.**  For the genuine non-self-dual
degree-three fiber, the two order-seven traces have *equal real part* (`Re η = Re η' = -1/2`) yet are
*distinct* (`η ≠ η'`, differing only in the imaginary part `±√7/2`).  So any real (scalar) `1`D readout
— a function of `Re`(trace) — assigns the **same** value to `7A` and `7B` and destroys the non-abelian
bit; only the complex multi-rail bank keeps `{ζ,ζ²,ζ⁴}` apart from `{ζ³,ζ⁵,ζ⁶}`. -/
theorem scalar_readout_cannot_separate :
    (eta z7).re = (etaPrime z7).re ∧ eta z7 ≠ etaPrime z7 := by
  refine ⟨?_, eta_ne_etaPrime z7_primitive⟩
  rw [etaPrime_eq_conj_eta, Complex.conj_re]

end CriticalLinePhasor.F21NonSelfDual
