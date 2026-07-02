import Mathlib

set_option maxHeartbeats 1000000

open scoped Real

namespace CriticalLinePhasor.Monodromy

/-!
# Exact finite circle monodromy of a harmonic cell

We model the **carrier monodromy on the circle** induced by a harmonic cell unit `H`.
After `k` cells the carrier phase is `k · H` read modulo `2π`:
```
C_H(k) = k · H  (mod 2π).
```

A cell unit `H` has **exact finite circle monodromy** when the carrier returns exactly to
its origin after finitely many (but at least one) cells, i.e. there is a positive number of
cells `k` and a positive winding number `m` with `k · H = 2π · m`.

The main results:

* `pi3_finite_monodromy` — the `π/3` carrier closes exactly after `6` cells (`k = 6`, `m = 1`).
* `unit_not_finite_monodromy` — the unit `H = 1` carrier never closes exactly, because that
  would force `π` to be rational.
* `circleMonodromy_iff_rat` — the general criterion: `H` has exact finite circle monodromy
  iff `H / (2π)` is a (positive) rational number.
-/

/-- Exact finite circle monodromy of a harmonic cell `H`: there exist a positive number of
cells `k` and a positive winding number `m` such that `k · H = 2π · m`, i.e. the carrier
phase `k · H` equals an exact whole number of full turns. -/
def CircleMonodromy (H : ℝ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ m : ℕ, 0 < m ∧ (k : ℝ) * H = 2 * Real.pi * (m : ℝ)

/-- The exact six-cell closure of the `π/3` carrier: `6 · (π/3) = 2π · 1`. -/
theorem pi3_six_cell : (6 : ℝ) * (Real.pi / 3) = 2 * Real.pi * (1 : ℕ) := by
  push_cast
  ring

/-- The `π/3` carrier has exact finite circle monodromy: it closes after `6` cells with
winding number `1`. -/
theorem pi3_finite_monodromy : CircleMonodromy (Real.pi / 3) := by
  exact ⟨6, by norm_num, 1, by norm_num, by push_cast; ring⟩

/-- The unit carrier `H = 1` has **no** exact finite circle monodromy: a closure
`k · 1 = 2π · m` would force `π = k / (2m)` to be rational. -/
theorem unit_not_finite_monodromy : ¬ CircleMonodromy (1 : ℝ) := by
  -- Assume for contradiction that `CircleMonodromy 1` holds.
  by_contra h_contra
  -- Then there exist `k` and `m` such that `k * 1 = 2 * Real.pi * m`.
  obtain ⟨k, hk, m, hm, h_eq⟩ := h_contra;
  exact irrational_pi <| ⟨ k / ( 2 * m ), by push_cast; rw [ div_eq_iff ( by positivity ) ] ; linarith ⟩

/-- General criterion: a harmonic cell `H` has exact finite circle monodromy iff `H / (2π)`
is a positive rational number, equivalently `H = 2π · q` for some positive rational `q`. -/
theorem circleMonodromy_iff_rat (H : ℝ) :
    CircleMonodromy H ↔ ∃ q : ℚ, 0 < q ∧ H = 2 * Real.pi * (q : ℝ) := by
  constructor;
  · intro h;
    obtain ⟨ k, hk, m, hm, h ⟩ := h; use m / k; exact ⟨ by positivity, by push_cast; rw [ mul_div, eq_div_iff ] <;> first | positivity | linarith ⟩ ;
  · rintro ⟨ q, hq, rfl ⟩;
    refine' ⟨ q.den, mod_cast q.pos, q.num.natAbs, _, _ ⟩ <;> simp_all +decide [ abs_of_pos, Rat.cast_def ];
    · linarith;
    · rw [ mul_left_comm, mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr q.pos.ne' ) ]

end CriticalLinePhasor.Monodromy