import Mathlib

/-!
# Log-free FTA geometry — the Hilbert–Pólya winding object

The helix winding is a **completely multiplicative character on the positive integers**, valued in
the unit circle, built from an assignment of an angle `θ p` to each prime and extended by the
**fundamental theorem of arithmetic**: `Θ(m·n) = Θ(m) + Θ(n)`. It uses **no logarithm** — the
additivity is read straight off the prime-factorization exponents, which is exactly what `log` is
*applied to the integers to recover*.

This is the object Hilbert–Pólya needed: a **geometric** (not analytic) realization of the
multiplicative prime structure, **log-free**. `log` is the *external bridge* `wind n ↔ n^{it}` to the
analytic `L`-function — used only to identify the geometric resonances with `L`'s named zeros, never
inside the geometry. The multiplicative prime structure lives entirely here, on the log-free side;
the analytic `L`-function and its explicit formula are across the bridge. Nothing in this file takes
a `Real.log` or `Complex.log`.
-/

open Complex

namespace HelixLogFree

variable (θ : ℕ → ℝ)

/-- **The log-free FTA winding angle** `Θ(n) = Σ_{pᵉ ‖ n} e · θ(p)`: the completely-additive
    extension of the prime-angle assignment `θ`, read off the factorization exponents. No `log`. -/
noncomputable def windAngle (n : ℕ) : ℝ :=
  n.factorization.sum (fun p e => (e : ℝ) * θ p)

@[simp] theorem windAngle_one : windAngle θ 1 = 0 := by
  simp [windAngle]

/-- **FTA-additivity** `Θ(m·n) = Θ(m) + Θ(n)` (for `m, n ≠ 0`) — straight from
    `Nat.factorization_mul`, i.e. the fundamental theorem of arithmetic. Log-free. -/
theorem windAngle_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    windAngle θ (m * n) = windAngle θ m + windAngle θ n := by
  rw [windAngle, windAngle, windAngle, Nat.factorization_mul hm hn,
    Finsupp.sum_add_index' (fun _ => by simp) (fun _ b₁ b₂ => by push_cast; ring)]

/-- **The log-free FTA winding** on the unit circle: `n ↦ exp(i·Θ(n))`, a completely multiplicative
    character `ℕ → Circle`. The angular winding of the 3-D helix carrier — built from primes, log-free. -/
noncomputable def wind (n : ℕ) : Circle := Circle.exp (windAngle θ n)

@[simp] theorem wind_one : wind θ 1 = 1 := by
  simp [wind]

/-- **The winding is a multiplicative character** (`wind(m·n) = wind m · wind n`): the FTA-additivity
    of the angle becomes multiplicativity on the circle, with no logarithm. -/
theorem wind_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    wind θ (m * n) = wind θ m * wind θ n := by
  rw [wind, wind, wind, windAngle_mul θ hm hn, Circle.exp_add]

/-- **The log-free helix point** at integer `n`: the **emergent** area-law radius `√n` — it is *not*
    posited; it falls out of winding the evenly-`π/3`-spaced integer line (arclength `∝ k²` forces
    radius `∝ √n`; the genuine construction is `ClosedForm`'s `Geometry`) — times the FTA winding.
    A site of the 3-D helix carrier, where the phasors ride and accumulate, in 3-D. -/
noncomputable def helixPt (n : ℕ) : ℂ := (Real.sqrt n : ℂ) * (wind θ n : ℂ)

/-- **The radius is the area-law baseline `√n`** — the winding contributes unit modulus, so the
    helix point's distance from the axis is exactly `√n`. (`½` lives here as `√ = ·^{1/2}`.) -/
theorem norm_helixPt (n : ℕ) : ‖helixPt θ n‖ = Real.sqrt n := by
  rw [helixPt, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Circle.norm_coe, mul_one]

end HelixLogFree
