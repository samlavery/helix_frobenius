import Mathlib

/-!
# The ζ₆-lattice rigidity threshold: sub-unit lattice residuals vanish exactly

The audit asked for the actual lattice constraint behind "exact ℤ[ζ₆] μ6 closure" — not
cancellation of an arbitrary residual by arbitrary real weights (which is two-dimensional real
linear algebra and arithmetic-neutral), but the statement that constrains integer-weighted
μ6-cell residuals.  That statement is a **rigidity threshold**:

* the μ6-cell sums with integer weights land in the lattice `ℤ[ζ₆] = {a + b·ζ₆ : a, b ∈ ℤ}`;
* the lattice is discrete with minimal nonzero norm `1` (the norm form is
  `a² + ab + b²`, positive definite over `ℤ`);
* hence a lattice residual of magnitude `< 1` is **exactly zero**.

This is the bridge from the measured register to the proved one: a machine-zero closure
(`|D| ~ 1e-14`) of an integer-weighted μ6 residual is not "small" — it is exact, by
`lattice_residual_exact`.  Real-weight cancellation can be soft; lattice-weight closure
cannot.  No `sorry`, no `axiom`.
-/

open Complex

namespace CriticalLinePhasor.ZetaSixLattice

/-- The primitive sixth root as an explicit algebraic number: `ζ₆ = (1 + √3·i)/2`. -/
noncomputable def zeta6 : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

theorem zeta6_normSq : Complex.normSq zeta6 = 1 := by
  simp only [zeta6, Complex.normSq_mk]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num)
  nlinarith

/-- The ζ₆-lattice element with integer coordinates `(a, b)`. -/
noncomputable def latticePoint (a b : ℤ) : ℂ := (a : ℂ) + (b : ℂ) * zeta6

/-- **The norm form of the lattice**: `‖a + b·ζ₆‖² = a² + ab + b²`, exactly. -/
theorem latticePoint_normSq (a b : ℤ) :
    Complex.normSq (latticePoint a b) = ((a ^ 2 + a * b + b ^ 2 : ℤ) : ℝ) := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num)
  simp only [latticePoint, zeta6, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.intCast_re, Complex.intCast_im, Complex.mul_re, Complex.mul_im]
  push_cast
  nlinarith

/-- **Discreteness at the origin**: the norm form is at least `1` off the origin —
`4(a² + ab + b²) = (2a + b)² + 3b²`. -/
theorem normForm_ge_one {a b : ℤ} (h : ¬ (a = 0 ∧ b = 0)) :
    1 ≤ a ^ 2 + a * b + b ^ 2 := by
  have key : 4 * (a ^ 2 + a * b + b ^ 2) = (2 * a + b) ^ 2 + 3 * b ^ 2 := by ring
  rcases eq_or_ne b 0 with rfl | hb
  · have ha : a ≠ 0 := fun h0 => h ⟨h0, rfl⟩
    nlinarith [sq_nonneg a, Int.one_le_abs ha, sq_abs a]
  · nlinarith [sq_nonneg (2 * a + b), Int.one_le_abs hb, sq_abs b]

/-- **The rigidity threshold**: a ζ₆-lattice residual of magnitude below `1` is exactly zero.
Sub-unit closure of an integer-weighted μ6 residual is not approximation — it is exactness. -/
theorem lattice_residual_exact {a b : ℤ} (hD : Complex.normSq (latticePoint a b) < 1) :
    latticePoint a b = 0 := by
  have hab : a = 0 ∧ b = 0 := by
    by_contra h
    have h1 := normForm_ge_one h
    rw [latticePoint_normSq] at hD
    have : (1 : ℝ) ≤ ((a ^ 2 + a * b + b ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
    linarith
  rw [latticePoint, hab.1, hab.2]
  simp

/-- The threshold is sharp: the lattice point `(1,0)` has norm exactly `1`. -/
theorem threshold_sharp : Complex.normSq (latticePoint 1 0) = 1 := by
  rw [latticePoint_normSq]
  norm_num

end CriticalLinePhasor.ZetaSixLattice

#print axioms CriticalLinePhasor.ZetaSixLattice.latticePoint_normSq
#print axioms CriticalLinePhasor.ZetaSixLattice.normForm_ge_one
#print axioms CriticalLinePhasor.ZetaSixLattice.lattice_residual_exact
#print axioms CriticalLinePhasor.ZetaSixLattice.threshold_sharp
