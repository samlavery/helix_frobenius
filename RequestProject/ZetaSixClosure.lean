import Mathlib

/-!
# The ζ₆-lattice closure theorem: algebraicity certificate ⟹ exact closure

Path-step-2 upgrade (companion §path).  The prior `ZetaSixLattice.lean`
proved the THRESHOLD half (a lattice residual of norm below one is zero).
This file proves the missing VALUE-CLASSIFICATION half and assembles the
closure theorem the architecture needs:

* Kronecker at the lattice: a ℤ[ζ₆]-point of norm one is exactly a sixth
  root of unity (`mu6_of_norm_one`, `mu6_pow_six`) — so a frozen algebraic
  lane value (integrality + unit-circle purity, the freeze certificate)
  IS a μ₆-address, proven rather than assumed;
* the residual of any integer-weighted frozen lane is a lattice point, and
  a measured sub-unit residual is EXACTLY zero (`closure_exact`);
* the general-number-field interface consumes Mathlib's Kronecker theorem
  (`NumberField.Embeddings.pow_eq_one_of_norm_eq_one`).

Scope: does not assume or prove RH/GRH or the Hodge conjecture.  The
algebraicity of a lane enters through the freeze certificate (integrality
+ purity + house-field membership); the theorem converts that certificate
into exact ℤ[ζ₆]-closure at the common height.
-/

namespace ZetaSixClosure

/-- The hexagonal lattice ℤ[ζ₆] as integer pairs a + b·ζ with ζ² = ζ − 1. -/
structure Zz6 where
  a : ℤ
  b : ℤ
deriving DecidableEq, Repr

namespace Zz6

def mul (x y : Zz6) : Zz6 :=
  ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩

def one : Zz6 := ⟨1, 0⟩

def zero : Zz6 := ⟨0, 0⟩

/-- The norm form N(a + bζ) = a² + ab + b². -/
def normForm (x : Zz6) : ℤ := x.a ^ 2 + x.a * x.b + x.b ^ 2

theorem norm_mul (x y : Zz6) :
    normForm (mul x y) = normForm x * normForm y := by
  unfold normForm mul
  ring

def pow6 (x : Zz6) : Zz6 := mul x (mul x (mul x (mul x (mul x x))))

theorem normForm_nonneg (x : Zz6) : 0 ≤ normForm x := by
  have h := sq_nonneg (2 * x.a + x.b)
  have h2 := sq_nonneg x.b
  unfold normForm
  nlinarith

theorem normForm_eq_zero_iff (x : Zz6) : normForm x = 0 ↔ x = ⟨0, 0⟩ := by
  obtain ⟨a, b⟩ := x
  unfold normForm
  simp only [Zz6.mk.injEq]
  constructor
  · intro h
    have hb : b = 0 := by
      have h2 : b ^ 2 = 0 := by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
    subst hb
    have ha : a = 0 := by
      have h2 : a ^ 2 = 0 := by nlinarith
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
    exact ⟨ha, rfl⟩
  · rintro ⟨ha, hb⟩
    subst ha; subst hb
    ring

/-- The threshold (re-proved self-contained): a nonzero lattice point has
norm at least one — machine-zero closure of a lattice residual is
exactness, not approximation. -/
theorem lattice_threshold (x : Zz6) (h : x ≠ ⟨0, 0⟩) : 1 ≤ normForm x := by
  have h0 := normForm_nonneg x
  have hne : normForm x ≠ 0 := fun hz => h ((normForm_eq_zero_iff x).mp hz)
  omega

/-- **Kronecker at the lattice.**  A norm-one point of ℤ[ζ₆] is one of the
six units — exactly μ₆.  The algebraic-integrality plus unit-circle purity
of a frozen lane value forces it ONTO the lattice's unit hexagon. -/
theorem mu6_of_norm_one (x : Zz6) (h : normForm x = 1) :
    x = ⟨1, 0⟩ ∨ x = ⟨0, 1⟩ ∨ x = ⟨-1, 1⟩ ∨ x = ⟨-1, 0⟩ ∨
    x = ⟨0, -1⟩ ∨ x = ⟨1, -1⟩ := by
  obtain ⟨a, b⟩ := x
  unfold normForm at h
  have hb : -1 ≤ b ∧ b ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (2 * a + b), sq_nonneg (b - 1),
                               sq_nonneg (b + 1)]
  have hs : -2 ≤ 2 * a + b ∧ 2 * a + b ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg b, sq_nonneg (2 * a + b - 2),
                               sq_nonneg (2 * a + b + 2)]
  have ha : -1 ≤ a ∧ a ≤ 1 := by omega
  simp only [Zz6.mk.injEq]
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨ha1, ha2⟩ := ha
  interval_cases a <;> interval_cases b <;> revert h <;> decide

/-- Every norm-one lattice point has sixth power one: the μ₆-address law. -/
theorem mu6_pow_six (x : Zz6) (h : normForm x = 1) : pow6 x = one := by
  rcases mu6_of_norm_one x h with h | h | h | h | h | h <;> subst h <;> decide

end Zz6

open Zz6

/-- A frozen algebraic lane: values carrying the freeze certificate
(lattice integrality + unit-circle purity, i.e. norm one) with integer
weights at a common height. -/
structure FrozenLane (n : ℕ) where
  val : Fin n → Zz6
  frozen : ∀ i, normForm (val i) = 1
  wt : Fin n → ℤ

namespace FrozenLane

variable {n : ℕ}

/-- The lane residual is a lattice point by construction. -/
def residual (L : FrozenLane n) : Zz6 :=
  ⟨∑ i, L.wt i * (L.val i).a, ∑ i, L.wt i * (L.val i).b⟩

/-- The μ₆-address law holds on every frozen lane. -/
theorem address (L : FrozenLane n) : ∀ i, pow6 (L.val i) = one :=
  fun i => mu6_pow_six _ (L.frozen i)

/-- **The closure theorem.**  A frozen algebraic lane whose residual is
measured below the lattice threshold closes EXACTLY: machine-zero is
zero.  This is the algebraicity-implies-ℤ[ζ₆]-closure statement: the
freeze certificate puts the values on the unit hexagon (Kronecker at the
lattice), integer weights keep the residual on the lattice, and the
threshold converts a sub-unit measurement into exact vanishing. -/
theorem closure_exact (L : FrozenLane n)
    (hsub : normForm (residual L) < 1) : residual L = ⟨0, 0⟩ := by
  by_contra h
  exact absurd (lattice_threshold _ h) (by omega)

end FrozenLane

/-- **The number-field interface (Kronecker, consumed from Mathlib).**
An algebraic integer of a number field with every complex-embedding norm
equal to one is a root of unity — the general-strength half of the
closure mechanism; the lattice theorems above are its concrete μ₆
instance on the house field. -/
theorem kronecker_interface (K : Type*) [Field K] [NumberField K] {x : K}
    (hint : IsIntegral ℤ x) (hnorm : ∀ φ : K →+* ℂ, ‖φ x‖ = 1) :
    ∃ n, 0 < n ∧ x ^ n = 1 := by
  obtain ⟨n, hn, h⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hint hnorm
  exact ⟨n, hn, h⟩

end ZetaSixClosure
