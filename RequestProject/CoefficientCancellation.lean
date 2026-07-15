import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-!
# The coefficient-cancellation target, with its abelian instance compiled

The load-bearing lemma of the functoriality claim, isolated by the audit: partial sums of the
twisted coefficients cancel, `∑_{n≤x} λ_n = O(x^θ)` with `θ < κ/2` and the weight explicit.
`CancellationBound` types the target.  The kernel pivot (ledger item 67) shows the synthesized
completion cannot deliver it — the completed object is coefficient-independent
(`positiveTheta_dilationKernel`: the coefficients cancel out as `a ⋆ a⁻¹`) — so the lemma
requires a functional equation against a coefficient-independent *fixed* kernel: adelic Poisson
on the actual bank, the Tate field.

This file compiles the instance where that fixed-kernel input is classical and fully present:
the abelian tower.  For a nontrivial Dirichlet character the cancellation holds with `θ = 0`
(bounded partial sums) — stronger than the target requires at any `κ > 0` — by pure
orthogonality: complete periods vanish (`MulChar.sum_eq_zero_of_ne_one`), so partial sums never
exceed one period of unit-normed terms.  `dirichlet_cancellation` inhabits `CancellationBound`
with `θ = 0`, weight identically one (explicit).  No RH/GRH assumed or proven.
-/

namespace CriticalLinePhasor.CoefficientCancellation

open Finset

/-- **The cancellation target** (the audit's lemma shape): the partial sums of the coefficient
sequence grow like `x^θ`.  The functoriality tower needs this for the `Sym^r × τ` coefficients
with `θ` below the convexity edge; the weight is carried explicitly by the sequence itself. -/
def CancellationBound (a : ℕ → ℂ) (C θ : ℝ) : Prop :=
  ∀ N : ℕ, ‖∑ n ∈ range N, a n‖ ≤ C * ((N : ℝ) + 1) ^ θ

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- Sums over `range q` of a function of the residue are sums over the residue ring. -/
theorem sum_range_natCast (g : ZMod q → ℂ) :
    ∑ m ∈ range q, g (m : ZMod q) = ∑ a : ZMod q, g a := by
  refine sum_nbij' (fun m => (m : ZMod q)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
  · intro m _
    exact mem_univ _
  · intro a _
    exact mem_range.mpr (ZMod.val_lt a)
  · intro m hm
    exact ZMod.val_natCast_of_lt (mem_range.mp hm)
  · intro a _
    exact ZMod.natCast_rightInverse a
  · intro m _
    rfl

/-- Every complete period of a nontrivial character sums to zero, at every shift. -/
theorem shifted_period_sum (hχ : χ ≠ 1) (s : ℕ) :
    ∑ m ∈ range q, χ ((s + m : ℕ) : ZMod q) = 0 := by
  have h0 : ∑ a : ZMod q, χ a = 0 := MulChar.sum_eq_zero_of_ne_one hχ
  calc ∑ m ∈ range q, χ ((s + m : ℕ) : ZMod q)
      = ∑ m ∈ range q, χ ((s : ZMod q) + (m : ZMod q)) := by
        refine sum_congr rfl fun m _ => ?_
        exact congrArg χ (by push_cast; ring)
    _ = ∑ a : ZMod q, χ ((s : ZMod q) + a) :=
        sum_range_natCast (fun a => χ ((s : ZMod q) + a))
    _ = ∑ a : ZMod q, χ a := Fintype.sum_equiv (Equiv.addLeft (s : ZMod q)) _ _ fun a => rfl
    _ = 0 := h0

/-- The partial sum is invariant under adding one full period. -/
theorem partial_sum_period (hχ : χ ≠ 1) (N : ℕ) :
    ∑ n ∈ range (N + q), χ (n : ZMod q) = ∑ n ∈ range N, χ (n : ZMod q) := by
  have hsplit :
      ∑ n ∈ Finset.Ico 0 N, χ (n : ZMod q) + ∑ n ∈ Finset.Ico N (N + q), χ (n : ZMod q) =
        ∑ n ∈ Finset.Ico 0 (N + q), χ (n : ZMod q) :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le N) (Nat.le_add_right N q)
  have htail : ∑ n ∈ Finset.Ico N (N + q), χ (n : ZMod q) = 0 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h1 : N + q - N = q := by omega
    rw [h1]
    exact shifted_period_sum χ hχ N
  rw [range_eq_Ico, range_eq_Ico, ← hsplit, htail, add_zero]

/-- **Bounded partial sums.**  The partial sums of a nontrivial Dirichlet character never exceed
one period of unit-normed terms. -/
theorem dirichlet_partial_sum_bound (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, χ (n : ZMod q)‖ ≤ q := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N q with h | h
    · calc ‖∑ n ∈ range N, χ (n : ZMod q)‖
          ≤ ∑ n ∈ range N, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ range N, 1 :=
            sum_le_sum fun n _ => DirichletCharacter.norm_le_one χ _
        _ = (N : ℝ) := by simp
        _ ≤ q := by exact_mod_cast h.le
    · have hq : 0 < q := NeZero.pos q
      have hN : N - q + q = N := Nat.sub_add_cancel h
      have := partial_sum_period χ hχ (N - q)
      rw [hN] at this
      rw [this]
      exact ih (N - q) (by omega)

/-- **The abelian instance of the cancellation lemma, compiled.**  For a nontrivial Dirichlet
character the target holds with `θ = 0` — strictly below `κ/2` for every `κ > 0` — with the
weight explicit (identically one) and the constant one period.  The fixed-kernel functional
equation this instance rests on is classical (Gauss sums / Poisson, present in Mathlib as the
Dirichlet `completedLFunction` theory); the cancellation itself is direct orthogonality,
stronger than the contour route requires. -/
theorem dirichlet_cancellation (hχ : χ ≠ 1) :
    CancellationBound (fun n => χ (n : ZMod q)) q 0 := by
  intro N
  rw [Real.rpow_zero, mul_one]
  exact dirichlet_partial_sum_bound χ hχ N

end CriticalLinePhasor.CoefficientCancellation

#print axioms CriticalLinePhasor.CoefficientCancellation.shifted_period_sum
#print axioms CriticalLinePhasor.CoefficientCancellation.dirichlet_partial_sum_bound
#print axioms CriticalLinePhasor.CoefficientCancellation.dirichlet_cancellation
