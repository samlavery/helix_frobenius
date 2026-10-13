import Mathlib

/-!
# No commuting fundamental symmetry can make an off-line pair positive (ledger 1226)

Let `B` be any Hermitian sesquilinear form for which the generator `T` is symmetric, `B(Tx, y) = B(x, Ty)`.

* `form_self_zero_of_nonreal`: an eigenvector `v` with NON-REAL eigenvalue is `B`-null, `B(v, v) = 0`.
* `commuting_symmetry_null`: if a LINEAR map `Ĵ` commutes with `T` and the eigenspace is one-dimensional
  (`Ĵ v = c·v`), the would-be Hilbert form `B(·, Ĵ·)` still vanishes on `v`.

So no `T`-commuting linear fundamental symmetry turns a hyperbolic (off-line) sector positive. An antilinear
one (the same-height partner, a PT-type symmetry) gives a bilinear rather than Hermitian pairing. The positive
sectors that native objects can select are the radical quotient (it KILLS off-line states) or `δ = 0` (circular).
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.FundamentalSymmetry

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- **A non-real eigenvector is null for any symmetric Hermitian form.** -/
theorem form_self_zero_of_nonreal (B : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (T : E →ₗ[ℂ] E)
    (hT : ∀ x y, B (T x) y = B x (T y)) {v : E} {μ : ℂ} (hv : T v = μ • v)
    (hnr : μ.im ≠ 0) : B v v = 0 := by
  have h := hT v v
  rw [hv, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at h
  have hfac : ((starRingEnd ℂ) μ - μ) * B v v = 0 := by
    rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp hfac with h0 | h0
  · exfalso
    apply hnr
    have := congrArg Complex.im h0
    simp at this
    linarith
  · exact h0

/-- **A commuting linear symmetry cannot make the off-line sector positive.** -/
theorem commuting_symmetry_null (B : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (T : E →ₗ[ℂ] E)
    (hT : ∀ x y, B (T x) y = B x (T y)) {v : E} {μ c : ℂ} (hv : T v = μ • v)
    (hnr : μ.im ≠ 0) (Ĵ : E →ₗ[ℂ] E) (hJv : Ĵ v = c • v) : B v (Ĵ v) = 0 := by
  rw [hJv, map_smul, form_self_zero_of_nonreal B T hT hv hnr, smul_zero]

end CriticalLinePhasor.FundamentalSymmetry

end

#print axioms CriticalLinePhasor.FundamentalSymmetry.form_self_zero_of_nonreal
#print axioms CriticalLinePhasor.FundamentalSymmetry.commuting_symmetry_null
