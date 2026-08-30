import Mathlib

open Finset

/-! B1: the algebraic core of the exact L1 representation.

With `Ξ(x) = ∫ρ(u)e^{ixu}du`, writing `S0 = ∫ρe^{ixu}`, `S1 = ∫uρe^{ixu}`,
`S2 = ∫u²ρe^{ixu}`, one has `Ξ = S0`, `Ξ' = iS1`, `Ξ'' = -S2`, so
`L1 = Ξ'² - ΞΞ'' = S0·S2 - S1²`.  The Lagrange identity below is exactly
`S0·S2 - S1² = ½ΣΣ a_j a_k (u_j - u_k)²` in the finite case — i.e. the
symmetrisation `u ↔ v` that turns `(v² - uv)` into `½(u-v)²`. -/

theorem lagrange_second_moment {ι : Type*} (s : Finset ι) (a u : ι → ℂ) :
    ∑ j ∈ s, ∑ k ∈ s, a j * a k * (u j - u k) ^ 2
      = 2 * ((∑ k ∈ s, a k) * (∑ k ∈ s, a k * u k ^ 2)
              - (∑ k ∈ s, a k * u k) ^ 2) := by
  have expand : ∀ j k : ι, a j * a k * (u j - u k) ^ 2
      = (a j * u j ^ 2) * a k - 2 * ((a j * u j) * (a k * u k))
        + a j * (a k * u k ^ 2) := fun j k => by ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Real nodes, nonnegative weights, evaluated at `x = 0`: the identity gives
`Cauchy–Schwarz`, hence the boundary value `L1(0) ≥ 0` unconditionally. -/
theorem lagrange_nonneg_real {ι : Type*} (s : Finset ι) (w u : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) :
    0 ≤ (∑ k ∈ s, w k) * (∑ k ∈ s, w k * u k ^ 2) - (∑ k ∈ s, w k * u k) ^ 2 := by
  have key : ∑ j ∈ s, ∑ k ∈ s, w j * w k * (u j - u k) ^ 2
      = 2 * ((∑ k ∈ s, w k) * (∑ k ∈ s, w k * u k ^ 2)
              - (∑ k ∈ s, w k * u k) ^ 2) := by
    have expand : ∀ j k : ι, w j * w k * (u j - u k) ^ 2
        = (w j * u j ^ 2) * w k - 2 * ((w j * u j) * (w k * u k))
          + w j * (w k * u k ^ 2) := fun j k => by ring
    simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hpos : 0 ≤ ∑ j ∈ s, ∑ k ∈ s, w j * w k * (u j - u k) ^ 2 :=
    Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk =>
      mul_nonneg (mul_nonneg (hw j hj) (hw k hk)) (sq_nonneg _)
  linarith [key ▸ hpos]

#print axioms lagrange_second_moment
#print axioms lagrange_nonneg_real
