import RequestProject.GlobalHelixGaussianFixedCompletion

/-!
# Bilateral Euler heights in the 3D helix

An integral exponent vector is read first as a positive multiplicative helix height.  Negating
the exponent vector is the geometric reciprocal-height involution required by the global
reflection.  No coefficient projection is used in this layer.
-/

open Real Complex
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

/-- The positive 3D helix height attached to a bilateral Euler exponent vector. -/
noncomputable def bilateralEulerHeight {V : Type*} (S : Finset V) (q : V → ℝ)
    (k : (v : S) → ℤ) : ℝ :=
  ∏ v : S, q v ^ k v

/-- A product of positive local Euler scales is a positive helix height. -/
theorem bilateralEulerHeight_pos {V : Type*} (S : Finset V) (q : V → ℝ)
    (hq : ∀ v ∈ S, 0 < q v) (k : (v : S) → ℤ) :
    0 < bilateralEulerHeight S q k := by
  unfold bilateralEulerHeight
  exact Finset.prod_pos fun v _ => zpow_pos (hq v v.property) _

/-- Negation is the involutive reindexing of the bilateral exponent lattice. -/
def negExponentEquiv {V : Type*} (S : Finset V) :
    ((v : S) → ℤ) ≃ ((v : S) → ℤ) where
  toFun k := -k
  invFun k := -k
  left_inv k := neg_neg k
  right_inv k := neg_neg k

@[simp] theorem negExponentEquiv_apply {V : Type*} (S : Finset V)
    (k : (v : S) → ℤ) :
    negExponentEquiv S k = -k := rfl

/-- Negating every Euler exponent reciprocates the 3D helix height. -/
theorem bilateralEulerHeight_neg {V : Type*} (S : Finset V) (q : V → ℝ)
    (k : (v : S) → ℤ) :
    bilateralEulerHeight S q (-k) = (bilateralEulerHeight S q k)⁻¹ := by
  unfold bilateralEulerHeight
  simp only [Pi.neg_apply, zpow_neg]
  exact Finset.prod_inv_distrib (fun v : S => q v ^ k v)

/-- The exponent-lattice involution carries each height to its reciprocal. -/
theorem bilateralEulerHeight_negExponentEquiv {V : Type*} (S : Finset V) (q : V → ℝ)
    (k : (v : S) → ℤ) :
    bilateralEulerHeight S q (negExponentEquiv S k) =
      (bilateralEulerHeight S q k)⁻¹ := by
  rw [negExponentEquiv_apply]
  exact bilateralEulerHeight_neg S q k

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.bilateralEulerHeight_pos
#print axioms CriticalLinePhasor.GlobalHelix.bilateralEulerHeight_neg
#print axioms CriticalLinePhasor.GlobalHelix.bilateralEulerHeight_negExponentEquiv
