import Mathlib

/-!
# The seat path for a finite positive atomic support

Sam's atomic-interpolation construction, formalized.  Given anchor nodes
`α₁ < ⋯ < α_m` with positive weights and target nodes `x₁ < ⋯ < x_m` with
positive weights, the straight-line interpolation

`λ_j(t) = (1-t)α_j + t x_j`,  `w_j(t) = (1-t)a_j + t μ_j`

is collision-free and positive for every `t ∈ [0,1]`, and its Hankel pair
interpolates the two endpoint Hankel pairs.  Consequently the whole path
consists of Hankel matrices of finite positive atomic measures on `m` distinct
real nodes, so every station is positive semidefinite.

What this contributes: the existence of the transport path is no longer an
unknown.  It removes the *transport-existence* question from the seat, leaving
only the reality of the target support.

Nothing here refers to zeta, to zeros, or to any positivity hypothesis about
them: this is the geometry of finite positive atomic moment data.
-/

open scoped BigOperators
open Finset

namespace CriticalLinePhasor.SeatAtomicPath

variable {m n : ℕ}

/-- The Vandermonde evaluation vector `(1, x, …, x^{n-1})`. -/
def evalVec (n : ℕ) (x : ℝ) : Fin n → ℝ := fun i => x ^ (i : ℕ)

/-- Hankel matrix of the finite atomic measure `∑ⱼ wⱼ δ(λⱼ)`. -/
def hankelOfAtoms (n : ℕ) (w lam : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => ∑ j, w j * lam j ^ ((i : ℕ) + (k : ℕ))

/-- The once-shifted Hankel matrix of the same measure. -/
def hankelOfAtomsShift (n : ℕ) (w lam : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => ∑ j, w j * lam j ^ ((i : ℕ) + (k : ℕ) + 1)

/-- **The quadratic form of an atomic Hankel matrix is a weighted sum of squares.**
This is the mechanism behind every positivity statement below. -/
theorem hankel_quadratic_form (w lam : Fin m → ℝ) (c : Fin n → ℝ) :
    (∑ i, ∑ k, c i * hankelOfAtoms n w lam i k * c k)
      = ∑ j, w j * (∑ i, c i * lam j ^ (i : ℕ)) ^ 2 := by
  have expand : ∀ i k : Fin n,
      c i * hankelOfAtoms n w lam i k * c k
        = ∑ j, (w j * (c i * lam j ^ (i : ℕ))) * (c k * lam j ^ (k : ℕ)) := by
    intro i k
    simp only [hankelOfAtoms, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]; ring
  calc (∑ i, ∑ k, c i * hankelOfAtoms n w lam i k * c k)
      = ∑ i, ∑ k, ∑ j, (w j * (c i * lam j ^ (i : ℕ))) * (c k * lam j ^ (k : ℕ)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => expand i k
    _ = ∑ i, ∑ j, ∑ k, (w j * (c i * lam j ^ (i : ℕ))) * (c k * lam j ^ (k : ℕ)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ k, (w j * (c i * lam j ^ (i : ℕ))) * (c k * lam j ^ (k : ℕ)) :=
        Finset.sum_comm
    _ = ∑ j, w j * (∑ i, c i * lam j ^ (i : ℕ)) ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hinner : ∀ i : Fin n,
            (∑ k, (w j * (c i * lam j ^ (i : ℕ))) * (c k * lam j ^ (k : ℕ)))
              = (w j * (c i * lam j ^ (i : ℕ))) * (∑ k, c k * lam j ^ (k : ℕ)) :=
          fun i => (Finset.mul_sum _ _ _).symm
        rw [Finset.sum_congr rfl (fun i _ => hinner i), ← Finset.sum_mul, ← Finset.mul_sum, sq]
        ring

/-- Atomic Hankel matrices with nonnegative weights are positive semidefinite. -/
theorem hankelOfAtoms_posSemidef {w lam : Fin m → ℝ} (hw : ∀ j, 0 ≤ w j) :
    (hankelOfAtoms n w lam).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i k
    simp only [Matrix.conjTranspose_apply, hankelOfAtoms, star_trivial]
    exact Finset.sum_congr rfl fun j _ => by rw [add_comm]
  · intro c
    have hform : star c ⬝ᵥ ((hankelOfAtoms n w lam).mulVec c)
        = ∑ i, ∑ k, c i * hankelOfAtoms n w lam i k * c k := by
      simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [hform, hankel_quadratic_form]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)

/-! ## The path -/

/-- Interpolated nodes. -/
def nodePath (al x : Fin m → ℝ) (t : ℝ) : Fin m → ℝ := fun j => (1 - t) * al j + t * x j

/-- Interpolated weights. -/
def weightPath (a mu : Fin m → ℝ) (t : ℝ) : Fin m → ℝ := fun j => (1 - t) * a j + t * mu j

/-- **Collision-freeness.**  If both endpoint node lists are strictly increasing then
so is every interpolated list, for every `t ∈ [0,1]`: no two nodes ever meet. -/
theorem nodePath_strictMono {al x : Fin m → ℝ} (hal : StrictMono al) (hx : StrictMono x)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : StrictMono (nodePath al x t) := by
  intro i j hij
  have hA : 0 < al j - al i := sub_pos.mpr (hal hij)
  have hB : 0 < x j - x i := sub_pos.mpr (hx hij)
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hpos : 0 < (1 - t) * (al j - al i) + t * (x j - x i) := by
    rcases le_total t (1 / 2) with hc | hc
    · have hhalf : (1 : ℝ) / 2 ≤ 1 - t := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hhalf hA.le, mul_nonneg ht0 hB.le]
    · nlinarith [mul_le_mul_of_nonneg_right hc hB.le, mul_nonneg h1t hA.le]
  simp only [nodePath]
  nlinarith [hpos]

/-- The interpolated nodes stay pairwise distinct. -/
theorem nodePath_injective {al x : Fin m → ℝ} (hal : StrictMono al) (hx : StrictMono x)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Function.Injective (nodePath al x t) :=
  (nodePath_strictMono hal hx ht0 ht1).injective

/-- **Weights stay strictly positive** along the whole path. -/
theorem weightPath_pos {a mu : Fin m → ℝ} (ha : ∀ j, 0 < a j) (hmu : ∀ j, 0 < mu j)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (j : Fin m) : 0 < weightPath a mu t j := by
  simp only [weightPath]
  rcases eq_or_lt_of_le ht1 with h | h
  · subst h; simpa using hmu j
  · have h1 : 0 < 1 - t := sub_pos.mpr h
    nlinarith [mul_pos h1 (ha j), mul_nonneg ht0 (hmu j).le]

@[simp] theorem nodePath_zero (al x : Fin m → ℝ) : nodePath al x 0 = al := by
  funext j; simp [nodePath]

@[simp] theorem nodePath_one (al x : Fin m → ℝ) : nodePath al x 1 = x := by
  funext j; simp [nodePath]

@[simp] theorem weightPath_zero (a mu : Fin m → ℝ) : weightPath a mu 0 = a := by
  funext j; simp [weightPath]

@[simp] theorem weightPath_one (a mu : Fin m → ℝ) : weightPath a mu 1 = mu := by
  funext j; simp [weightPath]

/-- **Every station of the path is a positive-semidefinite Hankel pair.** -/
theorem hankel_path_posSemidef {a mu al x : Fin m → ℝ}
    (ha : ∀ j, 0 < a j) (hmu : ∀ j, 0 < mu j) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (hankelOfAtoms n (weightPath a mu t) (nodePath al x t)).PosSemidef :=
  hankelOfAtoms_posSemidef fun j => (weightPath_pos ha hmu ht0 ht1 j).le

/-- **Terminal identification.**  At `t = 1` the transported pair is exactly the
target atomic pair. -/
theorem hankel_path_terminal (a mu al x : Fin m → ℝ) :
    hankelOfAtoms n (weightPath a mu 1) (nodePath al x 1) = hankelOfAtoms n mu x := by
  simp

/-- At `t = 0` it is exactly the anchor pair. -/
theorem hankel_path_initial (a mu al x : Fin m → ℝ) :
    hankelOfAtoms n (weightPath a mu 0) (nodePath al x 0) = hankelOfAtoms n a al := by
  simp

/-- The same two statements for the shifted matrix. -/
theorem hankelShift_path_terminal (a mu al x : Fin m → ℝ) :
    hankelOfAtomsShift n (weightPath a mu 1) (nodePath al x 1) = hankelOfAtomsShift n mu x := by
  simp

end CriticalLinePhasor.SeatAtomicPath

section AxiomAudit
#print axioms CriticalLinePhasor.SeatAtomicPath.hankel_quadratic_form
#print axioms CriticalLinePhasor.SeatAtomicPath.hankelOfAtoms_posSemidef
#print axioms CriticalLinePhasor.SeatAtomicPath.nodePath_strictMono
#print axioms CriticalLinePhasor.SeatAtomicPath.weightPath_pos
#print axioms CriticalLinePhasor.SeatAtomicPath.hankel_path_posSemidef
#print axioms CriticalLinePhasor.SeatAtomicPath.hankel_path_terminal
end AxiomAudit
