import Mathlib
import RequestProject.HarmonicPencilCell

/-!
# The enriched harmonic pencil: charged unsigned, charged signed, neutral (ledger 1145)

The existing pencil `HarmonicCell.harmonicPencil A B μ λ = !![A, B; μA, λB]` carries the charged
unsigned mass `A = Σ ‖χ(n)‖·a(n)` and the charged signed sum `B`; the neutral mass
`N₀ = Σ (1 − ‖χ(n)‖)·a(n)` is not an entry of it (ledger 1144). Here the neutral mass is given its
own channel: a third column, read with the unsigned parameter `μ` because it is unsigned mass,
like `A`.

    enrichedPencil A B N₀ μ λ = !![A, B, N₀; μA, λB, μN₀]

The three required properties:
* projection — forgetting the neutral column is the existing pencil (`enrichedPencil_project`);
* preservation — the neutral mass is an entry (`enrichedPencil_neutral`);
* rank-drop equivalence — the row Gram determinant is `|λ − μ|²·|B|²·(A² + N₀²)`
  (`enrichedPencil_rowGram_det`), so it vanishes exactly when `B = 0`
  (`enrichedPencil_rankDrop_iff`): the neutral mass neither obstructs a charged cancellation nor
  causes one. With `N₀ = 0` the row Gram is the existing pencil's (`enrichedPencil_rowGram_neutral_zero`),
  whose determinant equals the existing column Gram's (`rowGram_det_eq_colGram_det`).

Two designs that fail, recorded: putting `N₀` on a diagonal (`naivePencil`) makes every bank without
a neutral site rank-drop (`naivePencil_spurious`); the column Gram of the enriched pencil is always
singular (`enrichedPencil_colGram_det`), so the row Gram is the one that reads it.
-/

open Complex Matrix

namespace CriticalLinePhasor.EnrichedPencil

open CriticalLinePhasor.HarmonicCell

/-- The three-channel pencil: columns charged unsigned `A`, charged signed `B`, neutral `N₀`;
the neutral channel is read with the unsigned parameter `μ`. -/
def enrichedPencil (A : ℝ) (B : ℂ) (N₀ : ℝ) (μ lam : ℂ) : Matrix (Fin 2) (Fin 3) ℂ :=
  !![(A : ℂ), B, (N₀ : ℂ); μ * A, lam * B, μ * N₀]

/-- **Projection:** forgetting the neutral column gives the existing pencil. -/
theorem enrichedPencil_project (A : ℝ) (B : ℂ) (N₀ : ℝ) (μ lam : ℂ) :
    (fun i j => enrichedPencil A B N₀ μ lam i (Fin.castSucc j)) =
      harmonicPencil (A : ℂ) B μ lam := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **Preservation:** the neutral mass is an entry of the enriched pencil. -/
theorem enrichedPencil_neutral (A : ℝ) (B : ℂ) (N₀ : ℝ) (μ lam : ℂ) :
    enrichedPencil A B N₀ μ lam 0 2 = N₀ :=
  rfl

/-- The row Gram determinant: `(λ − μ)·conj(λ − μ) · B·conj B · (A² + N₀²)`. -/
theorem enrichedPencil_rowGram_det (A : ℝ) (B : ℂ) (N₀ : ℝ) (μ lam : ℂ) :
    (enrichedPencil A B N₀ μ lam * (enrichedPencil A B N₀ μ lam)ᴴ).det =
      (lam - μ) * star (lam - μ) * (B * star B) * ((A : ℂ) ^ 2 + (N₀ : ℂ) ^ 2) := by
  rw [Matrix.det_fin_two]
  simp only [enrichedPencil, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, star_sub, Complex.star_def, map_mul, Complex.conj_ofReal]
  ring

/-- **Rank-drop equivalence:** with `λ ≠ μ` and `A ≠ 0`, the enriched pencil's row Gram is
singular exactly when the charged signed channel vanishes, whatever the neutral mass. -/
theorem enrichedPencil_rankDrop_iff (A : ℝ) (B : ℂ) (N₀ : ℝ) (μ lam : ℂ) (hlam : lam ≠ μ)
    (hA : A ≠ 0) :
    (enrichedPencil A B N₀ μ lam * (enrichedPencil A B N₀ μ lam)ᴴ).det = 0 ↔ B = 0 := by
  rw [enrichedPencil_rowGram_det]
  have h1 : lam - μ ≠ 0 := sub_ne_zero.mpr hlam
  have h2 : star (lam - μ) ≠ 0 := star_ne_zero.mpr h1
  have hA2 : 0 < A ^ 2 := lt_of_le_of_ne (sq_nonneg A) (Ne.symm (pow_ne_zero 2 hA))
  have hpos : (0 : ℝ) < A ^ 2 + N₀ ^ 2 := by nlinarith [sq_nonneg N₀]
  have h3 : ((A : ℂ) ^ 2 + (N₀ : ℂ) ^ 2) ≠ 0 := by
    have : (((A ^ 2 + N₀ ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    simpa using this
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h h1
        · exact absurd h h2
      · rcases mul_eq_zero.mp h with h | h
        · exact h
        · exact star_eq_zero.mp h
    · exact absurd h h3
  · intro h
    rw [h]
    ring

/-- With no neutral mass the enriched row Gram is the existing pencil's row Gram. -/
theorem enrichedPencil_rowGram_neutral_zero (A : ℝ) (B : ℂ) (μ lam : ℂ) :
    enrichedPencil A B 0 μ lam * (enrichedPencil A B 0 μ lam)ᴴ =
      harmonicPencil (A : ℂ) B μ lam * (harmonicPencil (A : ℂ) B μ lam)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [enrichedPencil, harmonicPencil, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

/-- For a square pencil the row Gram and the existing column Gram have the same determinant. -/
theorem rowGram_det_eq_colGram_det (H : Matrix (Fin 2) (Fin 2) ℂ) :
    (H * Hᴴ).det = (Hᴴ * H).det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm]

/-! ## Two designs that fail -/

/-- Naive design: the neutral mass on the diagonal of a square pencil. -/
def naivePencil (A : ℝ) (B : ℂ) (N₀ : ℝ) (μ lam : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(A : ℂ), B, 0; μ * A, lam * B, 0; 0, 0, (N₀ : ℂ)]

theorem naivePencil_det (A : ℝ) (B : ℂ) (N₀ : ℝ) (μ lam : ℂ) :
    (naivePencil A B N₀ μ lam).det = (N₀ : ℂ) * ((lam - μ) * A * B) := by
  rw [Matrix.det_fin_three]
  simp [naivePencil]
  ring

/-- **The naive design manufactures focal events:** with no neutral mass it rank-drops although
the existing pencil does not. -/
theorem naivePencil_spurious :
    (harmonicPencil ((1 : ℝ) : ℂ) 1 0 1).det ≠ 0 ∧ (naivePencil 1 1 0 0 1).det = 0 := by
  refine ⟨?_, ?_⟩
  · rw [harmonicPencil_det]
    norm_num
  · rw [naivePencil_det]
    simp

/-- The column Gram of the enriched pencil is always singular (rank at most 2), so it cannot read
the pencil; the row Gram does. -/
theorem enrichedPencil_colGram_det (A : ℝ) (B : ℂ) (N₀ : ℝ) (μ lam : ℂ) :
    ((enrichedPencil A B N₀ μ lam)ᴴ * enrichedPencil A B N₀ μ lam).det = 0 := by
  rw [Matrix.det_fin_three]
  simp only [enrichedPencil, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  ring

end CriticalLinePhasor.EnrichedPencil

#print axioms CriticalLinePhasor.EnrichedPencil.enrichedPencil_project
#print axioms CriticalLinePhasor.EnrichedPencil.enrichedPencil_rowGram_det
#print axioms CriticalLinePhasor.EnrichedPencil.enrichedPencil_rankDrop_iff
#print axioms CriticalLinePhasor.EnrichedPencil.enrichedPencil_rowGram_neutral_zero
#print axioms CriticalLinePhasor.EnrichedPencil.naivePencil_spurious
#print axioms CriticalLinePhasor.EnrichedPencil.enrichedPencil_colGram_det
