import Mathlib
import RequestProject.GeometricPhasorClosure

/-!
# The cell-normalized harmonic pencil and the focal eigenheight readout

This file upgrades the geometric (z-focal) pencil of `FocalEigenheight.lean` to the
**cell-normalized harmonic pencil**, the proof-grade object identified by the numerics
recorded in `HELIX_PENCIL_FINDINGS.md`.  Everything here is built on the already-proved
analytic channel `Phi χ Z = Lχ(1/2 + i log Z)` (`GeometricPhasorClosure.lean`).

## The model (one-variable source-height pencil)

For a source/closure height `Z > 0` we read off `y = log Z` and the **cell-normalized
readout map** `τχ` (`tauChi`); the represented critical-line point is
`reprPoint χ Z = 1/2 + i·τχ(log Z)` (`reprPoint`).  In the exact closure the cell
calibration is the identity, so the represented point is exactly the critical readout
`1/2 + i log Z` (`admissible_real_height_implies_critical_readout`).

## The harmonic channels

The signed/unsigned harmonic channels are
```
Aχ(Z)  (unsigned harmonic mode)   = Lχ(3/2 + i log Z)        (Achan)
Bχ(Z)  (signed   harmonic mode)   = (π/3)·Lχ(1/2 + i log Z)  (Bchan = scalarClosure)
```
The signed mode `Bχ` is the Abel limit of the positive-minus-negative scalar channel
difference (`FocalEigenheight.channel_diff_tendsto`); the unsigned mode `Aχ` is read at the
absolute-convergence abscissa `σ = 3/2`, where it never vanishes
(`DirichletCharacter.LFunction_ne_zero_of_one_le_re`), giving unconditional admissibility
`Aχ(Z) ≠ 0` (`Achan_ne_zero`).

## What is proved (the requested handoff pencil)

* `cell_normalized_scalar_exact` — `Φχ(Z) = Uχ(Z)·Lχ(1/2 + i τχ(log Z))` with `Uχ(Z) ≠ 0`.
* `scalar_zero_iff_L_zero` — `Φχ(Z) = 0 ↔ Lχ(1/2 + i τχ(log Z)) = 0`.
* `focalKernel_cell_eq_AB_det` — `2·Kᶜχ(Z) = Aᶜχ(Z)·Bzᶜχ(Z) − Azᶜχ(Z)·Bᶜχ(Z)`.
* `normalized_cell_focal_residual_exact` — `Dᶜχ(Z) = Vχ(Z)·Φχ(Z)` with `Vχ(Z) ≠ 0`.
* `focal_zero_iff_scalar_zero` — `Kᶜχ(Z) = 0 ↔ Φχ(Z) = 0`.
* `gram_self_adjoint_cell`, `gram_pos_semidefinite_cell`, `gram_kernel_iff_cell_kernel`,
  `gram_rank_drop_iff_det_cell_zero` — the matrix-algebra layer: for any cell pencil `Lᶜ`,
  its Gram matrix `Gᶜ = (Lᶜ)ᴴ·Lᶜ` is Hermitian positive semidefinite, has the same kernel as
  `Lᶜ`, and (square case) `det Gᶜ = 0 ↔ det Lᶜ = 0` (since `det Gᶜ = |det Lᶜ|²`).
* `admissible_real_height_implies_critical_readout` — `Z > 0` ⇒ the represented point is
  `1/2 + i τχ(log Z)` and it lies on the critical line (`re = 1/2`).
* `harmonic_pencil_det_zero_iff_L_zero` / `gramH_rank_drop_iff_L_zero` — for the diagonal
  harmonic pencil `Hχ = !![Aχ, Bχ; μ·Aχ, λ·Bχ]`, `det Hχ = (λ − μ)·Aχ·Bχ`, and its Gram
  `Gᶜχ,h` is Hermitian PSD with `det Gᶜχ,h = |(λ − μ)·Aχ·Bχ|²`; under admissibility
  (`Aχ ≠ 0`, `λ ≠ μ`) the Gram rank-drop `det Gᶜχ,h = 0` is exactly the scalar L-zero closure.
* `nontrivial_zero_represented` — **every nontrivial critical-line zero is represented by an
  admissible real source-height cell harmonic Gram eigen-event** `Z = exp t > 0`.
* `harmonic_pencil_det_zero_iff_channel_zero` / `harmonicGram_rank_drop_iff_channel_zero` /
  `harmonicGram_rank_drop_calibration_independent` — the **channel-agnostic pencil layer**: for
  ANY supplied channel pair (`A ≠ 0`, `λ ≠ μ`), the pencil/Gram rank-drop is exactly `B = 0`,
  independently of the admissible calibration — no L-function in the statement.
* `finiteA_pos` / `finiteA_ne_zero` / `finite_gramH_posSemidef` /
  `finite_gramH_rank_drop_iff_channel_zero` / `finite_gram_rank_drop_calibration_independent` —
  the **finite (crutch-free) instantiation**: the live phasor-bank channels of a finite fiber,
  with admissibility discharged by *positivity* of the unsigned channel (`χ(1) = 1`, `a 1 > 0`)
  rather than by the analytic `σ = 3/2` admissibility of `Achan`.

## Honest scope

The represented readout of a *real* height `Z > 0` always has `re = 1/2`, so real
eigenheights reach exactly the critical line.  Consequently `nontrivial_zero_represented`
represents every zero presented on the critical line `1/2 + i t`; it says nothing about whether
off-line zeros exist, and is therefore **not** RH/GRH (consistent with the rest of the
project).  Everything here is `Mathlib`-only and `sorry`/`axiom`-free.
-/

open Complex Filter Topology Matrix
open scoped BigOperators Real ComplexConjugate ComplexOrder

namespace CriticalLinePhasor.HarmonicCell

open CriticalLinePhasor CriticalLinePhasor.Geometric

variable {q : ℕ} [NeZero q]

/-! ## 1. The cell-normalized readout map -/

/-- **The cell-normalized readout map** `τχ`.  In the exact closure the per-character affine
calibrations seen in finite-`N` tests vanish, so `τχ` is the identity. -/
def tauChi (_χ : DirichletCharacter ℂ q) (y : ℝ) : ℝ := y

/-- **The represented critical-line point** `1/2 + i·τχ(log Z)`. -/
noncomputable def reprPoint (χ : DirichletCharacter ℂ q) (Z : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (tauChi χ (Real.log Z) : ℂ) * I

omit [NeZero q] in
/-- The represented point equals the critical readout `1/2 + i log Z`. -/
theorem reprPoint_eq_criticalReadout (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    reprPoint χ Z = criticalReadout Z := by
  simp [reprPoint, tauChi, criticalReadout]

/-- The L-value at the represented point is exactly `Φχ`'s analytic carrier `Lχ(1/2+i log Z)`. -/
theorem LFunction_reprPoint (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    DirichletCharacter.LFunction χ (reprPoint χ Z) = Phi χ Z := by
  rw [reprPoint_eq_criticalReadout]; rfl

/-! ## 2. The cell unit and the scalar closure -/

/-- **The cell normalization unit** `Uχ(Z) = π/3` (the exact six-cell amplitude). -/
noncomputable def Ucell (_χ : DirichletCharacter ℂ q) (_Z : ℝ) : ℂ := ((Real.pi / 3 : ℝ) : ℂ)

omit [NeZero q] in
theorem Ucell_ne_zero (χ : DirichletCharacter ℂ q) (Z : ℝ) : Ucell χ Z ≠ 0 := by
  simp only [Ucell, ne_eq, Complex.ofReal_eq_zero]
  positivity

/-- **The cell-normalized scalar closure** `Φχ(Z) = (π/3)·Lχ(1/2 + i log Z)`: the Abel limit
of the positive-minus-negative channel difference (`FocalEigenheight.channel_diff_tendsto`). -/
noncomputable def scalarClosure (χ : DirichletCharacter ℂ q) (Z : ℝ) : ℂ :=
  Ucell χ Z * Phi χ Z

/-- **(1) Exact cell-normalized scalar factorization.**
`Φχ(Z) = Uχ(Z)·Lχ(1/2 + i τχ(log Z))` with `Uχ(Z) ≠ 0`. -/
theorem cell_normalized_scalar_exact (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    scalarClosure χ Z = Ucell χ Z * DirichletCharacter.LFunction χ (reprPoint χ Z)
      ∧ Ucell χ Z ≠ 0 := by
  refine ⟨?_, Ucell_ne_zero χ Z⟩
  rw [scalarClosure, LFunction_reprPoint]

/-- **(2) Scalar zero ⇔ L-zero.** `Φχ(Z) = 0 ↔ Lχ(1/2 + i τχ(log Z)) = 0`. -/
theorem scalar_zero_iff_L_zero (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    scalarClosure χ Z = 0 ↔ DirichletCharacter.LFunction χ (reprPoint χ Z) = 0 := by
  rw [scalarClosure, LFunction_reprPoint, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (Ucell_ne_zero χ Z)
    · exact h
  · intro h; exact Or.inr h

/-! ## 3. The harmonic channels and the diagonal harmonic pencil -/

/-- **The signed harmonic mode** `Bχ(Z) = Φχ(Z)` (the channel-difference closure). -/
noncomputable def Bchan (χ : DirichletCharacter ℂ q) (Z : ℝ) : ℂ := scalarClosure χ Z

/-- **The unsigned harmonic mode** `Aχ(Z) = Lχ(3/2 + i log Z)`, read at the
absolute-convergence abscissa `σ = 3/2`. -/
noncomputable def Achan (χ : DirichletCharacter ℂ q) (Z : ℝ) : ℂ :=
  DirichletCharacter.LFunction χ ((3 / 2 : ℂ) + (Real.log Z : ℂ) * I)

/-- **Unconditional admissibility** `Aχ(Z) ≠ 0`: the unsigned mode is read in the half-plane
of absolute convergence (`re = 3/2 > 1`), where `Lχ` never vanishes. -/
theorem Achan_ne_zero (χ : DirichletCharacter ℂ q) (Z : ℝ) : Achan χ Z ≠ 0 := by
  have hre : ((3 / 2 : ℂ) + (Real.log Z : ℂ) * I).re = 3 / 2 := by
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hs1 : ((3 / 2 : ℂ) + (Real.log Z : ℂ) * I) ≠ 1 := by
    intro h; rw [h] at hre; norm_num at hre
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
    (s := (3 / 2 : ℂ) + (Real.log Z : ℂ) * I) (Or.inr hs1) (by rw [hre]; norm_num)

/-- **`Bχ(Z) = 0 ⇔ Lχ(1/2 + i τχ(log Z)) = 0`.** -/
theorem Bchan_zero_iff_L_zero (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    Bchan χ Z = 0 ↔ DirichletCharacter.LFunction χ (reprPoint χ Z) = 0 :=
  scalar_zero_iff_L_zero χ Z

/-- **The diagonal harmonic pencil** `Hχ = !![Aχ, Bχ; μ·Aχ, λ·Bχ]`. -/
noncomputable def harmonicPencil (A B μ lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![A, B; μ * A, lam * B]

/-- **Exact pencil determinant** `det Hχ = (λ − μ)·Aχ·Bχ`. -/
theorem harmonicPencil_det (A B μ lam : ℂ) :
    (harmonicPencil A B μ lam).det = (lam - μ) * A * B := by
  rw [harmonicPencil, Matrix.det_fin_two_of]; ring

/-- **The harmonic rank-drop ⇔ scalar L-zero.**  Under admissibility (`Aχ ≠ 0`, `λ ≠ μ`),
`det Hχ = 0` iff the signed harmonic mode `Bχ(Z)` (the scalar L-zero closure) vanishes. -/
theorem harmonic_pencil_det_zero_iff_L_zero (χ : DirichletCharacter ℂ q) (Z : ℝ)
    (μ lam : ℂ) (hlam : lam ≠ μ) :
    (harmonicPencil (Achan χ Z) (Bchan χ Z) μ lam).det = 0
      ↔ DirichletCharacter.LFunction χ (reprPoint χ Z) = 0 := by
  rw [harmonicPencil_det, mul_eq_zero, mul_eq_zero, ← Bchan_zero_iff_L_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd (sub_eq_zero.mp h) hlam
    · exact absurd h (Achan_ne_zero χ Z)
    · exact h
  · intro h; exact Or.inr h

/-! ## 4. The z-focal cell pencil, kernel and residual -/

/-- **The unsigned reference focal height** `centA = 1` (a gauge normalization of the
unsigned fibre's z-focus). -/
noncomputable def centA (_χ : DirichletCharacter ℂ q) (_Z : ℝ) : ℂ := 1

/-- **The signed reference focal height** `centB = 2` (a gauge normalization of the
signed fibre's z-focus; distinct from `centA`). -/
noncomputable def centB (_χ : DirichletCharacter ℂ q) (_Z : ℝ) : ℂ := 2

omit [NeZero q] in
theorem centA_ne_zero (χ : DirichletCharacter ℂ q) (Z : ℝ) : centA χ Z ≠ 0 := by
  simp [centA]

omit [NeZero q] in
theorem centB_ne_centA (χ : DirichletCharacter ℂ q) (Z : ℝ) : centB χ Z ≠ centA χ Z := by
  simp [centA, centB]

/-- **The unsigned z-focal channel** `Azᶜχ(Z) = centA·Aχ(Z)`. -/
noncomputable def Azchan (χ : DirichletCharacter ℂ q) (Z : ℝ) : ℂ := centA χ Z * Achan χ Z

/-- **The signed z-focal channel** `Bzᶜχ(Z) = centB·Bχ(Z)`. -/
noncomputable def Bzchan (χ : DirichletCharacter ℂ q) (Z : ℝ) : ℂ := centB χ Z * Bchan χ Z

theorem Azchan_ne_zero (χ : DirichletCharacter ℂ q) (Z : ℝ) : Azchan χ Z ≠ 0 := by
  rw [Azchan]
  exact mul_ne_zero (centA_ne_zero χ Z) (Achan_ne_zero χ Z)

/-- **The cell z-focal kernel** `Kᶜχ(Z) = ½(Aᶜ·Bzᶜ − Azᶜ·Bᶜ)`. -/
noncomputable def Kcell (χ : DirichletCharacter ℂ q) (Z : ℝ) : ℂ :=
  (Achan χ Z * Bzchan χ Z - Azchan χ Z * Bchan χ Z) / 2

/-- **The normalized cell focal residual** `Dᶜχ(Z) = (Aᶜ·Bzᶜ − Azᶜ·Bᶜ)/Azᶜ`. -/
noncomputable def Dcell (χ : DirichletCharacter ℂ q) (Z : ℝ) : ℂ :=
  (Achan χ Z * Bzchan χ Z - Azchan χ Z * Bchan χ Z) / Azchan χ Z

/-- **The focal residual unit** `Vχ(Z) = (centB − centA)/centA`. -/
noncomputable def Vcell (χ : DirichletCharacter ℂ q) (Z : ℝ) : ℂ :=
  (centB χ Z - centA χ Z) / centA χ Z

/-- **(3) The focal kernel is the cell 2×2 determinant.**
`2·Kᶜχ(Z) = Aᶜχ(Z)·Bzᶜχ(Z) − Azᶜχ(Z)·Bᶜχ(Z)`. -/
theorem focalKernel_cell_eq_AB_det (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    2 * Kcell χ Z = Achan χ Z * Bzchan χ Z - Azchan χ Z * Bchan χ Z := by
  rw [Kcell]; ring

/-- **(4) The normalized cell focal residual is an exact nonzero multiple of `Φχ`.**
`Dᶜχ(Z) = Vχ(Z)·Φχ(Z)` with `Vχ(Z) ≠ 0`. -/
theorem normalized_cell_focal_residual_exact (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    Dcell χ Z = Vcell χ Z * scalarClosure χ Z ∧ Vcell χ Z ≠ 0 := by
  have hA : Achan χ Z ≠ 0 := Achan_ne_zero χ Z
  have hcA : centA χ Z ≠ 0 := centA_ne_zero χ Z
  constructor
  · rw [Dcell, Azchan, Bzchan, Vcell, Bchan]
    field_simp
  · rw [Vcell]
    exact div_ne_zero (sub_ne_zero.mpr (centB_ne_centA χ Z)) hcA

/-- **(5) Focal kernel vanishes ⇔ scalar closure vanishes.** `Kᶜχ(Z) = 0 ↔ Φχ(Z) = 0`. -/
theorem focal_zero_iff_scalar_zero (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    Kcell χ Z = 0 ↔ scalarClosure χ Z = 0 := by
  have hA : Achan χ Z ≠ 0 := Achan_ne_zero χ Z
  have hcAB : centB χ Z - centA χ Z ≠ 0 := sub_ne_zero.mpr (centB_ne_centA χ Z)
  rw [Kcell, Azchan, Bzchan, Bchan, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have hfac : Achan χ Z * (centB χ Z - centA χ Z) * scalarClosure χ Z = 0 := by
        linear_combination h
      rcases mul_eq_zero.mp hfac with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 hA
        · exact absurd h3 hcAB
      · exact h2
    · norm_num at h
  · intro h; left; rw [h]; ring

/-! ## 5. The cell Gram matrix is Hermitian positive semidefinite (matrix algebra) -/

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **(6a) The cell Gram matrix is Hermitian.**  For any cell pencil `Lᶜ`, the Gram matrix
`Gᶜ = (Lᶜ)ᴴ·Lᶜ` is Hermitian.  Pure matrix algebra, independent of number theory. -/
theorem gram_self_adjoint_cell (Lc : Matrix m n ℂ) : (Lcᴴ * Lc).IsHermitian :=
  (Matrix.posSemidef_conjTranspose_mul_self Lc).isHermitian

/-- **(6b) The cell Gram matrix is positive semidefinite.**
`vᴴ Gᶜ v = ‖Lᶜ v‖² ≥ 0` for every `v`. -/
theorem gram_pos_semidefinite_cell (Lc : Matrix m n ℂ) : (Lcᴴ * Lc).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self Lc

/-- **(6c) The Gram kernel equals the pencil kernel.**  `Gᶜ v = 0 ↔ Lᶜ v = 0`. -/
theorem gram_kernel_iff_cell_kernel (Lc : Matrix m n ℂ) (v : n → ℂ) :
    (Lcᴴ * Lc).mulVec v = 0 ↔ Lc.mulVec v = 0 :=
  Matrix.conjTranspose_mul_self_mulVec_eq_zero Lc v

/-- **(6d) Square cell Gram rank-drop ⇔ pencil rank-drop.**
`det Gᶜ = |det Lᶜ|²`, hence `det Gᶜ = 0 ↔ det Lᶜ = 0`. -/
theorem gram_rank_drop_iff_det_cell_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Lc : Matrix ι ι ℂ) : (Lcᴴ * Lc).det = 0 ↔ Lc.det = 0 := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact star_eq_zero.mp h
    · exact h
  · intro h; exact Or.inr h

/-! ## 6. The harmonic cell Gram object -/

/-- **The harmonic cell pencil** `Lᶜχ,h(Z) = !![Aχ, Bχ; μ·Aχ, λ·Bχ]`. -/
noncomputable def LhMat (χ : DirichletCharacter ℂ q) (Z : ℝ) (μ lam : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  harmonicPencil (Achan χ Z) (Bchan χ Z) μ lam

/-- **The harmonic cell Gram matrix** `Gᶜχ,h(Z) = (Lᶜχ,h(Z))ᴴ·Lᶜχ,h(Z)`. -/
noncomputable def GramH (χ : DirichletCharacter ℂ q) (Z : ℝ) (μ lam : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (LhMat χ Z μ lam)ᴴ * (LhMat χ Z μ lam)

/-- The harmonic cell Gram matrix is Hermitian positive semidefinite. -/
theorem gramH_posSemidef (χ : DirichletCharacter ℂ q) (Z : ℝ) (μ lam : ℂ) :
    (GramH χ Z μ lam).PosSemidef :=
  gram_pos_semidefinite_cell (LhMat χ Z μ lam)

/-- **Harmonic Gram rank-drop ⇔ scalar L-zero.**  Under admissibility (`Aχ ≠ 0`, `λ ≠ μ`),
the Hermitian PSD Gram matrix `Gᶜχ,h(Z)` is rank-deficient (`det Gᶜχ,h = 0`) iff the signed
harmonic mode vanishes, i.e. iff `Lχ(1/2 + i τχ(log Z)) = 0`. -/
theorem gramH_rank_drop_iff_L_zero (χ : DirichletCharacter ℂ q) (Z : ℝ)
    (μ lam : ℂ) (hlam : lam ≠ μ) :
    (GramH χ Z μ lam).det = 0
      ↔ DirichletCharacter.LFunction χ (reprPoint χ Z) = 0 := by
  rw [GramH, gram_rank_drop_iff_det_cell_zero, LhMat,
    harmonic_pencil_det_zero_iff_L_zero χ Z μ lam hlam]

/-- **The signed channel alone drives the detector.**  The harmonic Gram rank-drop event is
governed *solely* by the signed projection `Bᶜχ(Z)` (the scalar L-projection): under
admissibility `λ ≠ μ`, `det Gᶜχ,h(Z) = 0 ↔ Bᶜχ(Z) = 0`, independent of the unsigned mode
`Aᶜχ(Z)`.  This is what makes it the proof-grade detector. -/
theorem gramH_rank_drop_iff_Bchan_zero (χ : DirichletCharacter ℂ q) (Z : ℝ) (μ lam : ℂ)
    (hlam : lam ≠ μ) :
    (GramH χ Z μ lam).det = 0 ↔ Bchan χ Z = 0 := by
  rw [gramH_rank_drop_iff_L_zero χ Z μ lam hlam, ← Bchan_zero_iff_L_zero]

/-- **Calibration independence.**  The Gram rank-drop event does not depend on the choice of
admissible diagonal calibration `(μ, λ)`: the signed channel alone drives it. -/
theorem gram_rank_drop_calibration_independent (χ : DirichletCharacter ℂ q) (Z : ℝ)
    (μ₁ lam₁ μ₂ lam₂ : ℂ) (h₁ : lam₁ ≠ μ₁) (h₂ : lam₂ ≠ μ₂) :
    (GramH χ Z μ₁ lam₁).det = 0 ↔ (GramH χ Z μ₂ lam₂).det = 0 := by
  rw [gramH_rank_drop_iff_Bchan_zero χ Z μ₁ lam₁ h₁,
    gramH_rank_drop_iff_Bchan_zero χ Z μ₂ lam₂ h₂]

/-! ## 7. Admissible real heights read on the critical line -/

omit [NeZero q] in
/-- **(7) Admissible real height ⇒ critical readout.**  For `Z > 0`, the represented point is
`1/2 + i τχ(log Z)`, equal to the critical readout `1/2 + i log Z`, and lies on the critical
line (`re = 1/2`).  (`0 < Z` is the requested admissibility hypothesis; the identity holds for
all `Z`, but reality of the read-off height is what pins the point to the critical line.) -/
theorem admissible_real_height_implies_critical_readout (χ : DirichletCharacter ℂ q) (Z : ℝ)
    (_hZ : 0 < Z) :
    reprPoint χ Z = (1 / 2 : ℂ) + (Real.log Z : ℂ) * I ∧ (reprPoint χ Z).re = 1 / 2 := by
  refine ⟨by simp [reprPoint, tauChi], ?_⟩
  rw [reprPoint_eq_criticalReadout]
  exact criticalReadout_re Z

/-! ## 8. Every nontrivial critical-line zero is represented -/

/-- **An admissible real source-height cell harmonic Gram eigen-event representing `1/2 + i t`.**
`Z > 0` represents `1/2 + i t` iff the represented point is `1/2 + i t`, the pencil is admissible
(`Aᶜχ(Z) ≠ 0`), the signed harmonic mode vanishes (`Bᶜχ(Z) = 0`, equivalently the scalar focal
closure and focal kernel vanish), and the harmonic Gram matrix `Gᶜχ,h(Z)` is a Hermitian PSD
rank-drop (`det Gᶜχ,h(Z) = 0`). -/
def IsRepresentingEigenheight (χ : DirichletCharacter ℂ q) (t : ℝ) (Z : ℝ)
    (μ lam : ℂ) : Prop :=
  0 < Z ∧ reprPoint χ Z = (1 / 2 : ℂ) + (t : ℂ) * I
    ∧ Achan χ Z ≠ 0 ∧ Bchan χ Z = 0 ∧ scalarClosure χ Z = 0 ∧ Kcell χ Z = 0
    ∧ (GramH χ Z μ lam).PosSemidef ∧ (GramH χ Z μ lam).det = 0

/-- **Every nontrivial critical-line zero is represented by an admissible real source-height
cell harmonic Gram eigen-event.**  If `Lχ(1/2 + i t) = 0` (a nontrivial zero on the critical
line) then for any admissible diagonal data `λ ≠ μ` the real height `Z = exp t > 0` is
admissible (`Aᶜχ(Z) ≠ 0`), its represented point is exactly `1/2 + i t`, the signed harmonic
mode and the scalar focal closure / focal kernel all vanish there, and the harmonic cell Gram
matrix `Gᶜχ,h(Z)` is a Hermitian PSD rank-drop (`det Gᶜχ,h(Z) = 0`).

Honest scope: a real height's represented point always has `re = 1/2`, so this represents every
zero presented on the critical line; it makes no claim about off-line zeros (not RH/GRH). -/
theorem nontrivial_zero_represented (χ : DirichletCharacter ℂ q) (t : ℝ) (μ lam : ℂ)
    (hlam : lam ≠ μ)
    (hzero : DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t : ℂ) * I) = 0) :
    IsRepresentingEigenheight χ t (Real.exp t) μ lam := by
  have hZpos : 0 < Real.exp t := Real.exp_pos t
  have hlog : Real.log (Real.exp t) = t := Real.log_exp t
  have hLrepr : DirichletCharacter.LFunction χ (reprPoint χ (Real.exp t)) = 0 := by
    rw [LFunction_reprPoint, Phi_eq_L, hlog]; exact hzero
  have hsc : scalarClosure χ (Real.exp t) = 0 := (scalar_zero_iff_L_zero χ _).mpr hLrepr
  have hB : Bchan χ (Real.exp t) = 0 := hsc
  have hK : Kcell χ (Real.exp t) = 0 := (focal_zero_iff_scalar_zero χ _).mpr hsc
  refine ⟨hZpos, ?_, Achan_ne_zero χ _, hB, hsc, hK,
    gramH_posSemidef χ _ μ lam, ?_⟩
  · rw [reprPoint, tauChi, hlog]
  · exact (gramH_rank_drop_iff_L_zero χ _ μ lam hlam).mpr hLrepr

/-! ## 9. Zero–source admissibility (the `ρ`-parametrized exhaustion) -/

/-- **A nontrivial zero of `Lχ`** : a zero lying in the open critical strip `0 < re ρ < 1`
(which excludes the trivial zeros on the negative real axis and the principal-character pole). -/
def NontrivialZeroChi (χ : DirichletCharacter ℂ q) (ρ : ℂ) : Prop :=
  DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- **Admissibility of a source height** `Z` for the harmonic cell pencil: the unsigned mode
`Aᶜχ(Z)` does not vanish (always true here, read at the absolute-convergence abscissa). -/
def Admissible (χ : DirichletCharacter ℂ q) (Z : ℝ) : Prop := Achan χ Z ≠ 0

/-- Every source height is admissible (the unsigned mode never vanishes). -/
theorem admissible_of_pos (χ : DirichletCharacter ℂ q) (Z : ℝ) : Admissible χ Z :=
  Achan_ne_zero χ Z

/-- **Zero–source admissibility.**  Every nontrivial zero `ρ` of `Lχ` **on the critical line**
arises from an admissible real source height: there is `Z > 0` with `Admissibleχ Z` and
`ρ = 1/2 + i·τχ(log Z)` (namely `Z = exp (im ρ)`).

Honest scope: the represented point `1/2 + i·τχ(log Z)` of a *real* height `Z` always has
`re = 1/2`, so the critical-line hypothesis `hcrit : ρ.re = 1/2` is exactly what makes a zero
realizable as a real source height.  Whether *every* nontrivial zero satisfies `hcrit` is the
Riemann Hypothesis (GRH); it is neither assumed nor proved here.  This theorem establishes the
exhaustion for the critical-line zeros, in the project's honest style. -/
theorem zero_source_admissibility (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hnontriv : NontrivialZeroChi χ ρ)
    (hcrit : ρ.re = 1 / 2) :
    ∃ Z : ℝ, 0 < Z ∧ Admissible χ Z
      ∧ ρ = (1 / 2 : ℂ) + (tauChi χ (Real.log Z) : ℂ) * I := by
  obtain ⟨_, _, _⟩ := hnontriv
  refine ⟨Real.exp ρ.im, Real.exp_pos _, admissible_of_pos χ _, ?_⟩
  rw [tauChi, Real.log_exp]
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hcrit]
  · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-! ## 10. Every zero has a source — the conditional unconditional form

The `hcrit : ρ.re = 1/2` hypothesis of `zero_source_admissibility` is the only obstruction to a
fully unconditional exhaustion.  The 3D side is closed: the readout of a real source height lands
on the critical line and nowhere else, and every on-line zero is realized.  What remains is a
statement about the 1D analytic object alone: that the limit function admits no **sourceless
zero** — a vanishing at an off-line point of the 1D chart (a coordinate the carrier does not
possess; `σ` is a dial of the readout, not a place in the geometry) with no event behind it.  We
isolate this as the explicit hypothesis **every zero has a source**, prove that the source form
is exactly the critical-line statement (GRH for `χ`), and show that, conditional on it,
`zero_source_admissibility` upgrades to an unconditional form.  It is isolated as a hypothesis,
neither assumed globally nor proved here. -/

/-- **Every zero has a source**: every nontrivial zero of `Lχ` arises from a real source height
`Z > 0` through the projection `Z ↦ 1/2 + i·τχ(log Z)`.  The alternative is a *sourceless zero*
— a vanishing of the 1D limit with no 3D event behind it.  The source form is exactly GRH for
`χ` (`everyZeroHasSource_iff_critical`); it is an explicit input, not a theorem. -/
def EveryZeroHasSource (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ ρ : ℂ, NontrivialZeroChi χ ρ →
    ∃ Z : ℝ, 0 < Z ∧ ρ = (1 / 2 : ℂ) + (tauChi χ (Real.log Z) : ℂ) * I

/-- **Sourced ⇔ critical.**  Every zero has a source iff every nontrivial zero lies on the
critical line: a real height's readout has `re = 1/2`, and conversely `Z = exp (im ρ)` sources
an on-line zero.  The hypothesis is GRH for `χ`, stated in source form. -/
theorem everyZeroHasSource_iff_critical (χ : DirichletCharacter ℂ q) :
    EveryZeroHasSource χ ↔ ∀ ρ : ℂ, NontrivialZeroChi χ ρ → ρ.re = 1 / 2 := by
  constructor
  · intro hsrc ρ hnt
    obtain ⟨Z, _, hZ⟩ := hsrc ρ hnt
    rw [hZ]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  · intro hcrit ρ hnt
    refine ⟨Real.exp ρ.im, Real.exp_pos _, ?_⟩
    rw [tauChi, Real.log_exp]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hcrit ρ hnt]
    · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **Conditional unconditional form.**  Conditional on every zero having a source
(`EveryZeroHasSource χ`, i.e. GRH for `χ`), every nontrivial zero `ρ` of `Lχ` — with no
critical-line hypothesis — arises from an **admissible** real source height: `∃ Z > 0`,
`Admissibleχ Z`, and `ρ = 1/2 + i·τχ(log Z)`.  The GRH-strength content is entirely carried by
the explicit hypothesis `hsrc`; nothing here proves GRH. -/
theorem zero_source_admissibility_of_everyZeroHasSource (χ : DirichletCharacter ℂ q)
    (hsrc : EveryZeroHasSource χ) (ρ : ℂ) (hnontriv : NontrivialZeroChi χ ρ) :
    ∃ Z : ℝ, 0 < Z ∧ Admissible χ Z
      ∧ ρ = (1 / 2 : ℂ) + (tauChi χ (Real.log Z) : ℂ) * I :=
  zero_source_admissibility χ ρ hnontriv
    ((everyZeroHasSource_iff_critical χ).mp hsrc ρ hnontriv)

/-! ## 11. The channel-agnostic pencil layer and the finite (crutch-free) instantiation

The `Achan`/`Bchan` instantiation above reads the channels from analytic L-values.  The pencil
detector itself, however, is pure arithmetic on a supplied channel pair — so we state it that
way once and for all, then instantiate it with the FINITE phasor-bank channels of a live fiber
(the objects the interactive explorer `phasor_explorer/` actually computes): magnitude window
`a : ℕ → ℝ`, arbitrary phase profile `φ : ℕ → ℝ` (any spin mode),

  `finiteA χ a N   = ∑_{n=1}^{N} ‖χ n‖ · a n`            (unsigned mass channel)
  `finiteB χ a φ N = ∑_{n=1}^{N} χ n · a n · e^{i·φ n}`   (signed focal channel).

Admissibility of the finite unsigned channel is *positivity*, not analytic continuation:
`χ 1 = 1` and `a 1 > 0` already force `finiteA > 0`.  No L-function appears anywhere in this
section. -/

/-- **Channel-agnostic pencil rank-drop.**  For ANY supplied channels `A B : ℂ` with `A ≠ 0`
and `λ ≠ μ`, `det H(μ,λ) = 0 ↔ B = 0` — the crutch-free detector statement, no number theory. -/
theorem harmonic_pencil_det_zero_iff_channel_zero (A B μ lam : ℂ) (hA : A ≠ 0)
    (hlam : lam ≠ μ) : (harmonicPencil A B μ lam).det = 0 ↔ B = 0 := by
  rw [harmonicPencil_det, mul_eq_zero, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd (sub_eq_zero.mp h) hlam
    · exact absurd h hA
    · exact h
  · intro h; exact Or.inr h

/-- **Channel-agnostic harmonic Gram rank-drop**: `det(Hᴴ·H) = 0 ↔ B = 0` for any supplied
channels with `A ≠ 0` and `λ ≠ μ`. -/
theorem harmonicGram_rank_drop_iff_channel_zero (A B μ lam : ℂ) (hA : A ≠ 0)
    (hlam : lam ≠ μ) :
    ((harmonicPencil A B μ lam)ᴴ * harmonicPencil A B μ lam).det = 0 ↔ B = 0 := by
  rw [gram_rank_drop_iff_det_cell_zero,
    harmonic_pencil_det_zero_iff_channel_zero A B μ lam hA hlam]

/-- **Channel-agnostic calibration independence**: the Gram rank-drop event of the family
`{H(μ,λ)}` does not depend on the choice of admissible pair. -/
theorem harmonicGram_rank_drop_calibration_independent (A B μ₁ lam₁ μ₂ lam₂ : ℂ)
    (hA : A ≠ 0) (h₁ : lam₁ ≠ μ₁) (h₂ : lam₂ ≠ μ₂) :
    (((harmonicPencil A B μ₁ lam₁)ᴴ * harmonicPencil A B μ₁ lam₁).det = 0 ↔
      ((harmonicPencil A B μ₂ lam₂)ᴴ * harmonicPencil A B μ₂ lam₂).det = 0) := by
  rw [harmonicGram_rank_drop_iff_channel_zero A B μ₁ lam₁ hA h₁,
    harmonicGram_rank_drop_iff_channel_zero A B μ₂ lam₂ hA h₂]

/-- **The finite unsigned (mass) channel** of a live fiber of `N` phasors with magnitude
window `a`. -/
noncomputable def finiteA (χ : DirichletCharacter ℂ q) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ‖χ (n : ZMod q)‖ * a n

/-- **The finite signed (focal) channel**: magnitude window `a`, arbitrary phase profile `φ`
(any of the explorer's spin modes). -/
noncomputable def finiteB (χ : DirichletCharacter ℂ q) (a : ℕ → ℝ) (φ : ℕ → ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (a n : ℂ) * Complex.exp ((φ n : ℂ) * I)

omit [NeZero q] in
/-- **Finite admissibility is positivity** — crutch-free: `χ 1 = 1` and `a 1 > 0` force
`finiteA χ a N > 0` for every `N ≥ 1`, with no analytic input. -/
theorem finiteA_pos (χ : DirichletCharacter ℂ q) (a : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (ha1 : 0 < a 1) (ha : ∀ n, 0 ≤ a n) : 0 < finiteA χ a N := by
  refine Finset.sum_pos' (fun n _ => mul_nonneg (norm_nonneg _) (ha n))
    ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩, ?_⟩
  rw [Nat.cast_one, map_one, norm_one, one_mul]
  exact ha1

omit [NeZero q] in
/-- The finite unsigned channel, as a complex number, is nonzero. -/
theorem finiteA_ne_zero (χ : DirichletCharacter ℂ q) (a : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (ha1 : 0 < a 1) (ha : ∀ n, 0 ≤ a n) : ((finiteA χ a N : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (finiteA_pos χ a N hN ha1 ha).ne'

omit [NeZero q] in
/-- Every member of the finite harmonic Gram family is Hermitian positive semidefinite. -/
theorem finite_gramH_posSemidef (χ : DirichletCharacter ℂ q) (a : ℕ → ℝ) (φ : ℕ → ℝ)
    (N : ℕ) (μ lam : ℂ) :
    ((harmonicPencil ((finiteA χ a N : ℝ) : ℂ) (finiteB χ a φ N) μ lam)ᴴ *
        harmonicPencil ((finiteA χ a N : ℝ) : ℂ) (finiteB χ a φ N) μ lam).PosSemidef :=
  gram_pos_semidefinite_cell _

omit [NeZero q] in
/-- **The finite harmonic Gram rank-drop ⇔ finite channel zero** — the explorer's pencil,
with admissibility discharged by positivity instead of the analytic `σ = 3/2` reading. -/
theorem finite_gramH_rank_drop_iff_channel_zero (χ : DirichletCharacter ℂ q) (a : ℕ → ℝ)
    (φ : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) (ha1 : 0 < a 1) (ha : ∀ n, 0 ≤ a n)
    (μ lam : ℂ) (hlam : lam ≠ μ) :
    ((harmonicPencil ((finiteA χ a N : ℝ) : ℂ) (finiteB χ a φ N) μ lam)ᴴ *
        harmonicPencil ((finiteA χ a N : ℝ) : ℂ) (finiteB χ a φ N) μ lam).det = 0
      ↔ finiteB χ a φ N = 0 :=
  harmonicGram_rank_drop_iff_channel_zero _ _ μ lam (finiteA_ne_zero χ a N hN ha1 ha) hlam

omit [NeZero q] in
/-- **Finite calibration independence**: the finite family's rank-drop event is
`(μ,λ)`-independent — all admissible members drop simultaneously. -/
theorem finite_gram_rank_drop_calibration_independent (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℝ) (φ : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) (ha1 : 0 < a 1) (ha : ∀ n, 0 ≤ a n)
    (μ₁ lam₁ μ₂ lam₂ : ℂ) (h₁ : lam₁ ≠ μ₁) (h₂ : lam₂ ≠ μ₂) :
    (((harmonicPencil ((finiteA χ a N : ℝ) : ℂ) (finiteB χ a φ N) μ₁ lam₁)ᴴ *
        harmonicPencil ((finiteA χ a N : ℝ) : ℂ) (finiteB χ a φ N) μ₁ lam₁).det = 0 ↔
      ((harmonicPencil ((finiteA χ a N : ℝ) : ℂ) (finiteB χ a φ N) μ₂ lam₂)ᴴ *
        harmonicPencil ((finiteA χ a N : ℝ) : ℂ) (finiteB χ a φ N) μ₂ lam₂).det = 0) :=
  harmonicGram_rank_drop_calibration_independent _ _ μ₁ lam₁ μ₂ lam₂
    (finiteA_ne_zero χ a N hN ha1 ha) h₁ h₂

end CriticalLinePhasor.HarmonicCell
