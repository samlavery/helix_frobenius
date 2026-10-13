import RequestProject.ThreeDFocalEvent

/-!
# The bank's carrier-height pencil, upstream of focal cancellation (ledger 1150)

The focal cancellation of a phasor bank, `ThreeDFocal.focalClosure χ bank y`, is defined as the
vanishing of the plane resultant `B = Σ χ(n)·a(n)·e^{iφ_y(n)}`. The pencils attached to it are built
afterwards: `harmonicGram` with free parameters `μ, λ`, lifted as `G ⊗ I₃`; and the z-focal cell pencil
of `HarmonicPencilCell`, whose height row is the gauge `centA = 1`, `centB = 2`. No pencil feeding the
focal cancellation contains the carrier's height coordinate.

Here the bank's own pencil is computed from the carrier. Site `n` sits at physical height `h n`; for
the scaled carrier, `carrierSiteHeight n`, the height coordinate of `Geometry.windIntegerSite 1 3 n`.

    focalPencil χ bank h y = !![A,   B;
                               A_h, B_h]

Columns: the unsigned channel and the signed channel. Rows: the resultant and the height moment
(`A_h = Σ ‖χ(n)‖·a(n)·h(n)`, `B_h = Σ χ(n)·a(n)·e^{iφ_y(n)}·h(n)`).

* Fiber → pencil: the resultant row is the bank's channels (`focalPencil_signed_resultant`), and
  moving the height origin to `c` acts on the pencil by the shear `!![1, 0; −c, 1]`
  (`focalPencil_shift`).
* **Pencil → focal cancellation** (`focalClosure_iff_signed_column_origin_free`): the bank cancels at
  `y` exactly when the signed column of its pencil is fixed by every shift of the height origin, i.e.
  the signed channel is a pure height couple. The unsigned column is never origin-free
  (`unsigned_moment_ne_of_shift`); its moment vanishes about exactly one origin, the unsigned focus
  `A_h / A` (`unsigned_moment_zero_iff`).
* Focal cancellation → projection: `threeDZeroAtHeight_iff_pencil` (the event at physical height
  `Z`, read from the pencil at `log Z`).
* What the existing pencil represented: `focalPencil_eq_harmonicPencil` (for `B ≠ 0` the pencil is
  `harmonicPencil A B μ λ` with `μ, λ` the two focal heights), and
  `exists_harmonicPencil_iff` (the harmonic family contains the bank's pencil iff `B ≠ 0` or
  `B_h = 0`).
* The determinant is origin-free (`focalPencil_det_shift`); divided by `A` it is the signed moment
  about the unsigned focus, `B_h − μB` (`focalPencil_det_div`). At a focal cancellation it is `A·B_h`
  (`focalPencil_det_of_focalClosure`), so the pencil drops rank there iff `B_h = 0`
  (`focalPencil_rankDrop_at_closure_iff`).
* Destructive witness (`twoSite_old_rankDrop_native_not`, `carrier_twoSite_witness`): two sites of
  equal amplitude at the carrier phase `y₀ = π / log 2` cancel; the old harmonic Gram drops rank for
  every admissible `μ ≠ λ`, while the bank's pencil, at the carrier's site heights, does not.
-/

open Complex Matrix Finset
open scoped BigOperators

namespace CriticalLinePhasor.FocalHeightPencil

open CriticalLinePhasor.HarmonicCell CriticalLinePhasor.ThreeDFocal

variable {q : ℕ}

/-! ## 1. The pencil, computed from the bank on the carrier -/

/-- The physical height of site `n` on the scaled carrier: the height coordinate of the
arclength-placed site. -/
noncomputable def carrierSiteHeight (n : ℕ) : ℝ := (Geometry.windIntegerSite 1 3 n).2.2

/-- The unsigned height moment `Σ ‖χ(n)‖·a(n)·h(n)`. -/
noncomputable def momentA (χ : DirichletCharacter ℂ q) (bank : FocalBank) (h : ℕ → ℝ) : ℝ :=
  finiteA χ (fun n => bank.amplitude n * h n) bank.cutoff

/-- The signed height moment `Σ χ(n)·a(n)·e^{iφ_y(n)}·h(n)`. -/
noncomputable def momentB (χ : DirichletCharacter ℂ q) (bank : FocalBank) (h : ℕ → ℝ) (y : ℝ) :
    ℂ :=
  finiteB χ (fun n => bank.amplitude n * h n) (bank.phase y) bank.cutoff

/-- The bank's pencil: resultant and height-moment rows, unsigned and signed columns. -/
noncomputable def focalPencil (χ : DirichletCharacter ℂ q) (bank : FocalBank) (h : ℕ → ℝ)
    (y : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ),
      finiteB χ bank.amplitude (bank.phase y) bank.cutoff;
    ((momentA χ bank h : ℝ) : ℂ), momentB χ bank h y]

/-- The unsigned focus: the mass centroid `A_h / A` of the bank in carrier height. -/
noncomputable def unsignedFocus (χ : DirichletCharacter ℂ q) (bank : FocalBank) (h : ℕ → ℝ) : ℝ :=
  momentA χ bank h / finiteA χ bank.amplitude bank.cutoff

theorem finiteA_bank_pos (χ : DirichletCharacter ℂ q) (bank : FocalBank) :
    0 < finiteA χ bank.amplitude bank.cutoff :=
  finiteA_pos χ bank.amplitude bank.cutoff bank.cutoff_pos bank.amplitude_one_pos
    bank.amplitude_nonneg

/-- The signed resultant entry is the bank's focal sum. -/
theorem focalPencil_signed_resultant (χ : DirichletCharacter ℂ q) (bank : FocalBank)
    (h : ℕ → ℝ) (y : ℝ) :
    focalPencil χ bank h y 0 1 = finiteB χ bank.amplitude (bank.phase y) bank.cutoff :=
  rfl

theorem focalPencil_signed_moment (χ : DirichletCharacter ℂ q) (bank : FocalBank)
    (h : ℕ → ℝ) (y : ℝ) :
    focalPencil χ bank h y 1 1 = momentB χ bank h y :=
  rfl

theorem momentA_shift (χ : DirichletCharacter ℂ q) (bank : FocalBank) (h : ℕ → ℝ) (c : ℝ) :
    momentA χ bank (fun n => h n - c) =
      momentA χ bank h - c * finiteA χ bank.amplitude bank.cutoff := by
  unfold momentA finiteA
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem momentB_shift (χ : DirichletCharacter ℂ q) (bank : FocalBank) (h : ℕ → ℝ) (c y : ℝ) :
    momentB χ bank (fun n => h n - c) y =
      momentB χ bank h y - (c : ℂ) * finiteB χ bank.amplitude (bank.phase y) bank.cutoff := by
  unfold momentB finiteB
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  ring

/-- **Moving the height origin to `c` shears the pencil**: the resultant row is unchanged and the
moment row loses `c` times it. -/
theorem focalPencil_shift (χ : DirichletCharacter ℂ q) (bank : FocalBank) (h : ℕ → ℝ) (c y : ℝ) :
    focalPencil χ bank (fun n => h n - c) y =
      !![(1 : ℂ), 0; -(c : ℂ), 1] * focalPencil χ bank h y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [focalPencil, Matrix.mul_apply, Fin.sum_univ_two, momentA_shift, momentB_shift] <;> ring

/-! ## 2. Pencil → focal cancellation -/

/-- **Focal cancellation is read from the pencil**: the bank cancels at `y` exactly when the signed
column of its pencil is fixed by every shift of the carrier's height origin. -/
theorem focalClosure_iff_signed_column_origin_free (χ : DirichletCharacter ℂ q)
    (bank : FocalBank) (h : ℕ → ℝ) (y : ℝ) :
    focalClosure χ bank y ↔
      ∀ c : ℝ, ∀ i : Fin 2, focalPencil χ bank (fun n => h n - c) y i 1 = focalPencil χ bank h y i 1 := by
  unfold focalClosure
  constructor
  · intro hB c i
    fin_cases i
    · rfl
    · simp only [Fin.mk_one, focalPencil_signed_moment, momentB_shift, hB, mul_zero, sub_zero]
  · intro hc
    have h1 := hc 1 1
    simp only [focalPencil_signed_moment, momentB_shift, Complex.ofReal_one, one_mul,
      sub_eq_self] at h1
    exact h1

/-- The unsigned moment is never origin-free: a nonzero shift changes it. -/
theorem unsigned_moment_ne_of_shift (χ : DirichletCharacter ℂ q) (bank : FocalBank)
    (h : ℕ → ℝ) {c : ℝ} (hc : c ≠ 0) :
    momentA χ bank (fun n => h n - c) ≠ momentA χ bank h := by
  rw [momentA_shift]
  intro heq
  have : c * finiteA χ bank.amplitude bank.cutoff = 0 := by linarith
  exact mul_ne_zero hc (finiteA_bank_pos χ bank).ne' this

/-- The unsigned moment vanishes about exactly one origin: the unsigned focus. -/
theorem unsigned_moment_zero_iff (χ : DirichletCharacter ℂ q) (bank : FocalBank) (h : ℕ → ℝ)
    (c : ℝ) :
    momentA χ bank (fun n => h n - c) = 0 ↔ c = unsignedFocus χ bank h := by
  rw [momentA_shift, unsignedFocus, eq_div_iff (finiteA_bank_pos χ bank).ne', sub_eq_zero,
    eq_comm]

/-! ## 3. Focal cancellation → projection: the event at physical height -/

/-- **The event at physical height `Z` is read from the pencil at `log Z`.** -/
theorem threeDZeroAtHeight_iff_pencil (χ : DirichletCharacter ℂ q) (bank : FocalBank)
    (h : ℕ → ℝ) (Z : ℝ) :
    ThreeDZeroAtHeight χ bank Z ↔
      0 < Z ∧ ∀ c : ℝ, ∀ i : Fin 2,
        focalPencil χ bank (fun n => h n - c) (Real.log Z) i 1 =
          focalPencil χ bank h (Real.log Z) i 1 := by
  rw [ThreeDZeroAtHeight, ThreeDZero, focalClosure_iff_signed_column_origin_free χ bank h]

/-! ## 4. The determinant, the residual, and the existing pencil -/

theorem focalPencil_det (χ : DirichletCharacter ℂ q) (bank : FocalBank) (h : ℕ → ℝ) (y : ℝ) :
    (focalPencil χ bank h y).det =
      ((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ) * momentB χ bank h y -
        ((momentA χ bank h : ℝ) : ℂ) * finiteB χ bank.amplitude (bank.phase y) bank.cutoff := by
  rw [focalPencil, Matrix.det_fin_two_of]
  ring

/-- The determinant does not depend on where the height origin is placed. -/
theorem focalPencil_det_shift (χ : DirichletCharacter ℂ q) (bank : FocalBank) (h : ℕ → ℝ)
    (c y : ℝ) :
    (focalPencil χ bank (fun n => h n - c) y).det = (focalPencil χ bank h y).det := by
  rw [focalPencil_shift, Matrix.det_mul, Matrix.det_fin_two_of]
  ring

/-- **The native residual**: the determinant over the unsigned resultant is the signed moment
about the unsigned focus. -/
theorem focalPencil_det_div (χ : DirichletCharacter ℂ q) (bank : FocalBank) (h : ℕ → ℝ)
    (y : ℝ) :
    (focalPencil χ bank h y).det / ((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ) =
      momentB χ bank h y -
        ((unsignedFocus χ bank h : ℝ) : ℂ) * finiteB χ bank.amplitude (bank.phase y) bank.cutoff := by
  have hA : ((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (finiteA_bank_pos χ bank).ne'
  rw [focalPencil_det, unsignedFocus, Complex.ofReal_div]
  field_simp

theorem focalPencil_det_of_focalClosure (χ : DirichletCharacter ℂ q) (bank : FocalBank)
    (h : ℕ → ℝ) {y : ℝ} (hclose : focalClosure χ bank y) :
    (focalPencil χ bank h y).det =
      ((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ) * momentB χ bank h y := by
  rw [focalPencil_det, show finiteB χ bank.amplitude (bank.phase y) bank.cutoff = 0 from hclose,
    mul_zero, sub_zero]

/-- **At a focal cancellation the bank's pencil drops rank exactly when the signed height moment
also vanishes.** -/
theorem focalPencil_rankDrop_at_closure_iff (χ : DirichletCharacter ℂ q) (bank : FocalBank)
    (h : ℕ → ℝ) {y : ℝ} (hclose : focalClosure χ bank y) :
    (focalPencil χ bank h y).det = 0 ↔ momentB χ bank h y = 0 := by
  rw [focalPencil_det_of_focalClosure χ bank h hclose]
  have hA : ((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (finiteA_bank_pos χ bank).ne'
  exact ⟨fun h0 => (mul_eq_zero.mp h0).resolve_left hA, fun h0 => by rw [h0, mul_zero]⟩

/-- **What the existing pencil's parameters were**: away from a cancellation the bank's pencil is
`harmonicPencil A B μ λ` with `μ` the unsigned focus and `λ = B_h / B` the signed focus. -/
theorem focalPencil_eq_harmonicPencil (χ : DirichletCharacter ℂ q) (bank : FocalBank)
    (h : ℕ → ℝ) (y : ℝ) (hB : finiteB χ bank.amplitude (bank.phase y) bank.cutoff ≠ 0) :
    focalPencil χ bank h y =
      harmonicPencil ((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ)
        (finiteB χ bank.amplitude (bank.phase y) bank.cutoff)
        ((unsignedFocus χ bank h : ℝ) : ℂ)
        (momentB χ bank h y / finiteB χ bank.amplitude (bank.phase y) bank.cutoff) := by
  have hA : ((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (finiteA_bank_pos χ bank).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [focalPencil, harmonicPencil, unsignedFocus, Complex.ofReal_div, hA, hB]

/-- **The harmonic family contains the bank's pencil iff the bank does not cancel or its signed
moment cancels too.** At a cancellation with a nonzero couple no `μ, λ` represent it. -/
theorem exists_harmonicPencil_iff (χ : DirichletCharacter ℂ q) (bank : FocalBank) (h : ℕ → ℝ)
    (y : ℝ) :
    (∃ μ lam : ℂ, focalPencil χ bank h y =
        harmonicPencil ((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ)
          (finiteB χ bank.amplitude (bank.phase y) bank.cutoff) μ lam) ↔
      (finiteB χ bank.amplitude (bank.phase y) bank.cutoff ≠ 0 ∨ momentB χ bank h y = 0) := by
  constructor
  · rintro ⟨μ, lam, heq⟩
    by_cases hB : finiteB χ bank.amplitude (bank.phase y) bank.cutoff = 0
    · right
      have h11 := congrFun (congrFun heq 1) 1
      simp only [focalPencil, harmonicPencil, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one] at h11
      rw [h11, hB, mul_zero]
    · exact Or.inl hB
  · rintro (hB | hm)
    · exact ⟨_, _, focalPencil_eq_harmonicPencil χ bank h y hB⟩
    · have hA : ((finiteA χ bank.amplitude bank.cutoff : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (finiteA_bank_pos χ bank).ne'
      refine ⟨((unsignedFocus χ bank h : ℝ) : ℂ), 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [focalPencil, harmonicPencil, unsignedFocus, Complex.ofReal_div, hA, hm]

/-! ## 5. Destructive witness: a focal cancellation at which the bank's pencil is nonsingular -/

/-- Two sites of equal amplitude at the carrier phase. -/
noncomputable def twoSiteBank : FocalBank where
  amplitude := fun _ => 1
  phase := carrierPhase
  cutoff := 2
  cutoff_pos := by norm_num
  amplitude_one_pos := one_pos
  amplitude_nonneg := fun _ => zero_le_one

/-- The ordinate at which site 2's carrier spin is a half turn. -/
noncomputable def halfTurnOrdinate : ℝ := Real.pi / Real.log 2

theorem trivialChar_apply (x : ZMod 1) : (1 : DirichletCharacter ℂ 1) x = 1 :=
  MulChar.one_apply (isUnit_of_subsingleton _)

theorem Icc_one_two : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide

theorem twoSite_closure :
    focalClosure (1 : DirichletCharacter ℂ 1) twoSiteBank halfTurnOrdinate := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h2 : -(Real.pi / Real.log 2) * Real.log 2 = -Real.pi := by field_simp
  simp only [focalClosure, finiteB, twoSiteBank, Icc_one_two, halfTurnOrdinate, carrierPhase]
  rw [Finset.sum_pair (by norm_num)]
  simp only [trivialChar_apply, Nat.cast_one, Nat.cast_ofNat, Real.log_one, mul_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one, mul_one, h2,
    Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem twoSite_det (h : ℕ → ℝ) :
    (focalPencil (1 : DirichletCharacter ℂ 1) twoSiteBank h halfTurnOrdinate).det =
      2 * ((h 1 : ℂ) - h 2) := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h2 : -(Real.pi / Real.log 2) * Real.log 2 = -Real.pi := by field_simp
  rw [focalPencil_det_of_focalClosure _ _ h twoSite_closure]
  simp only [momentB, finiteA, finiteB, twoSiteBank, Icc_one_two, halfTurnOrdinate, carrierPhase]
  rw [Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num)]
  simp only [trivialChar_apply, norm_one, Nat.cast_one, Nat.cast_ofNat, Real.log_one, mul_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, one_mul, h2,
    Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  push_cast
  ring

/-- **The old pencil rank-drops at this cancellation for every admissible `μ ≠ λ`; the bank's
pencil does not, whenever the two sites sit at different heights.** -/
theorem twoSite_old_rankDrop_native_not (h : ℕ → ℝ) (hh : h 1 ≠ h 2) :
    focalClosure (1 : DirichletCharacter ℂ 1) twoSiteBank halfTurnOrdinate ∧
      (∀ μ lam : ℂ, lam ≠ μ →
        FocalRankDrop (1 : DirichletCharacter ℂ 1) twoSiteBank halfTurnOrdinate μ lam) ∧
      (focalPencil (1 : DirichletCharacter ℂ 1) twoSiteBank h halfTurnOrdinate).det ≠ 0 := by
  refine ⟨twoSite_closure, fun μ lam hlam =>
    (focalClosure_iff_rankDrop _ _ _ μ lam hlam).mp twoSite_closure, ?_⟩
  rw [twoSite_det]
  have : (h 1 : ℂ) - h 2 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hh
  exact mul_ne_zero two_ne_zero this

/-- The scaled carrier places sites 1 and 2 at different physical heights. -/
theorem carrierSiteHeight_one_ne_two : carrierSiteHeight 1 ≠ carrierSiteHeight 2 := by
  intro heq
  have hs1 := Geometry.windParameter_spec 1 3 (Geometry.spinAngle 1) (by norm_num)
    (Geometry.spinAngle_nonneg 1)
  have hs2 := Geometry.windParameter_spec 1 3 (Geometry.spinAngle 2) (by norm_num)
    (Geometry.spinAngle_nonneg 2)
  have hk : Geometry.windParameter 1 3 (Geometry.spinAngle 1) =
      Geometry.windParameter 1 3 (Geometry.spinAngle 2) := by
    simpa [carrierSiteHeight, Geometry.windIntegerSite, Geometry.helix] using heq
  have hang : Geometry.spinAngle 1 = Geometry.spinAngle 2 := by
    rw [← hs1.2, ← hs2.2, hk]
  simp only [Geometry.spinAngle] at hang
  have hpi : 0 < Real.pi := Real.pi_pos
  push_cast at hang
  linarith

/-- **The witness on the scaled carrier itself.** -/
theorem carrier_twoSite_witness :
    focalClosure (1 : DirichletCharacter ℂ 1) twoSiteBank halfTurnOrdinate ∧
      (∀ μ lam : ℂ, lam ≠ μ →
        FocalRankDrop (1 : DirichletCharacter ℂ 1) twoSiteBank halfTurnOrdinate μ lam) ∧
      (focalPencil (1 : DirichletCharacter ℂ 1) twoSiteBank carrierSiteHeight
        halfTurnOrdinate).det ≠ 0 :=
  twoSite_old_rankDrop_native_not carrierSiteHeight carrierSiteHeight_one_ne_two

end CriticalLinePhasor.FocalHeightPencil

#print axioms CriticalLinePhasor.FocalHeightPencil.focalPencil_shift
#print axioms CriticalLinePhasor.FocalHeightPencil.focalClosure_iff_signed_column_origin_free
#print axioms CriticalLinePhasor.FocalHeightPencil.unsigned_moment_zero_iff
#print axioms CriticalLinePhasor.FocalHeightPencil.threeDZeroAtHeight_iff_pencil
#print axioms CriticalLinePhasor.FocalHeightPencil.focalPencil_det_shift
#print axioms CriticalLinePhasor.FocalHeightPencil.focalPencil_det_div
#print axioms CriticalLinePhasor.FocalHeightPencil.focalPencil_rankDrop_at_closure_iff
#print axioms CriticalLinePhasor.FocalHeightPencil.exists_harmonicPencil_iff
#print axioms CriticalLinePhasor.FocalHeightPencil.carrier_twoSite_witness
