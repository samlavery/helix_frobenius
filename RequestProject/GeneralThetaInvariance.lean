import RequestProject.GeneralEpsteinZeta

/-!
# Modular invariance of the general lattice bank

Slice one of the Rankin–Selberg unfolding chain (brick (iv)).  The lattice bank is
`Γ = SL(2,ℤ)`-invariant in the point: `Θ_{γ·z}(t) = Θ_z(t)` (`latticeTheta_smul`).  The
mechanism is exact: the Möbius action on the point is the transpose lattice action on the
index — `gram(γ·z, p) = gram(z, p·γ)` (`gram_smul`, pure algebra through the cocycle), and
`p ↦ p·γ` is a bijection of the lattice (`latticeAut`, inverse supplied by `det γ = 1`).
Hence the whole compiled Epstein/Eisenstein package at `γ·z` *is* the package at `z`
(`generalFEPair_smul`), so the Rankin–Selberg kernel `Λ_z(s)` is a `Γ`-invariant function of
`z` with compiled continuation and functional equation in `s` — the integrand of the unfolding
integral is fully under control before any measure theory enters.  No RH/GRH.
-/

open Complex UpperHalfPlane Matrix Matrix.SpecialLinearGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.EpsteinTheta

/-- The Gram form via the complex norm-square. -/
lemma gram_eq_normSq (z : ℍ) (p : ℤ × ℤ) :
    gram z p = Complex.normSq ((p.1 : ℂ) * (z : ℂ) + (p.2 : ℂ)) / z.im := by
  rw [gram, Complex.normSq_apply]
  congr 1
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- The lattice automorphism attached to a modular matrix: right multiplication of the row
vector by the matrix, inverted by the adjugate since `det = 1`. -/
def latticeAut (γ : SL(2, ℤ)) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (p.1 * γ.1 0 0 + p.2 * γ.1 1 0, p.1 * γ.1 0 1 + p.2 * γ.1 1 1)
  invFun q := (q.1 * γ.1 1 1 - q.2 * γ.1 1 0, -(q.1 * γ.1 0 1) + q.2 * γ.1 0 0)
  left_inv p := by
    have h : γ.1 0 0 * γ.1 1 1 - γ.1 0 1 * γ.1 1 0 = 1 := by
      have h2 := γ.2
      rwa [Matrix.det_fin_two] at h2
    refine Prod.ext ?_ ?_
    · dsimp only
      linear_combination p.1 * h
    · dsimp only
      linear_combination p.2 * h
  right_inv q := by
    have h : γ.1 0 0 * γ.1 1 1 - γ.1 0 1 * γ.1 1 0 = 1 := by
      have h2 := γ.2
      rwa [Matrix.det_fin_two] at h2
    refine Prod.ext ?_ ?_
    · dsimp only
      linear_combination q.1 * h
    · dsimp only
      linear_combination q.2 * h

/-- The determinant of the real image of a modular matrix is one. -/
lemma mapGL_det_val (γ : SL(2, ℤ)) : ((mapGL ℝ γ).det).val = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, mapGL_coe_matrix]
  exact Matrix.SpecialLinearGroup.det_coe _

/-- The entries of the real image of a modular matrix are the integer entries. -/
lemma mapGL_entry (γ : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ γ) i j = ((γ.1 i j : ℤ) : ℝ) := by
  simp [mapGL_coe_matrix]

/-- **Gram equivariance**: the modular action on the point is the lattice action on the
index. -/
lemma gram_smul (γ : SL(2, ℤ)) (z : ℍ) (p : ℤ × ℤ) :
    gram (γ • z) p = gram z (latticeAut γ p) := by
  have haction : (mapGL ℝ γ) • z = γ • z := rfl
  have hdetpos : (0 : ℝ) < ((mapGL ℝ γ).det).val := by
    rw [mapGL_det_val]
    norm_num
  have hcoe : (↑(γ • z) : ℂ) = num (mapGL ℝ γ) ↑z / denom (mapGL ℝ γ) ↑z := by
    rw [← haction]
    exact coe_smul_of_det_pos hdetpos z
  have him := z.im_smul_eq_div_normSq (mapGL ℝ γ)
  rw [haction, mapGL_det_val, abs_one, one_mul] at him
  have hdenom : denom (mapGL ℝ γ) ↑z ≠ 0 := denom_ne_zero _ z
  have hnormSq : Complex.normSq (denom (mapGL ℝ γ) ↑z) ≠ 0 :=
    (Complex.normSq_pos.mpr hdenom).ne'
  have hkey : (p.1 : ℂ) * ↑(γ • z) + (p.2 : ℂ) =
      (((latticeAut γ p).1 : ℂ) * (z : ℂ) + ((latticeAut γ p).2 : ℂ)) /
        denom (mapGL ℝ γ) ↑z := by
    rw [eq_div_iff hdenom, hcoe]
    field_simp
    rw [num, denom, mapGL_entry, mapGL_entry, mapGL_entry, mapGL_entry]
    simp only [latticeAut, Equiv.coe_fn_mk]
    push_cast
    ring
  rw [gram_eq_normSq, gram_eq_normSq, hkey, him, Complex.normSq_div]
  rw [div_div_div_comm, div_self hnormSq, div_one]

/-- **Modular invariance of the bank**: `Θ_{γ·z}(t) = Θ_z(t)`. -/
theorem latticeTheta_smul (γ : SL(2, ℤ)) (z : ℍ) (t : ℝ) :
    latticeTheta (γ • z) t = latticeTheta z t := by
  rw [latticeTheta, latticeTheta,
    ← (latticeAut γ).tsum_eq fun p => Real.exp (-(π * t) * gram z p)]
  exact tsum_congr fun p => by rw [gram_smul]

/-- The complexified bank is modular invariant. -/
theorem latticeThetaC_smul (γ : SL(2, ℤ)) (z : ℍ) :
    latticeThetaC (γ • z) = latticeThetaC z := by
  funext t
  rw [latticeThetaC, latticeThetaC, latticeTheta_smul]

/-- **Invariance of the whole Epstein package**: the abstract functional-equation pair at
`γ·z` is the pair at `z` — the Rankin–Selberg kernel `Λ_z(s)` is a `Γ`-invariant function of
the point, with its compiled continuation and `s ↔ 1-s` reflection. -/
theorem generalFEPair_smul (γ : SL(2, ℤ)) (z : ℍ) :
    generalFEPair (γ • z) = generalFEPair z := by
  unfold generalFEPair
  have h := latticeThetaC_smul γ z
  congr 1

end CriticalLinePhasor.EpsteinTheta

#print axioms CriticalLinePhasor.EpsteinTheta.gram_smul
#print axioms CriticalLinePhasor.EpsteinTheta.latticeTheta_smul
#print axioms CriticalLinePhasor.EpsteinTheta.generalFEPair_smul
