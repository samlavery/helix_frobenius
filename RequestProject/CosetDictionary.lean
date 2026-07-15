import RequestProject.RSTransport

/-!
# The coset–row dictionary: Eisenstein heights are Gram values

The bookkeeping layer connecting the compiled Rankin–Selberg equation to the compiled lattice
machinery.  The Eisenstein height at a modular translate is the reciprocal Gram value of the
mover's bottom row (`im_smul_eq_gram_inv`, `im_smul_cpow`); bottom rows of modular matrices
are exactly the coprime pairs (`bottomRow_isCoprime`, `exists_SL2_bottomRow`); and two
matrices lie in the same `±⟨T⟩`-coset **iff** their bottom rows agree up to sign
(`bottomRow_T_zpow_mul`, `bottomRow_neg`, `cosetRel_of_bottomRow_eq`,
`cosetRel_of_bottomRow_neg`).  Together with the parity and scaling of the Gram form
(`gram_neg`, `gram_mul_left`) this is the complete local dictionary for reindexing the coset
sum `∑'_q (gram z (row γ_q))^{-s}` as the coprime slice of the full lattice Dirichlet series
`∑'_{p≠0} gram(z,p)^{-s} = ζ(2s)·(coprime slice)` — the series whose completion is the
compiled `Λ_z`.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Matrix.SpecialLinearGroup
open scoped Real MatrixGroups Pointwise

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta

/-- **The Eisenstein height is the reciprocal Gram value of the bottom row.** -/
lemma im_smul_eq_gram_inv (γ : SL(2, ℤ)) (z : ℍ) :
    (γ • z).im = (gram z (γ.1 1 0, γ.1 1 1))⁻¹ := by
  have haction : (mapGL ℝ γ) • z = γ • z := rfl
  have him := z.im_smul_eq_div_normSq (mapGL ℝ γ)
  rw [haction, mapGL_det_val, abs_one, one_mul] at him
  have hdenom : denom (mapGL ℝ γ) ↑z =
      ((γ.1 1 0 : ℤ) : ℂ) * (z : ℂ) + ((γ.1 1 1 : ℤ) : ℂ) := by
    rw [denom, mapGL_entry, mapGL_entry]
    push_cast
    ring
  rw [him, gram_eq_normSq, inv_div, hdenom]

/-- The Gram form is positive away from zero rows — read off the height. -/
lemma gram_bottomRow_pos (γ : SL(2, ℤ)) (z : ℍ) :
    0 < gram z (γ.1 1 0, γ.1 1 1) := by
  have h := (γ • z).im_pos
  rw [im_smul_eq_gram_inv] at h
  exact inv_pos.mp h

/-- The complex-power form of the dictionary: the Eisenstein kernel is the Gram value to the
power `-s`. -/
lemma im_smul_cpow (γ : SL(2, ℤ)) (z : ℍ) (s : ℂ) :
    (((γ • z).im : ℝ) : ℂ) ^ s =
      ((gram z (γ.1 1 0, γ.1 1 1) : ℝ) : ℂ) ^ (-s) := by
  rw [im_smul_eq_gram_inv]
  have hg := gram_bottomRow_pos γ z
  have harg : ((gram z (γ.1 1 0, γ.1 1 1) : ℝ) : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hg.le]
    exact Real.pi_ne_zero.symm
  push_cast
  rw [Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]

/-- Bottom rows of modular matrices are coprime. -/
lemma bottomRow_isCoprime (γ : SL(2, ℤ)) : IsCoprime (γ.1 1 0) (γ.1 1 1) := by
  have hdet : γ.1 0 0 * γ.1 1 1 - γ.1 0 1 * γ.1 1 0 = 1 := by
    have h2 := γ.2
    rwa [Matrix.det_fin_two] at h2
  exact ⟨-(γ.1 0 1), γ.1 0 0, by linear_combination hdet⟩

/-- Every coprime pair is a bottom row. -/
lemma exists_SL2_bottomRow {c d : ℤ} (h : IsCoprime c d) :
    ∃ γ : SL(2, ℤ), γ.1 1 0 = c ∧ γ.1 1 1 = d := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨⟨!![b, -a; c, d], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    show b * d - -a * c = 1
    linear_combination hab
  · rfl
  · rfl

/-- Left `T`-powers do not move the bottom row. -/
lemma bottomRow_T_zpow_mul (n : ℤ) (δ : SL(2, ℤ)) (j : Fin 2) :
    (ModularGroup.T ^ n * δ).1 1 j = δ.1 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
    Fin.sum_univ_two]
  simp

/-- Negation negates the bottom row. -/
lemma bottomRow_neg (δ : SL(2, ℤ)) (j : Fin 2) : (-δ).1 1 j = -(δ.1 1 j) := by
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]

/-- **Equal bottom rows force the same coset.** -/
lemma cosetRel_of_bottomRow_eq {δ δ' : SL(2, ℤ)}
    (h0 : δ'.1 1 0 = δ.1 1 0) (h1 : δ'.1 1 1 = δ.1 1 1) :
    cosetSetoid.r δ δ' := by
  have hdet : δ.1 0 0 * δ.1 1 1 - δ.1 0 1 * δ.1 1 0 = 1 := by
    have h2 := δ.2
    rwa [Matrix.det_fin_two] at h2
  set α : SL(2, ℤ) := δ' * δ⁻¹ with hα
  have hinv : (δ⁻¹).1 = !![δ.1 1 1, -(δ.1 0 1); -(δ.1 1 0), δ.1 0 0] := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hα10 : α.1 1 0 = 0 := by
    rw [hα, Matrix.SpecialLinearGroup.coe_mul, hinv, Matrix.mul_apply, Fin.sum_univ_two]
    show δ'.1 1 0 * δ.1 1 1 + δ'.1 1 1 * -(δ.1 1 0) = 0
    linear_combination δ.1 1 1 * h0 - δ.1 1 0 * h1
  have hα11 : α.1 1 1 = 1 := by
    rw [hα, Matrix.SpecialLinearGroup.coe_mul, hinv, Matrix.mul_apply, Fin.sum_univ_two]
    show δ'.1 1 0 * -(δ.1 0 1) + δ'.1 1 1 * δ.1 0 0 = 1
    linear_combination hdet - δ.1 0 1 * h0 + δ.1 0 0 * h1
  have hα00 : α.1 0 0 = 1 := by
    have h2 := α.2
    rw [Matrix.det_fin_two, hα10, hα11] at h2
    simpa using h2
  have hαT : α = ModularGroup.T ^ (α.1 0 1) := by
    apply Subtype.ext
    rw [ModularGroup.coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hα00, hα10, hα11]
  refine ⟨α.1 0 1, Or.inl ?_⟩
  rw [← hαT, hα, inv_mul_cancel_right]

/-- **Oppositely-signed bottom rows force the same coset.** -/
lemma cosetRel_of_bottomRow_neg {δ δ' : SL(2, ℤ)}
    (h0 : δ'.1 1 0 = -(δ.1 1 0)) (h1 : δ'.1 1 1 = -(δ.1 1 1)) :
    cosetSetoid.r δ δ' := by
  have h0' : (-δ').1 1 0 = δ.1 1 0 := by rw [bottomRow_neg, h0, neg_neg]
  have h1' : (-δ').1 1 1 = δ.1 1 1 := by rw [bottomRow_neg, h1, neg_neg]
  obtain ⟨n, hn | hn⟩ := cosetRel_of_bottomRow_eq h0' h1'
  · exact ⟨n, Or.inr (by rw [← hn, neg_neg])⟩
  · exact ⟨n, Or.inl (by rw [← neg_neg δ', hn, neg_neg])⟩

/-- The Gram form is even. -/
lemma gram_neg (z : ℍ) (p : ℤ × ℤ) : gram z (-p) = gram z p := by
  rw [gram, gram]
  congr 1
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring

/-- The Gram form scales quadratically. -/
lemma gram_mul_left (z : ℍ) (n : ℤ) (p : ℤ × ℤ) :
    gram z (n * p.1, n * p.2) = (n : ℝ) ^ 2 * gram z p := by
  rw [gram, gram]
  push_cast
  ring

open CriticalLinePhasor.HeckeSupBound in
/-- **The Rankin–Selberg equation in Gram vocabulary**: on `Re s > 2` the completed Dirichlet
series is the coset sum of Petersson integrals against reciprocal Gram powers of the coset
bottom rows — the shape that reindexes to the full lattice series of the compiled `Λ_z`. -/
theorem rankin_selberg_equation_gram {k : ℤ} (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    Complex.Gamma (s + k - 1) * ∑' n : ℕ,
        ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) /
          ((4 * π * n : ℝ) : ℂ) ^ (s + k - 1) =
      ∑' q : CosetQ, ∫ z in ModularGroup.fd,
        ((P k f z : ℝ) : ℂ) *
          ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s)
        ∂(volume : Measure ℍ) := by
  rw [rankin_selberg_equation f hk hs]
  refine tsum_congr fun q => setIntegral_congr_fun measurableSet_fd fun z _ => ?_
  rw [im_smul_cpow]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.rankin_selberg_equation_gram
#print axioms CriticalLinePhasor.Unfolding.im_smul_cpow
#print axioms CriticalLinePhasor.Unfolding.cosetRel_of_bottomRow_eq
#print axioms CriticalLinePhasor.Unfolding.exists_SL2_bottomRow
