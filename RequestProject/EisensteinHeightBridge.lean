import RequestProject.EisensteinZetaFactor

/-!
# The height is the Eisenstein summand at the bottom row

The bridge from this repo's coset-indexed sum `∑_{q : CosetQ} Im(γ_q·z)^s` to the lattice-indexed
`eisRealSummand`.  Combined with `cosetSetoid_iff_bottomRow_eq_or_neg` (the coset *is* the bottom
row up to sign) and `tsum_nonzero_eisRealSummand` (the `ζ(2s)` factor), this is what turns the
repo's Eisenstein sum into the Epstein lattice sum whose continuation `lambda_pole_split` supplies.

The identity is stated on the **real** base — `Im(γ·z) = y·‖cz+d‖^{-2}` — not on the complex power.
That is deliberate: the height and the modulus are both positive reals, so the relation is exact
with no branch bookkeeping, and the `cpow` step is taken once, later, where the exponent is fixed.
Same discipline as `eisRealSummand` itself.
-/

open UpperHalfPlane ModularGroup Complex
open scoped MatrixGroups

namespace CriticalLinePhasor.Unfolding

/-- **The Eisenstein height in terms of the bottom row.**  `Im(γ·z) = y·‖cz+d‖^{-2}`. -/
lemma im_smul_eq_mul_rpow (γ : SL(2, ℤ)) (z : ℍ) :
    (γ • z).im = z.im * ‖(γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)‖ ^ (-2 : ℝ) := by
  have hpos : (0:ℝ) < ‖(γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)‖ :=
    norm_pos_of_ne_zero z (p := (γ 1 0, γ 1 1)) (by
      rintro ⟨h0, h1⟩
      dsimp only at h0 h1
      have hcp := isCoprime_bottomRow γ
      rw [h0, h1] at hcp
      exact not_isCoprime_zero_zero hcp)
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply,
    Complex.normSq_eq_norm_sq,
    show ((-2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg, zpow_two,
    pow_two]
  norm_cast

/-- The height is positive, so the `cpow` step below is on a positive real base. -/
lemma im_smul_pos (γ : SL(2, ℤ)) (z : ℍ) : 0 < (γ • z).im := (γ • z).im_pos

/-- **The height power is the Eisenstein summand at the bottom row.**  The identity the coset sum
consumes.  Both bases are positive reals, so the `cpow` composition is legitimate: `log` of a
positive real is real, so the branch condition of `Complex.cpow_mul` is satisfied outright. -/
theorem im_smul_cpow_eq_eisRealSummand (γ : SL(2, ℤ)) (z : ℍ) (s : ℂ) :
    (((γ • z).im : ℝ) : ℂ) ^ s = eisRealSummand z s (γ 1 0, γ 1 1) := by
  set u : ℝ := ‖(γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)‖ with hu
  have hpos : (0:ℝ) < u :=
    norm_pos_of_ne_zero z (p := (γ 1 0, γ 1 1)) (by
      rintro ⟨h0, h1⟩
      dsimp only at h0 h1
      have hcp := isCoprime_bottomRow γ
      rw [h0, h1] at hcp
      exact not_isCoprime_zero_zero hcp)
  have hlogim : (Complex.log ((u : ℝ) : ℂ) * ((-2 : ℝ) : ℂ)).im = 0 := by
    have hz : (Complex.log ((u : ℝ) : ℂ)).im = 0 := by
      rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hpos.le]
    simp [Complex.mul_im, hz]
  have hstep : (((u ^ (-2 : ℝ) : ℝ)) : ℂ) ^ s = ((u : ℝ) : ℂ) ^ (-(2 * s)) := by
    rw [Complex.ofReal_cpow hpos.le, ← Complex.cpow_mul _
      (by rw [hlogim]; linarith [Real.pi_pos]) (by rw [hlogim]; linarith [Real.pi_pos])]
    congr 1
    push_cast
    ring
  rw [im_smul_eq_mul_rpow, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg z.im_pos.le (Real.rpow_nonneg hpos.le _), hstep]
  rfl

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.im_smul_eq_mul_rpow
#print axioms CriticalLinePhasor.Unfolding.im_smul_cpow_eq_eisRealSummand
