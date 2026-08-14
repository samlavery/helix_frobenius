import RequestProject.EisensteinHeightBridge
import RequestProject.GeneralLatticeTheta
import RequestProject.ReindexSum

/-!
# The Epstein Gram form is the Eisenstein modulus

Item (2) of the Eisenstein continuation needs the compiled Epstein pair `generalFEPair z` — whose
theta is `∑_p exp(-πt·gram z p)` and whose `Λ` is that theta's Mellin transform
(`RSPairInterface`) — to be recognised as the lattice sum built in this campaign.

The identification is exact and elementary: the Gram form carried by `GeneralLatticeTheta` is

  `gram z (c,d) = ((cx+d)² + c²y²)/y`,

and `(cx+d)² + c²y²` is precisely `‖cz+d‖²`.  So

  **`gram z p = ‖cz+d‖² / y`**,

i.e. the Gram form *is* the Eisenstein modulus measured against the height.  Consequently
`(gram z p)^{-s} = y^s‖cz+d‖^{-2s} = eisRealSummand z s p`, which is the summand whose `ζ(2s)`
factorization `tsum_nonzero_eisRealSummand` supplies.

Harmonically: the Gram form is the fiber's squared modulus in units of the carrier height.  Writing
it that way is what makes the two descriptions the same object rather than two computations that
happen to agree.

**Scope.**  This is the identification only.  The termwise Mellin transform of the theta series
(the `π^{-s}Γ(s)` factor) and the interchange are not proved here.
-/

open UpperHalfPlane Complex
open scoped Real

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta

/-- **The Gram form is the squared Eisenstein modulus over the height.** -/
lemma gram_eq_norm_sq_div (z : ℍ) (p : ℤ × ℤ) :
    gram z p = ‖(p.1 : ℂ) * (z : ℂ) + (p.2 : ℂ)‖ ^ 2 / z.im := by
  rw [gram, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  congr 1
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero, add_zero,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- `¬(c = 0 ∧ d = 0)` is `(c,d) ≠ 0`. -/
lemma ne_zero_of_not_and {p : ℤ × ℤ} (hp : ¬(p.1 = 0 ∧ p.2 = 0)) : p ≠ 0 := by
  intro h
  exact hp ⟨by rw [h]; rfl, by rw [h]; rfl⟩

/-- The Gram form is positive away from the origin.  **This is `ReindexSum.gram_pos` restated for
the `¬(c = 0 ∧ d = 0)` form of the hypothesis** — the corpus already had it. -/
lemma gram_pos_nz (z : ℍ) {p : ℤ × ℤ} (hp : ¬(p.1 = 0 ∧ p.2 = 0)) : 0 < gram z p :=
  gram_pos z (ne_zero_of_not_and hp)

/-- **The Epstein summand is the Eisenstein summand.**  `(gram z p)^{-s} = eisRealSummand z s p`,
so the Epstein lattice sum of `generalFEPair` and the campaign's Eisenstein sum are the same
object. -/
theorem gram_cpow_eq_eisRealSummand (z : ℍ) (p : ℤ × ℤ) (s : ℂ)
    (hp : ¬(p.1 = 0 ∧ p.2 = 0)) :
    ((gram z p : ℝ) : ℂ) ^ (-s) = eisRealSummand z s p := by
  set u : ℝ := ‖(p.1 : ℂ) * (z : ℂ) + (p.2 : ℂ)‖ with hu
  have hupos : (0:ℝ) < u := norm_pos_of_ne_zero z hp
  have hy : (0:ℝ) < z.im := z.im_pos
  have hlog : ∀ a : ℝ, 0 < a → (Complex.log ((a : ℝ) : ℂ)).im = 0 := by
    intro a ha
    rw [Complex.log_im, Complex.arg_ofReal_of_nonneg ha.le]
  -- split the quotient
  rw [gram_eq_norm_sq_div, ← hu, div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  unfold eisRealSummand
  have h1 : (((u ^ 2 : ℝ)) : ℂ) ^ (-s) = ((u : ℝ) : ℂ) ^ (-(2 * s)) := by
    rw [show ((u ^ 2 : ℝ)) = u ^ (2 : ℝ) by rw [← Real.rpow_natCast u 2]; norm_num,
      Complex.ofReal_cpow hupos.le, ← Complex.cpow_mul _
        (by simp [Complex.mul_im, hlog u hupos]; linarith [Real.pi_pos])
        (by simp [Complex.mul_im, hlog u hupos]; linarith [Real.pi_pos])]
    congr 1
    push_cast
    ring
  have h2 : (((z.im)⁻¹ : ℝ) : ℂ) ^ (-s) = ((z.im : ℝ) : ℂ) ^ s := by
    rw [Complex.ofReal_inv, ← Complex.cpow_neg_one, ← Complex.cpow_mul _
      (by simp [Complex.mul_im, hlog _ hy]; linarith [Real.pi_pos])
      (by simp [Complex.mul_im, hlog _ hy]; linarith [Real.pi_pos])]
    congr 1
    ring
  rw [h1, h2]
  ring

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.gram_eq_norm_sq_div
#print axioms CriticalLinePhasor.Unfolding.gram_pos
#print axioms CriticalLinePhasor.Unfolding.gram_cpow_eq_eisRealSummand
