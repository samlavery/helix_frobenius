import RequestProject.MaassLambda0Integrable
import RequestProject.LambdaGramIdentity
import RequestProject.EisensteinHeightBridge

/-!
# The Epstein kernel in terms of Eisenstein heights

The last identification.  `lambda_eq_zeta_mul_cosetSum` writes `Λ_z(s)` as a sum of **Gram powers**
over cosets; the Rankin--Selberg identity of this campaign is stated in **Eisenstein heights**
`Im(γ_q·z)^s`.  They are the same summand, by the two bridges already proved:

* `gram_cpow_eq_eisRealSummand` — `(gram z p)^{-s} = eisRealSummand z s p`;
* `im_smul_cpow_eq_eisRealSummand` — `(Im(γ·z))^s = eisRealSummand z s (bottom row of γ)`.

Both routes land on the same object, so the Gram power at a coset representative's bottom row *is*
the height power.  That is not a coincidence of normalisation: `gram z p = ‖cz+d‖²/y` and
`Im(γ·z) = y/‖cz+d‖²` are reciprocal by construction, which is exactly why one carries `-s` and the
other `+s`.

Consequently

  **`Λ_z(s) = π^{-s}·Γ(s)·ζ(2s)·2·∑_{q : CosetQ} Im(γ_q·z)^s`,**

the completed Eisenstein series in the coordinates the Rankin--Selberg pairing uses.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.ThreeDConverse

/-- A coset representative's bottom row is a nonzero pair. -/
lemma rep_bottomRow_ne_zero (q : CosetQ) :
    ¬((((rep q) 1 0 : ℤ)) = 0 ∧ (((rep q) 1 1 : ℤ)) = 0) := by
  rintro ⟨h0, h1⟩
  have hcp := isCoprime_bottomRow (rep q)
  rw [h0, h1] at hcp
  exact not_isCoprime_zero_zero hcp

/-- **The Gram power at a coset's bottom row is the Eisenstein height power.** -/
theorem gram_rep_cpow_eq_im_cpow (q : CosetQ) (z : ℍ) (s : ℂ) :
    ((gram z ((rep q) 1 0, (rep q) 1 1) : ℝ) : ℂ) ^ (-s) =
      (((rep q • z).im : ℝ) : ℂ) ^ s := by
  rw [gram_cpow_eq_eisRealSummand z _ s (rep_bottomRow_ne_zero q),
    im_smul_cpow_eq_eisRealSummand (rep q) z s]

/-- **The completed Epstein kernel is the Eisenstein height sum.** -/
theorem lambda_eq_zeta_mul_heightSum (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    (generalFEPair z).Λ s =
      (((Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s) *
        (riemannZeta (2 * s) *
          (2 * ∑' q : CosetQ, (((rep q • z).im : ℝ) : ℂ) ^ s)) := by
  rw [lambda_eq_zeta_mul_cosetSum z hs]
  congr 3
  exact tsum_congr fun q => gram_rep_cpow_eq_im_cpow q z s

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.gram_rep_cpow_eq_im_cpow
#print axioms CriticalLinePhasor.Unfolding.lambda_eq_zeta_mul_heightSum
