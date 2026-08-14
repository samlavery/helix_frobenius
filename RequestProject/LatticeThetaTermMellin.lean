import RequestProject.EpsteinGramIdentification

/-!
# The termwise Mellin transform of the lattice theta

`latticeTheta z t = ∑'_p exp(-(πt)·gram z p)`, so the Mellin transform of the theta series is —
modulo the interchange — the sum of the Mellin transforms of its terms.  Each term is a pure
exponential, whose Mellin transform is the Gamma integral scaled by the exponential's rate.

Combined with `gram_cpow_eq_eisRealSummand`, the `p`-th term contributes

  `π^{-s}·Γ(s) · eisRealSummand z s p`,

so the archimedean factor `π^{-s}Γ(s)` is a **common mode**: it does not depend on `p` at all, and
factors out of the whole lattice sum.  That is the DC/AC split for the Epstein side, exactly as
`archimedeanFactor` was for the Maass side.

**Scope.**  Termwise only.  The interchange (summability of the integrated norms) is not proved
here; it is the same shape as `mellin_tsum`'s hypotheses.
-/

open Complex MeasureTheory UpperHalfPlane
open scoped Real

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta

/-- **The Mellin transform of a decaying exponential is the scaled Gamma integral.** -/
lemma mellin_exp_neg_mul {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ)) s =
      ((a : ℝ) : ℂ) ^ (-s) * Complex.Gamma s := by
  have h := mellin_comp_mul_left (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) s ha
  have hfun : (fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ)) =
      fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ) := rfl
  rw [hfun]
  have hmel : mellin (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) s = Complex.Gamma s := by
    rw [← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral hs]
  rw [hmel] at h
  rw [h, smul_eq_mul]

/-- **The `p`-th term of the lattice theta transforms to the Eisenstein summand times a common
archimedean factor.**  The factor `π^{-s}Γ(s)` does not depend on `p`. -/
theorem mellin_latticeTheta_term (z : ℍ) {p : ℤ × ℤ} (hp : ¬(p.1 = 0 ∧ p.2 = 0))
    {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => ((Real.exp (-(Real.pi * t) * gram z p) : ℝ) : ℂ)) s =
      (((Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s) * eisRealSummand z s p := by
  have hg : 0 < gram z p := gram_pos_nz z hp
  have hpi : (0:ℝ) < Real.pi * gram z p := by positivity
  have hrw : (fun t : ℝ => ((Real.exp (-(Real.pi * t) * gram z p) : ℝ) : ℂ)) =
      fun t : ℝ => ((Real.exp (-((Real.pi * gram z p) * t)) : ℝ) : ℂ) := by
    funext t
    congr 2
    ring
  rw [hrw, mellin_exp_neg_mul hpi hs, ← gram_cpow_eq_eisRealSummand z p s hp,
    Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le hg.le]
  ring

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.mellin_exp_neg_mul
#print axioms CriticalLinePhasor.Unfolding.mellin_latticeTheta_term
