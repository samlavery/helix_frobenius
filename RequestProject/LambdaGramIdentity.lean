import RequestProject.LatticeThetaInterchangeHyps
import RequestProject.RSPairInterface

/-!
# The completed Epstein kernel as a Gram Dirichlet series

The piece the corpus did not have.  `ReindexSum.gram_sum_factor` already gives the `ζ(2s)`
factorization of the Gram Dirichlet series in the repo's `CosetQ` indexing; what was missing is the
link from that series back to the **completed Epstein kernel** `Λ` whose poles `lambda_pole_split`
supplies.

That link is the Mellin transform of the theta series, termwise:

  **`Λ(z,s) = π^{-s}·Γ(s) · ∑_{p ≠ 0} (gram z p)^{-s}`**   on `Re s > 1`,

the archimedean factor coming out whole because it does not depend on `p`.  Composed with
`gram_sum_factor` it reads

  `Λ(z,s) = π^{-s}Γ(s)·ζ(2s)·2·∑_{q : CosetQ} (gram z (bottom row of rep q))^{-s}`,

which is the Eisenstein series with its full completed archimedean factor — and `lambda_pole_split`
then locates its poles at `s ∈ {0,1}`.

**Scope.**  Pointwise in `z`.  Moving this under `∫_𝒟 ‖u‖²·` needs `z`-uniformity and is not done
here.
-/

open Complex MeasureTheory UpperHalfPlane
open scoped Real

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.ThreeDConverse

/-- The two spellings of "nonzero lattice point" agree. -/
def nzEquiv : {p : ℤ × ℤ // ¬(p.1 = 0 ∧ p.2 = 0)} ≃ NZ :=
  Equiv.subtypeEquivRight fun p => by
    constructor
    · intro hp; exact ne_zero_of_not_and hp
    · rintro hp ⟨h0, h1⟩
      exact hp (Prod.ext h0 h1)

/-- The termwise Mellin transform, in Gram form. -/
lemma mellin_latticeTheta_term_gram (z : ℍ) {p : ℤ × ℤ} (hp : ¬(p.1 = 0 ∧ p.2 = 0))
    {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => ((Real.exp (-(Real.pi * t) * gram z p) : ℝ) : ℂ)) s =
      (((Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s) * ((gram z p : ℝ) : ℂ) ^ (-s) := by
  rw [mellin_latticeTheta_term z hp hs, gram_cpow_eq_eisRealSummand z p s hp]

/-- **The completed Epstein kernel is the archimedean factor times the Gram Dirichlet series.** -/
theorem lambda_eq_archimedean_mul_gramSum (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    (generalFEPair z).Λ s =
      (((Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s) *
        ∑' p : NZ, ((gram z p.1 : ℝ) : ℂ) ^ (-s) := by
  have hs0 : (0:ℝ) < s.re := by linarith
  rw [← epstein_mellin_eq z hs]
  have hcong : mellin (fun t : ℝ => latticeThetaC z t - 1) s =
      mellin (fun t : ℝ => ∑' p : {p : ℤ × ℤ // ¬(p.1 = 0 ∧ p.2 = 0)},
        ((Real.exp (-(Real.pi * t) * gram z p.1) : ℝ) : ℂ)) s := by
    rw [mellin, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := ht
    congr 1
    rw [latticeThetaC, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      latticeTheta_sub_one z ht0, Complex.ofReal_tsum]
  rw [hcong,
    mellin_tsum_countable
      (F := fun p : {p : ℤ × ℤ // ¬(p.1 = 0 ∧ p.2 = 0)} => fun t : ℝ =>
        ((Real.exp (-(Real.pi * t) * gram z p.1) : ℝ) : ℂ))
      (fun p => integrableOn_latticeTheta_term z p.2 hs0)
      (summable_latticeTheta_mellin_norms z hs),
    tsum_congr fun p => mellin_latticeTheta_term_gram z p.2 hs0, tsum_mul_left]
  congr 1
  exact nzEquiv.tsum_eq (fun p : NZ => ((gram z p.1 : ℝ) : ℂ) ^ (-s))

/-- **The completed Epstein kernel, factored.**  Composing with `ReindexSum.gram_sum_factor`: the
Eisenstein series carries its full archimedean factor and a `ζ(2s)`. -/
theorem lambda_eq_zeta_mul_cosetSum (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    (generalFEPair z).Λ s =
      (((Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s) *
        (riemannZeta (2 * s) *
          (2 * ∑' q : CosetQ,
            ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s))) := by
  rw [lambda_eq_archimedean_mul_gramSum z hs, gram_sum_factor z hs]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.lambda_eq_archimedean_mul_gramSum
#print axioms CriticalLinePhasor.Unfolding.lambda_eq_zeta_mul_cosetSum
