import RequestProject.LatticeThetaInterchangeHyps
import RequestProject.RSPairInterface

/-!
# The completed Epstein kernel is the Eisenstein sum times the archimedean factor

Item (2) of the Eisenstein continuation, assembled.  Every ingredient is compiled:

* `epstein_mellin_eq` — `Λ(z,s)` is the Mellin transform of the theta tail on `Re s > 1`;
* `latticeTheta_sub_one` — the tail is the sum over **nonzero** lattice points;
* `mellin_tsum_countable` with the two hypotheses of `LatticeThetaInterchangeHyps`;
* `mellin_latticeTheta_term` — each term transforms to `π^{-s}Γ(s)·eisRealSummand z s p`.

The archimedean factor is `p`-independent, so it comes out of the sum whole:

  **`Λ(z,s) = π^{-s}·Γ(s) · ∑_{p ≠ 0} eisRealSummand z s p`.**

With `lambda_pole_split` (`Λ = Λ₀ − 1/s − 1/(1−s)`, `Λ₀` entire) this is the meromorphic
continuation of the Epstein lattice sum, pointwise in `z` — and via
`tsum_nonzero_eisRealSummand` and `im_smul_cpow_eq_eisRealSummand`, of the Eisenstein sum this
repo's Rankin--Selberg identity is stated in.

**Scope.**  Pointwise in `z`.  Moving this under `∫_𝒟 ‖u‖²·` needs `z`-uniformity (item (3)) and is
not done here.
-/

open Complex MeasureTheory UpperHalfPlane
open scoped Real

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.ThreeDConverse

/-- **The completed Epstein kernel is the archimedean factor times the Eisenstein sum.** -/
theorem lambda_eq_archimedean_mul_eisenstein (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    (generalFEPair z).Λ s =
      (((Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s) *
        ∑' p : {p : ℤ × ℤ // ¬(p.1 = 0 ∧ p.2 = 0)}, eisRealSummand z s p := by
  have hs0 : (0:ℝ) < s.re := by linarith
  rw [← epstein_mellin_eq z hs]
  -- present the tail as the nonzero-lattice sum
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
      (summable_latticeTheta_mellin_norms z hs)]
  rw [tsum_congr fun p => mellin_latticeTheta_term z p.2 hs0, tsum_mul_left]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.lambda_eq_archimedean_mul_eisenstein
