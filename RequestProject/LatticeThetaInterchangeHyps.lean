import RequestProject.LatticeThetaZeroSplit

/-!
# The two interchange hypotheses for the lattice theta

`mellin_tsum_countable` asks for per-term integrability and summability of the integrated norms.
Both are now assemblies of pieces already proved:

* per-term: each term is a decaying exponential of rate `π·gram z p`, so
  `integrableOn_exp_neg_mul_mellin` applies once the exponent is rewritten on that rate;
* the norms: `integral_norm_mellin_exp` evaluates each to `Γ(σ)·(π·gram z p)^{-σ}`, and the
  `p`-dependence is exactly `(gram z p)^{-σ}`, which `summable_gram_rpow` controls.

The archimedean constants `Γ(σ)·π^{-σ}` factor out of the summability question entirely — they are
the common mode again, and a common mode never affects convergence.
-/

open Complex MeasureTheory UpperHalfPlane
open scoped Real

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.ThreeDConverse

/-- Per-term integrability of the lattice-theta Mellin integrand. -/
lemma integrableOn_latticeTheta_term (z : ℍ) {p : ℤ × ℤ} (hp : ¬(p.1 = 0 ∧ p.2 = 0))
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • ((Real.exp (-(Real.pi * t) * gram z p) : ℝ) : ℂ))
      (Set.Ioi (0:ℝ)) := by
  have hg : 0 < gram z p := gram_pos_nz z hp
  have hpi : (0:ℝ) < Real.pi * gram z p := by positivity
  refine (integrableOn_exp_neg_mul_mellin hpi hs).congr ?_
  filter_upwards with t
  congr 3
  ring

/-- The integrated norms of the lattice-theta terms are summable for `Re s > 1`. -/
theorem summable_latticeTheta_mellin_norms (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : {p : ℤ × ℤ // ¬(p.1 = 0 ∧ p.2 = 0)} =>
      ∫ t in Set.Ioi (0:ℝ),
        ‖(t : ℂ) ^ (s - 1) • ((Real.exp (-(Real.pi * t) * gram z p.1) : ℝ) : ℂ)‖ := by
  have hs0 : (0:ℝ) < s.re := by linarith
  have hval : ∀ p : {p : ℤ × ℤ // ¬(p.1 = 0 ∧ p.2 = 0)},
      (∫ t in Set.Ioi (0:ℝ),
        ‖(t : ℂ) ^ (s - 1) • ((Real.exp (-(Real.pi * t) * gram z p.1) : ℝ) : ℂ)‖) =
      (Real.Gamma s.re * Real.pi ^ (-s.re)) * (gram z p.1) ^ (-s.re) := by
    intro p
    have hg : 0 < gram z p.1 := gram_pos_nz z p.2
    have hpi : (0:ℝ) < Real.pi * gram z p.1 := by positivity
    have hrw : (fun t : ℝ =>
        ‖(t : ℂ) ^ (s - 1) • ((Real.exp (-(Real.pi * t) * gram z p.1) : ℝ) : ℂ)‖) =
        fun t : ℝ =>
          ‖(t : ℂ) ^ (s - 1) • ((Real.exp (-((Real.pi * gram z p.1) * t)) : ℝ) : ℂ)‖ := by
      funext t
      congr 4
      ring
    rw [hrw, integral_norm_mellin_exp hpi hs0,
      Real.mul_rpow Real.pi_pos.le hg.le]
    ring
  refine (Summable.congr ?_ fun p => (hval p).symm)
  exact (summable_gram_rpow_nz z hs).mul_left _

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.integrableOn_latticeTheta_term
#print axioms CriticalLinePhasor.Unfolding.summable_latticeTheta_mellin_norms
