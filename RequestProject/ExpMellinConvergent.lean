import RequestProject.MellinTsumGeneral

/-!
# Mellin convergence of a decaying exponential

Per-term integrability for the lattice-theta interchange: each term of
`latticeTheta z t = ∑'_p exp(-(πt)·gram z p)` is a pure exponential, and its Mellin integrand is
integrable on the whole ray for `Re s > 0`.

Both ends are the object's own scale: at the cusp the exponential beats every power (`b = s.re+1`
works, and so would any exponent), at the boundary it is bounded by `1` (`b = 0`).  The condition
`0 < Re s` comes only from the boundary end — it is the Gamma integral's own half-plane, not an
imported restriction.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Real Topology

namespace CriticalLinePhasor.ThreeDConverse

/-- **A decaying exponential is Mellin-convergent on `Re s > 0`.** -/
theorem mellinConvergent_exp_neg_mul {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ)) s := by
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := (0:ℝ)) ?_ ?_ (by linarith) ?_ hs
  · exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (by fun_prop))).continuousOn.locallyIntegrableOn
      measurableSet_Ioi
  · -- cusp end: the exponential beats every power
    have hO : (fun t : ℝ => ((Real.exp (-(a * t)) : ℝ) : ℂ)) =O[atTop]
        (fun t : ℝ => Real.exp (-a * t)) := by
      rw [isBigO_iff]
      refine ⟨1, ?_⟩
      filter_upwards with t
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
      apply le_of_eq
      congr 1
      ring
    exact hO.trans (CriticalLinePhasor.EpsteinTheta.exp_neg_isBigO_rpow ha (-(s.re + 1)))
  · -- boundary end: bounded by one
    rw [isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0:ℝ) < t := ht
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
    apply Real.exp_le_one_iff.mpr
    nlinarith

/-- The per-term integrability the lattice-theta interchange consumes. -/
theorem integrableOn_exp_neg_mul_mellin {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • ((Real.exp (-(a * t)) : ℝ) : ℂ))
      (Set.Ioi (0:ℝ)) :=
  mellinConvergent_exp_neg_mul ha hs

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.mellinConvergent_exp_neg_mul
#print axioms CriticalLinePhasor.ThreeDConverse.integrableOn_exp_neg_mul_mellin
