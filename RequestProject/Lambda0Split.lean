import RequestProject.TruncatedMellin

/-!
# The entire completion splits symmetrically through the weld

Continuation, part two.  The abstract entire completion `Λ₀_z` — Mathlib's Mellin transform
of the piecewise-modified bank — splits as the symmetric sum of truncated transforms
(`lambda0_split`):

  `Λ₀_z(s) = mellin (truncTheta z) s + mellin (truncTheta z) (1-s)`.

This is Riemann's classical trick, executed on the compiled objects: on `(0,1)` the modified
bank is the reflected tail through the compiled weld `Θ_z(1/t) = t·Θ_z(t)`
(`latticeTheta_inv`), and the reflection transports the Mellin variable `s ↦ 1-s`
(`mellin_cpow_smul` + `mellin_comp_inv`).  Combined with `truncMellin_norm_le` this bounds
`Λ₀_z(s)` explicitly in `z`, on every vertical strip — the domination for differentiating the
master equation under the `𝒟`-integral.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane Set
open scoped Real Topology

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta

/-- **The symmetric splitting of the entire completion** through the compiled weld. -/
theorem lambda0_split (z : ℍ) (s : ℂ) :
    (generalFEPair z).Λ₀ s =
      mellin (truncTheta z) s + mellin (truncTheta z) (1 - s) := by
  set B : ℝ → ℂ := fun t => (t : ℂ) ^ (-1 : ℂ) • truncTheta z t⁻¹ with hB
  -- the pointwise identity on the half-line
  have hpt : Set.EqOn ((generalFEPair z).f_modif)
      (fun t => truncTheta z t + B t) (Set.Ioi 0) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    rw [WeakFEPair.f_modif]
    simp only [generalFEPair, Pi.add_apply]
    congr 1
    by_cases h1 : t ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem h1, hB]
      have hinv1 : t⁻¹ ∈ Set.Ioi (1 : ℝ) := by
        rw [Set.mem_Ioi]
        rw [Set.mem_Ioo] at h1
        exact (one_lt_inv₀ h1.1).mpr h1.2
      simp only [truncTheta, Set.indicator_of_mem hinv1]
      have hFE : latticeThetaC z t⁻¹ = (t : ℂ) * latticeThetaC z t := by
        rw [latticeThetaC, latticeThetaC, latticeTheta_inv z ht0]
        push_cast
        ring
      rw [hFE, show ((t ^ (-(1 : ℝ)) : ℝ) : ℂ) = (t : ℂ) ^ (-1 : ℂ) by
        rw [Complex.ofReal_cpow ht0.le]
        norm_num]
      rw [smul_eq_mul, smul_eq_mul, one_mul, mul_one, Complex.cpow_neg_one]
      field_simp
    · rw [Set.indicator_of_notMem h1, hB]
      have ht1 : (1 : ℝ) ≤ t := by
        rw [Set.mem_Ioo, not_and] at h1
        exact not_lt.mp (h1 ht0)
      have hnot : t⁻¹ ∉ Set.Ioi (1 : ℝ) := by
        rw [Set.mem_Ioi, not_lt]
        exact inv_le_one_of_one_le₀ ht1
      simp only [truncTheta, Set.indicator_of_notMem hnot, smul_zero]
  -- convergence of the reflected piece
  have hconvB : MellinConvergent B s := by
    rw [hB, MellinConvergent.cpow_smul,
      show (fun t : ℝ => truncTheta z t⁻¹) = fun t => truncTheta z (t ^ (-1 : ℝ)) from
        funext fun t => by rw [Real.rpow_neg_one],
      MellinConvergent.comp_rpow (by norm_num : (-1 : ℝ) ≠ 0),
      show (s + (-1)) / ((-1 : ℝ) : ℂ) = 1 - s by push_cast; ring]
    exact truncMellin_convergent z (1 - s)
  have hAB := hasMellin_add (truncMellin_convergent z s) hconvB
  have hmel_congr : (generalFEPair z).Λ₀ s =
      mellin (fun t => truncTheta z t + B t) s := by
    rw [WeakFEPair.Λ₀]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [hpt ht]
  rw [hmel_congr, hAB.2]
  congr 1
  rw [hB, mellin_cpow_smul, mellin_comp_inv]
  congr 1
  ring

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.lambda0_split
