import RequestProject.MaassRankinMellin
import RequestProject.MaassMellinInterchange

/-!
# The strip side evaluates to the Rankin--Selberg series

Assembly of the left-hand side of the unconditional unfolding.  Every ingredient is compiled:

* `maass_horizontal_energy_of_pos` — Parseval at every height, no hypothesis;
* `mellin_tsum` — the interchange, whose two hypotheses are
  `radialKernelSq_mellinConvergent_scaled` and `summable_maass_mellin_norms`;
* `mellin_maass_term` — each mode's transform, `(n+1)^{-s}` times the archimedean factor.

Two pieces of bookkeeping are what remained.  The `y/2` prefactor of Parseval is not a constant:
multiplication by the height **shifts the Mellin exponent by one** (`mellin_mul_id`), which is why
the answer lands at `s + 1` rather than `s` — the Rankin--Selberg convention, recovered rather than
imposed.  And the coercion `ℝ → ℂ` passes through the sum unconditionally (`Complex.ofReal_tsum`),
so the real Parseval identity transfers with no extra summability hypothesis.

Result: `mellin_maassEnergy`.  The strip integral of `‖u‖²` against the height is
`½·(∑ₙ|λₙ|²(n+1)^{-(s+1)})·A(s+1)` — arithmetic times archimedean, cleanly split.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex Filter
open scoped Real Topology

set_option maxHeartbeats 1000000

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed

/-- The horizontal energy of the Maass wave at height `y`. -/
noncomputable def maassEnergy (M : GenuineMaassCuspForm3D) (y : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, ‖maassWaveCoordinates M.eigenData M.radialKernel x y‖ ^ 2

/-- **Multiplication by the height shifts the Mellin exponent by one.** -/
lemma mellin_mul_id (G : ℝ → ℂ) (s : ℂ) :
    mellin (fun y : ℝ => (y : ℂ) * G y) s = mellin G (s + 1) := by
  rw [mellin, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0:ℝ) < t := ht
  have hne : (t : ℂ) ≠ 0 := by
    simpa using ht0.ne'
  simp only [smul_eq_mul, ← mul_assoc]
  congr 1
  calc (t : ℂ) ^ (s - 1) * (t : ℂ)
      = (t : ℂ) ^ (s - 1) * (t : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
    _ = (t : ℂ) ^ (s - 1 + 1) := (Complex.cpow_add _ _ hne).symm
    _ = (t : ℂ) ^ (s + 1 - 1) := by congr 1; ring

/-- Constants pass through the Mellin transform. -/
lemma mellin_const_mul (c : ℂ) (G : ℝ → ℂ) (s : ℂ) :
    mellin (fun y : ℝ => c * G y) s = c * mellin G s := by
  rw [mellin, mellin, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul]
  ring

/-- `summable_maass_mellin_norms` at a complex exponent: the norm sees only the real part. -/
theorem summable_maass_mellin_norms_cpx (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < s.re) :
    Summable fun n : ℕ => ∫ t in Set.Ioi (0:ℝ),
      ‖(t : ℂ) ^ (s - 1) •
        ((‖M.eigenData.lam (n + 1)‖ ^ 2 *
          ‖M.radialKernel (((n : ℝ) + 1) * t)‖ ^ 2 : ℝ) : ℂ)‖ := by
  refine (summable_maass_mellin_norms M (σ := s.re) hs).congr fun n => ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0:ℝ) < t := ht
  rw [norm_smul, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
    Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  congr 2

/-- The Mellin integrand of each Fourier mode is integrable on `Re s > 1`. -/
theorem maass_mode_mellin_integrable (M : GenuineMaassCuspForm3D) {s : ℂ} (hs : 1 < s.re)
    (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) •
      ((‖M.eigenData.lam (n + 1)‖ ^ 2 *
        ‖M.radialKernel (((n : ℝ) + 1) * t)‖ ^ 2 : ℝ) : ℂ)) (Set.Ioi (0:ℝ)) := by
  have hc : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hbase := radialKernelSq_mellinConvergent_scaled M hs hc
  have := hbase.const_mul ((‖M.eigenData.lam (n + 1)‖ ^ 2 : ℝ) : ℂ)
  refine this.congr ?_
  filter_upwards with t
  simp only [smul_eq_mul, Complex.ofReal_mul]
  ring

/-- **The strip side, evaluated.**  Parseval, the interchange, and the per-mode transform assemble
into arithmetic times archimedean, at the shifted exponent the `y/2` prefactor dictates. -/
theorem mellin_maassEnergy (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < (s + 1).re) :
    mellin (fun y : ℝ => ((maassEnergy M y : ℝ) : ℂ)) s =
      (2 : ℂ)⁻¹ *
        ((∑' n : ℕ, rankinSelbergTerm M (s + 1) n) * archimedeanFactor M (s + 1)) := by
  have hE : (0:ℝ) ≤ 2 * (M.eigenData.E₀ + 2) := by positivity
  have hs1 : 1 < (s + 1).re := by linarith
  have h1 : mellin (fun y : ℝ => ((maassEnergy M y : ℝ) : ℂ)) s =
      mellin (fun y : ℝ => (2 : ℂ)⁻¹ * ((y : ℂ) *
        ∑' n : ℕ, ((‖M.eigenData.lam (n + 1)‖ ^ 2 *
          ‖M.radialKernel (((n : ℝ) + 1) * y)‖ ^ 2 : ℝ) : ℂ))) s := by
    rw [mellin, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := ht
    congr 1
    rw [maassEnergy, maass_horizontal_energy_of_pos M ht0, Complex.ofReal_mul,
      Complex.ofReal_tsum, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [h1, mellin_const_mul, mellin_mul_id,
    mellin_tsum (F := fun n t => ((‖M.eigenData.lam (n + 1)‖ ^ 2 *
        ‖M.radialKernel (((n : ℝ) + 1) * t)‖ ^ 2 : ℝ) : ℂ)) (s := s + 1)
      (fun n => maass_mode_mellin_integrable M hs1 n)
      (summable_maass_mellin_norms_cpx M hs)]
  rw [tsum_congr (fun n => mellin_maass_term M n (s + 1)), tsum_mul_right]

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.mellin_mul_id
#print axioms CriticalLinePhasor.ThreeDConverse.summable_maass_mellin_norms_cpx
#print axioms CriticalLinePhasor.ThreeDConverse.maass_mode_mellin_integrable
#print axioms CriticalLinePhasor.ThreeDConverse.mellin_maassEnergy
