import RequestProject.MaassArchimedeanFactor
import RequestProject.MaassRankinSeries

/-!
# The dilation law for the archimedean integral

The Rankin--Selberg evaluation runs the Mellin transform through the Fourier series, and
`MaassMellinInterchange.mellin_tsum` asks for two things: each mode's Mellin integrand integrable,
and the *integrated norms* summable.  Both reduce to one computation — how the archimedean integral
responds to the dilation `t ↦ (n+1)t`.

`mellin_kernelSq_scaled` already does this for the transform's **value**.  What the interchange
needs is the same law for the **integral of the norm**, which is a genuinely different object (the
value can cancel; the norm cannot).  Here it is, from Mathlib's `integral_comp_mul_left_Ioi`:

  `∫₀^∞ t^{σ-1}‖K(ct)‖²dt = c^{-σ}·∫₀^∞ t^{σ-1}‖K(t)‖²dt`.

With that, the `n`-th integrated norm is `|λₙ|²(n+1)^{-σ}·A(σ)`, so summability is exactly
`summable_rankinSeries` — the arithmetic side — times one finite constant.  This is the DC/AC split
of the interchange: the archimedean factor is the common mode, evaluated once, and the dilation
costs a pure power that the arithmetic series absorbs.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex Filter Asymptotics
open scoped Real Topology

set_option maxHeartbeats 1000000

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed

/-- The archimedean factor at a real exponent, as a real integral. -/
noncomputable def archimedeanFactorReal (M : GenuineMaassCuspForm3D) (σ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0:ℝ), t ^ (σ - 1) * ‖M.radialKernel t‖ ^ 2

/-- **The scaled kernel square is Mellin-convergent** on `Re s > 1`, for every dilation.  Same
proof as the undilated case: the derived `C/t` boundary bound and the cusp decay both survive
`t ↦ c·t`. -/
theorem radialKernelSq_mellinConvergent_scaled (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : 1 < s.re) {c : ℝ} (hc : 0 < c) :
    MellinConvergent (fun t : ℝ => ((‖M.radialKernel (c * t)‖ ^ 2 : ℝ) : ℂ)) s := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := radialKernel_sq_le_div M
  obtain ⟨C₁, hC₁1, hC₁⟩ := radialKernel_norm_le_exp_of_pos M (a := 1) one_pos
  have hKcont : ContinuousOn M.radialKernel (Set.Ioi (0:ℝ)) := (M.radial_smooth 0).continuousOn
  have hpi : (0:ℝ) < 4 * Real.pi * c := by positivity
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := (1:ℝ)) ?_ ?_ (by linarith) ?_ hs
  · have hmap : ContinuousOn (fun t : ℝ => c * t) (Set.Ioi (0:ℝ)) := (continuous_const.mul
      continuous_id).continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => c * t) (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ)) := by
      intro t ht; exact mul_pos hc ht
    exact ((Complex.continuous_ofReal.comp_continuousOn
      (((hKcont.comp hmap hmaps)).norm.pow 2))).locallyIntegrableOn measurableSet_Ioi
  · -- cusp end
    have hOexp : (fun t : ℝ => ((‖M.radialKernel (c * t)‖ ^ 2 : ℝ) : ℂ)) =O[atTop]
        (fun t : ℝ => Real.exp (-(4 * Real.pi * c) * t)) := by
      rw [isBigO_iff]
      refine ⟨C₁ ^ 2, ?_⟩
      filter_upwards [eventually_ge_atTop (1 / c)] with t ht
      have hct : (1:ℝ) ≤ c * t := by
        rw [div_le_iff₀ hc] at ht
        linarith [ht]
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (Real.exp_pos _).le]
      have hsq : ‖M.radialKernel (c * t)‖ ^ 2 ≤
          (C₁ * Real.exp (-(2 * Real.pi * (c * t)))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hC₁ _ hct) 2
      refine le_trans hsq (le_of_eq ?_)
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    exact hOexp.trans
      (CriticalLinePhasor.EpsteinTheta.exp_neg_isBigO_rpow hpi (-(s.re + 1)))
  · -- boundary end
    rw [isBigO_iff]
    refine ⟨C₀ / c, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0:ℝ) < t := ht
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), Real.rpow_neg_one]
    have hb := hC₀ (c * t) (mul_pos hc ht0)
    calc ‖M.radialKernel (c * t)‖ ^ 2 ≤ C₀ / (c * t) := hb
      _ = C₀ / c * t⁻¹ := by field_simp

/-- The real-exponent archimedean integrand is integrable on `Re s > 1`. -/
theorem archimedeanFactorReal_integrableOn (M : GenuineMaassCuspForm3D) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖M.radialKernel t‖ ^ 2) (Set.Ioi (0:ℝ)) := by
  have hre : ((σ : ℂ) - 1).re = σ - 1 := by simp
  have hmel := archimedeanFactor_mellinConvergent M (s := (σ : ℂ)) (by simpa using hσ)
  refine (hmel.norm).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0:ℝ) < t := ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), hre]

/-- The same, dilated. -/
theorem archimedeanFactorReal_integrableOn_scaled (M : GenuineMaassCuspForm3D) {σ : ℝ}
    (hσ : 1 < σ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖M.radialKernel (c * t)‖ ^ 2)
      (Set.Ioi (0:ℝ)) := by
  have hre : ((σ : ℂ) - 1).re = σ - 1 := by simp
  have hmel := radialKernelSq_mellinConvergent_scaled M (s := (σ : ℂ)) (by simpa using hσ) hc
  refine (hmel.norm).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0:ℝ) < t := ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), hre]

/-- **The dilation law for the archimedean integral.**  A dilation costs exactly `c^{-σ}` — the
same power the transform's value picks up, but proved here for the integral of the *norm*, which is
what the series interchange consumes.  No half-plane condition: the substitution is unconditional,
and when both sides diverge it reads `0 = 0`. -/
theorem archimedeanFactorReal_scaled (M : GenuineMaassCuspForm3D) {σ : ℝ}
    {c : ℝ} (hc : 0 < c) :
    (∫ t in Set.Ioi (0:ℝ), t ^ (σ - 1) * ‖M.radialKernel (c * t)‖ ^ 2) =
      c ^ (-σ) * archimedeanFactorReal M σ := by
  set g : ℝ → ℝ := fun x => (x / c) ^ (σ - 1) * ‖M.radialKernel x‖ ^ 2 with hg
  have hstep1 : (∫ t in Set.Ioi (0:ℝ), t ^ (σ - 1) * ‖M.radialKernel (c * t)‖ ^ 2) =
      ∫ t in Set.Ioi (0:ℝ), g (c * t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := ht
    rw [hg]
    simp only
    congr 2
    field_simp
  have hstep2 : (∫ t in Set.Ioi (0:ℝ), g (c * t)) = c⁻¹ • ∫ x in Set.Ioi (0:ℝ), g x := by
    have := integral_comp_mul_left_Ioi g 0 hc
    rwa [mul_zero] at this
  have hstep3 : (∫ x in Set.Ioi (0:ℝ), g x) =
      c ^ (-(σ - 1)) * archimedeanFactorReal M σ := by
    rw [archimedeanFactorReal, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0:ℝ) < x := hx
    rw [hg]
    simp only
    rw [Real.div_rpow hx0.le hc.le, Real.rpow_neg hc.le, div_eq_mul_inv]
    ring
  rw [hstep1, hstep2, hstep3, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [show c⁻¹ = c ^ (-(1:ℝ)) from (Real.rpow_neg_one c).symm, ← Real.rpow_add hc]
  congr 1
  ring

/-- **The integrated norms of the Fourier modes are summable** — the second hypothesis of
`mellin_tsum`, reduced to the arithmetic series times one finite archimedean constant. -/
theorem summable_maass_mellin_norms (M : GenuineMaassCuspForm3D) {σ : ℝ}
    (hσ : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < σ) :
    Summable fun n : ℕ => ∫ t in Set.Ioi (0:ℝ),
      ‖(t : ℂ) ^ ((σ : ℂ) - 1) •
        ((‖M.eigenData.lam (n + 1)‖ ^ 2 *
          ‖M.radialKernel (((n : ℝ) + 1) * t)‖ ^ 2 : ℝ) : ℂ)‖ := by
  have hE : (0:ℝ) ≤ 2 * (M.eigenData.E₀ + 2) := by positivity
  have hσ1 : 1 < σ := by linarith
  have hval : ∀ n : ℕ, (∫ t in Set.Ioi (0:ℝ),
      ‖(t : ℂ) ^ ((σ : ℂ) - 1) •
        ((‖M.eigenData.lam (n + 1)‖ ^ 2 *
          ‖M.radialKernel (((n : ℝ) + 1) * t)‖ ^ 2 : ℝ) : ℂ)‖) =
      archimedeanFactorReal M σ *
        (rankinCoeff M n * (((n : ℝ) + 1) ^ (-σ))) := by
    intro n
    have hc : (0:ℝ) < (n : ℝ) + 1 := by positivity
    have hpt : ∀ t : ℝ, t ∈ Set.Ioi (0:ℝ) →
        ‖(t : ℂ) ^ ((σ : ℂ) - 1) •
          ((‖M.eigenData.lam (n + 1)‖ ^ 2 *
            ‖M.radialKernel (((n : ℝ) + 1) * t)‖ ^ 2 : ℝ) : ℂ)‖ =
        rankinCoeff M n * (t ^ (σ - 1) * ‖M.radialKernel (((n : ℝ) + 1) * t)‖ ^ 2) := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), rankinCoeff]
      have hre : ((σ : ℂ) - 1).re = σ - 1 := by simp
      rw [hre]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      MeasureTheory.integral_const_mul, archimedeanFactorReal_scaled M hc]
    ring
  refine (Summable.congr ?_ (fun n => (hval n).symm))
  exact (summable_rankinSeries M hσ).mul_left _

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.radialKernelSq_mellinConvergent_scaled
#print axioms CriticalLinePhasor.ThreeDConverse.archimedeanFactorReal_integrableOn
#print axioms CriticalLinePhasor.ThreeDConverse.archimedeanFactorReal_scaled
#print axioms CriticalLinePhasor.ThreeDConverse.summable_maass_mellin_norms
