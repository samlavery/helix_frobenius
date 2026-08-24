import RequestProject.DVPWindowBound
import RequestProject.DVPLittlewoodInterface

/-!
# The `S_all` window bound

The bridge (step v, first half): good heights are dense (bad ordinates are
finite per window) and co-null, and at every good height the compiled
census identity gives `S_all(t) = classicalSContour = F(t)/π`.  The window
integral of `S_all` therefore inherits 409's bound.
-/

open Metric Complex MeasureTheory Topology Filter Set
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.ResidueJump

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **Good heights are dense**: every unit window above `0` contains one. -/
theorem exists_goodHeight_between {a : ℝ} (ha : 0 < a) :
    ∃ T', a < T' ∧ T' < a + 1 ∧ GoodHeight T' := by
  have hbad : (Complex.im '' stripZeroWindow (a + 1)).Finite :=
    (stripZeroWindow_finite (a + 1)).image _
  have hIoo : (Set.Ioo a (a + 1)).Infinite :=
    Set.Ioo_infinite (by linarith)
  obtain ⟨T', hT'mem, hT'bad⟩ := hIoo.exists_notMem_finite hbad
  refine ⟨T', hT'mem.1, hT'mem.2, ⟨by linarith [hT'mem.1], ?_⟩⟩
  intro ρ hρ him
  apply hT'bad
  refine ⟨ρ, ⟨hρ, ?_, ?_⟩, him⟩
  · rw [him]
    linarith [hT'mem.1]
  · rw [him]
    linarith [hT'mem.2]

/-- **The `S_all` window bound**: over good-height windows above `e⁴`,
`|∫ S_all| ≤ 12 + 1600·log t₁` — the compiled census identity transports
409's bound from the contour argument to the census ledger. -/
theorem window_SAll_integral_bound {t₀ t₁ : ℝ}
    (h₀ : GoodHeight t₀) (h₁ : GoodHeight t₁)
    (he : Real.exp 4 ≤ t₀) (ht : t₀ ≤ t₁) :
    |∫ t in t₀..t₁, SAll t| ≤ 12 + 1600 * Real.log t₁ := by
  have hπ := Real.pi_pos
  have hT50 : (50:ℝ) ≤ t₀ := by
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
        * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    nlinarith [he2, Real.exp_pos 1]
  -- a.e. identity S_all = F/π on the window
  have hae : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc t₀ t₁ →
      SAll t = (1 / Real.pi) *
        ((Complex.log (riemannZeta ((2:ℂ) + (t:ℂ) * I))).im
          - ∫ x in (1/2 : ℝ)..2,
              (deriv riemannZeta ((x:ℂ) + (t:ℂ) * I) /
                riemannZeta ((x:ℂ) + (t:ℂ) * I)).im) := by
    have hbadfin : (Complex.im '' stripZeroWindow t₁).Finite :=
      (stripZeroWindow_finite t₁).image _
    have hnull := hbadfin.measure_zero MeasureTheory.volume
    rw [ae_iff]
    refine measure_mono_null ?_ hnull
    intro t hmem
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hmem
    obtain ⟨htI, hne⟩ := hmem
    rw [Set.uIoc_of_le ht] at htI
    by_contra htbad
    apply hne
    -- t is a good height
    have hgood : GoodHeight t := by
      refine ⟨by linarith [htI.1], ?_⟩
      intro ρ hρ him
      apply htbad
      refine ⟨ρ, ⟨hρ, ?_, ?_⟩, him⟩
      · rw [him]
        linarith [htI.1]
      · rw [him]
        exact htI.2
    have hcensus := classicalSContour_eq_Smult_add_offLine hgood
    have hident := classicalSContour_eq_log_sub_integral hgood
    rw [SAll, ← hcensus]
    field_simp
    linarith [hident]
  have hcong := intervalIntegral.integral_congr_ae hae
  rw [hcong, intervalIntegral.integral_const_mul]
  have h409 := window_arg_integral_bound h₀ h₁ he ht
  have hL4 : (4:ℝ) ≤ Real.log t₁ := by
    have h1 : Real.exp 4 ≤ t₁ := le_trans he ht
    have := Real.log_le_log (Real.exp_pos 4) h1
    rwa [Real.log_exp] at this
  have hπ1 : (1:ℝ) ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  have hnn : (0:ℝ) ≤ 12 + 1600 * Real.log t₁ := by linarith
  calc (1 / Real.pi) * |∫ t in t₀..t₁,
        ((Complex.log (riemannZeta ((2:ℂ) + (t:ℂ) * I))).im
          - ∫ x in (1/2 : ℝ)..2,
              (deriv riemannZeta ((x:ℂ) + (t:ℂ) * I) /
                riemannZeta ((x:ℂ) + (t:ℂ) * I)).im)|
      ≤ (1 / Real.pi) * (12 + 1600 * Real.log t₁) :=
        mul_le_mul_of_nonneg_left h409 (by positivity)
    _ ≤ 1 * (12 + 1600 * Real.log t₁) := by
        apply mul_le_mul_of_nonneg_right _ hnn
        rw [div_le_one hπ]
        exact hπ1
    _ = 12 + 1600 * Real.log t₁ := one_mul _

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.exists_goodHeight_between
#print axioms CriticalLinePhasor.DVP.window_SAll_integral_bound
end AxiomAudit
