import RequestProject.DVPOffLineIff
import RequestProject.DVPLittlewoodTheorem

/-!
# The `S_all` cell mass is uniformly bounded (Lebesgue)

The engine's cell input is `∫_cell |Smult| = o(height)` — NOT a uniform
constant (426 recon: `CellMassBounded` was sufficient packaging, never the
requirement).  For the `S_all` part the answer is stronger than needed:
on every π-cell above `e⁶+1`, the cell length `≤ 2π/(log a − 2.2)` cancels
the a.e. Backlund size `20·log b + 3`, giving a UNIFORM Lebesgue bound

`∫_cell |S_all| ≤ 240`.

The `Smult` cell mass therefore differs from a bounded quantity by the
`N_off` cell mass alone — the register-content residual dissolves into
[this theorem] + [the single count-RH node].
-/

open Complex
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.ResidueJump

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The clock-rate logarithmic floor: `clockRate t ≥ (1/2)·log t − 1.1`
for `t ≥ 403`. -/
theorem clockRate_lower_log {t : ℝ} (ht : (403:ℝ) ≤ t) :
    (1/2) * Real.log t - 1.1 ≤ clockRate t := by
  have ht0 : (0:ℝ) < t := by linarith
  have habs : |t| = t := abs_of_pos ht0
  have hmu := mu_stirling_explicit (τ := t) (by rw [habs]; linarith)
  rw [habs] at hmu
  have hcr := CriticalLinePhasor.CarrierScale.clockRate_eq_pi_mul_mu t
  have hπ := Real.pi_pos
  have hlow := (abs_le.mp hmu).1
  -- log(2π) ≤ 2  (2π ≤ e²)
  have hlog2π : Real.log (2*Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have he2 : (7.38:ℝ) ≤ Real.exp 2 := by
      have h22 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
    nlinarith [Real.pi_lt_d4]
  have herr : (10/Real.pi)/t^2 ≤ 1/10 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have ht2 : (403:ℝ)^2 ≤ t^2 := by nlinarith
    nlinarith [Real.pi_gt_three]
  have hlogdiv : Real.log (t/(2*Real.pi))
      = Real.log t - Real.log (2*Real.pi) := by
    rw [Real.log_div (by linarith) (by positivity)]
  have hmu_low : (1/(2*Real.pi)) * (Real.log t - 2) - 1/10 / Real.pi
      ≤ Zeta23.mu t := by
    have h1 : (1/(2*Real.pi)) * Real.log (t/(2*Real.pi))
        ≥ (1/(2*Real.pi)) * (Real.log t - 2) := by
      rw [hlogdiv]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h2 : Zeta23.mu t
        ≥ (1/(2*Real.pi)) * Real.log (t/(2*Real.pi)) - (10/Real.pi)/t^2 := by
      linarith [hlow]
    have h3 : (10/Real.pi)/t^2 ≤ 1/10 / Real.pi := by
      rw [div_div]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have ht2 : (403:ℝ)^2 ≤ t^2 := by nlinarith
      nlinarith [hπ]
    linarith
  rw [hcr]
  have hchain : Real.pi * ((1/(2*Real.pi)) * (Real.log t - 2) - 1/10/Real.pi)
      ≤ Real.pi * Zeta23.mu t :=
    mul_le_mul_of_nonneg_left hmu_low hπ.le
  have hval : Real.pi * ((1/(2*Real.pi)) * (Real.log t - 2) - 1/10/Real.pi)
      = (1/2) * Real.log t - 1 - 1/10 := by
    field_simp
  rw [hval] at hchain
  linarith

/-- **The `S_all` cell-mass bound**: on every π-cell above `e⁶+1`,
`∫_cell |S_all| ≤ 240`, uniformly.  (Lebesgue measure: the cell length
cancels the ledger's Backlund size.) -/
theorem cell_sall_abs_mass_bound {a b : ℝ}
    (ha : Real.exp 6 + 1 ≤ a) (hab : a ≤ b)
    (hθ : theta b - theta a = Real.pi) :
    ∫ t in a..b, |SAll t| ≤ 240 := by
  have he6 : (403:ℝ) ≤ Real.exp 6 := by
    have h3 : (20.08:ℝ) ≤ Real.exp 3 := by
      have h33 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        norm_num
      nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
    have h66 : Real.exp 6 = Real.exp 3 * Real.exp 3 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h3, Real.exp_pos 3]
  have ha403 : (403:ℝ) ≤ a := by linarith
  have hL6 : (6:ℝ) ≤ Real.log a := by
    have := Real.log_le_log (Real.exp_pos 6) (by linarith : Real.exp 6 ≤ a)
    rwa [Real.log_exp] at this
  -- the cell length bound from the θ-span
  have hfloor : (0:ℝ) < (1/2) * Real.log a - 1.1 := by linarith
  have hlen : (b - a) * ((1/2) * Real.log a - 1.1) ≤ Real.pi := by
    have hspan := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := theta) (f' := clockRate) (a := a) (b := b)
      (fun t _ => theta_hasDerivAt t)
      (continuous_clockRate.intervalIntegrable _ _)
    have hlow : (∫ _t in a..b, ((1/2) * Real.log a - 1.1 : ℝ))
        ≤ ∫ t in a..b, clockRate t := by
      apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
        (continuous_clockRate.intervalIntegrable _ _)
      intro t htm
      have h1 := clockRate_lower_log (t := t) (by linarith [htm.1])
      have h2 : Real.log a ≤ Real.log t :=
        Real.log_le_log (by linarith) htm.1
      linarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
    linarith [hspan, hlow, hθ.le, hθ.ge]
  have hlen' : b - a ≤ Real.pi / ((1/2) * Real.log a - 1.1) := by
    rw [le_div_iff₀ hfloor]
    linarith [hlen]
  -- the a.e. Backlund majorant over the cell
  have hM : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc a b →
      |SAll t| ≤ 20 * Real.log b + 3 := by
    have hae := sall_ae_bound (T₁ := a) (T₂ := b) (by linarith) hab
    have hanull : (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ({a} : Set ℝ) = 0 := MeasureTheory.measure_singleton a
    rw [MeasureTheory.ae_iff] at hae ⊢
    refine MeasureTheory.measure_mono_null ?_
      (MeasureTheory.measure_union_null hae hanull)
    intro t htmem
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at htmem
    obtain ⟨htIcc, hbnd⟩ := htmem
    rcases eq_or_lt_of_le htIcc.1 with heq | hlt
    · exact Set.mem_union_right _ (by simp [← heq])
    · refine Set.mem_union_left _ ?_
      simp only [Set.mem_ofPred_eq, Classical.not_imp]
      refine ⟨?_, hbnd⟩
      rw [Set.uIoc_of_le hab]
      exact ⟨hlt, htIcc.2⟩
  have hint_abs : IntervalIntegrable (fun t => |SAll t|)
      MeasureTheory.volume a b := (sall_intervalIntegrable a b).abs
  have hmono : (∫ t in a..b, |SAll t|)
      ≤ ∫ _t in a..b, (20 * Real.log b + 3 : ℝ) := by
    apply intervalIntegral.integral_mono_ae_restrict hab hint_abs
      intervalIntegrable_const
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr hM
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  -- numeric assembly: (b−a)(20 log b + 3) ≤ 240
  have hb_a : b - a ≤ 2 := by
    have h1 : Real.pi / ((1/2) * Real.log a - 1.1) ≤ Real.pi / 1.9 := by
      apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
      linarith
    have h2 : Real.pi / 1.9 ≤ 2 := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith [Real.pi_lt_d4]
    linarith [hlen']
  have hlogb : Real.log b ≤ Real.log a + 1 := by
    have h1 : b ≤ a * Real.exp 1 := by
      have he1 : (2:ℝ) ≤ Real.exp 1 := by
        nlinarith [Real.exp_one_gt_d9]
      nlinarith [ha403]
    calc Real.log b ≤ Real.log (a * Real.exp 1) :=
          Real.log_le_log (by linarith) h1
      _ = Real.log a + 1 := by
          rw [Real.log_mul (by linarith) (Real.exp_ne_zero 1), Real.log_exp]
  have hkey : (b - a) * (20 * Real.log b + 3) ≤ 240 := by
    have hba0 : (0:ℝ) ≤ b - a := by linarith
    -- (b−a)·(log a − 2.2) ≤ 2π ≤ 6.3 and log b ≤ log a + 1
    have hprod : (b - a) * (Real.log a - 2.2) ≤ 2 * Real.pi := by
      nlinarith [hlen]
    have h2π : (2:ℝ) * Real.pi ≤ 6.3 := by nlinarith [Real.pi_lt_d4]
    -- (b−a)(20 log b + 3) ≤ 20(b−a)(log a −2.2) + (b−a)(20·(2.2+1)+3)
    have hexp : (b - a) * (20 * Real.log b + 3)
        ≤ 20 * ((b - a) * (Real.log a - 2.2)) + (b - a) * 67 := by
      nlinarith [hba0, hlogb]
    nlinarith [hprod, h2π, hba0, hb_a]
  calc (∫ t in a..b, |SAll t|)
      ≤ (b - a) * (20 * Real.log b + 3) := hmono
    _ ≤ 240 := hkey

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.clockRate_lower_log
#print axioms CriticalLinePhasor.DVP.cell_sall_abs_mass_bound
end AxiomAudit
