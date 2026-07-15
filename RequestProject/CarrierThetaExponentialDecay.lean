import RequestProject.CarrierThetaDirichletInverse

/-!
# Exponential tails of completed carrier theta functions

The self-dual envelope contains `exp (-x - x⁻¹)`.  After reserving half of the `exp (-x)` factor
to absorb any real-power growth of the logarithmic carrier readout, a completed carrier theta has
the sharper tail `O(exp(-x/2))`.  The same estimate holds for the dual readout because conjugation
preserves norms.
-/

open Complex Set Filter Topology Asymptotics

namespace CriticalLinePhasor.StrandExchange

/-- Polynomial logarithmic readout growth is upgraded by the completion envelope to an exponential
tail. -/
theorem completedLogTheta_isBigO_exp_neg_half
    (E : ℂ → ℂ) (k A : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ A)) :
    completedLogTheta E k =O[atTop] (fun x : ℝ => Real.exp (-x / 2)) := by
  rw [isBigO_iff'] at hpoly ⊢
  obtain ⟨C, hCpos, hC⟩ := hpoly
  have hdec := (isLittleO_exp_neg_mul_rpow_atTop (a := (1 / 2 : ℝ)) (by norm_num)
    (k / 2 - A)).isBigO
  rw [isBigO_iff'] at hdec
  obtain ⟨D, hDpos, hD⟩ := hdec
  refine ⟨C * D, mul_pos hCpos hDpos, ?_⟩
  filter_upwards [hC, hD, eventually_gt_atTop (1 : ℝ)] with x hxC hxD hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hexpenv : Real.exp (-x - x⁻¹) ≤ Real.exp (-x) := by
    rw [Real.exp_le_exp]
    exact sub_le_self _ (inv_nonneg.mpr hx0.le)
  have hexpsplit : Real.exp (-x) = Real.exp (-x / 2) * Real.exp (-x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [completedLogTheta, selfDualEnvelope, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _),
    abs_of_pos (Real.exp_pos _)]
  have hxa : ‖x ^ A‖ = x ^ A := Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)
  have hxD' : Real.exp (-x / 2) ≤ D * x ^ (k / 2 - A) := by
    have hxD'' := hxD
    rw [Real.norm_of_nonneg (Real.exp_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hxD''
    convert hxD'' using 1 <;> ring
  rw [hxa] at hxC
  calc
    x ^ (-k / 2) * Real.exp (-x - x⁻¹) * ‖logTheta E x‖
        ≤ x ^ (-k / 2) * Real.exp (-x) * (C * x ^ A) := by gcongr
    _ = x ^ (-k / 2) * (Real.exp (-x / 2) * Real.exp (-x / 2)) *
        (C * x ^ A) := by rw [hexpsplit]
    _ ≤ x ^ (-k / 2) * (D * x ^ (k / 2 - A) * Real.exp (-x / 2)) *
        (C * x ^ A) := by gcongr
    _ = (C * D) * Real.exp (-x / 2) := by
      calc
        x ^ (-k / 2) * (D * x ^ (k / 2 - A) * Real.exp (-x / 2)) *
            (C * x ^ A) = (C * D) * Real.exp (-x / 2) *
              ((x ^ (-k / 2) * x ^ (k / 2 - A)) * x ^ A) := by ring
        _ = (C * D) * Real.exp (-x / 2) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
          simp only [show -k / 2 + (k / 2 - A) + A = 0 by ring, Real.rpow_zero,
            mul_one]

/-- The dual completed logarithmic readout has the same exponential tail. -/
theorem completedLogThetaDual_isBigO_exp_neg_half
    (E : ℂ → ℂ) (k A : ℝ)
    (hpoly : logTheta E =O[atTop] (fun x : ℝ => x ^ A)) :
    completedLogThetaDual E k =O[atTop] (fun x : ℝ => Real.exp (-x / 2)) := by
  have hp := completedLogTheta_isBigO_exp_neg_half E k A hpoly
  rw [isBigO_iff] at hp ⊢
  obtain ⟨C, hC⟩ := hp
  refine ⟨C, hC.mono fun x hx => ?_⟩
  simpa [completedLogTheta, completedLogThetaDual, logTheta, logThetaDual,
    RCLike.norm_conj] using hx

end CriticalLinePhasor.StrandExchange

#print axioms CriticalLinePhasor.StrandExchange.completedLogTheta_isBigO_exp_neg_half
#print axioms CriticalLinePhasor.StrandExchange.completedLogThetaDual_isBigO_exp_neg_half
