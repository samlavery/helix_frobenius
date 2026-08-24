import RequestProject.DVPSqrtTable

/-!
# Auxiliary shifts for the second-order station cost

The first-order cost bottoms out at `N^{−5/2}` (`rpow_half_shifts`); the
second-order residual reads one power further, `N^{−7/2}`.  This lives in
its OWN module rather than in `DVPSqrtTable` so that adding it does not
invalidate the compiled station corpus (ledger 486).
-/

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The seventh half-power shift: `N^{−7/2} = N^{−1/2}/N³`. -/
theorem rpow_half_shift_seven {N : ℕ} (hN : 1 ≤ N) :
    (N:ℝ) ^ (-(7/2 : ℝ)) = (N:ℝ) ^ (-(1/2 : ℝ)) / N ^ 3 := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have h := Real.rpow_add hN0 (-(1/2 : ℝ)) (-3 : ℝ)
  have h3 : (N:ℝ) ^ ((-3 : ℝ)) = ((N:ℝ) ^ 3)⁻¹ := by
    rw [show ((-3:ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast,
      zpow_neg]
    norm_num
  rw [show (-(7/2 : ℝ)) = -(1/2 : ℝ) + (-3 : ℝ) by norm_num, h, h3]
  ring

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.rpow_half_shift_seven
end AxiomAudit
