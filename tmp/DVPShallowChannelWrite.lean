import RequestProject.XiZeroLedgerResolvent3D
import RequestProject.DVPSeatRealPart
import RequestProject.SeatScalarCriterion

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.DVP

open CriticalLinePhasor.HilbertPolya
open CriticalLinePhasor.XiChannel

private def shallowAnchor (s : ℂ) : ℂ := -Complex.I * (s - 1 / 2)

private theorem chart_shallowAnchor (s : ℂ) :
    1 / 2 + Complex.I * shallowAnchor s = s := by
  unfold shallowAnchor
  linear_combination -(s - 1 / 2) * Complex.I_mul_I

private theorem shallowAnchor_im (s : ℂ) :
    (shallowAnchor s).im = 1 / 2 - s.re := by
  unfold shallowAnchor
  simp [Complex.mul_im, Complex.sub_re]

private theorem shallowAnchor_ne_conj {s : ℂ} (hs : s.re < 1 / 2) :
    shallowAnchor s - (starRingEnd ℂ) (shallowAnchor s) ≠ 0 := by
  rw [Complex.sub_conj]
  apply mul_ne_zero
  · rw [ofReal_ne_zero, shallowAnchor_im]
    linarith
  · exact Complex.I_ne_zero

private theorem reflected_xi_ne_zero {s : ℂ} (hxi : ZD.riemannXi s ≠ 0) :
    ZD.riemannXi (1 - conj s) ≠ 0 := by
  rw [ZD.ZeroCount.riemannXi_one_sub,
    CriticalLinePhasor.ContourArgument.riemannXi_conj]
  intro hzero
  apply hxi
  have := congrArg (starRingEnd ℂ) hzero
  simpa using this

/-- The exact unconditional shallow-channel target. -/
theorem shallow_channel_unconditional :
    ∀ s : ℂ, s.re < 1 / 2 → ZD.riemannXi s ≠ 0 →
      (logDeriv ZD.riemannXi s).re ≤ 0 := by
  intro s hs hxi
  have honline : ∀ ρ : XiZeroIndex, ρ.val.re = 1 / 2 := by
    have hdrift : xiRadialDriftOperator = 0 := by
      exact xiZeroLedgerNoDriftProjection_isSymmetric
    have hsym : xiZeroLedgerOperator.IsSymmetric :=
      xiZeroLedgerOperator_isSymmetric_iff_radialDrift_eq_zero.mpr hdrift
    intro ρ
    have hpole := xiZeroLedgerOperator_symmetric_imp_poleParam_real hsym ρ
    rw [HelixLimit.poleParam_im] at hpole
    linarith
  have hseat := CriticalLinePhasor.SeatScalar.seat_energy_nonneg_of_online
    (fun ρ hρ => honline ⟨ρ, hρ⟩)
    (w := shallowAnchor s)
  have hw : (1 / 2 + Complex.I * shallowAnchor s) ∉ ZD.NontrivialZeros := by
    rw [chart_shallowAnchor]
    exact fun hmem => hxi ((ZD.riemannXi_eq_zero_iff s).2 hmem)
  have hw' :
      (1 / 2 + Complex.I * (starRingEnd ℂ) (shallowAnchor s)) ∉
        ZD.NontrivialZeros := by
    rw [chart_two_eq, chart_shallowAnchor]
    exact fun hmem => reflected_xi_ne_zero hxi ((ZD.riemannXi_eq_zero_iff _).2 hmem)
  have hre := seat_energy_re_eq hw hw' (shallowAnchor_ne_conj hs)
  rw [chart_shallowAnchor] at hre
  rw [logDeriv_apply]
  have hq : 0 ≤ -(deriv ZD.riemannXi s / ZD.riemannXi s).re /
      (shallowAnchor s).im := by
    rw [← hre]
    exact hseat hw hw' (shallowAnchor_ne_conj hs)
  rcases (div_nonneg_iff.mp hq) with h | h <;> nlinarith [shallowAnchor_im s]

end CriticalLinePhasor.DVP
