import RequestProject.DVPSeatRealPart
import RequestProject.SeatScalarCriterion

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.DVP

open CriticalLinePhasor.HilbertPolya

private def leftAnchor (s : ℂ) : ℂ := -Complex.I * (s - 1 / 2)

private theorem chart_leftAnchor (s : ℂ) :
    1 / 2 + Complex.I * leftAnchor s = s := by
  unfold leftAnchor
  linear_combination -(s - 1 / 2) * Complex.I_mul_I

private theorem leftAnchor_im (s : ℂ) :
    (leftAnchor s).im = 1 / 2 - s.re := by
  unfold leftAnchor
  simp [Complex.mul_im, Complex.sub_re]

private theorem reflected_xi_ne_zero {s : ℂ} (hxi : ZD.riemannXi s ≠ 0) :
    ZD.riemannXi (1 - conj s) ≠ 0 := by
  rw [ZD.ZeroCount.riemannXi_one_sub,
    CriticalLinePhasor.ContourArgument.riemannXi_conj]
  simpa using hxi

/-- Seat nonnegativity at the chart anchor gives the requested pointwise sign. -/
theorem xi_logDeriv_re_nonpos_of_seat {s : ℂ}
    (hs : s.re < 1 / 2) (hxi : ZD.riemannXi s ≠ 0)
    (hseat : 0 ≤ (∑' rho : {rho : ℂ // rho ∈ ZD.NontrivialZeros},
      (ZD.xiOrderNat rho.val : ℂ) *
        ((spectralCoord rho.val - leftAnchor s)⁻¹ *
          (spectralCoord rho.val - (starRingEnd ℂ) (leftAnchor s))⁻¹)).re) :
    (logDeriv ZD.riemannXi s).re ≤ 0 := by
  have hw : (1 / 2 + Complex.I * leftAnchor s) ∉ ZD.NontrivialZeros := by
    rw [chart_leftAnchor]
    exact fun hmem => hxi ((ZD.riemannXi_eq_zero_iff s).2 hmem)
  have hw' :
      (1 / 2 + Complex.I * (starRingEnd ℂ) (leftAnchor s)) ∉
        ZD.NontrivialZeros := by
    rw [chart_two_eq, chart_leftAnchor]
    exact fun hmem => reflected_xi_ne_zero hxi
      ((ZD.riemannXi_eq_zero_iff _).2 hmem)
  have hwim : 0 < (leftAnchor s).im := by
    rw [leftAnchor_im]
    linarith
  have him : leftAnchor s - (starRingEnd ℂ) (leftAnchor s) ≠ 0 := by
    rw [Complex.sub_conj]
    exact mul_ne_zero (ofReal_ne_zero.mpr (by linarith)) Complex.I_ne_zero
  have hre := seat_energy_re_eq hw hw' him
  rw [chart_leftAnchor] at hre
  rw [logDeriv_apply]
  have hq : 0 ≤ -(deriv ZD.riemannXi s / ZD.riemannXi s).re /
      (leftAnchor s).im := by
    rw [← hre]
    exact hseat
  rcases (div_nonneg_iff.mp hq) with h | h <;> nlinarith

/-- Unconditional requested sign in the pole-free half-plane `Re s < 0`. -/
theorem xi_logDeriv_re_nonpos_of_re_neg {s : ℂ}
    (hs : s.re < 0) (hxi : ZD.riemannXi s ≠ 0) :
    (logDeriv ZD.riemannXi s).re ≤ 0 := by
  apply xi_logDeriv_re_nonpos_of_seat (by linarith) hxi
  apply CriticalLinePhasor.SeatScalar.seat_energy_nonneg_of_outside_strip
  have him : (leftAnchor s).im = 1 / 2 - s.re := leftAnchor_im s
  rw [abs_of_pos (by linarith [him])]
  linarith [him]

/-- If all nontrivial zeros are on-line, the requested sign holds throughout
the entire left half of the critical strip. -/
theorem xi_logDeriv_re_nonpos_of_zeros_online
    (hon : ∀ rho ∈ ZD.NontrivialZeros, rho.re = 1 / 2) :
    ∀ s : ℂ, s.re < 1 / 2 → ZD.riemannXi s ≠ 0 →
      (logDeriv ZD.riemannXi s).re ≤ 0 := by
  intro s hs hxi
  apply xi_logDeriv_re_nonpos_of_seat hs hxi
  apply CriticalLinePhasor.SeatScalar.seat_energy_nonneg_of_online hon
  · rw [chart_leftAnchor]
    exact fun hmem => hxi ((ZD.riemannXi_eq_zero_iff s).2 hmem)
  · rw [chart_two_eq, chart_leftAnchor]
    exact fun hmem => reflected_xi_ne_zero hxi
      ((ZD.riemannXi_eq_zero_iff _).2 hmem)
  · rw [Complex.sub_conj]
    apply mul_ne_zero
    · rw [ofReal_ne_zero, leftAnchor_im]
      linarith
    · exact Complex.I_ne_zero

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.xi_logDeriv_re_nonpos_of_seat
#print axioms CriticalLinePhasor.DVP.xi_logDeriv_re_nonpos_of_re_neg
#print axioms CriticalLinePhasor.DVP.xi_logDeriv_re_nonpos_of_zeros_online
