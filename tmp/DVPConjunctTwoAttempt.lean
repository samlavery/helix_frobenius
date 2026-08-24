import RequestProject.DVPLadder1269o2
import RequestProject.DVPSeatRealPart

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
  ring

private theorem leftAnchor_re (s : ℂ) :
    (leftAnchor s).re = s.im := by
  unfold leftAnchor
  simp [Complex.mul_re, Complex.sub_im]

private theorem reflected_xi_ne_zero {s : ℂ} (hxi : ZD.riemannXi s ≠ 0) :
    ZD.riemannXi (1 - conj s) ≠ 0 := by
  rw [ZD.ZeroCount.riemannXi_one_sub,
    CriticalLinePhasor.ContourArgument.riemannXi_conj]
  exact map_ne_zero_of_injective Complex.conjCLE.injective hxi

theorem xi_logDeriv_re_nonpos_of_seat {s : ℂ}
    (hs : s.re < 1 / 2) (hxi : ZD.riemannXi s ≠ 0)
    (hseat : 0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      (ZD.xiOrderNat ρ.val : ℂ) *
        ((spectralCoord ρ.val - leftAnchor s)⁻¹ *
          (spectralCoord ρ.val - (starRingEnd ℂ) (leftAnchor s))⁻¹)).re) :
    (logDeriv ZD.riemannXi s).re ≤ 0 := by
  have hw : (1 / 2 + Complex.I * leftAnchor s) ∉ ZD.NontrivialZeros := by
    rw [chart_leftAnchor]
    exact fun hmem => hxi ((ZD.riemannXi_eq_zero_iff s).2 hmem)
  have hw' :
      (1 / 2 + Complex.I * (starRingEnd ℂ) (leftAnchor s)) ∉ ZD.NontrivialZeros := by
    rw [chart_two_eq, chart_leftAnchor]
    exact fun hmem => reflected_xi_ne_zero hxi ((ZD.riemannXi_eq_zero_iff _).2 hmem)
  have hwim : 0 < (leftAnchor s).im := by
    rw [leftAnchor_im]
    linarith
  have him : leftAnchor s - (starRingEnd ℂ) (leftAnchor s) ≠ 0 := by
    rw [Complex.sub_conj]
    exact mul_ne_zero (ofReal_ne_zero.mpr (by linarith)) Complex.I_ne_zero
  have hre := seat_energy_re_eq hw hw' him
  rw [chart_leftAnchor] at hre
  rw [logDeriv_apply]
  nlinarith

theorem xi_logDeriv_re_nonpos_left_below_634 {s : ℂ}
    (hs : s.re < 1 / 2) (hxi : ZD.riemannXi s ≠ 0)
    (ht : |s.im| ≤ 634) :
    (logDeriv ZD.riemannXi s).re ≤ 0 := by
  apply xi_logDeriv_re_nonpos_of_seat hs hxi
  apply seat_channel_to_634
  · rw [chart_leftAnchor]
    exact fun hmem => hxi ((ZD.riemannXi_eq_zero_iff s).2 hmem)
  · rw [chart_two_eq, chart_leftAnchor]
    exact fun hmem => reflected_xi_ne_zero hxi ((ZD.riemannXi_eq_zero_iff _).2 hmem)
  · rw [Complex.sub_conj]
    apply mul_ne_zero
    · rw [ofReal_ne_zero, leftAnchor_im]
      linarith
    · exact Complex.I_ne_zero
  · rw [leftAnchor_re]
    exact ht

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.xi_logDeriv_re_nonpos_of_seat
#print axioms CriticalLinePhasor.DVP.xi_logDeriv_re_nonpos_left_below_634
