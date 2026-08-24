import RequestProject.DVPSeatRealPart
import RequestProject.DVPLadder126

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.DVP

open CriticalLinePhasor.HilbertPolya

private def bandAnchor (s : ℂ) : ℂ := -Complex.I * (s - 1 / 2)

private theorem chart_bandAnchor (s : ℂ) :
    1 / 2 + Complex.I * bandAnchor s = s := by
  unfold bandAnchor
  linear_combination -(s - 1 / 2) * Complex.I_mul_I

private theorem bandAnchor_re (s : ℂ) : (bandAnchor s).re = s.im := by
  unfold bandAnchor
  simp [Complex.mul_re, Complex.sub_im]

private theorem bandAnchor_im (s : ℂ) :
    (bandAnchor s).im = 1 / 2 - s.re := by
  unfold bandAnchor
  simp [Complex.mul_im, Complex.sub_re]

private theorem reflected_xi_ne_zero_band {s : ℂ}
    (hxi : ZD.riemannXi s ≠ 0) : ZD.riemannXi (1 - conj s) ≠ 0 := by
  rw [ZD.ZeroCount.riemannXi_one_sub,
    CriticalLinePhasor.ContourArgument.riemannXi_conj]
  simpa using hxi

/-- The full requested sign on the horizontal band covered by the compiled
zero census through ordinate `126`; every zero outside the census enters
with a nonnegative seat term. -/
theorem xi_logDeriv_re_nonpos_of_abs_im_le_125_5 {s : ℂ}
    (hs : s.re < 1 / 2) (ht : |s.im| ≤ 251 / 2)
    (hxi : ZD.riemannXi s ≠ 0) :
    (logDeriv ZD.riemannXi s).re ≤ 0 := by
  have hw : (1 / 2 + Complex.I * bandAnchor s) ∉ ZD.NontrivialZeros := by
    rw [chart_bandAnchor]
    exact fun hmem => hxi ((ZD.riemannXi_eq_zero_iff s).2 hmem)
  have hw' :
      (1 / 2 + Complex.I * (starRingEnd ℂ) (bandAnchor s)) ∉
        ZD.NontrivialZeros := by
    rw [chart_two_eq, chart_bandAnchor]
    exact fun hmem => reflected_xi_ne_zero_band hxi
      ((ZD.riemannXi_eq_zero_iff _).2 hmem)
  have him : bandAnchor s - (starRingEnd ℂ) (bandAnchor s) ≠ 0 := by
    rw [Complex.sub_conj]
    apply mul_ne_zero
    · rw [ofReal_ne_zero, bandAnchor_im]
      linarith
    · exact Complex.I_ne_zero
  have hseat := seat_channel_to_125_5 hw hw' him (by simpa [bandAnchor_re] using ht)
  have hre := seat_energy_re_eq hw hw' him
  rw [chart_bandAnchor] at hre
  rw [logDeriv_apply]
  have hq : 0 ≤ -(deriv ZD.riemannXi s / ZD.riemannXi s).re /
      (bandAnchor s).im := by
    rw [← hre]
    exact hseat
  have himpos : 0 < (bandAnchor s).im := by
    rw [bandAnchor_im]
    linarith
  rcases (div_nonneg_iff.mp hq) with h | h <;> nlinarith

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.xi_logDeriv_re_nonpos_of_abs_im_le_125_5
