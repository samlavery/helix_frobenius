import RequestProject.DVPSeatRealPart
import RequestProject.DVPSeatRungOne

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.DVP

open CriticalLinePhasor.HilbertPolya

private def interiorAnchor (s : ℂ) : ℂ := -Complex.I * (s - 1 / 2)

private theorem chart_interiorAnchor (s : ℂ) :
    1 / 2 + Complex.I * interiorAnchor s = s := by
  unfold interiorAnchor
  linear_combination -(s - 1 / 2) * Complex.I_mul_I

private theorem interiorAnchor_re (s : ℂ) : (interiorAnchor s).re = s.im := by
  unfold interiorAnchor
  simp [Complex.mul_re, Complex.sub_im]

private theorem interiorAnchor_im (s : ℂ) :
    (interiorAnchor s).im = 1 / 2 - s.re := by
  unfold interiorAnchor
  simp [Complex.mul_im, Complex.sub_re]

private theorem reflected_xi_ne_zero_interior {s : ℂ}
    (hxi : ZD.riemannXi s ≠ 0) : ZD.riemannXi (1 - conj s) ≠ 0 := by
  rw [ZD.ZeroCount.riemannXi_one_sub,
    CriticalLinePhasor.ContourArgument.riemannXi_conj]
  simpa using hxi

/-- The high-ordinate interior rung transferred from seat energy to the
requested logarithmic-derivative sign. -/
theorem exists_xi_logDeriv_re_nonpos_interior_rung :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ,
      Real.exp 4 + 2 ≤ |s.im| →
      s.re < 1 / 2 →
      s.re ≤ c / Real.log (|s.im| + 1 / 2) →
      ZD.riemannXi s ≠ 0 →
      (logDeriv ZD.riemannXi s).re ≤ 0 := by
  obtain ⟨c, hc, hrung⟩ := seat_interior_rung_one'
  refine ⟨c, hc, fun s ht hs hdepth hxi => ?_⟩
  have hw : (1 / 2 + Complex.I * interiorAnchor s) ∉ ZD.NontrivialZeros := by
    rw [chart_interiorAnchor]
    exact fun hmem => hxi ((ZD.riemannXi_eq_zero_iff s).2 hmem)
  have hw' :
      (1 / 2 + Complex.I * (starRingEnd ℂ) (interiorAnchor s)) ∉
        ZD.NontrivialZeros := by
    rw [chart_two_eq, chart_interiorAnchor]
    exact fun hmem => reflected_xi_ne_zero_interior hxi
      ((ZD.riemannXi_eq_zero_iff _).2 hmem)
  have himpos : 0 < (interiorAnchor s).im := by
    rw [interiorAnchor_im]
    linarith
  have him : interiorAnchor s - (starRingEnd ℂ) (interiorAnchor s) ≠ 0 := by
    rw [Complex.sub_conj]
    apply mul_ne_zero
    · rw [ofReal_ne_zero]
      nlinarith
    · exact Complex.I_ne_zero
  have hseat := hrung (interiorAnchor s)
    (by simpa [interiorAnchor_re] using ht)
    (by
      rw [interiorAnchor_re]
      rw [abs_of_pos himpos, interiorAnchor_im]
      linarith)
    hw hw' him
  have hre := seat_energy_re_eq hw hw' him
  rw [chart_interiorAnchor] at hre
  rw [logDeriv_apply]
  have hq : 0 ≤ -(deriv ZD.riemannXi s / ZD.riemannXi s).re /
      (interiorAnchor s).im := by
    rw [← hre]
    exact hseat
  rcases (div_nonneg_iff.mp hq) with h | h <;> nlinarith

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.exists_xi_logDeriv_re_nonpos_interior_rung
