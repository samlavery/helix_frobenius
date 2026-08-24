import RequestProject.DVPSeatRealPart
import RequestProject.SeatScalarCriterion

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.DVP

open CriticalLinePhasor.HilbertPolya

/-- The requested logarithmic-derivative sign on the left of the critical line. -/
def XiLeftSign : Prop :=
  ∀ s : ℂ, s.re < 1 / 2 → ZD.riemannXi s ≠ 0 →
    (logDeriv ZD.riemannXi s).re ≤ 0

/-- Conjunct 2 in its scalar-seat form. -/
def SeatConjunctTwo : Prop :=
  ∀ w : ℂ,
    (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros →
    (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros →
    w - (starRingEnd ℂ) w ≠ 0 →
    0 ≤ (∑' rho : {rho : ℂ // rho ∈ ZD.NontrivialZeros},
      (ZD.xiOrderNat rho.val : ℂ) *
        ((spectralCoord rho.val - w)⁻¹ *
          (spectralCoord rho.val - (starRingEnd ℂ) w)⁻¹)).re

private def signAnchor (s : ℂ) : ℂ := -Complex.I * (s - 1 / 2)

private theorem chart_signAnchor (s : ℂ) :
    1 / 2 + Complex.I * signAnchor s = s := by
  unfold signAnchor
  linear_combination -(s - 1 / 2) * Complex.I_mul_I

private theorem signAnchor_im (s : ℂ) :
    (signAnchor s).im = 1 / 2 - s.re := by
  unfold signAnchor
  simp [Complex.mul_im, Complex.sub_re]

private theorem reflected_xi_ne_zero_sign {s : ℂ}
    (hxi : ZD.riemannXi s ≠ 0) : ZD.riemannXi (1 - conj s) ≠ 0 := by
  rw [ZD.ZeroCount.riemannXi_one_sub,
    CriticalLinePhasor.ContourArgument.riemannXi_conj]
  simpa using hxi

/-- The requested left-half-plane sign is exactly conjunct 2 at every admissible seat. -/
theorem xiLeftSign_iff_seatConjunctTwo : XiLeftSign ↔ SeatConjunctTwo := by
  constructor
  · intro hsign w hw hw' him
    let s : ℂ := 1 / 2 + Complex.I * w
    have hsre : s.re = 1 / 2 - w.im := by
      simp [s, Complex.mul_re]
      ring
    have hwimne : w.im ≠ 0 := by
      intro hzero
      apply him
      rw [Complex.sub_conj, hzero]
      norm_num
    have hxi : ZD.riemannXi s ≠ 0 := by
      intro hzero
      exact hw ((ZD.riemannXi_eq_zero_iff s).mp hzero)
    have hre := seat_energy_re_eq hw hw' him
    rcases lt_or_gt_of_ne hwimne with hneg | hpos
    · let s' : ℂ := 1 / 2 + Complex.I * (starRingEnd ℂ) w
      have hs're : s'.re = 1 / 2 + w.im := by
        simp [s', Complex.mul_re]
      have hxi' : ZD.riemannXi s' ≠ 0 := by
        intro hzero
        exact hw' ((ZD.riemannXi_eq_zero_iff s').mp hzero)
      have hsign' := hsign s' (by rw [hs're]; linarith) hxi'
      have href :
          (deriv ZD.riemannXi s' / ZD.riemannXi s').re =
            -(deriv ZD.riemannXi s / ZD.riemannXi s).re := by
        rw [show s' = 1 - conj s by
          simp only [s', s]
          exact chart_two_eq w]
        calc
          (deriv ZD.riemannXi (1 - conj s) /
              ZD.riemannXi (1 - conj s)).re =
              (-conj (deriv ZD.riemannXi s / ZD.riemannXi s)).re :=
            congrArg Complex.re (xi_logDeriv_one_sub_conj s)
          _ = -(deriv ZD.riemannXi s / ZD.riemannXi s).re := by
            rw [Complex.neg_re, Complex.conj_re]
      rw [logDeriv_apply, href] at hsign'
      rw [hre]
      exact div_nonneg_of_nonpos (by linarith) (le_of_lt hneg)
    · have hsigns := hsign s (by rw [hsre]; linarith) hxi
      rw [logDeriv_apply] at hsigns
      rw [hre]
      exact div_nonneg (neg_nonneg.mpr hsigns) (le_of_lt hpos)
  · intro hseat s hs hxi
    let w := signAnchor s
    have hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros := by
      rw [show 1 / 2 + Complex.I * w = s by exact chart_signAnchor s]
      exact fun hmem => hxi ((ZD.riemannXi_eq_zero_iff s).2 hmem)
    have hw' :
        (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros := by
      rw [chart_two_eq, show 1 / 2 + Complex.I * w = s by exact chart_signAnchor s]
      exact fun hmem => reflected_xi_ne_zero_sign hxi
        ((ZD.riemannXi_eq_zero_iff _).2 hmem)
    have hwim : 0 < w.im := by
      rw [show w.im = 1 / 2 - s.re by exact signAnchor_im s]
      linarith
    have him : w - (starRingEnd ℂ) w ≠ 0 := by
      rw [Complex.sub_conj]
      apply mul_ne_zero
      · rw [ofReal_ne_zero]
        nlinarith
      · exact Complex.I_ne_zero
    have henergy := hseat w hw hw' him
    have hre := seat_energy_re_eq hw hw' him
    rw [show 1 / 2 + Complex.I * w = s by exact chart_signAnchor s] at hre
    rw [logDeriv_apply]
    rw [hre] at henergy
    rcases (div_nonneg_iff.mp henergy) with h | h <;> nlinarith

/-- The sign target, scalar seat, and critical-line placement have identical content. -/
theorem xiLeftSign_iff_zeros_online :
    XiLeftSign ↔ ∀ rho ∈ ZD.NontrivialZeros, rho.re = 1 / 2 :=
  xiLeftSign_iff_seatConjunctTwo.trans
    CriticalLinePhasor.SeatScalar.seat_criterion_iff.symm

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.xiLeftSign_iff_seatConjunctTwo
#print axioms CriticalLinePhasor.DVP.xiLeftSign_iff_zeros_online
