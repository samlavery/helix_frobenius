import RequestProject.SeatScalarCriterion
import RequestProject.DVPSeatRealPart
import RequestProject.XiHelixChart

/-!
# Road B wiring: the chart numerator sign on the strip implies RH

The Road B chain (theta representation, batch-27 O-lane) computes the sign of the chart
numerator `Im[Ξ′(z) · conj Ξ(z)]` for `z` in the strip `0 < Im z < 5/2`, where
`Ξ(z) = riemannXi (1/2 − i z)` is the Xi chart readout.  The seat criterion
(`seat_criterion_iff`) consumes seat-energy nonnegativity at every admissible anchor.
This file compiles the missing wiring:

* the **numerator → quotient bridge**: `(w/v).im = (w · conj v).im / normSq v`, so the
  numerator sign transfers to the log-derivative sign unconditionally (Lean's `x/0 = 0`
  removes the nonvanishing side condition);
* the **rotation identity**: `Im[(xiChart)′/xiChart] = −Re[ξ′/ξ]` across the chart;
* the **strip reduction**: anchors with `|Im w| > 1/2` are compiled unconditional
  (`seat_energy_nonneg_of_outside_strip`), and anchors with `|Im w| ≤ 1/2` correspond
  to chart points with `0 < |Im z| ≤ 1/2` — inside the strip Road B covers.

Main theorem: `rh_of_chart_numerator_im_nonpos` — the numerator sign on
`0 < Im z ≤ 1/2` alone implies every nontrivial zero is on the critical line.
-/

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.XiSeatWiring

open CriticalLinePhasor.HilbertPolya
open CriticalLinePhasor.XiHelixChart

/-- The Xi chart readout: the entire function whose numerator sign Road B computes. -/
def xiChart (z : ℂ) : ℂ := ZD.riemannXi (sOfZ z)

/-! ## 1. The numerator → quotient bridge -/

/-- The imaginary part of a quotient is the numerator pairing over the squared norm.
Holds with no nonvanishing hypothesis: at `v = 0` both sides are `0`. -/
theorem div_im_eq_mul_conj_im_div (w v : ℂ) :
    (w / v).im = (w * (starRingEnd ℂ) v).im / Complex.normSq v := by
  rw [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **The bridge**: numerator sign transfers to quotient sign, unconditionally. -/
theorem div_im_nonpos_of_mul_conj_im_nonpos {w v : ℂ}
    (h : (w * (starRingEnd ℂ) v).im ≤ 0) : (w / v).im ≤ 0 := by
  rw [div_im_eq_mul_conj_im_div]
  exact div_nonpos_of_nonpos_of_nonneg h (Complex.normSq_nonneg v)

/-! ## 2. The chart derivative and the rotation identity -/

theorem sOfZ_hasDerivAt (z : ℂ) : HasDerivAt sOfZ (-Complex.I) z := by
  have h : HasDerivAt (fun x : ℂ => 1 / 2 - Complex.I * x) (0 - Complex.I * 1) z :=
    (hasDerivAt_const z ((1 : ℂ) / 2)).sub ((hasDerivAt_id z).const_mul Complex.I)
  have h2 : (0 : ℂ) - Complex.I * 1 = -Complex.I := by ring
  rw [h2] at h
  unfold sOfZ
  exact h

theorem xiChart_hasDerivAt (z : ℂ) :
    HasDerivAt xiChart (-Complex.I * deriv ZD.riemannXi (sOfZ z)) z := by
  have h2 : HasDerivAt ZD.riemannXi (deriv ZD.riemannXi (sOfZ z)) (sOfZ z) :=
    (ZD.riemannXi_differentiable (sOfZ z)).hasDerivAt
  have h := h2.comp z (sOfZ_hasDerivAt z)
  have hmul : deriv ZD.riemannXi (sOfZ z) * -Complex.I
      = -Complex.I * deriv ZD.riemannXi (sOfZ z) := mul_comm _ _
  rw [hmul] at h
  unfold xiChart
  exact h

theorem xiChart_deriv (z : ℂ) :
    deriv xiChart z = -Complex.I * deriv ZD.riemannXi (sOfZ z) :=
  (xiChart_hasDerivAt z).deriv

/-- **The rotation identity**: the chart's imaginary-part functional is minus the native
real-part functional. -/
theorem chart_logDeriv_im (z : ℂ) :
    (deriv xiChart z / xiChart z).im
      = -(deriv ZD.riemannXi (sOfZ z) / ZD.riemannXi (sOfZ z)).re := by
  rw [xiChart_deriv]
  show (-Complex.I * deriv ZD.riemannXi (sOfZ z) / ZD.riemannXi (sOfZ z)).im = _
  rw [mul_div_assoc]
  simp [Complex.mul_im]

/-- Numerator sign at `z` gives the native log-derivative real-part sign at `sOfZ z`. -/
theorem xi_logDeriv_re_nonneg_of_numerator {z : ℂ}
    (h : (deriv xiChart z * (starRingEnd ℂ) (xiChart z)).im ≤ 0) :
    0 ≤ (deriv ZD.riemannXi (sOfZ z) / ZD.riemannXi (sOfZ z)).re := by
  have h1 : (deriv xiChart z / xiChart z).im ≤ 0 :=
    div_im_nonpos_of_mul_conj_im_nonpos h
  rw [chart_logDeriv_im] at h1
  linarith

/-! ## 3. Seat symmetry under anchor conjugation -/

/-- The seat energy is invariant under `w ↦ conj w`: the two resolvent factors swap. -/
theorem seat_energy_conj (w : ℂ) :
    (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) ((starRingEnd ℂ) w))⁻¹))
      = ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) *
            ((spectralCoord ρ.val - w)⁻¹ *
              (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹) := by
  simp only [Complex.conj_conj]
  exact tsum_congr fun ρ => by ring

/-! ## 4. The strip reduction -/

/-- Seat nonnegativity at a strip anchor with `Im w < 0`, from the numerator sign at the
chart point `z = −w` (which has `0 < Im z ≤ 1/2`). -/
theorem seat_nonneg_of_neg_im {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hneg : w.im < 0) (hge : -(1 / 2) ≤ w.im)
    (h : ∀ z : ℂ, 0 < z.im → z.im ≤ 1 / 2 →
      (deriv xiChart z * (starRingEnd ℂ) (xiChart z)).im ≤ 0) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  have hz : 0 < (-w).im := by simp only [Complex.neg_im]; linarith
  have hz2 : (-w).im ≤ 1 / 2 := by simp only [Complex.neg_im]; linarith
  have hkey := xi_logDeriv_re_nonneg_of_numerator (h (-w) hz hz2)
  have hs : sOfZ (-w) = 1 / 2 + Complex.I * w := by unfold sOfZ; ring
  rw [hs] at hkey
  rw [CriticalLinePhasor.DVP.seat_energy_re_eq hw hw' him]
  exact div_nonneg_iff.mpr (Or.inr ⟨neg_nonpos.mpr hkey, hneg.le⟩)

/-- **THE ROAD B WIRING.**  If the chart numerator `Im[Ξ′(z)·conj Ξ(z)]` is nonpositive on
the strip `0 < Im z ≤ 1/2`, every nontrivial zero lies on the critical line.

The hypothesis is exactly what the batch-27 theta representation computes
(`numerator_folded` holds on `|Im z| < 5/2 ⊃ (0, 1/2]`), so this theorem is the point
where Road B meets the compiled seat criterion. -/
theorem rh_of_chart_numerator_im_nonpos
    (h : ∀ z : ℂ, 0 < z.im → z.im ≤ 1 / 2 →
      (deriv xiChart z * (starRingEnd ℂ) (xiChart z)).im ≤ 0) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  rw [CriticalLinePhasor.SeatScalar.seat_criterion_iff]
  intro w hw hw' him
  by_cases hstrip : |w.im| ≤ 1 / 2
  · -- inside the strip: |Im w| ≤ 1/2, Im w ≠ 0 by admissibility
    have hne : w ≠ (starRingEnd ℂ) w := sub_ne_zero.mp him
    have himne : w.im ≠ 0 := by
      intro h0
      apply hne
      apply Complex.ext
      · simp
      · simp [Complex.conj_im, h0]
    rcases lt_or_gt_of_ne himne with hneg | hpos
    · -- Im w < 0: direct
      exact seat_nonneg_of_neg_im hw hw' him hneg
        (by have := abs_le.mp hstrip; linarith) h
    · -- Im w > 0: route through the conjugate anchor
      have hw2 : (1 / 2 + Complex.I * (starRingEnd ℂ) ((starRingEnd ℂ) w))
          ∉ ZD.NontrivialZeros := by
        rw [Complex.conj_conj]; exact hw
      have him2 : (starRingEnd ℂ) w - (starRingEnd ℂ) ((starRingEnd ℂ) w) ≠ 0 := by
        rw [Complex.conj_conj]
        exact sub_ne_zero.mpr (Ne.symm hne)
      have hneg2 : ((starRingEnd ℂ) w).im < 0 := by
        simp only [Complex.conj_im]; linarith
      have hge2 : -(1 / 2) ≤ ((starRingEnd ℂ) w).im := by
        simp only [Complex.conj_im]
        have := abs_le.mp hstrip; linarith
      have hconj := seat_nonneg_of_neg_im hw' hw2 him2 hneg2 hge2 h
      rw [seat_energy_conj] at hconj
      exact hconj
  · -- outside the strip: compiled unconditional positivity
    exact CriticalLinePhasor.SeatScalar.seat_energy_nonneg_of_outside_strip
      (not_le.mp hstrip)

end CriticalLinePhasor.XiSeatWiring

section AxiomAudit
#print axioms CriticalLinePhasor.XiSeatWiring.div_im_eq_mul_conj_im_div
#print axioms CriticalLinePhasor.XiSeatWiring.div_im_nonpos_of_mul_conj_im_nonpos
#print axioms CriticalLinePhasor.XiSeatWiring.xiChart_deriv
#print axioms CriticalLinePhasor.XiSeatWiring.chart_logDeriv_im
#print axioms CriticalLinePhasor.XiSeatWiring.xi_logDeriv_re_nonneg_of_numerator
#print axioms CriticalLinePhasor.XiSeatWiring.seat_energy_conj
#print axioms CriticalLinePhasor.XiSeatWiring.seat_nonneg_of_neg_im
#print axioms CriticalLinePhasor.XiSeatWiring.rh_of_chart_numerator_im_nonpos
end AxiomAudit
