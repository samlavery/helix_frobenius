import RequestProject.XiStructureFunction
import RequestProject.SeatScalarCriterion
import RequestProject.DVPSeatRungOne

/-!
# The Hermite–Biehler hypothesis IS the seat sign condition

`XiStructureFunction.rh_of_xiStructure_isHB` reduces RH to `IsHB xiStructure`, a
*modulus* inequality `‖E*z‖ < ‖E z‖` on the open upper half plane.  This file
converts that modulus inequality into a **real-part sign condition** and then
identifies it with the repository's already-compiled scalar seat.

The conversion is the polarization identity `‖a+b‖² − ‖a−b‖² = 4·Re(a·conj b)`
applied to `a = ξ(½−iz)`, `b = ξ′(½−iz)` — the two components read off by
`xiStructure_Estar`.  The chart `z ↦ ½ − iz` carries the open upper half plane
onto `{Re s > ½}`, so

  `IsHB xiStructure  ↔  ∀ Re s > ½ : 0 < Re[ ξ(s) · conj ξ′(s) ]`.

Off the zero set that is `Re[ξ′/ξ(s)] > 0`, and by `DVP.seat_energy_re_eq` the
seat energy at the anchor `w` with `½ + iw = s` is `−Re[ξ′/ξ(s)]/Im w` with
`Im w = ½ − Re s < 0`.  So the Hermite–Biehler hypothesis and the seat criterion
are the same object, and the seat's compiled partial positivity transports.

SCOPE.  Everything here is an identity or a transport of an already-compiled
inequality.  No new analytic input.
-/

open Complex ComplexConjugate
open CriticalLinePhasor.DeBranges

noncomputable section

namespace CriticalLinePhasor.XiStructure

open CriticalLinePhasor.DVP

/-! ## The polarization rewrite -/

/-- **Polarization.**  `‖a − b‖ < ‖a + b‖ ↔ 0 < Re(a · conj b)`. -/
theorem norm_sub_lt_norm_add_iff_re_pos (a b : ℂ) :
    ‖a - b‖ < ‖a + b‖ ↔ 0 < (a * (starRingEnd ℂ) b).re := by
  have hs : Complex.normSq (a - b) = ‖a - b‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have ha : Complex.normSq (a + b) = ‖a + b‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have hs' := Complex.normSq_sub a b
  have ha' := Complex.normSq_add a b
  rw [hs] at hs'
  rw [ha] at ha'
  constructor
  · intro h
    nlinarith [norm_nonneg (a - b), norm_nonneg (a + b)]
  · intro h
    nlinarith [norm_nonneg (a - b), norm_nonneg (a + b)]

/-- **Polarization, non-strict.**  `‖a − b‖ ≤ ‖a + b‖ ↔ 0 ≤ Re(a · conj b)`. -/
theorem norm_sub_le_norm_add_iff_re_nonneg (a b : ℂ) :
    ‖a - b‖ ≤ ‖a + b‖ ↔ 0 ≤ (a * (starRingEnd ℂ) b).re := by
  have hs : Complex.normSq (a - b) = ‖a - b‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have ha : Complex.normSq (a + b) = ‖a + b‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have hs' := Complex.normSq_sub a b
  have ha' := Complex.normSq_add a b
  rw [hs] at hs'
  rw [ha] at ha'
  constructor
  · intro h
    nlinarith [norm_nonneg (a - b), norm_nonneg (a + b)]
  · intro h
    nlinarith [norm_nonneg (a - b), norm_nonneg (a + b)]

/-! ## `IsHB` as a sign condition -/

/-- **The Hermite–Biehler hypothesis, in the spectral chart, as a sign condition.** -/
theorem isHB_xiStructure_iff_chart :
    IsHB xiStructure ↔
      ∀ z : ℂ, 0 < z.im →
        0 < (ZD.riemannXi (1 / 2 - Complex.I * z) *
              (starRingEnd ℂ) (deriv ZD.riemannXi (1 / 2 - Complex.I * z))).re := by
  constructor
  · intro h z hz
    have hz' := h z hz
    rw [xiStructure_Estar] at hz'
    exact (norm_sub_lt_norm_add_iff_re_pos _ _).mp hz'
  · intro h z hz
    rw [xiStructure_Estar]
    exact (norm_sub_lt_norm_add_iff_re_pos _ _).mpr (h z hz)

/-- The chart real part: `Re(½ − i z) = ½ + Im z`. -/
theorem chart_re (z : ℂ) : ((1 : ℂ) / 2 - Complex.I * z).re = 1 / 2 + z.im := by
  simp [Complex.sub_re, Complex.mul_re]

/-- **`IsHB` on the half plane `Re s > ½`.**  The chart `z ↦ ½ − i z` is a bijection
of the open upper half plane onto `{Re s > ½}`, so the Hermite–Biehler hypothesis
is exactly the sign condition `Re[ξ · conj ξ′] > 0` there. -/
theorem isHB_xiStructure_iff_halfplane :
    IsHB xiStructure ↔
      ∀ s : ℂ, 1 / 2 < s.re →
        0 < (ZD.riemannXi s * (starRingEnd ℂ) (deriv ZD.riemannXi s)).re := by
  rw [isHB_xiStructure_iff_chart]
  constructor
  · intro h s hs
    have him : 0 < (Complex.I * (s - 1 / 2)).im := by
      rw [chart_im]; linarith
    have := h (Complex.I * (s - 1 / 2)) him
    rwa [chart_at_zero] at this
  · intro h z hz
    exact h _ (by rw [chart_re]; linarith)

/-! ## The logarithmic-derivative form, and the seat -/

/-- `Re[ξ′/ξ]` and `Re[ξ · conj ξ′]` have the same sign: they differ by `‖ξ‖² > 0`. -/
theorem re_logDeriv_mul_normSq (s : ℂ) :
    (ZD.riemannXi s * (starRingEnd ℂ) (deriv ZD.riemannXi s)).re
      = (deriv ZD.riemannXi s / ZD.riemannXi s).re * Complex.normSq (ZD.riemannXi s) := by
  by_cases h : ZD.riemannXi s = 0
  · simp [h]
  · rw [Complex.div_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have hn : Complex.normSq (ZD.riemannXi s) ≠ 0 := by
      simpa [Complex.normSq_eq_zero] using h
    field_simp
    ring

/-- **The sign condition in logarithmic-derivative form**, off the zero set. -/
theorem re_mul_conj_pos_iff_re_logDeriv_pos {s : ℂ} (h : ZD.riemannXi s ≠ 0) :
    0 < (ZD.riemannXi s * (starRingEnd ℂ) (deriv ZD.riemannXi s)).re
      ↔ 0 < (deriv ZD.riemannXi s / ZD.riemannXi s).re := by
  have hn : 0 < Complex.normSq (ZD.riemannXi s) := by
    simpa [Complex.normSq_pos] using h
  rw [re_logDeriv_mul_normSq]
  constructor
  · intro hh; nlinarith
  · intro hh; nlinarith

/-- **The anchor dictionary.**  The seat anchor `w = I·(s − ½)` has `½ + i w = s`
and `Im w = Re s − ½`.  (Note the seat chart is `s = ½ + i w`, so `Im w` is the
*negative* of the abscissa offset used in the `xiStructure` chart.) -/
theorem seat_anchor_chart (s : ℂ) :
    (1 : ℂ) / 2 + Complex.I * (-(Complex.I * (s - 1 / 2))) = s := by
  ring_nf
  rw [Complex.I_sq]
  ring

theorem seat_anchor_im (s : ℂ) : (-(Complex.I * (s - 1 / 2))).im = 1 / 2 - s.re := by
  simp [Complex.mul_im, Complex.sub_re]

end CriticalLinePhasor.XiStructure

section AxiomAudit
#print axioms CriticalLinePhasor.XiStructure.norm_sub_lt_norm_add_iff_re_pos
#print axioms CriticalLinePhasor.XiStructure.norm_sub_le_norm_add_iff_re_nonneg
#print axioms CriticalLinePhasor.XiStructure.isHB_xiStructure_iff_chart
#print axioms CriticalLinePhasor.XiStructure.isHB_xiStructure_iff_halfplane
#print axioms CriticalLinePhasor.XiStructure.re_logDeriv_mul_normSq
#print axioms CriticalLinePhasor.XiStructure.re_mul_conj_pos_iff_re_logDeriv_pos
#print axioms CriticalLinePhasor.XiStructure.seat_anchor_chart
end AxiomAudit

/-! ## Transport: the compiled seat positivity becomes Hermite–Biehler domination

The two charts differ by a sign: the `xiStructure` chart point is `½ − i z` and the
seat chart point is `½ + i w`, so **`w = −z`**.  Under that dictionary every compiled
seat-positivity theorem becomes an unconditional *non-strict* Hermite–Biehler
domination `‖E* z‖ ≤ ‖E z‖` on the corresponding region of the upper half plane.
-/

namespace CriticalLinePhasor.XiStructure

open CriticalLinePhasor.DVP CriticalLinePhasor.SeatScalar
open CriticalLinePhasor.HilbertPolya

/-- The chart dictionary: the seat anchor of `z` is `w = −z`. -/
theorem seat_anchor_eq_neg (z : ℂ) :
    (1 : ℂ) / 2 + Complex.I * (-z) = 1 / 2 - Complex.I * z := by ring

/-- At a chart zero of `ξ` the domination is automatic: `E = P`, `E* = −P`. -/
theorem dominates_of_chart_zero {z : ℂ}
    (h : ZD.riemannXi (1 / 2 - Complex.I * z) = 0) :
    ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖ := by
  rw [xiStructure_Estar]
  refine (norm_sub_le_norm_add_iff_re_nonneg _ _).mpr ?_
  rw [h]
  simp

/-- Membership in the zero set is stable under the FE-conjugate chart reflection. -/
theorem chart_conj_mem_iff (w : ℂ) :
    (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∈ ZD.NontrivialZeros
      ↔ (1 / 2 + Complex.I * w) ∈ ZD.NontrivialZeros := by
  constructor
  · intro h
    rw [chart_two_eq w] at h
    have h3 : CriticalLinePhasor.FoliatedPolarization.feReflect
        (1 / 2 + Complex.I * w) ∈ ZD.NontrivialZeros := h
    have h4 := CriticalLinePhasor.FoliatedGlobalPolarization.feReflect_mem h3
    rwa [CriticalLinePhasor.FoliatedPolarization.feReflect_involutive] at h4
  · intro h
    rw [chart_two_eq w]
    exact CriticalLinePhasor.FoliatedGlobalPolarization.feReflect_mem h

/-- **THE TRANSPORT.**  Seat positivity at the anchor `w = −z` yields Hermite–Biehler
domination at `z`.  Unconditional in itself: only the seat hypothesis is consumed. -/
theorem dominates_of_seat_nonneg {z : ℂ} (hz : 0 < z.im)
    (hseat : ((1 / 2 + Complex.I * (-z)) ∉ ZD.NontrivialZeros) →
      ((1 / 2 + Complex.I * (starRingEnd ℂ) (-z)) ∉ ZD.NontrivialZeros) →
      ((-z) - (starRingEnd ℂ) (-z) ≠ 0) →
      0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) *
            ((spectralCoord ρ.val - (-z))⁻¹ *
              (spectralCoord ρ.val - (starRingEnd ℂ) (-z))⁻¹)).re) :
    ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖ := by
  by_cases hxi : ZD.riemannXi (1 / 2 - Complex.I * z) = 0
  · exact dominates_of_chart_zero hxi
  have hchart : (1 : ℂ) / 2 + Complex.I * (-z) = 1 / 2 - Complex.I * z :=
    seat_anchor_eq_neg z
  have hw : (1 / 2 + Complex.I * (-z)) ∉ ZD.NontrivialZeros := by
    intro hmem
    exact hxi (by
      rw [← hchart]
      exact ZD.ZeroCount.riemannXi_zero_of_mem_NontrivialZeros _ hmem)
  have hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) (-z)) ∉ ZD.NontrivialZeros := by
    intro hmem
    exact hw ((chart_conj_mem_iff (-z)).mp hmem)
  have him : (-z) - (starRingEnd ℂ) (-z) ≠ 0 := by
    intro h
    have h2 : ((-z) - (starRingEnd ℂ) (-z)).im = 0 := by rw [h]; simp
    rw [Complex.sub_im, Complex.conj_im, Complex.neg_im] at h2
    linarith
  have hnn := hseat hw hw' him
  have hid := seat_energy_re_eq hw hw' him
  rw [hid, hchart] at hnn
  -- `hnn : 0 ≤ -(ξ'/ξ (½ − iz)).re / (-z).im`
  rw [Complex.neg_im] at hnn
  set A : ℝ := (deriv ZD.riemannXi (1 / 2 - Complex.I * z)
      / ZD.riemannXi (1 / 2 - Complex.I * z)).re with hA
  have hApos : 0 ≤ A := by
    by_contra hcon
    push Not at hcon
    have hneg : -A / -z.im < 0 :=
      div_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  rw [xiStructure_Estar]
  refine (norm_sub_le_norm_add_iff_re_nonneg _ _).mpr ?_
  rw [re_logDeriv_mul_normSq, ← hA]
  exact mul_nonneg hApos (Complex.normSq_nonneg _)

/-- **Unconditional Hermite–Biehler domination outside the critical strip.**  For every
`z` with `Im z > ½` — chart abscissa `Re(½ − iz) > 1` — the helix dominates the
anti-helix.  Transport of `seat_energy_nonneg_of_outside_strip`; no hypothesis. -/
theorem xiStructure_dominates_of_deep {z : ℂ} (hz : 1 / 2 < z.im) :
    ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖ := by
  refine dominates_of_seat_nonneg (by linarith) (fun _ _ _ => ?_)
  refine seat_energy_nonneg_of_outside_strip ?_
  rw [Complex.neg_im, abs_neg, abs_of_pos (by linarith : (0:ℝ) < z.im)]
  exact hz

end CriticalLinePhasor.XiStructure

section AxiomAudit2
#print axioms CriticalLinePhasor.XiStructure.chart_conj_mem_iff
#print axioms CriticalLinePhasor.XiStructure.dominates_of_seat_nonneg
#print axioms CriticalLinePhasor.XiStructure.xiStructure_dominates_of_deep
end AxiomAudit2

/-! ## The interior rung, and the non-strict criterion -/

namespace CriticalLinePhasor.XiStructure

open CriticalLinePhasor.DVP CriticalLinePhasor.SeatScalar
open CriticalLinePhasor.HilbertPolya

/-- The seat energy is invariant under conjugating the anchor. -/
theorem seat_energy_conj_eq (w : ℂ) :
    (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) ((starRingEnd ℂ) w))⁻¹))
      = ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹) := by
  refine tsum_congr fun ρ => ?_
  rw [Complex.conj_conj]
  ring

/-- **UNCONDITIONAL HERMITE–BIEHLER DOMINATION INSIDE THE STRIP.**  Transport of the
compiled interior rung `DVP.seat_interior_rung_one'` (de la Vallée Poussin region at
exponent one) through the chart dictionary `w = −z`: there is `c > 0` such that the
helix dominates the anti-helix at every `z` of height `|Re z| ≥ e⁴ + 2` whose depth is
at least `½ − c / log(|Re z| + ½)`.  No hypothesis of any kind. -/
theorem xiStructure_dominates_interior_rung :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, 0 < z.im →
      Real.exp 4 + 2 ≤ |z.re| →
      1 / 2 - c / Real.log (|z.re| + 1 / 2) ≤ z.im →
      ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖ := by
  obtain ⟨c, hcpos, hrung⟩ := seat_interior_rung_one'
  refine ⟨c, hcpos, fun z hz hre hdep => ?_⟩
  refine dominates_of_seat_nonneg hz (fun hw hw' him => ?_)
  refine hrung (-z) ?_ ?_ hw hw' him
  · rwa [Complex.neg_re, abs_neg]
  · rw [Complex.neg_im, abs_neg, abs_of_pos hz, Complex.neg_re, abs_neg]
    exact hdep

/-- **RH gives the non-strict domination.**  Transport of `seat_energy_nonneg_of_online`. -/
theorem xiStructure_dominates_of_rh (hon : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2)
    {z : ℂ} (hz : 0 < z.im) :
    ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖ :=
  dominates_of_seat_nonneg hz (fun hw hw' him =>
    seat_energy_nonneg_of_online hon hw hw' him)

/-- **THE NON-STRICT CRITERION, AS AN IFF.**  The Riemann Hypothesis is *equivalent* to
the **non-strict** Hermite–Biehler domination `‖E* z‖ ≤ ‖E z‖` of the Lagarias structure
function on the open upper half plane.

This strictly improves `rh_of_xiStructure_isHB`, which consumes the strict hypothesis
`IsHB xiStructure`: the strict inequality is not needed.  The converse direction runs
through `SeatScalar.exists_seat_energy_neg`; note that the strictly negative seat value
already forces `ξ ≠ 0` at the anchor, so no separate non-vanishing input is used. -/
theorem rh_iff_xiStructure_dominates :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2)
      ↔ ∀ z : ℂ, 0 < z.im → ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖ := by
  constructor
  · intro hon z hz
    exact xiStructure_dominates_of_rh hon hz
  · intro hdom ρ hρ
    by_contra hne
    -- pass to the side of the critical line with `Re > ½`
    obtain ⟨ρ₀, hρ₀mem, hρ₀re⟩ :
        ∃ ρ₀ : ℂ, ρ₀ ∈ ZD.NontrivialZeros ∧ 1 / 2 < ρ₀.re := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine ⟨CriticalLinePhasor.FoliatedPolarization.feReflect ρ,
          CriticalLinePhasor.FoliatedGlobalPolarization.feReflect_mem hρ, ?_⟩
        have : (CriticalLinePhasor.FoliatedPolarization.feReflect ρ).re = 1 - ρ.re := by
          simp [CriticalLinePhasor.FoliatedPolarization.feReflect,
            Complex.sub_re, Complex.conj_re]
        rw [this]; linarith
      · exact ⟨ρ, hρ, hgt⟩
    obtain ⟨w, -, -, h1, h2, h3, h4⟩ := exists_seat_energy_neg hρ₀mem hρ₀re 1 one_pos
    -- choose the anchor sign so that the chart point has `Re > ½`
    obtain ⟨v, hv1, hv2, hv3, hv4, hvim⟩ :
        ∃ v : ℂ, ((1 / 2 + Complex.I * v) ∉ ZD.NontrivialZeros) ∧
          ((1 / 2 + Complex.I * (starRingEnd ℂ) v) ∉ ZD.NontrivialZeros) ∧
          (v - (starRingEnd ℂ) v ≠ 0) ∧
          (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
              (ZD.xiOrderNat ρ.val : ℂ) *
                ((spectralCoord ρ.val - v)⁻¹ *
                  (spectralCoord ρ.val - (starRingEnd ℂ) v)⁻¹)).re < 0 ∧ v.im < 0 := by
      have hwim : w.im ≠ 0 := by
        intro h0
        exact h3 (by rw [Complex.ext_iff]; simp [Complex.conj_re, Complex.conj_im, h0])
      rcases lt_or_gt_of_ne hwim with hlt | hgt
      · exact ⟨w, h1, h2, h3, h4, hlt⟩
      · refine ⟨(starRingEnd ℂ) w, h2, ?_, ?_, ?_, ?_⟩
        · rwa [Complex.conj_conj]
        · rw [Complex.conj_conj]
          intro h
          apply h3
          have hswap : w - (starRingEnd ℂ) w = -((starRingEnd ℂ) w - w) := by ring
          rw [hswap, h, neg_zero]
        · rw [seat_energy_conj_eq]; exact h4
        · rw [Complex.conj_im]; linarith
    -- read the seat value as `Re[ξ′/ξ]` and contradict the domination at `z = −v`
    have hid := seat_energy_re_eq hv1 hv2 hv3
    rw [hid] at hv4
    set s : ℂ := 1 / 2 + Complex.I * v with hs
    set A : ℝ := (deriv ZD.riemannXi s / ZD.riemannXi s).re with hA
    have hAneg : A < 0 := by
      by_contra hcon
      push Not at hcon
      have heq : -A / v.im = A / (-v.im) := by ring
      have : 0 ≤ -A / v.im := by rw [heq]; exact div_nonneg hcon (by linarith)
      linarith
    have hxi : ZD.riemannXi s ≠ 0 := by
      intro h0
      rw [hA, h0] at hAneg
      simp at hAneg
    have hz : (0 : ℝ) < (-v).im := by rw [Complex.neg_im]; linarith
    have hchart : (1 : ℂ) / 2 - Complex.I * (-v) = s := by rw [hs]; ring
    have hdom0 := hdom (-v) hz
    rw [xiStructure_Estar] at hdom0
    have hdom' : 0 ≤ (ZD.riemannXi (1 / 2 - Complex.I * (-v)) *
        (starRingEnd ℂ) (deriv ZD.riemannXi (1 / 2 - Complex.I * (-v)))).re :=
      (norm_sub_le_norm_add_iff_re_nonneg _ _).mp hdom0
    rw [hchart, re_logDeriv_mul_normSq, ← hA] at hdom'
    have hns : 0 < Complex.normSq (ZD.riemannXi s) := by
      simpa [Complex.normSq_pos] using hxi
    nlinarith

end CriticalLinePhasor.XiStructure

section AxiomAudit3
#print axioms CriticalLinePhasor.XiStructure.seat_energy_conj_eq
#print axioms CriticalLinePhasor.XiStructure.xiStructure_dominates_interior_rung
#print axioms CriticalLinePhasor.XiStructure.xiStructure_dominates_of_rh
#print axioms CriticalLinePhasor.XiStructure.rh_iff_xiStructure_dominates
end AxiomAudit3
