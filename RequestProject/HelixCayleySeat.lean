import RequestProject.HelixPencilDegreeOne
import RequestProject.GeometricReadout

/-!
# The seat sum read through the Cayley/Möbius projection (ledger 1331)

Sam (2026-10-14): "leverage cayley/mobius projection". The 3D → 2D step of the descent drops the RADIUS by a
Möbius/Cayley map onto the unit circle; the chart's abscissa is the radial coordinate of that disc, and the axis
`Re s = ½` is the circle itself. Compiled here, with no verified window:

* `cayleyPoint s = (s + ½)/(s − 3/2)` is the house Cayley chart `Readout.cayley` applied to the spectral coordinate
  `−i(s − ½)` (`cayleyPoint_eq`); it sends the axis to the unit circle and nothing else there
  (`cayleyPoint_norm_eq_one_iff`): the radius of the Cayley image IS the drift.
* `cayleyAt s ρ = (ρ − s)/(ρ − (1 − s̄))` is the Möbius map of the strip's reflection about the axis, anchored at `s`:
  unimodular exactly on the axis (`cayleyAt_norm_eq_one_iff`).
* `seatTerm_eq_cayley`: every zero's seat term (1329) is `−m_ρ · cayleyAt s ρ / (s − ρ)²` — the anchored Cayley
  factor of the zero times the squared resolvent. On the axis the Cayley factor is the phase `−(s−ρ)/conj(s−ρ)` and
  cancels the resolvent's phase exactly: `seatTerm_on_axis : seatTerm s ρ = m_ρ / |s − ρ|²`, real and positive.
* `riemannHypothesis_of_cayley_seat_nonneg`: the leaf in Cayley words — if, from every anchor of the open right
  half-strip, the zeros' anchored Cayley factors weighted by the squared resolvents have nonnegative real sum, every
  zero is on the axis.

What the projection gives and does not give. It gives the exact dictionary: drift = radius in the Cayley disc; the
seat sign = "the Cayley phases of the zeros cancel the resolvent phases"; on the circle this is an identity. It does
not give the sign off the circle: that is the leaf (1326/1328/1329), unchanged. No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixCayleySeat

open CriticalLinePhasor.HilbertPolya CriticalLinePhasor.HelixPencilDegreeOne CriticalLinePhasor.HelixTiltMass

/-- The Cayley image of a chart point: the house chart on the spectral coordinate. -/
def cayleyPoint (s : ℂ) : ℂ := (s + 1 / 2) / (s - 3 / 2)

theorem cayleyPoint_eq (s : ℂ) (hs : s ≠ 3 / 2) :
    Readout.cayley (spectralCoord s) = cayleyPoint s := by
  unfold Readout.cayley cayleyPoint spectralCoord
  have h1 : -Complex.I * (s - 1 / 2) + Complex.I = -Complex.I * (s - 3 / 2) := by ring
  have h2 : -Complex.I * (s - 1 / 2) - Complex.I = -Complex.I * (s + 1 / 2) := by ring
  rw [h1, h2]
  have hne : s - 3 / 2 ≠ 0 := sub_ne_zero.mpr hs
  rw [mul_div_mul_left _ _ (neg_ne_zero.mpr Complex.I_ne_zero)]

/-- Squared norms of `s + ½` and `s − 3/2`. -/
theorem normSq_add_half (s : ℂ) : Complex.normSq (s + 1 / 2) = (s.re + 1 / 2) ^ 2 + s.im ^ 2 := by
  rw [Complex.normSq_apply]; simp [Complex.add_re, Complex.add_im]; ring

theorem normSq_sub_threeHalf (s : ℂ) : Complex.normSq (s - 3 / 2) = (s.re - 3 / 2) ^ 2 + s.im ^ 2 := by
  rw [Complex.normSq_apply]; simp [Complex.sub_re, Complex.sub_im]; ring

/-- **The axis is the unit circle of the Cayley chart, and only the axis.** -/
theorem cayleyPoint_norm_eq_one_iff {s : ℂ} (hs : s ≠ 3 / 2) : ‖cayleyPoint s‖ = 1 ↔ s.re = 1 / 2 := by
  unfold cayleyPoint
  have hne : s - 3 / 2 ≠ 0 := sub_ne_zero.mpr hs
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hne)]
  constructor
  · intro h
    have h2 : Complex.normSq (s + 1 / 2) = Complex.normSq (s - 3 / 2) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h]
    rw [normSq_add_half, normSq_sub_threeHalf] at h2
    nlinarith
  · intro h
    have h2 : Complex.normSq (s + 1 / 2) = Complex.normSq (s - 3 / 2) := by
      rw [normSq_add_half, normSq_sub_threeHalf, h]; ring
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- **The drift is the radius**: the Cayley image lies outside the unit circle exactly for `Re s > ½`. -/
theorem cayleyPoint_norm_gt_one_iff {s : ℂ} (hs : s ≠ 3 / 2) : 1 < ‖cayleyPoint s‖ ↔ 1 / 2 < s.re := by
  unfold cayleyPoint
  have hne : s - 3 / 2 ≠ 0 := sub_ne_zero.mpr hs
  have hpos : 0 < ‖s - 3 / 2‖ := norm_pos_iff.mpr hne
  rw [norm_div, one_lt_div hpos]
  constructor
  · intro h
    have h2 : Complex.normSq (s - 3 / 2) < Complex.normSq (s + 1 / 2) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mpr h
    rw [normSq_add_half, normSq_sub_threeHalf] at h2
    nlinarith
  · intro h
    have h2 : Complex.normSq (s - 3 / 2) < Complex.normSq (s + 1 / 2) := by
      rw [normSq_add_half, normSq_sub_threeHalf]; nlinarith
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-! ## The anchored Cayley factor of a zero -/

/-- The Möbius map of the reflection about the axis, anchored at `s`, evaluated at `ρ`. -/
def cayleyAt (s ρ : ℂ) : ℂ := (ρ - s) / (ρ - (1 - conj s))

theorem normSq_sub (ρ s : ℂ) : Complex.normSq (ρ - s) = (ρ.re - s.re) ^ 2 + (ρ.im - s.im) ^ 2 := by
  rw [Complex.normSq_apply]; simp [Complex.sub_re, Complex.sub_im]; ring

theorem normSq_sub_mirror (ρ s : ℂ) :
    Complex.normSq (ρ - (1 - conj s)) = (ρ.re + s.re - 1) ^ 2 + (ρ.im - s.im) ^ 2 := by
  rw [Complex.normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **Unimodular exactly on the axis**: for an anchor off the axis, `|cayleyAt s ρ| = 1 ↔ Re ρ = ½`. -/
theorem cayleyAt_norm_eq_one_iff {s ρ : ℂ} (hs : s.re ≠ 1 / 2) (hρ : ρ ≠ 1 - conj s) :
    ‖cayleyAt s ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  unfold cayleyAt
  have hne : ρ - (1 - conj s) ≠ 0 := sub_ne_zero.mpr hρ
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hne)]
  constructor
  · intro h
    have h2 : Complex.normSq (ρ - s) = Complex.normSq (ρ - (1 - conj s)) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h]
    rw [normSq_sub, normSq_sub_mirror] at h2
    have h3 : (ρ.re - s.re) ^ 2 = (ρ.re + s.re - 1) ^ 2 := by linarith
    have h4 : (ρ.re - s.re - (ρ.re + s.re - 1)) * (ρ.re - s.re + (ρ.re + s.re - 1)) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exfalso; apply hs; linarith
    · linarith
  · intro h
    have h2 : Complex.normSq (ρ - s) = Complex.normSq (ρ - (1 - conj s)) := by
      rw [normSq_sub, normSq_sub_mirror, h]; ring
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- **The seat term is the anchored Cayley factor times the squared resolvent.** -/
theorem seatTerm_eq_cayley {s : ℂ} (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) (h1 : s ≠ ρ.val) :
    seatTerm s ρ = -(ZD.xiOrderNat ρ.val : ℂ) * cayleyAt s ρ.val / (s - ρ.val) ^ 2 := by
  unfold seatTerm cayleyAt
  rw [← mul_inv, seat_denominator]
  have ha : s - ρ.val ≠ 0 := sub_ne_zero.mpr h1
  by_cases h2 : ρ.val = 1 - conj s
  · -- the mirror point: both sides vanish (`x⁻¹ = 0` at `x = 0`)
    have hb : ρ.val + conj s - 1 = 0 := by linear_combination h2
    have hc : ρ.val - (1 - conj s) = 0 := sub_eq_zero.mpr h2
    rw [hb, hc]; simp
  · have hb : ρ.val + conj s - 1 ≠ 0 := by
      intro h0; apply h2; linear_combination h0
    have hc : ρ.val - (1 - conj s) ≠ 0 := sub_ne_zero.mpr h2
    field_simp
    ring

/-- On the axis the anchored Cayley factor is the phase `−(s − ρ)/conj(s − ρ)`. -/
theorem cayleyAt_on_axis {s ρ : ℂ} (hρ : ρ.re = 1 / 2) : cayleyAt s ρ = -(s - ρ) / conj (s - ρ) := by
  unfold cayleyAt
  have hmir : ρ - (1 - conj s) = conj (s - ρ) := by
    apply Complex.ext
    · simp [Complex.sub_re, Complex.conj_re]; linarith
    · simp [Complex.sub_im, Complex.conj_im]; ring
  rw [hmir]
  ring

/-- **On the axis the phases cancel**: the seat term is `m_ρ / |s − ρ|²`, real and positive. -/
theorem seatTerm_on_axis {s : ℂ} (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) (hρ : ρ.val.re = 1 / 2)
    (h1 : s ≠ ρ.val) :
    seatTerm s ρ = ((ZD.xiOrderNat ρ.val : ℝ) / Complex.normSq (s - ρ.val) : ℝ) := by
  unfold seatTerm
  rw [← mul_inv, seat_denominator]
  have hmir : ρ.val + conj s - 1 = conj (s - ρ.val) := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.sub_re, Complex.conj_re]; linarith
    · simp [Complex.add_im, Complex.sub_im, Complex.conj_im]; ring
  rw [hmir, Complex.mul_conj, Complex.ofReal_div]
  have hn : (Complex.normSq (s - ρ.val) : ℂ) ≠ 0 := by
    exact_mod_cast (fun h => (sub_ne_zero.mpr h1) (Complex.normSq_eq_zero.mp h))
  field_simp
  norm_cast

/-- **The leaf in Cayley words**: nonnegative real sum of the anchored Cayley factors, weighted by the squared
resolvents, from every anchor of the open right half-strip ⟹ RH. -/
theorem riemannHypothesis_of_cayley_seat_nonneg
    (h : ∀ s : ℂ, Region s → s ∉ ZD.NontrivialZeros →
      0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        -(ZD.xiOrderNat ρ.val : ℂ) * cayleyAt s ρ.val / (s - ρ.val) ^ 2).re) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_seat_nonneg
  intro s hs hsz
  have hcongr : (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} => seatTerm s ρ)
      = fun ρ => -(ZD.xiOrderNat ρ.val : ℂ) * cayleyAt s ρ.val / (s - ρ.val) ^ 2 := by
    funext ρ
    exact seatTerm_eq_cayley ρ (fun h0 => hsz (h0 ▸ ρ.2))
  rw [hcongr]
  exact h s hs hsz

end CriticalLinePhasor.HelixCayleySeat

end

#print axioms CriticalLinePhasor.HelixCayleySeat.cayleyPoint_norm_eq_one_iff
#print axioms CriticalLinePhasor.HelixCayleySeat.cayleyAt_norm_eq_one_iff
#print axioms CriticalLinePhasor.HelixCayleySeat.seatTerm_eq_cayley
#print axioms CriticalLinePhasor.HelixCayleySeat.seatTerm_on_axis
#print axioms CriticalLinePhasor.HelixCayleySeat.riemannHypothesis_of_cayley_seat_nonneg
