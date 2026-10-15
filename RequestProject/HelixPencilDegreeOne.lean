import RequestProject.DVPSeatRealPart
import RequestProject.HelixTiltMassDoor

/-!
# The seat sum at an anchor: the degree-one pencil rung and the leaf's zero-side form (ledger 1329)

The pencil register (Sam, 2026-10-13: "3D pencils"). The harmonic pencil's positivity door
(`PencilPositivityRH.riemannHypothesis_of_pencilPositivity`, ledger 932) asks the Hermitian jet form at anchors
`1 < σ₀ < 3/2` to be nonnegative for every polynomial; its degree-one instance is the sign of `Re ξ′/ξ` at the anchor.
Here that sign is compiled from the seat identity (505–512): with `w = spectralCoord s`, so that `s = ½ + i w`,

  `Re ξ′/ξ(s) = (Re s − ½) · Re Σ_ρ m_ρ (z_ρ − w)⁻¹ (z_ρ − w̄)⁻¹`,   `z_ρ = spectralCoord ρ`,

and the term of each zero is `m_ρ / ((s − ρ)(ρ + s̄ − 1))`, whose real part is
`m_ρ · [(σ − β)(σ + β − 1) + (t − γ)²] / |…|²` — nonnegative termwise as soon as `σ ≥ 1`, for every zero, wherever
it lies. So:

* `re_logDeriv_xi_nonneg_of_one_le_re` — `0 ≤ Re ξ′/ξ(s)` on `Re s ≥ 1`, unconditionally, no window: the
  degree-one rung of the pencil ladder.
* `riemannHypothesis_of_seat_nonneg` — the leaf of 1326/1328 in its zero-side form: the seat sum is nonnegative on
  the open right half-strip ⟹ RH. On the strip the termwise sign is lost exactly for a zero with `β > σ` or
  `β < 1 − σ`, i.e. for an off-axis pair straddling the anchor — the content of the leaf, now a compiled statement.

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixPencilDegreeOne

open CriticalLinePhasor.DVP CriticalLinePhasor.HilbertPolya CriticalLinePhasor.HelixTiltMass

/-- The seat term of a zero at the anchor `s`: `m_ρ (z_ρ − w)⁻¹ (z_ρ − w̄)⁻¹`, `w = spectralCoord s`. -/
def seatTerm (s : ℂ) (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) : ℂ :=
  (ZD.xiOrderNat ρ.val : ℂ) *
    ((spectralCoord ρ.val - spectralCoord s)⁻¹ * (spectralCoord ρ.val - conj (spectralCoord s))⁻¹)

theorem chart_spectralCoord (s : ℂ) : (1 / 2 : ℂ) + Complex.I * spectralCoord s = s := by
  unfold spectralCoord
  linear_combination (-(s - 1 / 2)) * Complex.I_sq

theorem chart_conj_spectralCoord (s : ℂ) :
    (1 / 2 : ℂ) + Complex.I * conj (spectralCoord s) = 1 - conj s := by
  rw [chart_two_eq, chart_spectralCoord]

theorem spectralCoord_im (s : ℂ) : (spectralCoord s).im = -(s.re - 1 / 2) := by
  unfold spectralCoord
  simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]

theorem spectralCoord_sub_spectralCoord (ρ s : ℂ) :
    spectralCoord ρ - spectralCoord s = Complex.I * (s - ρ) := by
  unfold spectralCoord; ring

theorem spectralCoord_sub_conj (ρ s : ℂ) :
    spectralCoord ρ - conj (spectralCoord s) = -Complex.I * (ρ + conj s - 1) := by
  unfold spectralCoord
  simp only [map_mul, map_neg, map_sub, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

/-- The product of the two resolvent factors is `(s − ρ)(ρ + s̄ − 1)`. -/
theorem seat_denominator (ρ s : ℂ) :
    (spectralCoord ρ - spectralCoord s) * (spectralCoord ρ - conj (spectralCoord s))
      = (s - ρ) * (ρ + conj s - 1) := by
  rw [spectralCoord_sub_spectralCoord, spectralCoord_sub_conj]
  linear_combination (-(s - ρ) * (ρ + conj s - 1)) * Complex.I_sq

/-- The real part of the denominator: `(σ − β)(σ + β − 1) + (t − γ)²`. -/
theorem seat_denominator_re (ρ s : ℂ) :
    ((s - ρ) * (ρ + conj s - 1)).re = (s.re - ρ.re) * (s.re + ρ.re - 1) + (s.im - ρ.im) ^ 2 := by
  simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re, Complex.sub_im,
    Complex.add_im, Complex.conj_im, Complex.one_im]
  ring

/-- **Termwise sign at `σ ≥ 1`**: every zero's seat term has nonnegative real part. -/
theorem seatTerm_re_nonneg {s : ℂ} (hs : 1 ≤ s.re) (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    0 ≤ (seatTerm s ρ).re := by
  unfold seatTerm
  rw [← mul_inv, seat_denominator]
  have hre : 0 ≤ ((s - ρ.val) * (ρ.val + conj s - 1)).re := by
    rw [seat_denominator_re]
    obtain ⟨h0, h1, _⟩ := ρ.2
    have ha : 0 ≤ s.re - ρ.val.re := by linarith
    have hb : 0 ≤ s.re + ρ.val.re - 1 := by linarith
    nlinarith [mul_nonneg ha hb, sq_nonneg (s.im - ρ.val.im)]
  have hinv : 0 ≤ (((s - ρ.val) * (ρ.val + conj s - 1))⁻¹).re := by
    rw [Complex.inv_re]
    exact div_nonneg hre (Complex.normSq_nonneg _)
  have hm : (0 : ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
  have : ((ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val) * (ρ.val + conj s - 1))⁻¹).re
      = (ZD.xiOrderNat ρ.val : ℝ) * (((s - ρ.val) * (ρ.val + conj s - 1))⁻¹).re := by
    rw [Complex.mul_re]; simp
  rw [this]
  exact mul_nonneg hm hinv

/-- Nonvanishing of the two resolvent factors off the zero set and its mirror. -/
theorem factors_ne_zero {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hs' : 1 - conj s ∉ ZD.NontrivialZeros)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    spectralCoord ρ.val - spectralCoord s ≠ 0 ∧ spectralCoord ρ.val - conj (spectralCoord s) ≠ 0 := by
  constructor
  · rw [spectralCoord_sub_spectralCoord]
    refine mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr ?_)
    intro h; exact hs (h ▸ ρ.2)
  · rw [spectralCoord_sub_conj]
    refine mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    intro h
    apply hs'
    have : (1 : ℂ) - conj s = ρ.val := by linear_combination -h
    rw [this]; exact ρ.2

/-- The seat terms are summable (from the resolvent-trace summability of the differences). -/
theorem seatTerm_summable {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hs' : 1 - conj s ∉ ZD.NontrivialZeros)
    (hσ : s.re ≠ 1 / 2) : Summable (seatTerm s) := by
  have hw : (1 / 2 : ℂ) + Complex.I * spectralCoord s ∉ ZD.NontrivialZeros := by
    rw [chart_spectralCoord]; exact hs
  have hw' : (1 / 2 : ℂ) + Complex.I * conj (spectralCoord s) ∉ ZD.NontrivialZeros := by
    rw [chart_conj_spectralCoord]; exact hs'
  have hsum := (summable_spectral_diff hw hw').div_const (spectralCoord s - conj (spectralCoord s))
  refine hsum.congr fun ρ => ?_
  obtain ⟨h1, h2⟩ := factors_ne_zero hs hs' ρ
  have hww : spectralCoord s - conj (spectralCoord s) ≠ 0 := by
    rw [Complex.sub_conj]
    refine mul_ne_zero ?_ Complex.I_ne_zero
    rw [spectralCoord_im]
    exact_mod_cast (mul_ne_zero two_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr hσ)))
  unfold seatTerm
  field_simp
  ring

/-- **The seat identity at an anchor**: `Re ξ′/ξ(s) = (Re s − ½) · Re Σ_ρ seatTerm s ρ`. -/
theorem re_logDeriv_xi_eq_seat {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hs' : 1 - conj s ∉ ZD.NontrivialZeros)
    (hσ : s.re ≠ 1 / 2) :
    (deriv ZD.riemannXi s / ZD.riemannXi s).re = (s.re - 1 / 2) * (∑' ρ, seatTerm s ρ).re := by
  have hw : (1 / 2 : ℂ) + Complex.I * spectralCoord s ∉ ZD.NontrivialZeros := by
    rw [chart_spectralCoord]; exact hs
  have hw' : (1 / 2 : ℂ) + Complex.I * conj (spectralCoord s) ∉ ZD.NontrivialZeros := by
    rw [chart_conj_spectralCoord]; exact hs'
  have him : spectralCoord s - conj (spectralCoord s) ≠ 0 := by
    rw [Complex.sub_conj]
    refine mul_ne_zero ?_ Complex.I_ne_zero
    rw [spectralCoord_im]
    exact_mod_cast (mul_ne_zero two_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr hσ)))
  have h := seat_energy_re_eq hw hw' him
  rw [chart_spectralCoord, spectralCoord_im] at h
  have hne : s.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hσ
  unfold seatTerm
  rw [h, neg_div_neg_eq, mul_div_cancel₀ _ hne]

/-- **The degree-one pencil rung, unconditional**: `0 ≤ Re ξ′/ξ(s)` for `Re s ≥ 1`. No window. -/
theorem re_logDeriv_xi_nonneg_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    0 ≤ (deriv ZD.riemannXi s / ZD.riemannXi s).re := by
  have hsz : s ∉ ZD.NontrivialZeros := fun h => by linarith [h.2.1]
  have hs' : 1 - conj s ∉ ZD.NontrivialZeros := fun h => by
    have := h.1
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re] at this
    linarith
  have hσ : s.re ≠ 1 / 2 := by intro h; linarith
  rw [re_logDeriv_xi_eq_seat hsz hs' hσ, Complex.re_tsum (seatTerm_summable hsz hs' hσ)]
  exact mul_nonneg (by linarith) (tsum_nonneg fun ρ => seatTerm_re_nonneg hs ρ)

/-- **The leaf in its zero-side form**: the seat sum nonnegative on the open right half-strip ⟹ RH. -/
theorem riemannHypothesis_of_seat_nonneg
    (h : ∀ s : ℂ, Region s → s ∉ ZD.NontrivialZeros → 0 ≤ (∑' ρ, seatTerm s ρ).re) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_logDeriv_re_nonneg
  intro s hs hξ
  have hsz : s ∉ ZD.NontrivialZeros := fun hz => hξ (ZD.riemannXi_eq_zero_of_mem_NontrivialZeros s hz)
  have hs' : 1 - conj s ∉ ZD.NontrivialZeros := fun hz => by
    have := ZD.riemannXi_eq_zero_of_mem_NontrivialZeros _ hz
    rw [CriticalLinePhasor.ContourArgument.riemannXi_one_sub_conj] at this
    exact hξ (by simpa using congrArg conj this)
  have hσ : s.re ≠ 1 / 2 := by intro h0; linarith [hs.1]
  rw [re_logDeriv_xi_eq_seat hsz hs' hσ]
  exact mul_nonneg (by linarith [hs.1]) (h s hs hsz)

end CriticalLinePhasor.HelixPencilDegreeOne

end

#print axioms CriticalLinePhasor.HelixPencilDegreeOne.re_logDeriv_xi_eq_seat
#print axioms CriticalLinePhasor.HelixPencilDegreeOne.re_logDeriv_xi_nonneg_of_one_le_re
#print axioms CriticalLinePhasor.HelixPencilDegreeOne.riemannHypothesis_of_seat_nonneg
