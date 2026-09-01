import RequestProject.SeatingMassWrap
import RequestProject.XiLogDerivConstantFree

/-!
# Mass positivity from on-line-ness: the mass door at exact strength

`seatMass ≥ 0` on the high-left channel, proved from the on-line hypothesis
alone — and the striking register fact Sam predicted: **even multiplicities
are ignored entirely**.  Under `∀ ρ, ρ.re = ½` each summand of the compiled
constant-free partial fraction has real part

  `m·[(σ−½)/N₁ + (σ−½)/N₂] = (σ−½)·m·(N₁⁻¹ + N₂⁻¹)`,

so the mass is HALF A TERMWISE-NONNEGATIVE tsum — no mirror pairing, no
parity, no simplicity: multiplicities enter only as nonnegative weights.
The mass register is parity-blind, unlike the count register whose defect
`D` (SeatingRDefect / SeatingFlipConservation) books the even-order on-line
class.  Combined with the compiled `rh_of_channel_mass` this pins the mass
door at EXACT RH strength:

  `channel_mass_iff_online` — channel mass nonnegativity ⟺ every
  nontrivial zero on the critical line.

The flip/census doors carry RH ∧ (no even-order zeros); the mass door
carries RH, full stop.  Its obstruction class is off-line zeros alone.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- **Two-point summability** at the mirror pair `(s, 1−s)`: the compiled
Hadamard-term summability differenced, the `1/ρ` normalizers cancelling. -/
theorem summable_two_point_mirror {s : ℂ}
    (hs : s ∉ ZD.NontrivialZeros) (hs' : (1 - s) ∉ ZD.NontrivialZeros) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      (ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹ - ((1 - s) - ρ.val)⁻¹)) := by
  apply ((HilbertPolya.summable_hadamard_term hs).sub
    (HilbertPolya.summable_hadamard_term hs')).congr
  intro ρ
  ring

/-- **Mass nonnegativity from on-line-ness, everywhere off the line** —
even multiplicities ignored entirely: if every nontrivial zero is on the
critical line, each two-point summand contributes `(σ−½)·m·(N₁⁻¹+N₂⁻¹)`,
so the seat mass is half a nonnegative series.  Multiplicity `m` appears
only as a nonnegative weight; its parity never enters. -/
theorem seatMass_nonneg_of_online
    (hRH : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2)
    {s : ℂ} (hs : s.re ≠ 1/2) :
    0 ≤ seatMass s := by
  have hsz : s ∉ ZD.NontrivialZeros := fun h => hs (hRH s h)
  have hs1re : (1 - s).re = 1 - s.re := by
    simp [Complex.sub_re, Complex.one_re]
  have hsz' : (1 - s) ∉ ZD.NontrivialZeros := by
    intro h
    have h2 := hRH _ h
    rw [hs1re] at h2
    apply hs
    linarith
  have hid := CriticalLinePhasor.XiStructure.xiLogDeriv_constant_free hsz hsz'
  have hsum := summable_two_point_mirror hsz hsz'
  -- real parts of the identity, termwise
  have hre := congrArg Complex.re hid
  rw [Complex.re_tsum hsum] at hre
  have hlhs : ((2:ℂ) * (deriv ZD.riemannXi s / ZD.riemannXi s)).re
      = 2 * (deriv ZD.riemannXi s / ZD.riemannXi s).re := by
    simp [Complex.mul_re]
  rw [hlhs] at hre
  -- each term is (σ − ½) times a nonnegative weight
  have hterm : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ((ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹ - ((1 - s) - ρ.val)⁻¹)).re
        = (s.re - 1/2) * ((ZD.xiOrderNat ρ.val : ℝ)
            * ((Complex.normSq (s - ρ.val))⁻¹
              + (Complex.normSq ((1 - s) - ρ.val))⁻¹)) := by
    intro ρ
    have hρre : ρ.val.re = 1/2 := hRH ρ.val ρ.2
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    simp only [Complex.sub_re, Complex.inv_re, Complex.one_re]
    rw [hρre]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [tsum_congr hterm, tsum_mul_left] at hre
  set T : ℝ := ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      (ZD.xiOrderNat ρ.val : ℝ)
        * ((Complex.normSq (s - ρ.val))⁻¹
          + (Complex.normSq ((1 - s) - ρ.val))⁻¹) with hTdef
  have hT : 0 ≤ T := by
    rw [hTdef]
    apply tsum_nonneg
    intro ρ
    have h1 : (0:ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
    have h2 : (0:ℝ) ≤ (Complex.normSq (s - ρ.val))⁻¹ :=
      inv_nonneg.mpr (Complex.normSq_nonneg _)
    have h3 : (0:ℝ) ≤ (Complex.normSq ((1 - s) - ρ.val))⁻¹ :=
      inv_nonneg.mpr (Complex.normSq_nonneg _)
    exact mul_nonneg h1 (add_nonneg h2 h3)
  have hne : s.re - 1/2 ≠ 0 := sub_ne_zero.mpr hs
  unfold seatMass
  rw [logDeriv_apply]
  have hFeq : (deriv ZD.riemannXi s / ZD.riemannXi s).re
      = (s.re - 1/2) * (T/2) := by
    linear_combination hre / 2
  rw [hFeq, mul_div_cancel_left₀ _ hne]
  linarith

/-- **The mass door at exact strength**: channel mass nonnegativity is
EQUIVALENT to RH — no simplicity, no parity contamination.  The forward
direction is the compiled `rh_of_channel_mass`; the backward direction is
`seatMass_nonneg_of_online` restricted to the channel. -/
theorem channel_mass_iff_online :
    ∃ A : ℝ, 0 < A ∧
      ((∀ s : ℂ, 1269/2 < |s.im| →
          A / (Real.log |s.im|)^9 < s.re → s.re < 1/2 →
          0 ≤ seatMass s)
        ↔ ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2) := by
  obtain ⟨A, hA0, hdoor⟩ := rh_of_channel_mass
  exact ⟨A, hA0, ⟨hdoor,
    fun hRH s _ _ hhalf => seatMass_nonneg_of_online hRH (ne_of_lt hhalf)⟩⟩

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.summable_two_point_mirror
#print axioms CriticalLinePhasor.SeatingLedger.seatMass_nonneg_of_online
#print axioms CriticalLinePhasor.SeatingLedger.channel_mass_iff_online
