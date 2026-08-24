import RequestProject.DVPSeatResonance
import RequestProject.DVPLadder

/-!
# The channel base: seat positivity below height 57.5, unconditional

Conjunct 2's opening slab.  With `online_below_58` compiled, every zero
within any half-unit height window below `58` is ON the line, so the
deep tube of `seat_channel_off_tubes` is EMPTY for anchors of height
`|Re w| ≤ 57.5`: the instrument fires with `W = ∅, M = 0, K = 0,
δ = 1, H = 1` and the balance `0 ≤ 0`.  Since `e⁴ + 2 < 57.5`, the
channel's base segment `[e⁴+2, 57.5]` is DISCHARGED — and the argument
is generic: every future extension of the certified on-line range
extends the channel by the same instrument.
-/

open Complex
open CriticalLinePhasor.FoliatedPolarization

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The deep tube is empty below the certified height. -/
theorem deep_tube_empty {u : ℂ} (hre : |u.re| ≤ 115/2) :
    ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ¬(|ρ.val.im - u.re| < 1/2 ∧ |u.im| < |ρ.val.re - 1/2|) := by
  rintro ρ ⟨h1, h2⟩
  have hρ58 : |ρ.val.im| ≤ 58 := by
    have h3 : |ρ.val.im| - |u.re| ≤ |ρ.val.im - u.re| :=
      abs_sub_abs_le_abs_sub _ _
    linarith
  have hon := online_below_58 ρ.val ρ.2 hρ58
  rw [hon] at h2
  simp at h2
  linarith [abs_nonneg u.im]

/-- **The channel base (upper half)**: seat positivity at every anchor
with `0 < Im w` and `|Re w| ≤ 57.5`, unconditionally. -/
theorem seat_channel_base_upper {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hd : 0 < w.im) (hre : |w.re| ≤ 115/2) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  have hempty := deep_tube_empty (u := w) hre
  haveI hie : IsEmpty {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|} :=
    ⟨fun x => hempty x.val x.2⟩
  refine seat_channel_off_tubes hw hw' him hd (H := 1) (δ := 1)
    (K := 0) (M := 0) (by norm_num) (by norm_num) ∅
    (by intro ρ hρ; exact absurd hρ (Finset.notMem_empty ρ))
    (by intro ρ hρ; exact absurd hρ (Finset.notMem_empty ρ))
    (by intro ρ hρ; exact absurd hρ (Finset.notMem_empty ρ))
    (by intro ρ hρ; exact absurd hρ (Finset.notMem_empty ρ))
    (by simp) ?_ ?_ ?_ ?_
  · intro ρ h1 h2
    exact absurd ⟨h1, h2⟩ (hempty ρ)
  · exact .of_finite
  · rw [tsum_empty]
  · rw [zero_div]
    positivity

/-- **The channel base**: seat positivity at every admissible anchor of
height `|Re w| ≤ 57.5` — in particular on the channel segment
`[e⁴ + 2, 57.5]`.  Unconditional. -/
theorem seat_channel_base {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hre : |w.re| ≤ 115/2) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  have himne : w.im ≠ 0 := by
    intro h0
    apply him
    apply Complex.ext
    · simp
    · simp [h0]
  rcases lt_or_gt_of_ne himne with hneg | hpos
  · -- reflect to the conjugate anchor
    have hconj : (starRingEnd ℂ) ((starRingEnd ℂ) w) = w := by
      simp
    have h1 := seat_channel_base_upper (w := (starRingEnd ℂ) w)
      hw'
      (by rw [hconj]; exact hw)
      (by
        rw [hconj]
        intro h
        exact him (sub_eq_zero.mpr (sub_eq_zero.mp h).symm))
      (by simp only [Complex.conj_im]; linarith)
      (by simp only [Complex.conj_re]; exact hre)
    have hswap : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) ((starRingEnd ℂ) w))⁻¹)
        = (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹) := by
      intro ρ
      rw [hconj]
      ring
    rw [tsum_congr hswap] at h1
    exact h1
  · exact seat_channel_base_upper hw hw' him hpos hre

/-- **The channel-extension transfer**: a certified on-line range `[0, T]`
discharges the channel to height `T − 1/2`, generically.  Conjunct 2 IS
the unbounded limit of conjunct-1-type certificates — this theorem is
the compiled induction step. -/
theorem seat_channel_of_online_range {T : ℝ}
    (honline : ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ T → ρ.re = 1/2)
    {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hre : |w.re| ≤ T - 1/2) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  have hempty : ∀ u : ℂ, |u.re| ≤ T - 1/2 →
      ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ¬(|ρ.val.im - u.re| < 1/2 ∧ |u.im| < |ρ.val.re - 1/2|) := by
    rintro u hu ρ ⟨h1, h2⟩
    have hρT : |ρ.val.im| ≤ T := by
      have h3 : |ρ.val.im| - |u.re| ≤ |ρ.val.im - u.re| :=
        abs_sub_abs_le_abs_sub _ _
      linarith
    have hon := honline ρ.val ρ.2 hρT
    rw [hon] at h2
    simp at h2
    linarith [abs_nonneg u.im]
  have hupper : ∀ u : ℂ,
      (1 / 2 + Complex.I * u) ∉ ZD.NontrivialZeros →
      (1 / 2 + Complex.I * (starRingEnd ℂ) u) ∉ ZD.NontrivialZeros →
      u - (starRingEnd ℂ) u ≠ 0 → 0 < u.im → |u.re| ≤ T - 1/2 →
      0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) *
            ((spectralCoord ρ.val - u)⁻¹ *
              (spectralCoord ρ.val - (starRingEnd ℂ) u)⁻¹)).re := by
    intro u huw huw' huim hud hure
    have he := hempty u hure
    haveI hie : IsEmpty {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - u.re| < 1 / 2 ∧ |u.im| < |ρ.val.re - 1 / 2|} :=
      ⟨fun x => he x.val x.2⟩
    refine seat_channel_off_tubes huw huw' huim hud (H := 1) (δ := 1)
      (K := 0) (M := 0) (by norm_num) (by norm_num) ∅
      (by intro ρ hρ; exact absurd hρ (Finset.notMem_empty ρ))
      (by intro ρ hρ; exact absurd hρ (Finset.notMem_empty ρ))
      (by intro ρ hρ; exact absurd hρ (Finset.notMem_empty ρ))
      (by intro ρ hρ; exact absurd hρ (Finset.notMem_empty ρ))
      (by simp) ?_ ?_ ?_ ?_
    · intro ρ h1 h2
      exact absurd ⟨h1, h2⟩ (he ρ)
    · exact .of_finite
    · rw [tsum_empty]
    · rw [zero_div]
      positivity
  have himne : w.im ≠ 0 := by
    intro h0
    apply him
    apply Complex.ext
    · simp
    · simp [h0]
  rcases lt_or_gt_of_ne himne with hneg | hpos
  · have hconj : (starRingEnd ℂ) ((starRingEnd ℂ) w) = w := by
      simp
    have h1 := hupper ((starRingEnd ℂ) w)
      hw'
      (by rw [hconj]; exact hw)
      (by
        rw [hconj]
        intro h
        exact him (sub_eq_zero.mpr (sub_eq_zero.mp h).symm))
      (by simp only [Complex.conj_im]; linarith)
      (by simp only [Complex.conj_re]; exact hre)
    have hswap : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) ((starRingEnd ℂ) w))⁻¹)
        = (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹) := by
      intro ρ
      rw [hconj]
      ring
    rw [tsum_congr hswap] at h1
    exact h1
  · exact hupper w hw hw' him hpos hre

/-- **The remaining node, exactly**: with the base absorbed, RH is
equivalent to every zero of ordinate ABOVE `58` lying on the line. -/
theorem rh_iff_online_above_58 :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2)
      ↔ (∀ ρ ∈ ZD.NontrivialZeros, 58 < |ρ.im| → ρ.re = 1/2) := by
  constructor
  · intro h ρ hρ _
    exact h ρ hρ
  · intro h ρ hρ
    rcases le_or_gt |ρ.im| 58 with hle | hgt
    · exact online_below_58 ρ hρ hle
    · exact h ρ hρ hgt

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.deep_tube_empty
#print axioms CriticalLinePhasor.DVP.seat_channel_base
#print axioms CriticalLinePhasor.DVP.seat_channel_of_online_range
#print axioms CriticalLinePhasor.DVP.rh_iff_online_above_58
end AxiomAudit
