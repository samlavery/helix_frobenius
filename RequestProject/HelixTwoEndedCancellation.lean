import RequestProject.HelixOriginCentered
import RequestProject.FocalFeetDatum

/-!
# The two-ended focal cancellation at physical height Z (ledgers 1261–1262)

The two-ended fiber about the origin (`HelixOriginCentered.origin_two_ended`), applied to the house's 3D Gaussian
bank (`HelixTwoEndedNative.nativePair`: the helix bank, the anti-helix bank of the global involution, and the
native reflection). Here it is read as a focal cancellation in the house's feet/eigenstate/detector machinery
(`FocalFeet.PhasorConfig`).

Coordinates: the origin is signed height `h = 0`. A cut is a signed height `hc`; the reflected cut is `-hc`. The
Lean bank variable is the encoding `exp h`; its value at the origin is not the origin.

At the event's physical height `Z` (offset `v = i·log Z / 2` from the origin, on the axis):
* `helixFoot Z hc`: the helix end of the bank above the cut height `hc`.
  `antiHelixFoot Z hc`: the J-image of the helix end above the reflected cut `-hc`.
* `twoEndedConfig Z hc`: the two feet as a configuration at height `Z`.
* `twoEnded_resultant`: its resultant is the completed fiber `2·completedRiemannZeta(½ + i·log Z)`, for every
  cut height. The `½` appears only in this readout.
* `twoEnded_cancels_iff`: **the configuration cancels exactly when `ζ(½ + i·log Z) = 0`**, for every cut height.
* With the cut at the origin (`hc = 0`):
  - `antiHelixFoot_origin`: the anti-helix foot IS the J-image of the helix foot;
  - `feet_origin`: same weight, same height `Z`, opposite direction;
  - `J_twoEnded_origin`: J swaps the two feet.
* `helixFoot_re_of_cancels`, `antiHelixFoot_of_cancels`: at a cancellation the helix foot points straight across
  the standing axis, and the anti-helix foot is its negative. This is derived from the cancellation, not built in.
* `twoEnded_channels_of_cancels`, `twoEnded_post_state`: after cancellation, the standing mode `(0, M)` at height
  `Z`, with `M = 2·‖helixFoot‖` (`mass_origin`).
* `twoEnded_rankDrop_iff`: the harmonic pencil fed the two-ended channels drops rank exactly at the zero
  (for `M ≠ 0`, which always holds: `HelixFootMass.twoEnded_mass_pos`).

Measured (ledger 1261, `tmp/att1261_feet.py`): at the first six zeros the helix foot is nonzero and points
straight across. The mass is positive at every cut height and every height `Z`
(`HelixFootMass.twoEnded_mass_pos`, ledger 1263): the bank's zero mode, booked at the cut, dominates its other
modes. `twoEndedEigenstate` keeps `M > 0` as an argument only because that proof lives downstream;
`HelixFootMass.cancellationEigenstate` supplies it.
`FocalEvent` is unchanged.
-/

open Complex
open scoped ComplexConjugate Matrix

noncomputable section

namespace CriticalLinePhasor.HelixTwoEndedCancellation

open CriticalLinePhasor CriticalLinePhasor.HelixTwoEndedClosure CriticalLinePhasor.HelixTwoEndedNative
  CriticalLinePhasor.HelixOriginCentered CriticalLinePhasor.FocalFeet

/-- The event's offset from the origin at physical height `Z`, on the axis. -/
def eventOffset (Z : ℝ) : ℂ := (Real.log Z : ℂ) * I / 2

/-- **The helix foot** at physical height `Z`: the helix end of the 3D Gaussian bank above the cut height `hc`. -/
def helixFoot (Z hc : ℝ) : ℂ := originEnd nativePair (Real.exp hc) (eventOffset Z)

/-- **The anti-helix foot**: the J-image of the helix end above the reflected cut height `-hc`. -/
def antiHelixFoot (Z hc : ℝ) : ℂ := conj (originEnd nativePair (Real.exp (-hc)) (eventOffset Z))

/-- **The two-ended configuration at height `Z`**: the two feet. -/
def twoEndedConfig (Z hc : ℝ) : PhasorConfig := ⟨Z, 2, ![helixFoot Z hc, antiHelixFoot Z hc]⟩

theorem eventOffset_mirror (Z : ℝ) : -conj (eventOffset Z) = eventOffset Z := by
  unfold eventOffset
  rw [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem nativePair_k : (nativePair.k : ℂ) = 1 / 2 := by
  show ((1 / 2 : ℝ) : ℂ) = 1 / 2
  push_cast
  ring

theorem offset_ne_zero (Z : ℝ) : (nativePair.k : ℂ) / 2 + eventOffset Z ≠ 0 := by
  rw [nativePair_k]
  intro h
  have := congrArg Complex.re h
  simp [eventOffset] at this

theorem offset_ne_k (Z : ℝ) : (nativePair.k : ℂ) / 2 + eventOffset Z ≠ nativePair.k := by
  rw [nativePair_k]
  intro h
  have := congrArg Complex.re h
  simp [eventOffset] at this
  norm_num at this

theorem resultant_eq_feet (Z hc : ℝ) :
    (twoEndedConfig Z hc).resultant = helixFoot Z hc + antiHelixFoot Z hc := by
  show ∑ k : Fin 2, (![helixFoot Z hc, antiHelixFoot Z hc] : Fin 2 → ℂ) k = _
  rw [Fin.sum_univ_two]
  rfl

/-- **The two feet sum to the completed fiber**, for every cut height. -/
theorem twoEnded_resultant (Z hc : ℝ) :
    (twoEndedConfig Z hc).resultant = 2 * completedRiemannZeta (1 / 2 + (Real.log Z : ℂ) * I) := by
  rw [resultant_eq_feet]
  have h := origin_two_ended nativePair nativePair_conj nativePair_conj₀ (Real.exp_pos hc) (offset_ne_zero Z)
    (offset_ne_k Z)
  rw [eventOffset_mirror, show nativePair.ε = 1 from rfl, one_mul, ← Real.exp_neg] at h
  unfold helixFoot antiHelixFoot
  rw [← h]
  unfold originΛ
  rw [nativePair_Λ]
  have hr := originΛ_readout (eventOffset Z)
  unfold originΛ at hr
  rw [show ((HurwitzZeta.hurwitzEvenFEPair 0).k : ℂ) = nativePair.k from rfl] at hr
  rw [hr]
  congr 2
  unfold eventOffset
  ring

/-- **The two-ended configuration cancels exactly at the zero**, for every cut height. -/
theorem twoEnded_cancels_iff (Z hc : ℝ) :
    (twoEndedConfig Z hc).Cancels ↔ riemannZeta (1 / 2 + (Real.log Z : ℂ) * I) = 0 := by
  set s : ℂ := 1 / 2 + (Real.log Z : ℂ) * I with hsdef
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hsdef] at this
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp [hsdef])
  unfold PhasorConfig.Cancels
  rw [twoEnded_resultant Z hc, riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff, or_iff_left hΓ]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  · intro h
    rw [h, mul_zero]

/-! ## The cut at the origin: the two feet are a J-pair -/

/-- With the cut at the origin, the anti-helix foot is the J-image of the helix foot. -/
theorem antiHelixFoot_origin (Z : ℝ) : antiHelixFoot Z 0 = conj (helixFoot Z 0) := by
  unfold antiHelixFoot helixFoot
  rw [neg_zero]

/-- **Same weight, same height `Z`, opposite direction.** -/
theorem feet_origin (Z : ℝ) :
    phasorFoot (antiHelixFoot Z 0) Z = FocalFeet.J (phasorFoot (helixFoot Z 0) Z) := by
  rw [antiHelixFoot_origin, phasorFoot_conj]

/-- **J swaps the two feet**: the J-configuration is the same two feet, exchanged. -/
theorem J_twoEnded_origin (Z : ℝ) :
    PhasorConfig.J (twoEndedConfig Z 0) = ⟨Z, 2, ![antiHelixFoot Z 0, helixFoot Z 0]⟩ := by
  unfold PhasorConfig.J twoEndedConfig
  congr 1
  funext k
  fin_cases k <;> simp [antiHelixFoot_origin]

/-- At a cancellation the helix foot points straight across the standing axis. -/
theorem helixFoot_re_of_cancels {Z : ℝ} (h : (twoEndedConfig Z 0).Cancels) : (helixFoot Z 0).re = 0 := by
  unfold PhasorConfig.Cancels at h
  rw [resultant_eq_feet, antiHelixFoot_origin, Complex.add_conj] at h
  have h2 : (2 * (helixFoot Z 0).re : ℝ) = 0 := by exact_mod_cast h
  linarith

/-- At a cancellation the anti-helix foot is the negative of the helix foot. -/
theorem antiHelixFoot_of_cancels {Z hc : ℝ} (h : (twoEndedConfig Z hc).Cancels) :
    antiHelixFoot Z hc = -helixFoot Z hc := by
  unfold PhasorConfig.Cancels at h
  rw [resultant_eq_feet] at h
  linear_combination h

/-- The total weight of the two feet, with the cut at the origin. -/
theorem mass_origin (Z : ℝ) : (twoEndedConfig Z 0).mass = 2 * ‖helixFoot Z 0‖ := by
  show ∑ k : Fin 2, ‖(![helixFoot Z 0, antiHelixFoot Z 0] : Fin 2 → ℂ) k‖ = _
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, antiHelixFoot_origin, Complex.norm_conj]
  ring

/-- **After cancellation**: the standing mode `(0, M)` at height `Z`. -/
theorem twoEnded_channels_of_cancels {Z hc : ℝ} (h : (twoEndedConfig Z hc).Cancels) :
    (twoEndedConfig Z hc).channels = (CriticalLinePhasor.FocalCancellation.standingMode
      (twoEndedConfig Z hc).mass, Z) :=
  PhasorConfig.channels_of_cancels h

/-- **The detector**: the harmonic pencil fed the two-ended channels drops rank exactly at the zero. -/
theorem twoEnded_rankDrop_iff (Z hc : ℝ) (hm : (twoEndedConfig Z hc).mass ≠ 0) (μ lam : ℂ) (hlam : lam ≠ μ) :
    ((HarmonicCell.harmonicPencil (((twoEndedConfig Z hc).mass : ℝ) : ℂ) (twoEndedConfig Z hc).resultant μ lam)ᴴ *
        HarmonicCell.harmonicPencil (((twoEndedConfig Z hc).mass : ℝ) : ℂ) (twoEndedConfig Z hc).resultant μ lam).det
        = 0 ↔ riemannZeta (1 / 2 + (Real.log Z : ℂ) * I) = 0 := by
  rw [HarmonicCell.harmonicGram_rank_drop_iff_channel_zero _ _ μ lam (by exact_mod_cast hm) hlam]
  exact twoEnded_cancels_iff Z hc

/-- **The post-cancellation eigenstate** `(M, Z)`. -/
def twoEndedEigenstate (Z hc : ℝ) (hZ : 0 < Z) (hm : 0 < (twoEndedConfig Z hc).mass) : FocalEigenstate :=
  ⟨(twoEndedConfig Z hc).mass, hm, Z, hZ⟩

theorem twoEnded_post_state {Z hc : ℝ} (hZ : 0 < Z) (hm : 0 < (twoEndedConfig Z hc).mass)
    (h : (twoEndedConfig Z hc).Cancels) :
    (twoEndedConfig Z hc).channels = ((twoEndedEigenstate Z hc hZ hm).standing, Z) := by
  rw [twoEnded_channels_of_cancels h]
  rfl

end CriticalLinePhasor.HelixTwoEndedCancellation

end

#print axioms CriticalLinePhasor.HelixTwoEndedCancellation.twoEnded_resultant
#print axioms CriticalLinePhasor.HelixTwoEndedCancellation.twoEnded_cancels_iff
#print axioms CriticalLinePhasor.HelixTwoEndedCancellation.feet_origin
#print axioms CriticalLinePhasor.HelixTwoEndedCancellation.J_twoEnded_origin
#print axioms CriticalLinePhasor.HelixTwoEndedCancellation.helixFoot_re_of_cancels
#print axioms CriticalLinePhasor.HelixTwoEndedCancellation.antiHelixFoot_of_cancels
#print axioms CriticalLinePhasor.HelixTwoEndedCancellation.mass_origin
#print axioms CriticalLinePhasor.HelixTwoEndedCancellation.twoEnded_rankDrop_iff
#print axioms CriticalLinePhasor.HelixTwoEndedCancellation.twoEnded_post_state
