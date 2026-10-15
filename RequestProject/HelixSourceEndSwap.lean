import RequestProject.HelixZetaSource
import RequestProject.HelixCancellationProjection
import RequestProject.OneAssumptionRH

/-!
# The J-pair of chart zeros is one event read from the two ends (ledger 1314)

Sam (2026-10-13): "we have proven 1 vanishing per height by construction because the phasor banks grow one at a
time so it can't cancel its opposite bank twice." The end-swap side of that fact, compiled on the 1270 source.

The source of a zero `ρ` is the two-foot configuration `sourceConfig v Z hc` at offset `v = ρ/2 − ¼` and height
`Z = e^{Im ρ}` (1270). The chart's partner zero `1 − ρ̄` has offset `−v̄`. Here:

* `partnerSource_phasor`: the source at `(−v̄, −hc)` is the J-image of the source at `(v, hc)` with its two feet
  swapped. One pair of feet, read from the other end. No functional equation is used: this is the construction.
* `partnerSource_resultant`, `partnerSource_cancels_iff`, `partnerSource_mass`: the partner's resultant is the
  conjugate, so it cancels exactly when the source cancels, with the same mass. "Cancelling the opposite bank"
  is one event, not two.
* `zero_symm_of_source`: read through `sourceConfig_cancels_iff`, that is the zero-set symmetry
  `ζ(½ + 2v) = 0 ↔ ζ(½ − 2v̄) = 0` on the band, obtained from the geometry's end swap.
* `source_foot_readout`: every foot of the source at height `e^{Im ρ}` reads at `½ + i·Im ρ`, whatever `Re ρ` is.
  One event, one readout (1263's chain, `foot_stripReadout`).

What the end swap does NOT do: it does not identify the chart point `ρ` with the readout `½ + i Im ρ`. The
proposition that does is `CarrierReadout.OneVanishingPerHeight3D` (FiberZeroMidpointRoute.lean), from which RH
follows (`rh_of_oneVanishingPerHeight3D`). Stated here as `oneVanishing_goal`, verbatim, as the construction site.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixSourceEndSwap

open CriticalLinePhasor.HelixZetaSource CriticalLinePhasor.HelixOriginCentered CriticalLinePhasor.HelixTwoEndedNative
open CriticalLinePhasor.HelixTwoEndedCancellation CriticalLinePhasor.HelixCancellationProjection FocalFeet
open CriticalLinePhasor CriticalLinePhasor.GlobalHelix CriticalLinePhasor.FocalLine
open CriticalLinePhasor.HelixFiberIsTwoEnded CarrierReadout

/-- **The partner source is the J-image of the source with its feet swapped.** -/
theorem partnerSource_phasor (v : ℂ) (Z hc : ℝ) (k : Fin 2) :
    (sourceConfig (-conj v) Z (-hc)).phasor k = (sourceConfig v Z hc).J.phasor (Fin.rev k) := by
  fin_cases k <;> simp [sourceConfig, PhasorConfig.J, Fin.rev]

/-- The partner's resultant is the conjugate of the source's resultant. -/
theorem partnerSource_resultant (v : ℂ) (Z hc : ℝ) :
    (sourceConfig (-conj v) Z (-hc)).resultant = conj ((sourceConfig v Z hc).resultant) := by
  rw [sourceConfig_resultant_feet, sourceConfig_resultant_feet]
  simp only [map_add, map_neg, Complex.conj_conj, neg_neg]
  ring

/-- **One event, two ends**: the partner source cancels exactly when the source cancels. No functional equation. -/
theorem partnerSource_cancels_iff (v : ℂ) (Z hc : ℝ) :
    (sourceConfig (-conj v) Z (-hc)).Cancels ↔ (sourceConfig v Z hc).Cancels := by
  unfold PhasorConfig.Cancels
  rw [partnerSource_resultant]
  constructor
  · intro h
    have := congrArg conj h
    rwa [Complex.conj_conj, map_zero] at this
  · intro h
    rw [h, map_zero]

/-- The partner source has the same mass. -/
theorem partnerSource_mass (v : ℂ) (Z hc : ℝ) :
    (sourceConfig (-conj v) Z (-hc)).mass = (sourceConfig v Z hc).mass := by
  unfold PhasorConfig.mass
  show ∑ k : Fin 2, ‖(sourceConfig (-conj v) Z (-hc)).phasor k‖ =
    ∑ k : Fin 2, ‖(sourceConfig v Z hc).phasor k‖
  rw [Fin.sum_univ_two, Fin.sum_univ_two, partnerSource_phasor, partnerSource_phasor]
  simp [PhasorConfig.J, sourceConfig, Fin.rev, add_comm]

/-- **The zero-set symmetry of the readout, from the end swap**: on the band, `ζ(½ + 2v) = 0 ↔ ζ(½ − 2v̄) = 0`. -/
theorem zero_symm_of_source {v : ℂ} (hv : |v.re| < 1 / 4) :
    riemannZeta (1 / 2 + 2 * v) = 0 ↔ riemannZeta (1 / 2 + 2 * (-conj v)) = 0 := by
  have hv' : |(-conj v).re| < 1 / 4 := by simpa using hv
  rw [← sourceConfig_cancels_iff hv 1 0, ← sourceConfig_cancels_iff hv' 1 (-0),
    partnerSource_cancels_iff]

/-- **One event, one readout**: every foot of the source of `ρ` reads at `½ + i·Im ρ`, for every `Re ρ`. -/
theorem source_foot_readout (ρ : ℂ) (hc : ℝ) (k : Fin 2) :
    stripReadout (footFiber ((sourceConfig (ρ / 2 - 1 / 4) (Real.exp ρ.im) hc).phasor k) (Real.exp ρ.im)) =
      1 / 2 + (ρ.im : ℂ) * I := by
  rw [foot_stripReadout, Real.log_exp]

/-! ## The σ-family at one height is read against the one source -/

/-- **The lane chart at `(σ, y)` vanishes exactly when the source at offset `(σ + yi)/2 − ¼` cancels** at height
`e^y` (1269's `fiber_vanishes_iff_two_ended` read through 1270's `sourceConfig_resultant`). -/
theorem laneChart3D_zero_iff_source {σ y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hc : ℝ) :
    laneChart3D σ y = 0 ↔ (sourceConfig (((σ : ℂ) + y * I) / 2 - 1 / 4) (Real.exp y) hc).Cancels := by
  have hre : (((σ : ℂ) + y * I) / 2 - 1 / 4).re = σ / 2 - 1 / 4 := by simp
  have hv : |(((σ : ℂ) + y * I) / 2 - 1 / 4).re| < 1 / 4 := by
    rw [hre, abs_lt]; constructor <;> linarith
  rw [fiber_vanishes_iff_two_ended hσ0 hσ1]
  unfold PhasorConfig.Cancels
  rw [sourceConfig_resultant hv]

/-- The offset of the partner abscissa `1 − σ` at the same height is the J-partner offset `−v̄`. -/
theorem partner_offset (σ y : ℝ) :
    (((1 - σ : ℝ) : ℂ) + y * I) / 2 - 1 / 4 = -conj ((((σ : ℂ) + y * I) / 2 - 1 / 4)) := by
  simp only [map_sub, map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_one, map_ofNat]
  push_cast
  ring

/-- **The two vanishings of the σ-family at one height are one event**: the lane chart at `1 − σ` vanishes exactly
when the lane chart at `σ` does, by the end swap alone. -/
theorem laneChart3D_partner_zero_iff {σ y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    laneChart3D (1 - σ) y = 0 ↔ laneChart3D σ y = 0 := by
  have h1 : (0 : ℝ) < 1 - σ := by linarith
  have h2 : 1 - σ < 1 := by linarith
  rw [laneChart3D_zero_iff_source h1 h2 0, laneChart3D_zero_iff_source hσ0 hσ1 0, partner_offset]
  simpa using partnerSource_cancels_iff (((σ : ℂ) + y * I) / 2 - 1 / 4) (Real.exp y) 0

/-- **The proposition the route consumes, in the event's words**: at height `e^y`, the sources of at most one
abscissa cancel. -/
theorem oneVanishing_iff_source : CarrierReadout.OneVanishingPerHeight3D ↔
    ∀ (y σ₁ σ₂ : ℝ), 0 < σ₁ → σ₁ < 1 → 0 < σ₂ → σ₂ < 1 →
      (sourceConfig (((σ₁ : ℂ) + y * I) / 2 - 1 / 4) (Real.exp y) 0).Cancels →
      (sourceConfig (((σ₂ : ℂ) + y * I) / 2 - 1 / 4) (Real.exp y) 0).Cancels → σ₁ = σ₂ := by
  unfold CarrierReadout.OneVanishingPerHeight3D
  constructor
  · intro h y σ₁ σ₂ h1 h2 h3 h4 c1 c2
    exact h y σ₁ σ₂ h1 h2 h3 h4 ((laneChart3D_zero_iff_source h1 h2 0).mpr c1)
      ((laneChart3D_zero_iff_source h3 h4 0).mpr c2)
  · intro h y σ₁ σ₂ h1 h2 h3 h4 z1 z2
    exact h y σ₁ σ₂ h1 h2 h3 h4 ((laneChart3D_zero_iff_source h1 h2 0).mp z1)
      ((laneChart3D_zero_iff_source h3 h4 0).mp z2)

/-- **The construction site**, verbatim: at one height the fiber's chart vanishes for at most one abscissa.
`rh_of_oneVanishingPerHeight3D` takes it to RH. The end swap above supplies "one event, two ends, one readout";
this is the sentence that would make the chart point of a zero that readout. -/
def oneVanishing_goal : Prop := CarrierReadout.OneVanishingPerHeight3D

theorem rh_of_goal (h : oneVanishing_goal) : RiemannHypothesis :=
  OneAssumptionRH.riemannHypothesis_of_oneAssumption h

end CriticalLinePhasor.HelixSourceEndSwap

end

#print axioms CriticalLinePhasor.HelixSourceEndSwap.partnerSource_cancels_iff
#print axioms CriticalLinePhasor.HelixSourceEndSwap.zero_symm_of_source
#print axioms CriticalLinePhasor.HelixSourceEndSwap.source_foot_readout
#print axioms CriticalLinePhasor.HelixSourceEndSwap.rh_of_goal
#print axioms CriticalLinePhasor.HelixSourceEndSwap.laneChart3D_partner_zero_iff
#print axioms CriticalLinePhasor.HelixSourceEndSwap.oneVanishing_iff_source
