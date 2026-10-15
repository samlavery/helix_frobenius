import RequestProject.HelixNativeDilation
import RequestProject.WarpFactorAudit

/-!
# Fixed-carrier compatibility (ledger 1285)

Chatbibibi (via Sam, 2026-10-13): "Does the full integer carrier impose a unique geometric configuration at each
physical height? … Determine whether both source configurations arise from one fixed native carrier under its
already-proved scaling, warp, and J transformations. Check whether the Mellin weighting `n^(−4δ)` represents a
physical change in the carrier or only a change in how the same carrier is evaluated. If the native constraints imply
δ = 0, prove the precise implication. If not, exhibit the compatible off-axis configuration."

Existing objects only. Offsets `v` from the origin; the carrier exponent `k + 2v` is the readout (1281
`mode_functional`).

* `jPair_bank_ratio`: the carrier entries at the two J-related offsets `v` and `−v̄` differ by the REAL POSITIVE site
  factor `(n+1)^{−4 Re v}`: no phase, the same height.
* With `WarpFactor.eSH_split` (1197): `(n+1)^{−s} = (n+1)^{−Re s}·mellinSpin(Im s)`, i.e. `e^{−sH} = D_{Re s} U_{Im s}`.
  Both offsets read ONE native state at height `Z` (the same `U`), through opposite real dilations.
* `dilate_native_iff`: the native constraint (determinant `1` of each site's J-pair block, the Frobenius similitude of
  the conjugate ends) holds for a `D_δ`-image at every site exactly when `δ = 0`.

**Answers.**
1. One native carrier per height: yes (`ThreeDFocal.carrierState3D`, `CarrierState3D` has no radial field). The two
   J-related off-axis configurations are not two states. They are the one native state seen through `D_{±}`.
2. `n^{−4δ}` is the dilation `D`. It keeps the carrier, the height and every site's direction
   (`dilate_direction`, `dilate_height`), and reweights the fiber's site amplitudes. It is a change of evaluation of
   the same carrier (Sam's 1193 "observer warp"), not a change of the carrier.
3. The native constraint does imply `δ = 0`, **for configurations**: a `D_δ`-image has native determinant-1 blocks iff
   `δ = 0` (`dilate_native_iff`).
4. Compatible off-axis configuration: for every `δ` the dilated configuration exists, with nonzero feet
   (`HelixZetaSource.sourceConfig`, `sourceConfig_mass_pos`). It respects scaling, warp and J
   (`dilate_J`, `dilate_frob_comm`) and violates only the determinant-1 endowment. It cancels exactly when the readout
   vanishes off the line (`sourceConfig_cancels_iff`).

So the carrier's arithmetic does not exclude an off-axis zero. It classifies the configuration that would cancel there
as non-native (determinant ≠ 1). Whether every zero is the cancellation of a native configuration is the open
statement, `Source.SourcesOfZerosOnAxis`.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixFixedCarrier

/-- **The two J-related offsets differ by a real positive site factor**: `(n+1)^{−4 Re v}`. -/
theorem jPair_bank_ratio (k : ℝ) (v : ℂ) (n : ℕ) :
    CarrierReadout.bank ((k : ℂ) + 2 * v) n =
      ((((n : ℝ) + 1) ^ (-(4 * v.re)) : ℝ) : ℂ) * CarrierReadout.bank ((k : ℂ) - 2 * conj v) n := by
  have hs : (k : ℂ) + 2 * v = ((k : ℂ) - 2 * conj v) + ((4 * v.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
    ring
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [hs, CarrierReadout.bank_flow]
  congr 1
  rw [show ((n : ℂ) + 1) = ((((n : ℝ) + 1 : ℝ)) : ℂ) by push_cast; ring, ← Complex.ofReal_neg,
    ← Complex.ofReal_cpow hpos.le]

/-- **The native determinant-1 constraint holds for a dilated configuration exactly at `δ = 0`.** -/
theorem dilate_native_iff (δ : ℝ) :
    (∀ k : ℕ, Matrix.det !![((((k : ℝ) + 1) ^ (-δ) : ℝ) : ℂ), 0;
      0, (starRingEnd ℂ) ((((k : ℝ) + 1) ^ (-δ) : ℝ) : ℂ)] = 1) ↔ δ = 0 := by
  constructor
  · intro h
    have h1 := h 1
    rw [WarpFactor.dilate_block_det] at h1
    have h2 : (((1 : ℕ) : ℝ) + 1) ^ (-(2 * δ)) = 1 := by exact_mod_cast h1
    have h3 := congrArg Real.log h2
    rw [Real.log_rpow (by norm_num), Real.log_one] at h3
    have hlog : Real.log (((1 : ℕ) : ℝ) + 1) ≠ 0 := by
      rw [show (((1 : ℕ) : ℝ) + 1) = 2 by norm_num]
      exact (Real.log_pos (by norm_num)).ne'
    have := (mul_eq_zero.mp h3).resolve_right hlog
    linarith
  · rintro rfl k
    rw [WarpFactor.dilate_block_det]
    simp

end CriticalLinePhasor.HelixFixedCarrier

end

#print axioms CriticalLinePhasor.HelixFixedCarrier.jPair_bank_ratio
#print axioms CriticalLinePhasor.HelixFixedCarrier.dilate_native_iff
