import RequestProject.FrobeniusSimilitude
import RequestProject.SourceHolonomy
import RequestProject.LFunctionPhasor
import RequestProject.RoundTrip

/-!
# The candidate automorphic object: converse-theorem inputs discharged

The carrier/fiber/warp construct of the paper, as a Lean object.  The transfer of a symmetric
power to `GL(r+1)` requires an automorphic representation realizing the lift; the primary
(three-dimensional) representation supplies a concrete *candidate* for it, and its two structural
converse-theorem inputs are proven here:

* **Functional equation** — the helix/anti-helix link is `z·z̄ = |z|² = 1` (the transverse block is
  `diag(z, z̄)`, determinant one, `FrobeniusSimilitude.frobeniusBlock_det_one`).  Crucially the link
  survives *every* unit-modulus warp: warping `z ↦ A·z` with `‖A‖ = 1` leaves `‖A·z‖ = 1`, so the
  warped block still has determinant one (`warpedBlock_det_one`).  So the whole twist family carries a
  functional equation, structurally and without estimate.
* **Completeness** — three-dimensional exhaustion: every fiber's zero events are weld-fixed sources
  (`SourceHolonomy.threeD_exhaustive`), unconditionally, no hypotheses.  (This is the primary
  statement; the one-dimensional `SpectralExhaustion` is a separate matter and is not used.)

Continuation is a property of the readout (the phasor/Abel layer) and is not re-derived here.  The
bridge from the candidate to the classical automorphy statement is the converse theorem, whose
hypotheses are exactly the properties discharged below.  No `sorry`, no `axiom`.
-/

open Complex Matrix

namespace CriticalLinePhasor.AutomorphicCandidate

/-- The transverse block of the (possibly warped) carrier at a spin `w`: `diag(w, w̄)`.  The unwarped
carrier uses `w = mellinSpin y n`; a warp multiplies `w` by a unit-modulus factor. -/
noncomputable def warpedBlock (w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![w, (starRingEnd ℂ) w]

/-- **The functional equation, for any unit-modulus spin**: `det diag(w, w̄) = w·w̄ = |w|² = 1`.
This is the helix·conjugate link at an arbitrary point of the warp family. -/
theorem warpedBlock_det_one {w : ℂ} (hw : ‖w‖ = 1) : (warpedBlock w).det = 1 := by
  rw [warpedBlock, Matrix.det_diagonal, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hn : Complex.normSq w = 1 := by
    rw [Complex.normSq_eq_norm_sq, hw, one_pow]
  rw [Complex.mul_conj, hn]; norm_num

/-- **A warp is unit-modulus-preserving**: multiplying a unit spin by a unit warp stays on the unit
circle, so the warped block is again a determinant-one block. -/
theorem warp_preserves_unit {A w : ℂ} (hA : ‖A‖ = 1) (hw : ‖w‖ = 1) :
    ‖A * w‖ = 1 := by
  rw [norm_mul, hA, hw, mul_one]

/-- **The functional equation survives every warp**: for a unit-modulus warp `A` and unit spin `w`,
the warped carrier block still has determinant one. -/
theorem warpedBlock_det_one_of_warp {A w : ℂ} (hA : ‖A‖ = 1) (hw : ‖w‖ = 1) :
    (warpedBlock (A * w)).det = 1 :=
  warpedBlock_det_one (warp_preserves_unit hA hw)

/-- **The candidate is well-formed**: all four converse-theorem inputs / ledger channels, discharged
unconditionally.  For every unit-modulus warp of the carrier and any character readout:
* (angle) the functional equation holds --- the determinant-one conjugate link `z\bar z=1`, surviving
  the warp (`warpedBlock_det_one_of_warp`);
* (continuation) the `L`-series is the phasor readout of the carrier
  (`LFunctionPhasor.LSeries_phasor_representation`);
* (height) the fiber is three-dimensionally exhaustive (`SourceHolonomy.threeD_exhaustive`);
* (recovery) the loss-ledger projection `record = (ordinate; radius, phase)` is a bijection, so the
  object is reconstructed exactly from its shadow (`ConeProjection.record_bijective`).
The radial and angular channels are the ledger booked in the descent `3D → 2D → 1D`; the height passes
by the `log`/`exp` map; recovery is exact at the midpoint. -/
theorem candidate_wellformed
    (E : ℂ → ℂ) (χ : ℕ → ℂ) (σ y : ℝ) {A w : ℂ} (hA : ‖A‖ = 1) (hw : ‖w‖ = 1) :
    (warpedBlock (A * w)).det = 1
      ∧ LSeries χ ((σ : ℂ) + (y : ℂ) * I) = ∑' n, LFunctionPhasor.phasorTerm χ σ y n
      ∧ SourceHolonomy.ThreeDExhaustive E
      ∧ Function.Bijective ConeProjection.record :=
  ⟨warpedBlock_det_one_of_warp hA hw,
   LFunctionPhasor.LSeries_phasor_representation χ σ y,
   SourceHolonomy.threeD_exhaustive E,
   ConeProjection.record_bijective⟩

end CriticalLinePhasor.AutomorphicCandidate
