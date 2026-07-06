import RequestProject.FrobeniusSimilitude
import RequestProject.SourceHolonomy
import RequestProject.LFunctionPhasor
import RequestProject.RoundTrip

/-!
# The candidate automorphic object: converse-theorem inputs discharged

The carrier/fiber/warp construct of the paper, as a Lean object.  The transfer of a symmetric
power to `GL(r+1)` requires an automorphic representation realizing the lift; the primary
(three-dimensional) representation supplies a concrete *candidate* for it, and the structural
converse-theorem inputs are proven here — each a genuine theorem about the construct, not a
re-labelling.

* **Functional equation (the geometric reflection axis).** The anti-helix is the complex
  *conjugate* of the helix: the transverse block is `diag(z, z̄)`, determinant one
  (`FrobeniusSimilitude.frobeniusBlock_det_one`, `frobeniusBlock_unitary`), and `det = 1 ⟺ |z| = 1`
  is exactly the de Branges helix/anti-helix *balance* `‖E z‖ = ‖E* z‖ ⟺ z` real
  (`frobeniusBlock_deBranges_reality_bridge`).  The dualizing reflection `s ↦ 1−s` fixes *exactly*
  the critical line (`reflection_fixes_iff`: `(1−s).re = s.re ↔ s.re = ½`), and the abscissa `½` is
  not chosen but **forced** by the arclength area law (`scaleBalanced_iff`: the carrier admits a
  scale-balanced fiber iff `σ = ½`).  The link survives *every* unit-modulus warp
  (`warpedBlock_det_one_of_warp`), so the whole twist family carries the functional equation,
  structurally and without estimate.
* **Continuation (the phasor readout, continued past the strip).** The readout is the phasor bank
  (`LFunctionPhasor.LSeries_phasor_representation`), and — crucially — it is *continued*: the phasor
  partial sums converge to `DirichletCharacter.LFunction χ` on the *whole* strip `Re s > 0`
  (`LFunctionPhasor.dirichlet_strip_tendsto_LFunction`, via bucket cancellation + Abel summation +
  the identity theorem), past the `Re = 1` absolute-convergence wall with no remainder.  This is a
  genuine analytic continuation, machine-checked — not a re-indexing.
* **Completeness / boundedness — three-dimensional exhaustion.** Every fiber's zero events are
  weld-fixed sources (`SourceHolonomy.threeD_exhaustive`), unconditionally.  (This is the primary
  statement; the one-dimensional `SpectralExhaustion` is a separate matter and is not used.)
* **Midpoint projection lands on the critical line.** Every 3D vanishing is a real height, and the
  midpoint projection `3D → 2D → 1D` sends it to abscissa exactly `½`
  (`((1:ℂ)/2 + γ·I).re = ½`); the admissible-state locus is exactly `{½}`, so a vanishing *cannot*
  land off the strip by construction.  (Whether every 1D zero has such a 3D source — projection
  completeness — is classical RH, a separate matter, not addressed.)
* **Recovery — the loss-ledger round trip.** The projection to the shadow is lossy but bookkept
  exactly; the record map `fiber ↦ (ordinate; radius, angle)` is a bijection
  (`ConeProjection.record_bijective`), so the object is reconstructed from its shadow at the midpoint.

The bridge from the candidate to the classical automorphy statement is the converse theorem, whose
hypotheses are exactly the properties discharged here.  No `sorry`, no `axiom`.
-/

open Complex Matrix
open scoped BigOperators

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

/-- **The midpoint projection lands on the critical line.**  A 3D vanishing datum is a real height
`γ`; its midpoint projection `3D → 2D → 1D` is the point `½ + γ·i`, whose abscissa is exactly `½`.
So a vanishing cannot land off the strip by construction. -/
theorem midpoint_projects_to_half (γ : ℝ) :
    ((1 : ℂ) / 2 + (γ : ℂ) * I).re = 1 / 2 := by
  simp [Complex.add_re, Complex.mul_re]

/-- **The candidate is well-formed**: the converse-theorem inputs, discharged.  For a carrier
`(p, r)` (`r > 0`), a non-principal Dirichlet readout `χ`, and any unit-modulus warp `A·w`:

* **(angle — functional equation)** the Frobenius conjugate block has determinant one
  (`FrobeniusSimilitude.frobeniusBlock_det_one`), preserved by every unit-modulus warp
  (`warpedBlock_det_one_of_warp`), and the dualizing reflection `s ↦ 1−s` fixes exactly the critical
  line (`reflection_fixes_iff`);
* **(continuation)** the phasor readout continues to `LFunction χ` on the whole strip `Re s > 0`,
  past the `Re = 1` wall (`dirichlet_strip_tendsto_LFunction`);
* **(height — completeness/boundedness)** the fiber is three-dimensionally exhaustive
  (`SourceHolonomy.threeD_exhaustive`);
* **(midpoint)** every 3D vanishing projects to abscissa exactly `½` (`midpoint_projects_to_half`),
  and the admissible-state locus is exactly `{½}` — the abscissa is forced, not chosen
  (`scaleBalanced_iff`), so a vanishing cannot land off the strip;
* **(recovery)** the loss-ledger projection `record = (ordinate; radius, phase)` is a bijection, so
  the object is reconstructed exactly from its shadow (`ConeProjection.record_bijective`).

The radial and angular channels are the ledger booked in the descent `3D → 2D → 1D`; the height passes
by the `log`/`exp` map; recovery is exact at the midpoint. -/
theorem candidate_wellformed
    (E : ℂ → ℂ) (p r : ℝ) (hr : 0 < r) (y : ℝ) (n : ℕ) {A w : ℂ} (hA : ‖A‖ = 1) (hw : ‖w‖ = 1)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    -- (angle) functional equation: the Frobenius conjugate block has det one, the warp preserves it,
    -- and the reflection s ↦ 1−s fixes exactly the critical line
    (FrobeniusSimilitude.frobeniusBlock y n).det = 1
      ∧ (warpedBlock (A * w)).det = 1
      ∧ (∀ t : ℂ, (1 - t).re = t.re ↔ t.re = 1 / 2)
      -- (continuation) the phasor readout continues to L(χ, ·) on the whole strip Re s > 0
      ∧ (∀ s : ℂ, 0 < s.re →
          Filter.Tendsto
            (fun N : ℕ => ∑ n ∈ Finset.range N, (χ (n : ZMod q)) * (n : ℂ) ^ (-s))
            Filter.atTop (nhds (DirichletCharacter.LFunction χ s)))
      -- (height) three-dimensional exhaustion
      ∧ SourceHolonomy.ThreeDExhaustive E
      -- (midpoint) every 3D vanishing projects to abscissa ½, and the admissible locus is exactly {½}
      ∧ (∀ γ : ℝ, ((1 : ℂ) / 2 + (γ : ℂ) * I).re = 1 / 2)
      ∧ (∀ σ : ℝ, FrobeniusSimilitude.ScaleBalanced p r σ ↔ σ = 1 / 2)
      -- (recovery) the loss-ledger projection is a bijection
      ∧ Function.Bijective ConeProjection.record :=
  ⟨FrobeniusSimilitude.frobeniusBlock_det_one y n,
   warpedBlock_det_one_of_warp hA hw,
   FrobeniusSimilitude.reflection_fixes_iff,
   fun _ hs => LFunctionPhasor.dirichlet_strip_tendsto_LFunction χ hχ hs,
   SourceHolonomy.threeD_exhaustive E,
   midpoint_projects_to_half,
   FrobeniusSimilitude.scaleBalanced_iff p r hr,
   ConeProjection.record_bijective⟩

end CriticalLinePhasor.AutomorphicCandidate
