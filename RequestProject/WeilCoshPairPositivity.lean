import Mathlib
import RequestProject.CoshBalance
import RequestProject.ZetaZeroDefs
import RequestProject.GaussianDetectorPair
-- import RequestProject.RiemannHypothesisBridge

/-!
# Cosh separation + Weil vanishing target (cosh-pair side only)

## Architecture

This file owns two things and ONLY two things:

1. **Cosh separation (proved here / in `GaussianDetectorPair.lean`).**
   Off-line σ ≠ CoshBalance ⟹ `gaussianPairDefect σ ≠ 0`. This is pure cosh
   geometry: the cosh detector pair anchored at `π/6` and `1 − π/6`
   reads `1/2` as the unique balance point. The Gaussian-weighted
   squared difference factors as `4·sinh²((1/2 − π/6)·t)·sinh²((β − 1/2)·t)·ψ²`,
   strictly positive on a positive-measure set whenever `β ≠ CoshBalance`.

2. **`WeilVanishesOnZeros` Prop — the cosh-side target.**
   `∀ ρ ∈ NontrivialZeros, gaussianPairDefect ρ.re = 0`. With the proved
   one-direction `re_half_of_gaussianPairDefect_zero` in
   `GaussianDetectorPair.lean`, it puts every zero on the line. The
   substantive content that would close `WeilVanishesOnZeros` is the Weil
   positivity criterion at our test (cf. `WeilUnconditionalRHEndpoint.lean`,
   `PerZeroForcing_target`).

The legacy name `pair_defect_vanishes_at_zeros` is preserved as a thin
alias for backward compatibility with downstream files that still
reference it.

It documents the propositional shape of the cosh-side endpoint.
-/

open Real Complex

noncomputable section

namespace ZD

namespace WeilPositivity

/-- **Cosh separation (nonzero form).** Off-line σ ≠ CoshBalance yields a nonzero
Gaussian pair defect. Pure cosh geometry. -/
theorem gaussianPairDefect_nonzero_of_ne_half {σ : ℝ} (hσ : σ ≠ CoshBalance) :
    gaussianPairDefect σ ≠ 0 :=
  ne_of_gt (gaussianPairDefect_pos_offline hσ)

/-- **Cosh separation (positivity form).** Off-line σ ≠ CoshBalance yields a
strictly positive Gaussian pair defect. Pure cosh geometry; identical
content to `gaussianPairDefect_pos_offline`, exposed under the
architecture-aligned name. -/
theorem gaussianPairDefect_pos_of_ne_half {σ : ℝ} (hσ : σ ≠ CoshBalance) :
    0 < gaussianPairDefect σ :=
  gaussianPairDefect_pos_offline hσ

/-- **Weil vanishing TARGET.**

At every nontrivial ζ zero ρ, the Gaussian pair defect at `β = ρ.re`
vanishes. By the proved one-direction `re_half_of_gaussianPairDefect_zero`
(`GaussianDetectorPair.lean`), it gives `∀ ρ, ρ.re = CoshBalance`. The cosh
side is a CLASSIFIER, not a witness.

This Prop is the input the cosh-side bridge consumes; closing it requires
Weil-criterion-level analytic content. -/
def WeilVanishesOnZeros : Prop :=
  ∀ ρ : ℂ, ρ ∈ NontrivialZeros → gaussianPairDefect ρ.re = 0

/-- **Backward-compatibility alias.** The old name
`pair_defect_vanishes_at_zeros` is preserved as an alias for
`WeilVanishesOnZeros` so downstream code continues to typecheck. New
code should use `WeilVanishesOnZeros`. -/
def pair_defect_vanishes_at_zeros : Prop := WeilVanishesOnZeros

#print axioms gaussianPairDefect_nonzero_of_ne_half
#print axioms gaussianPairDefect_pos_of_ne_half

end WeilPositivity

end ZD

end
