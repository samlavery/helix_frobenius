import Mathlib

/-!
# The weighted strand transformation law: the compiled degree-one harmonic modulation

Certifier (a) of the standing wave, fourth brick — the geometric source of nontrivial
root structure.  The unweighted strand `S(t) = ∑ e^{-πn²t}` transforms to itself
(`strandTheta_inv`, weight `1/2`, root number `1`).  The **degree-one harmonically
modulated strands** — Mathlib's odd Hurwitz pair

  `oddKernel a t  = ∑_{n ∈ ℤ} (n+a)·e^{-π(n+a)²t}`,
  `sinKernel a t  = ∑_{n ≥ 1} 2n·sin(2πna)·e^{-πn²t}`

— transformation law to **each other**, at shifted weight `3/2`:

* `sinKernel_inv` — `sin(1/t) = t^{3/2}·odd(t)`;
* `oddKernel_inv` — `odd(1/t) = t^{3/2}·sin(t)`.

This is the `d = 1` rung of the harmonic-modulation ladder (Hecke's identity
`FT(P·gauss) = i^{-d}·P·gauss`): the primal and dual kernels *differ*, the weight is
shifted by the harmonic degree, and the exchange closes only after two reflections —
exactly the `ε ≠ 1` two-kernel shape that even-rank rungs require, compiled at strand
level.  The Mellin side is also compiled upstream: `completedHurwitzZetaOdd` /
`completedSinZeta` carry the `Γℝ(s+1)` chart with the functional equations
`completedHurwitzZetaOdd_one_sub` and `completedSinZeta_one_sub` exchanging the pair.

Both lemmas are one-line consequences of Mathlib's
`oddKernel_functional_equation`; the value is the lattice transformation law normal form (the exact shape of
`matrixTheta_inv` and `strandTheta_inv`, with the reciprocal on the left), which is the
form the rank-uniform reduction consumes.  No `axiom`, no `sorry`.
-/

open Real HurwitzZeta

namespace CriticalLinePhasor.WeightedStrandTransformation

/-- **The weighted strand transformation law, sine side**: `sin(1/t) = t^{3/2}·odd(t)`. -/
theorem sinKernel_inv (a : UnitAddCircle) {t : ℝ} (ht : 0 < t) :
    sinKernel a t⁻¹ = t ^ ((3 : ℝ) / 2) * oddKernel a t := by
  have h := oddKernel_functional_equation a t
  rw [one_div, one_div] at h
  rw [h, ← mul_assoc,
    mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ht _)), one_mul]

/-- **The weighted strand transformation law, odd side**: `odd(1/t) = t^{3/2}·sin(t)`. -/
theorem oddKernel_inv (a : UnitAddCircle) {t : ℝ} (ht : 0 < t) :
    oddKernel a t⁻¹ = t ^ ((3 : ℝ) / 2) * sinKernel a t := by
  have h := oddKernel_functional_equation a t⁻¹
  rw [one_div] at h
  rw [h, one_div, inv_inv, Real.inv_rpow ht.le, inv_inv]

end CriticalLinePhasor.WeightedStrandTransformation

#print axioms CriticalLinePhasor.WeightedStrandTransformation.sinKernel_inv
#print axioms CriticalLinePhasor.WeightedStrandTransformation.oddKernel_inv
