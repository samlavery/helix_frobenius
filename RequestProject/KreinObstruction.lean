import Mathlib

/-!
# The exact obstruction: an off-line pair spans a hyperbolic plane (ledger 1225)

The same-height partner pairing (`SameHeight.partner`, implemented by the area duality) gives the native
two-sided geometry a Hermitian pairing under which the dilations act as boosts. In any symmetric
realization an off-line zero-state `v_ρ` is self-orthogonal and can pair only with its same-height partner
`v_{ρ*}` (`SymPair.inner_eq_zero_unless_reflect`, in its form version). The Gram form of the pair is
therefore `!![0, k; conj k, 0]`.

* `pairForm x₁ x₂ = 2·Re(conj x₁ · k · x₂)`, that Gram form evaluated at `x₁ v_ρ + x₂ v_{ρ*}`.
* `hyperbolic_pair_negative`: if `k ≠ 0` (the pair is nondegenerately represented), the vector `(1, −conj k)`
  has `pairForm = −2|k|² < 0`. The form is INDEFINITE.
* `hyperbolic_pair_zero`: if `k = 0` the form vanishes on the pair (degenerate: the zero is not
  represented by a nonzero Hilbert state).

So in a single positive-definite space an off-line zero is either absent or null. The HP step on the
exhaustive native object is exactly DEFINITENESS of the same-height pairing on the span of all
zero-states. Nothing here decides it.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.KreinObstruction

/-- The Gram form of an off-line pair `{v_ρ, v_{ρ*}}`: `!![0, k; conj k, 0]` at `(x₁, x₂)`. -/
def pairForm (k x₁ x₂ : ℂ) : ℝ :=
  ((starRingEnd ℂ) x₁ * k * x₂ + (starRingEnd ℂ) x₂ * (starRingEnd ℂ) k * x₁).re

/-- **A nondegenerately represented off-line pair produces a negative direction.** -/
theorem hyperbolic_pair_negative {k : ℂ} (hk : k ≠ 0) :
    pairForm k 1 (-(starRingEnd ℂ) k) = -2 * Complex.normSq k ∧
      pairForm k 1 (-(starRingEnd ℂ) k) < 0 := by
  have hval : pairForm k 1 (-(starRingEnd ℂ) k) = -2 * Complex.normSq k := by
    unfold pairForm
    simp only [map_one, one_mul, map_neg, Complex.conj_conj, mul_one]
    rw [show k * -(starRingEnd ℂ) k + -k * (starRingEnd ℂ) k = -(2 * (k * (starRingEnd ℂ) k)) by ring,
      Complex.mul_conj]
    simp
  refine ⟨hval, ?_⟩
  rw [hval]
  have : 0 < Complex.normSq k := Complex.normSq_pos.mpr hk
  linarith

/-- **A degenerate pair is null.** -/
theorem hyperbolic_pair_zero (x₁ x₂ : ℂ) : pairForm 0 x₁ x₂ = 0 := by
  simp [pairForm]

end CriticalLinePhasor.KreinObstruction

end

#print axioms CriticalLinePhasor.KreinObstruction.hyperbolic_pair_negative
#print axioms CriticalLinePhasor.KreinObstruction.hyperbolic_pair_zero
