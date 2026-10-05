import RequestProject.XiJetsArithmetic
import RequestProject.RiemannHypothesisBridge

/-!
# Mathlib's `RiemannHypothesis` from one assumption: the pencil's positivity (ledger 932)

The one assumption, `PencilPositivity`, is the sign condition of the harmonic pencil's Hermitian
(Pascal–Hankel) form at every anchor `s = σ₀ + iγ` with `1 < σ₀ < 3/2`.  Its entries `jetValueP`
are built from `1/s`, `1/(s − 1)`, `log π`, the jets of `½Γ′/Γ(·/2)` and `Σ Λ(n)(log n)^m n^{−s}`,
all in the half-plane of absolute convergence.  No zero of `ζ` appears in it; every instance
(fixed `γ`, `σ₀`, `R`) is a finite inequality between absolutely convergent prime sums.

* `riemannHypothesis_of_pencilPositivity` — the assumption gives Mathlib's `RiemannHypothesis`,
  through the positivity door compiled in ledger 595 and `RHBridge.no_offline_zeros_implies_rh`.

No `sorry`, no `axiom`.
-/

open Complex

namespace PencilPositivityRH

open CriticalLinePhasor.ContourArgument

/-- **The one assumption**: the pencil's Hermitian form is nonnegative at every anchor
`σ₀ + iγ` with `1 < σ₀ < 3/2`, for every polynomial `R` with `R(0) = 0`. -/
def PencilPositivity : Prop :=
  ∀ γ σ₀ : ℝ, 1 < σ₀ → σ₀ < 3 / 2 → ∀ R : Polynomial ℂ, R.coeff 0 = 0 →
    0 ≤ (∑ j ∈ Finset.range (R.natDegree + 1), ∑ k ∈ Finset.range (R.natDegree + 1),
        ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
          * jetValueP ((σ₀ : ℂ) + (γ : ℂ) * I) ((2 * σ₀ - 1 : ℝ) : ℂ)
              (2 * R.natDegree + 2) j k).re

/-- **`RiemannHypothesis` from the pencil's positivity.** -/
theorem riemannHypothesis_of_pencilPositivity (h : PencilPositivity) : RiemannHypothesis :=
  RHBridge.no_offline_zeros_implies_rh (online_of_prime_jets_nonneg h)

end PencilPositivityRH

#print axioms PencilPositivityRH.riemannHypothesis_of_pencilPositivity
