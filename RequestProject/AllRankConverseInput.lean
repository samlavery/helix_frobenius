import RequestProject.CPSCompletionUnification3D

/-!
# The all-rank converse input: one theorem, every rank, every CPS twist

The program's route to every symmetric power, assembled as a single quantified
statement.  For **every** rank `r`, every twist degree `m` in the CPS range
`1 ≤ m < r`, and every polynomial Satake twist datum, simultaneously:

* the exact reciprocal-height reflection of the primal and contragredient 3D banks;
* the identification of both prescribed conductor/Gamma-product Mellin projections
  with their completed Dirichlet readouts on the initial half-plane;
* entirety of both completed transforms, vertical-strip bounds, and the functional
  equation of the strong pair.

This is the complete analytic input family of the Cogdell--Piatetski-Shapiro converse
theorem, compiled uniformly in the rank — no per-rank argument, no rank bound.

**Register.**  The reflection here is the carrier's own: the kernel is the self-dual
lattice theta, the height system is closed under reciprocals, and the contragredient
side is the transported dual bank — the fiber's native completion, in which the
functional equation holds at every rank by the compiled Poisson transport.  The
classical converse theorem (cited, not formalized) consumes such a family together
with the local identification of the candidate with `Sym^r π` (the paper's global
identification theorem).  The separation between this compiled completion and the
classical one-sided chart is the amplitude-exchange wall recorded in the standing-wave
campaign: one statement, the same from both sides.  No `axiom`, no `sorry`.
-/

namespace CriticalLinePhasor.AllRankConverseInput

open CriticalLinePhasor.GlobalHelix

/-- **The all-rank converse input.**  Every rank, every CPS twist degree, every twist
datum: reflection, both completed identifications, entirety, strip bounds, and the
functional equation — one quantified conclusion over all of them simultaneously. -/
theorem allRank_converseInput :
    ∀ r : ℕ, ∀ m : ℕ, 1 ≤ m → m < r → ∀ W : CPSPolynomialTwist r m,
      ∀ (clock : CPSCompletionClock) (point : CPSCompletionPoint W clock),
      (∀ x : ℝ, 0 < x →
        cpsPolynomialPrimal3DBankReadout W (1 / x) =
          (x : ℂ) * cpsPolynomialDual3DBankReadout W x) ∧
      mellin (cpsPolynomialFullPrimal3DBankReadout
          W clock.conductor clock.shifts) point.s =
        cpsPolynomialFullPrimalCompletedReadout
          W clock.conductor clock.shifts point.s ∧
      mellin (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout
          W clock.conductor clock.shifts (1 / x)) point.s =
        cpsPolynomialFullDualCompletedReadout
          W clock.conductor clock.shifts point.s ∧
      (let P := cpsPolynomialStrongFEPair W;
        Differentiable ℂ P.Λ ∧
        Differentiable ℂ P.symm.Λ ∧
        (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
          u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
        (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
          u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
        (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s)) :=
  fun r => cpsPolynomialAllTwists_fullCompletion3D_unified r

end CriticalLinePhasor.AllRankConverseInput

#print axioms CriticalLinePhasor.AllRankConverseInput.allRank_converseInput
