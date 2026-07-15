import RequestProject.GlobalHelixCPSFullCompletion
import RequestProject.GlobalHelixFiniteTensorEulerZeroMode

/-!
# Completed three-dimensional CPS readouts

This file collects the two completed carrier constructions at the point where all of their Lean
proofs meet.

* The fixed-completion theorem identifies both the primal and contragredient three-dimensional
  banks with the prescribed conductor and Deligne Gamma-product readouts.
* The finite tensor-Euler theorem uses one zero-mode-free three-dimensional source throughout: its
  scalar projection, reciprocal-height reflection, Euler readout, entire Mellin transform,
  vertical-strip bounds, and functional equation are fields of one assembled result.

No identification or chart-conversion proposition is left as a theorem parameter.
-/

open Complex Set MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

/-- Prescribed standard completion data, with its domain facts carried as data. -/
structure CPSCompletionClock where
  conductor : ℝ
  conductor_pos : 0 < conductor
  shifts : List ℂ
  shifts_nonempty : shifts ≠ []

/-- A point in the common initial half-plane of the primal and contragredient readouts. -/
structure CPSCompletionPoint
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (clock : CPSCompletionClock) where
  s : ℂ
  shifts_pos : ∀ μ ∈ clock.shifts, 0 < (s + μ).re
  primal_dirichlet :
    ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re
  dual_dirichlet :
    ((Fintype.card ι + W.dualExponent : ℕ) : ℝ) + 1 < s.re

/-- The reciprocal-height contragredient 3D bank has the prescribed completed Mellin readout. -/
theorem cpsPolynomialFullDual3D_initialIdentification
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hμ : ∀ μ ∈ μs, 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.dualExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)) s =
      cpsPolynomialFullDualCompletedReadout W C μs s := by
  rw [← cpsPolynomialFullDual_initialIdentification W C hC μs hne s hμ hs]
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hxpos : 0 < x := Set.mem_Ioi.mp hx
  change ((x : ℂ) ^ (s - 1)) •
      cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x) =
    ((x : ℂ) ^ (s - 1)) •
      CarrierTheta.theta (cpsPolynomialDualCoeff W)
        (conductorScaledCompletionKernelLog C μs) x
  rw [cpsPolynomialFullDual3DTransformedReadout_eq_theta_one_div W C μs
    (one_div_pos.mpr hxpos)]
  simp

/-- Both prescribed Gamma-product completions are read directly from their 3D banks. -/
theorem cpsPolynomialFullCompletion3D_identification
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (clock : CPSCompletionClock) (point : CPSCompletionPoint W clock) :
    mellin (cpsPolynomialFullPrimal3DBankReadout
        W clock.conductor clock.shifts) point.s =
      cpsPolynomialFullPrimalCompletedReadout
        W clock.conductor clock.shifts point.s ∧
    mellin (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout
        W clock.conductor clock.shifts (1 / x)) point.s =
      cpsPolynomialFullDualCompletedReadout
        W clock.conductor clock.shifts point.s := by
  exact ⟨cpsPolynomialFullPrimal3D_initialIdentification W
      clock.conductor clock.conductor_pos clock.shifts clock.shifts_nonempty point.s
      point.shifts_pos point.primal_dirichlet,
    cpsPolynomialFullDual3D_initialIdentification W
      clock.conductor clock.conductor_pos clock.shifts clock.shifts_nonempty point.s
      point.shifts_pos point.dual_dirichlet⟩

/--
The all-twist CPS capstone over the actual polynomial radial Satake input.

For every twist degree in the CPS range and every primal/contragredient polynomial Satake pair
`W`, this single result packages:

* reciprocal-height reflection of the radial three-dimensional banks;
* identification of both prescribed conductor/Gamma-product three-dimensional Mellin projections
  with their completed Dirichlet readouts; and
* the full analytic niceness and functional equation of the strong pair built from the same
  primal and contragredient coefficient datum `W`.

Thus the completion clock, initial-half-plane identification, continuation data, strip bounds,
reflection, and all twists are exposed without changing the underlying Satake input.
-/
theorem cpsPolynomialAllTwists_fullCompletion3D_unified
    (r : ℕ) : ∀ m : ℕ, 1 ≤ m → m < r → ∀ W : CPSPolynomialTwist r m,
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
        (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s)) := by
  intro m hm hmr W clock point
  have htwist := cpsPolynomialAllTwists_payload r m hm hmr W
  have hcompletion := cpsPolynomialFullCompletion3D_identification W clock point
  exact ⟨htwist.1, hcompletion.1, hcompletion.2, htwist.2⟩

/--
One-source unification of the finite tensor-Euler 3D bank.

The first clause identifies the scalar field of the strong pair with the projection of the actual
3D bank.  The remaining clauses prove, for that same source, reciprocal-height reflection, exact
Euler/completion identification, entirety, vertical-strip bounds, and the global functional
equation.
-/
theorem finiteTensorEulerZeroMode3D_unified
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) (c : ℝ) (hc : 0 < c) :
    let P := finiteTensorEulerZeroModeStrongFEPair S W q N hq c hc
    (∀ x : ℝ, 0 < x →
      P.f x = finiteTensorEulerZeroMode3DBankReadout S W q N c x) ∧
    (∀ x : ℝ, 0 < x →
      finiteTensorEulerZeroMode3DBankReadout S W q N c x =
        ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          finiteTensorEulerZeroMode3DTransformedReadout S W q N c x) ∧
    (∀ s : ℂ,
      P.Λ s = finiteTensorEulerTruncatedDirichletReadout S W q N s *
        mellin (zeroModeGaussianKernel c) s) ∧
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  dsimp only
  let P := finiteTensorEulerZeroModeStrongFEPair S W q N hq c hc
  have hnice := finiteTensorEulerZeroMode_twistedNiceness S W q N hq c hc
  refine ⟨?_, ?_, ?_, hnice.1, hnice.2.1, hnice.2.2.1, hnice.2.2.2.1,
    hnice.2.2.2.2⟩
  · intro x hx
    change indexedZeroModeGaussianTheta
        (finiteTensorEulerSeedAmplitude S W N)
        (finiteTensorEulerGaussianHeight S q N) c x =
      indexedZeroModeGaussian3DBankReadout
        (finiteTensorEulerSeedAmplitude S W N)
        (finiteTensorEulerGaussianHeight S q N) c x
    exact (indexedZeroModeGaussian3DBankReadout_eq_theta
      (finiteTensorEulerSeedAmplitude S W N)
      (finiteTensorEulerGaussianHeight S q N)
      (finiteTensorEulerGaussianHeight_pos S q N hq) c hx).symm
  · intro x hx
    exact finiteTensorEulerZeroMode3D_globalHelixReflection S W q N hq hc hx
  · intro s
    exact finiteTensorEulerZeroMode_initialIdentification S W q N hq c hc s

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullDual3D_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullCompletion3D_identification
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialAllTwists_fullCompletion3D_unified
#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorEulerZeroMode3D_unified
