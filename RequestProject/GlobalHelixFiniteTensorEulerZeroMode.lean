import RequestProject.GlobalHelixFiniteTensorEulerStrongFE
import RequestProject.GlobalHelixZeroModeMellin

/-!
# Actual finite tensor-Euler banks with a zero-mode-free 3D completion

The primal amplitude is the original tensor-Euler seed, extended by zero to negative exponents.
The symmetric exponent box is used only to carry the reciprocal-height anti-helix bank.  Thus the
primal Mellin readout is the ordinary truncated Euler bank, not the bilateral fixed-point
completion.
-/

open Real Complex Filter Asymptotics MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

/-- The original tensor-Euler seed restricted to a finite symmetric exponent box. -/
noncomputable def finiteTensorEulerSeedAmplitude
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (N : ℕ) :
    FiniteExponentBox S N → ℂ :=
  fun k => bilateralTensorEulerSeed S W (finiteExponentBoxValue k)

/-- The actual truncated tensor-Euler source, constructed as a zero-mode-free 3D bank. -/
noncomputable def finiteTensorEulerZeroMode3DBankReadout
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (N : ℕ) (c x : ℝ) : ℂ :=
  indexedZeroModeGaussian3DBankReadout
    (finiteTensorEulerSeedAmplitude S W N)
    (finiteTensorEulerGaussianHeight S q N) c x

/-- The reciprocal-height sheared anti-helix bank of the actual truncated tensor-Euler source. -/
noncomputable def finiteTensorEulerZeroMode3DTransformedReadout
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (N : ℕ) (c x : ℝ) : ℂ :=
  indexedZeroModeGaussian3DTransformedReadout
    (finiteTensorEulerSeedAmplitude S W N)
    (finiteTensorEulerGaussianHeight S q N)
    (finiteExponentBoxNegEquiv S N) c x

/-- Exact 3D reflection of the actual truncated tensor-Euler source. -/
theorem finiteTensorEulerZeroMode3D_globalHelixReflection
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    finiteTensorEulerZeroMode3DBankReadout S W q N c x =
      ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        finiteTensorEulerZeroMode3DTransformedReadout S W q N c x := by
  exact indexedZeroModeGaussian3D_globalHelixReflection
    (finiteTensorEulerSeedAmplitude S W N)
    (finiteTensorEulerGaussianHeight S q N)
    (finiteExponentBoxNegEquiv S N)
    (finiteTensorEulerGaussianHeight_pos S q N hq)
    (finiteTensorEulerGaussianHeight_neg S q N) hc hx

/-- Strong Mellin pair of the actual finite tensor-Euler 3D bank and its dual. -/
noncomputable def finiteTensorEulerZeroModeStrongFEPair
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) (c : ℝ) (hc : 0 < c) : StrongFEPair ℂ :=
  finiteZeroModeGaussianStrongFEPair
    (finiteTensorEulerSeedAmplitude S W N)
    (finiteTensorEulerGaussianHeight S q N)
    (finiteExponentBoxNegEquiv S N)
    (finiteTensorEulerGaussianHeight_pos S q N hq)
    (finiteTensorEulerGaussianHeight_neg S q N) c hc

/-- The truncated tensor-Euler coefficient-height readout. -/
noncomputable def finiteTensorEulerTruncatedDirichletReadout
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (N : ℕ) (s : ℂ) : ℂ :=
  finiteIndexedDirichletReadout
    (finiteTensorEulerSeedAmplitude S W N)
    (finiteTensorEulerGaussianHeight S q N) s

/-- The primal readout uses only the nonnegative-orthant tensor-Euler coefficients. -/
theorem finiteTensorEulerSeedAmplitude_apply
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (N : ℕ)
    (k : FiniteExponentBox S N) :
    finiteTensorEulerSeedAmplitude S W N k =
      if ∀ v, 0 ≤ (finiteExponentBoxValue k) v then
        ∏ v : S, localEulerCoeff (W v) ((finiteExponentBoxValue k) v).toNat
      else 0 := by
  rfl

/-- Exact identification of the entire 3D Mellin transform with the actual truncated tensor-Euler
readout times the fixed zero-mode completion multiplier. -/
theorem finiteTensorEulerZeroMode_initialIdentification
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) (c : ℝ) (hc : 0 < c) (s : ℂ) :
    let P := finiteTensorEulerZeroModeStrongFEPair S W q N hq c hc
    P.Λ s = finiteTensorEulerTruncatedDirichletReadout S W q N s *
      mellin (zeroModeGaussianKernel c) s := by
  exact finiteZeroModeGaussian_initialIdentification
    (finiteTensorEulerSeedAmplitude S W N)
    (finiteTensorEulerGaussianHeight S q N)
    (finiteExponentBoxNegEquiv S N)
    (finiteTensorEulerGaussianHeight_pos S q N hq)
    (finiteTensorEulerGaussianHeight_neg S q N) c hc s

/-- Full twisted niceness of the actual truncated tensor-Euler 3D bank. -/
theorem finiteTensorEulerZeroMode_twistedNiceness
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) (c : ℝ) (hc : 0 < c) :
    let P := finiteTensorEulerZeroModeStrongFEPair S W q N hq c hc
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  exact finiteZeroModeGaussian_twistedNiceness
    (finiteTensorEulerSeedAmplitude S W N)
    (finiteTensorEulerGaussianHeight S q N)
    (finiteExponentBoxNegEquiv S N)
    (finiteTensorEulerGaussianHeight_pos S q N hq)
    (finiteTensorEulerGaussianHeight_neg S q N) c hc

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorEulerZeroMode3D_globalHelixReflection
#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorEulerZeroModeStrongFEPair
#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorEulerSeedAmplitude_apply
#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorEulerZeroMode_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorEulerZeroMode_twistedNiceness
