import RequestProject.GlobalHelixBilateralTensorCompletion
import RequestProject.GlobalHelixFiniteGaussianStrongFE

/-!
# Finite bilateral tensor-Euler boxes as strong 3D helix sources

The finite index type is a symmetric box in the integral exponent lattice.  Negation stays inside
the box, so the bilateral tensor-Euler completion restricts to a finite Gaussian bank with the
same reciprocal-height and dual-amplitude identities as the full lattice.
-/

open Real Complex

namespace CriticalLinePhasor.GlobalHelix

/-- Integral exponents in the symmetric interval `[-N, N]`. -/
abbrev SymmetricExponentBox (N : ℕ) := ↥(Finset.Icc (-(N : ℤ)) (N : ℤ))

noncomputable instance symmetricExponentBoxFintype (N : ℕ) :
    Fintype (SymmetricExponentBox N) := Fintype.ofFinite _

/-- Negation preserves a symmetric exponent interval. -/
def symmetricExponentBoxNegEquiv (N : ℕ) :
    SymmetricExponentBox N ≃ SymmetricExponentBox N where
  toFun k := ⟨-k.1, by
    have hk : -(N : ℤ) ≤ k.1 ∧ k.1 ≤ (N : ℤ) := by
      simpa only [Finset.mem_Icc] using k.property
    rw [Finset.mem_Icc]
    exact ⟨by simpa using neg_le_neg hk.2, by simpa using neg_le_neg hk.1⟩⟩
  invFun k := ⟨-k.1, by
    have hk : -(N : ℤ) ≤ k.1 ∧ k.1 ≤ (N : ℤ) := by
      simpa only [Finset.mem_Icc] using k.property
    rw [Finset.mem_Icc]
    exact ⟨by simpa using neg_le_neg hk.2, by simpa using neg_le_neg hk.1⟩⟩
  left_inv k := Subtype.ext (neg_neg k.1)
  right_inv k := Subtype.ext (neg_neg k.1)

@[simp] theorem symmetricExponentBoxNegEquiv_coe (N : ℕ)
    (k : SymmetricExponentBox N) :
    ((symmetricExponentBoxNegEquiv N k : SymmetricExponentBox N) : ℤ) = -(k : ℤ) := rfl

/-- A finite symmetric box of exponent vectors over the selected Euler places. -/
abbrev FiniteExponentBox {V : Type*} (S : Finset V) (N : ℕ) :=
  (v : S) → SymmetricExponentBox N

noncomputable instance finiteExponentBoxFintype {V : Type*} (S : Finset V) (N : ℕ) :
    Fintype (FiniteExponentBox S N) := Fintype.ofFinite _

/-- Pointwise negation on a finite symmetric exponent box. -/
def finiteExponentBoxNegEquiv {V : Type*} (S : Finset V) (N : ℕ) :
    FiniteExponentBox S N ≃ FiniteExponentBox S N where
  toFun k v := symmetricExponentBoxNegEquiv N (k v)
  invFun k v := symmetricExponentBoxNegEquiv N (k v)
  left_inv k := by
    funext v
    exact (symmetricExponentBoxNegEquiv N).left_inv (k v)
  right_inv k := by
    funext v
    exact (symmetricExponentBoxNegEquiv N).right_inv (k v)

/-- Forget the finite-box bounds and read an integral exponent vector. -/
def finiteExponentBoxValue {V : Type*} {S : Finset V} {N : ℕ}
    (k : FiniteExponentBox S N) : (v : S) → ℤ :=
  fun v => (k v : ℤ)

@[simp] theorem finiteExponentBoxValue_neg {V : Type*} (S : Finset V) (N : ℕ)
    (k : FiniteExponentBox S N) :
    finiteExponentBoxValue (finiteExponentBoxNegEquiv S N k) =
      -finiteExponentBoxValue k := by
  funext v
  rfl

@[simp] theorem finiteExponentBoxValue_neg_symm {V : Type*} (S : Finset V) (N : ℕ)
    (k : FiniteExponentBox S N) :
    finiteExponentBoxValue ((finiteExponentBoxNegEquiv S N).symm k) =
      -finiteExponentBoxValue k := by
  funext v
  rfl

/-- The bilateral tensor-Euler completion restricted to a finite symmetric exponent box. -/
noncomputable def finiteTensorEulerGaussianAmplitude
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (N : ℕ) :
    FiniteExponentBox S N → ℂ :=
  fun k => bilateralTensorEulerCompletionAmplitude S W q (finiteExponentBoxValue k)

/-- Euler height restricted to a finite symmetric exponent box. -/
noncomputable def finiteTensorEulerGaussianHeight
    {V : Type*} (S : Finset V) (q : V → ℝ) (N : ℕ) :
    FiniteExponentBox S N → ℝ :=
  fun k => bilateralEulerHeight S q (finiteExponentBoxValue k)

theorem finiteTensorEulerGaussianHeight_pos
    {V : Type*} (S : Finset V) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) (k : FiniteExponentBox S N) :
    0 < finiteTensorEulerGaussianHeight S q N k :=
  bilateralEulerHeight_pos S q hq (finiteExponentBoxValue k)

theorem finiteTensorEulerGaussianHeight_neg
    {V : Type*} (S : Finset V) (q : V → ℝ) (N : ℕ)
    (k : FiniteExponentBox S N) :
    finiteTensorEulerGaussianHeight S q N
        ((finiteExponentBoxNegEquiv S N).symm k) =
      (finiteTensorEulerGaussianHeight S q N k)⁻¹ := by
  unfold finiteTensorEulerGaussianHeight
  rw [finiteExponentBoxValue_neg_symm, bilateralEulerHeight_neg]

theorem gaussianPoissonDualAmplitude_finiteTensorEuler
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) (k : FiniteExponentBox S N) :
    gaussianPoissonDualAmplitude
        (finiteTensorEulerGaussianAmplitude S W q N)
        (finiteTensorEulerGaussianHeight S q N)
        (finiteExponentBoxNegEquiv S N) k =
      finiteTensorEulerGaussianAmplitude S W q N k := by
  unfold finiteTensorEulerGaussianAmplitude finiteTensorEulerGaussianHeight
  change
    gaussianPoissonDualAmplitude
        (bilateralTensorEulerCompletionAmplitude S W q)
        (bilateralEulerHeight S q) (negExponentEquiv S)
        (finiteExponentBoxValue k) =
      bilateralTensorEulerCompletionAmplitude S W q (finiteExponentBoxValue k)
  exact gaussianPoissonDualAmplitude_bilateralGaussianCompletion
    S q hq (bilateralTensorEulerSeed S W) (finiteExponentBoxValue k)

/-- The finite tensor-Euler source, constructed first as an enveloped 3D Gaussian helix bank. -/
noncomputable def finiteTensorEulerEnveloped3DBankReadout
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (N : ℕ) (x : ℝ) : ℂ :=
  finiteEnvelopedGaussian3DBankReadout
    (finiteTensorEulerGaussianAmplitude S W q N)
    (finiteTensorEulerGaussianHeight S q N) x

/-- The globally reflected/sheared finite tensor-Euler 3D bank. -/
noncomputable def finiteTensorEulerEnveloped3DTransformedReadout
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (N : ℕ) (x : ℝ) : ℂ :=
  finiteEnvelopedGaussian3DTransformedReadout
    (finiteTensorEulerGaussianAmplitude S W q N)
    (finiteTensorEulerGaussianHeight S q N)
    (finiteExponentBoxNegEquiv S N) x

/-- Exact reflection of the finite completed tensor-Euler 3D bank. -/
theorem finiteTensorEulerEnveloped3D_globalHelixReflection
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) {x : ℝ} (hx : 0 < x) :
    finiteTensorEulerEnveloped3DBankReadout S W q N x =
      ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        finiteTensorEulerEnveloped3DTransformedReadout S W q N x := by
  exact finiteEnvelopedGaussian3D_globalHelixReflection
    (finiteTensorEulerGaussianAmplitude S W q N)
    (finiteTensorEulerGaussianHeight S q N)
    (finiteExponentBoxNegEquiv S N)
    (finiteTensorEulerGaussianHeight_pos S q N hq)
    (finiteTensorEulerGaussianHeight_neg S q N) hx

/-- The finite symmetric tensor-Euler 3D bank as a strong Mellin functional-equation pair. -/
noncomputable def finiteTensorEulerStrongFEPair
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) : StrongFEPair ℂ :=
  finiteEnvelopedGaussianStrongFEPair
    (finiteTensorEulerGaussianAmplitude S W q N)
    (finiteTensorEulerGaussianHeight S q N)
    (finiteExponentBoxNegEquiv S N)
    (finiteTensorEulerGaussianHeight_pos S q N hq)
    (finiteTensorEulerGaussianHeight_neg S q N)
    (gaussianPoissonDualAmplitude_finiteTensorEuler S W q N hq)

/-- Global twisted niceness for every finite symmetric tensor-Euler exponent box. -/
theorem finiteTensorEuler_twistedNiceness
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) :
    let P := finiteTensorEulerStrongFEPair S W q N hq
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  exact finiteEnvelopedGaussian_twistedNiceness
    (finiteTensorEulerGaussianAmplitude S W q N)
    (finiteTensorEulerGaussianHeight S q N)
    (finiteExponentBoxNegEquiv S N)
    (finiteTensorEulerGaussianHeight_pos S q N hq)
    (finiteTensorEulerGaussianHeight_neg S q N)
    (gaussianPoissonDualAmplitude_finiteTensorEuler S W q N hq)

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.finiteExponentBoxValue_neg
#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorEulerGaussianHeight_neg
#print axioms CriticalLinePhasor.GlobalHelix.gaussianPoissonDualAmplitude_finiteTensorEuler
#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorEulerEnveloped3D_globalHelixReflection
#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorEulerStrongFEPair
#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorEuler_twistedNiceness
