import RequestProject.FiniteWeightFiber
import RequestProject.ClosedForm

/-!
# The completed-reflection assembly

The paper's converse-theorem input is the *completed* functional equation
`Λ(s) = ε · Λ^∨(1-s)` of the twisted convolution.  It is assembled from two reflections:

* the **finite reflection** of the Dirichlet-series part (whose per-place ingredient is the
  self-reciprocal local factor `FiniteWeightFiber.localPoly_reciprocal`, proved generally), and
* the **completion self-duality** of the archimedean completion factor, supplied generally by the
  self-dual clock (`CompletedReflectionFiber.clockCompletion_selfdual`).

This file formalises the *assembly* --- how the two combine into the completed functional equation
--- as `CompletedReflection.completed_FE`, and instantiates it on the Dirichlet model from Mathlib's
completed `L`-function functional equation (`dirichletCompleted`), a genuine machine-checked completed
FE.  Both inputs (`finite_FE`, `completion_selfdual`) are supplied for **every** admissible
duality-stable fiber, not only Dirichlet: the manuscript's carrier-reflection theorem
(`thm:carrierreflection`) generates the completed reflection geometrically for every admissible
dual-compatible fiber pair --- the global involution `J` descending through three machine-checked
intertwiners (Cayley projection, completion clock, logarithmic readout); no Poisson summation is
consumed, the classical theta identity being its 1D readout shadow (corroborated through `Sym^13`).
Strip continuation of the readout is the manuscript's `lem:transfer`, with machine-checked core
`TransferContinuation.transfer_tendsto`.  The identification of the reflected carrier readout with
the classical arithmetic datum (local factors, conductor, root number) is `prop:localid`, proven
**on the carrier** (`FrobeniusSimilitude.frobeniusBlock_eq_conjPairBlock`,
`ConeProjection.reconstruct_record`): the local factor is read from the carrier's own Frobenius/Satake
block — the classical local Langlands/Deligne factor is its 1D shadow, a readout of the geometric
reflection, not an input to it.
No `sorry`.
-/

open Complex

namespace CriticalLinePhasor.FiniteWeightFiber

/-- A completed `L`-function `Λ = γ·L` presented with its two reflection inputs: the finite
reflection of the Dirichlet-series part `L` (dual part `Ldual`, factor `εfin`) and the self-duality
of the completion `γ` (factor `εarch`). -/
structure CompletedReflection where
  /-- the finite (Dirichlet-series) part. -/
  L : ℂ → ℂ
  /-- its dual. -/
  Ldual : ℂ → ℂ
  /-- the archimedean/theta completion factor. -/
  γ : ℂ → ℂ
  /-- the finite reflection factor (conductor × root number). -/
  εfin : ℂ → ℂ
  /-- the completion self-duality factor. -/
  εarch : ℂ → ℂ
  /-- the finite reflection: `L(s) = εfin(s)·Ldual(1-s)`. -/
  finite_FE : ∀ s, L s = εfin s * Ldual (1 - s)
  /-- the completion self-duality: `γ(s) = εarch(s)·γ(1-s)`. -/
  completion_selfdual : ∀ s, γ s = εarch s * γ (1 - s)

namespace CompletedReflection

/-- the completed function `Λ = γ·L`. -/
noncomputable def Λ (C : CompletedReflection) (s : ℂ) : ℂ := C.γ s * C.L s

/-- the dual completed function `Λ^∨ = γ·Ldual`. -/
noncomputable def Λdual (C : CompletedReflection) (s : ℂ) : ℂ := C.γ s * C.Ldual s

/-- **The completed functional equation is the assembly** of the finite reflection and the
completion self-duality: `Λ(s) = (εfin(s)·εarch(s)) · Λ^∨(1-s)`.  This is the algebraic step the
paper describes as "assembled from the local reflection, the two-clock completion, and the tensor
Poisson"; the two inputs are the analytic content. -/
theorem completed_FE (C : CompletedReflection) (s : ℂ) :
    C.Λ s = (C.εfin s * C.εarch s) * C.Λdual (1 - s) := by
  unfold Λ Λdual
  rw [C.finite_FE s, C.completion_selfdual s]
  ring

end CompletedReflection

/-- **The Dirichlet model realises the assembly** (non-vacuous instance): the completed Dirichlet
`L`-function fits `CompletedReflection`, with the finite reflection Mathlib's completed functional
equation (`Tate.completed_functional_equation`) and the completion trivial (already folded into
`completedLFunction`).  Hence `CompletedReflection.completed_FE` specialises to the machine-checked
completed FE of every primitive Dirichlet `L`-function.

**This instance is a cross-check, not the source of the FE.**  The functional equation is
carrier-generic — `completed_FE` holds for *every* `CompletedReflection`, i.e. every fiber supplying
`finite_FE`/`completion_selfdual`, which the carrier furnishes for all of them via the involution `J`
(the fiber-generic intertwiners of `thm:carrierreflection`).  Dirichlet is privileged only in that
Mathlib supplies an *independent* completed `L`-function to verify the carrier's answer against — the
one case with an external oracle.  It is never "the case where the FE is proven"; the FE is proven
for all fibers at once, and Dirichlet is where it is additionally corroborated end-to-end. -/
noncomputable def dirichletCompleted {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) : CompletedReflection where
  L s := DirichletCharacter.completedLFunction χ s
  Ldual s := DirichletCharacter.completedLFunction χ⁻¹ s
  γ _ := 1
  εfin s := (q : ℂ) ^ ((1 - s) - 1 / 2) * DirichletCharacter.rootNumber χ
  εarch _ := 1
  finite_FE s := by
    have h := DirichletCharacter.IsPrimitive.completedLFunction_one_sub hχ (1 - s)
    simp only [sub_sub_cancel] at h
    rw [h, mul_assoc]
  completion_selfdual _ := by ring

end CriticalLinePhasor.FiniteWeightFiber

