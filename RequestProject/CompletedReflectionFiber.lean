import RequestProject.CompletedReflection
import RequestProject.ChiralityHB

/-!
# The general finite-weight-fiber completed reflection

`CompletedReflection.lean` derives the completed functional equation `completed_FE` from two inputs
(`finite_FE`, `completion_selfdual`) and instantiates it on the Dirichlet model (`dirichletCompleted`).
This file supplies the **general finite duality-stable fiber** instance of that assembly, wiring the two
inputs to the carrier's own proven theorems.

**Scope (important).**  Here `L(s) = localPoly(c^{s-1/2})` is the fiber's **local numerator** as a function
of `s` — NOT the global `L`-series `L(s, Sym^r π × σ)` (an infinite Euler product).  So `fiberCompleted`
certifies the fiber's admissible **local** completed reflection (fiber admissibility packaged at the
completed-object level); it is step (1) of the paper's `prop:completedFE`.  The **global** twisted functional
equation is NOT derived here and must not be read off `localPoly_reciprocal`: it requires the quantified
carrier-reflection / Poisson theorem `thm:carrierreflection` (step (2)), which is proven for the Dirichlet
model (Mathlib `completedLFunction_one_sub`) and otherwise verified numerically through `Sym^13`.

* the **finite reflection** `finite_FE` is `FiniteWeightFiber.localPoly_reciprocal` — the per-place
  functional equation of any duality-stable weight multiset — evaluated at the reflecting local variable
  `X(s) = c^{s-1/2}`, for which `X(1-s) = X(s)⁻¹` (`reflVar_one_sub`);
* the **completion self-duality** `completion_selfdual` is supplied by the **self-dual clock**
  `ChiralityHB.symClock` (`symClock_selfdual_modulus`): the completion is the clock at the reflecting
  argument times its `s ↦ 1-s` reflection, manifestly invariant under `s ↦ 1-s` (`clockCompletion_selfdual`).

`fiberCompleted` is the resulting `CompletedReflection`; `symTensorCompleted` is the `Sym^r π × σ` fiber
instance. No `axiom`, no `sorry`.
-/

open Complex CriticalLinePhasor.ChiralityHB
open scoped BigOperators

namespace CriticalLinePhasor.FiniteWeightFiber

variable {ι : Type*} [Fintype ι]

/-- The reflecting local variable `X(s) = c^{s-1/2}`, satisfying `X(1-s) = X(s)⁻¹`: the argument at
which `localPoly_reciprocal` becomes the `s ↦ 1-s` functional equation. -/
noncomputable def reflVar (c s : ℂ) : ℂ := c ^ (s - 1 / 2)

/-- `X(s) = c^{s-1/2} ≠ 0` for `c ≠ 0` (a `cpow` of a nonzero base is `exp`, never zero). -/
theorem reflVar_ne_zero {c : ℂ} (hc : c ≠ 0) (s : ℂ) : reflVar c s ≠ 0 := by
  rw [reflVar, Complex.cpow_def_of_ne_zero hc]
  exact Complex.exp_ne_zero _

/-- `X(1-s) = X(s)⁻¹`: the reflecting variable exchanges `s` and `1-s` with inversion. -/
theorem reflVar_one_sub {c : ℂ} (s : ℂ) :
    reflVar c (1 - s) = (reflVar c s)⁻¹ := by
  rw [reflVar, reflVar, show (1 - s) - 1 / 2 = -(s - 1 / 2) by ring, Complex.cpow_neg]

/-- **The self-dual completion clock.**  The self-dual clock `symClock α ℓ` (`ChiralityHB`) at the
reflecting argument `s-1/2`, times its `s ↦ 1-s` reflection.  Manifestly invariant under `s ↦ 1-s`. -/
noncomputable def clockCompletion (α : ℂ) (ℓ : ℝ) (s : ℂ) : ℂ :=
  symClock α ℓ (s - 1 / 2) * symClock α ℓ (1 / 2 - s)

/-- **The completion is self-dual**: `γ(s) = 1·γ(1-s)`.  The two symClock legs swap under `s ↦ 1-s`,
so the product is fixed — the archimedean completion self-duality `completed_FE` consumes, supplied by
the self-dual clock. -/
theorem clockCompletion_selfdual (α : ℂ) (ℓ : ℝ) (s : ℂ) :
    clockCompletion α ℓ s = 1 * clockCompletion α ℓ (1 - s) := by
  rw [one_mul, clockCompletion, clockCompletion,
    show (1 - s) - 1 / 2 = 1 / 2 - s by ring, show 1 / 2 - (1 - s) = s - 1 / 2 by ring]
  exact mul_comm _ _

/-- **The general fiber completed reflection.**  For any finite duality-stable weight fiber `W`, any
conductor base `c ≠ 0`, and any self-dual clock face `α` / rate `ℓ`, the completed object `Λ = γ·L`
with finite part `L(s) = localPoly(c^{s-1/2})` and completion the self-dual clock fits
`CompletedReflection`.  The finite reflection is `localPoly_reciprocal`; the completion self-duality is
the self-dual clock.  Hence `CompletedReflection.completed_FE` specialises to `W`. -/
noncomputable def fiberCompleted (W : FiniteWeightFiber ι) (c : ℂ) (hc : c ≠ 0)
    (α : ℂ) (ℓ : ℝ) : CompletedReflection where
  L s := W.localPoly (reflVar c s)
  Ldual s := W.localPoly (reflVar c s)
  γ s := clockCompletion α ℓ s
  εfin s := (-(reflVar c s)) ^ (Fintype.card ι)
  εarch _ := 1
  finite_FE s := by
    show W.localPoly (reflVar c s)
      = (-(reflVar c s)) ^ (Fintype.card ι) * W.localPoly (reflVar c (1 - s))
    rw [W.localPoly_reciprocal (reflVar_ne_zero hc s), reflVar_one_sub s]
  completion_selfdual s := clockCompletion_selfdual α ℓ s

/-- **The fiber's local completed reflection FE.**  Composing the finite reflection
(`localPoly_reciprocal`, via `finite_FE`) with the self-dual clock completion (`clockCompletion_selfdual`,
via `completion_selfdual`) through `CompletedReflection.completed_FE`:
`Λ(s) = (εfin(s)·εarch(s))·Λ^∨(1-s)` for the **local** object `Λ = γ·localPoly(c^{s-1/2})`.  This certifies
fiber admissibility; it is NOT the global twisted `L`-function FE (which needs the carrier-reflection /
Poisson theorem — see the module docstring). -/
theorem fiberCompleted_FE (W : FiniteWeightFiber ι) (c : ℂ) (hc : c ≠ 0) (α : ℂ) (ℓ : ℝ) (s : ℂ) :
    (fiberCompleted W c hc α ℓ).Λ s
      = ((fiberCompleted W c hc α ℓ).εfin s * (fiberCompleted W c hc α ℓ).εarch s)
        * (fiberCompleted W c hc α ℓ).Λdual (1 - s) :=
  CompletedReflection.completed_FE _ s

/-- **The `Sym^r π × σ` completed reflection**: `fiberCompleted` at the Rankin–Selberg tensor of the
symmetric-power fiber `symFiber r α` and any duality-stable twist fiber `Wσ`.  So the completed twisted
functional equation is a `CompletedReflection` for the whole converse-theorem twist family, wiring in
`localPoly_reciprocal` (finite) and the self-dual clock (completion). -/
noncomputable def symTensorCompleted (r : ℕ) (α : ℂ) (hα : ‖α‖ = 1)
    {κ : Type*} [Fintype κ] (Wσ : FiniteWeightFiber κ) (c : ℂ) (hc : c ≠ 0)
    (β : ℂ) (ℓ : ℝ) : CompletedReflection :=
  fiberCompleted (tensorFiber (symFiber r α hα) Wσ) c hc β ℓ

/-- **The `Sym^r π × σ` completed twisted reflection FE.**  The completed carrier readout of the
symmetric-power/twist fiber satisfies `Λ(s) = (εfin·εarch)(s)·Λ^∨(1-s)` — the carrier involution `J`,
**unconditional** for the whole converse-theorem twist family (any `r`, any duality-stable twist `Wσ`,
any conductor base `c ≠ 0` and clock `β, ℓ`), with **no** Dirichlet hypothesis.  This is the general-fiber
completed reflection of `prop:completedFE`; it reflects the completed carrier object `Λ = γ·localPoly`.
The identification of this carrier readout with the classical global `L(s, Sym^r π × σ)` is the separate,
Dirichlet-instantiated / numerically-calibrated step. -/
theorem symTensorCompleted_FE (r : ℕ) (α : ℂ) (hα : ‖α‖ = 1)
    {κ : Type*} [Fintype κ] (Wσ : FiniteWeightFiber κ) (c : ℂ) (hc : c ≠ 0)
    (β : ℂ) (ℓ : ℝ) (s : ℂ) :
    (symTensorCompleted r α hα Wσ c hc β ℓ).Λ s
      = ((symTensorCompleted r α hα Wσ c hc β ℓ).εfin s
          * (symTensorCompleted r α hα Wσ c hc β ℓ).εarch s)
        * (symTensorCompleted r α hα Wσ c hc β ℓ).Λdual (1 - s) :=
  CompletedReflection.completed_FE _ s

end CriticalLinePhasor.FiniteWeightFiber
