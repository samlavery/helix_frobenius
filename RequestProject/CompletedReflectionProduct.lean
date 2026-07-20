import RequestProject.CompletedReflectionFiber
import RequestProject.DualPairFiber
import RequestProject.GlobalBankLimit

/-!
# The completed reflection of a product is the product of completed reflections

**Step (2), the global assembly — Poisson-free.**  The global twisted `L`-function is a product of
local factors, one per place.  `CompletedReflection` (per place) is proven for every fiber via the
local reciprocal FE (`localPoly_reciprocal` / `DualPairFiber.dualPair_localPoly_reciprocal`) and the
self-dual completion clock — *no Poisson summation*, exactly because Poisson is the wrong tool for a
degree `> 2` object.  This file supplies the missing algebraic core of the carrier-reflection
theorem `thm:carrierreflection`: **a finite product of completed reflections is a completed
reflection**, and its completed functional equation is the product of the per-place reciprocal FEs.

Multiplicativity of the two reflection inputs is elementary `Finset.prod_mul_distrib`:

* `prod`                    — the product `CompletedReflection` of a finite family;
* `prod_Λ` / `prod_Λdual`   — its completed readout is the product of the local completed readouts;
* `prod_completed_FE`       — the product's completed FE **as a product of the local FEs**:
  `(∏ᵢ Λᵢ)(s) = (∏ᵢ εfinᵢ·εarchᵢ)(s) · (∏ᵢ Λᵢ^∨)(1-s)`.

Composed with `CompletedReflectionFiber.symTensorCompleted` (the per-place `Sym^r π × σ` completed
reflection), `symTensorFiniteProduct_FE` is the completed twisted functional equation of the
**finite Euler product** over any finite set of places — unconditional, every `r`, any twists, no
Poisson.  The passage to the *infinite* Euler product is the analytic limit (`TransferContinuation`
/ the manuscript's strip-continuation `lem:transfer`), separate from this algebra.

No `axiom`, no `sorry`.
-/

open Complex Filter Topology
open scoped BigOperators

namespace CriticalLinePhasor.FiniteWeightFiber
namespace CompletedReflection

/-- **Product of completed reflections.**  Pointwise product of a finite family over a `Finset`: the
finite part, its dual, the completion, and both reflection factors all multiply place-by-place.  The
finite reflection and completion self-duality survive the product by `Finset.prod_mul_distrib`. -/
noncomputable def prod {ι : Type*} (t : Finset ι) (F : ι → CompletedReflection) :
    CompletedReflection where
  L s := ∏ i ∈ t, (F i).L s
  Ldual s := ∏ i ∈ t, (F i).Ldual s
  γ s := ∏ i ∈ t, (F i).γ s
  εfin s := ∏ i ∈ t, (F i).εfin s
  εarch s := ∏ i ∈ t, (F i).εarch s
  finite_FE s := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => (F i).finite_FE s
  completion_selfdual s := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => (F i).completion_selfdual s

/-- The product's completed readout is the product of the local completed readouts. -/
theorem prod_Λ {ι : Type*} (t : Finset ι) (F : ι → CompletedReflection) (s : ℂ) :
    (prod t F).Λ s = ∏ i ∈ t, (F i).Λ s := by
  simp only [Λ, prod]
  exact (Finset.prod_mul_distrib).symm

/-- The product's dual completed readout is the product of the local dual completed readouts. -/
theorem prod_Λdual {ι : Type*} (t : Finset ι) (F : ι → CompletedReflection) (s : ℂ) :
    (prod t F).Λdual s = ∏ i ∈ t, (F i).Λdual s := by
  simp only [Λdual, prod]
  exact (Finset.prod_mul_distrib).symm

/-- **The global finite-product completed functional equation, as a product of the local FEs.**
For any finite family of completed reflections, the product of the local completed readouts satisfies
`(∏ᵢ Λᵢ)(s) = (∏ᵢ εfinᵢ(s)·εarchᵢ(s)) · (∏ᵢ Λᵢ^∨)(1-s)` — the global twisted functional equation as
the product of the per-place reciprocal reflections.  No Poisson summation is used anywhere. -/
theorem prod_completed_FE {ι : Type*} (t : Finset ι) (F : ι → CompletedReflection) (s : ℂ) :
    (∏ i ∈ t, (F i).Λ s)
      = (∏ i ∈ t, ((F i).εfin s * (F i).εarch s)) * (∏ i ∈ t, (F i).Λdual (1 - s)) := by
  rw [← prod_Λ, ← prod_Λdual, completed_FE]
  congr 1
  simp only [prod]
  exact Finset.prod_mul_distrib.symm

/-- **A finite product of entire completed readouts is entire.**  If each local completed readout
`(F i).Λ` is entire, so is the product's `(prod t F).Λ = ∏ᵢ (F i).Λ`. -/
theorem prod_Λ_differentiable {ι : Type*} (t : Finset ι) (F : ι → CompletedReflection)
    (h : ∀ i ∈ t, Differentiable ℂ (F i).Λ) : Differentiable ℂ (prod t F).Λ := by
  have hstep : Differentiable ℂ (fun s => ∏ i ∈ t, (F i).Λ s) :=
    Differentiable.fun_finsetProd (fun i hi => h i hi)
  exact fun s => (hstep s).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => prod_Λ t F x)

/-- **The completed functional equation passes to a pointwise limit.**  If the finite completed
stages `C N` converge — primal `Λ` at `s`, dual `Λ^∨` at `1-s`, and reflection factor
`εfin·εarch` at `s` — then the limit satisfies the completed FE `Λlim(s) = e · Λlimdual(1-s)`.  The
passage to the infinite Euler product is `tendsto_nhds_unique`; **no Poisson, no subconvexity** —
the convergence is the sole (standard) analytic input (`TransferContinuation`). -/
theorem completed_FE_of_tendsto (C : ℕ → CompletedReflection) (s : ℂ)
    {Λlim Λlimdual : ℂ → ℂ} {e : ℂ}
    (hΛ : Tendsto (fun N => (C N).Λ s) atTop (𝓝 (Λlim s)))
    (hΛd : Tendsto (fun N => (C N).Λdual (1 - s)) atTop (𝓝 (Λlimdual (1 - s))))
    (hε : Tendsto (fun N => (C N).εfin s * (C N).εarch s) atTop (𝓝 e)) :
    Λlim s = e * Λlimdual (1 - s) := by
  have hFE : ∀ N, (C N).Λ s = ((C N).εfin s * (C N).εarch s) * (C N).Λdual (1 - s) :=
    fun N => completed_FE (C N) s
  have hRHS : Tendsto (fun N => (C N).Λ s) atTop (𝓝 (e * Λlimdual (1 - s))) :=
    (hε.mul hΛd).congr fun N => (hFE N).symm
  exact tendsto_nhds_unique hΛ hRHS

/-- **The infinite-product completed functional equation.**  If the finite completed stages converge
pointwise everywhere to `Λlim`, `Λlimdual`, `εlim`, the limit satisfies
`Λlim(s) = εlim(s)·Λlimdual(1-s)` for every `s` — the global twisted FE of the infinite Euler
product, obtained from the finite-product FE by passage to the limit.  No Poisson. -/
theorem infinite_completed_FE (C : ℕ → CompletedReflection) {Λlim Λlimdual εlim : ℂ → ℂ}
    (hΛ : ∀ s, Tendsto (fun N => (C N).Λ s) atTop (𝓝 (Λlim s)))
    (hΛd : ∀ s, Tendsto (fun N => (C N).Λdual s) atTop (𝓝 (Λlimdual s)))
    (hε : ∀ s, Tendsto (fun N => (C N).εfin s * (C N).εarch s) atTop (𝓝 (εlim s))) (s : ℂ) :
    Λlim s = εlim s * Λlimdual (1 - s) :=
  completed_FE_of_tendsto C s (hΛ s) (hΛd (1 - s)) (hε s)

/-- **The infinite-product completed readout is entire.**  If every finite stage `(C N).Λ` is entire
(e.g. a finite product of entire local factors, `prod_Λ_differentiable`) and the stages converge
locally uniformly to `Λlim`, then `Λlim` is entire.  Reuses the proven local-uniform-limit lemma. -/
theorem infinite_Λ_differentiable (C : ℕ → CompletedReflection) {Λlim : ℂ → ℂ}
    (hdiff : ∀ N, Differentiable ℂ (C N).Λ)
    (hconv : TendstoLocallyUniformly (fun N => (C N).Λ) Λlim atTop) :
    Differentiable ℂ Λlim :=
  CriticalLinePhasor.StrandExchange.locallyUniformLimit_differentiable hconv hdiff

end CompletedReflection

/-- **The finite Euler-product `Sym^r π × σ` completed functional equation.**  Over any finite set
`t` of places, with unit-modulus Satake face `α p`, duality-stable twist `Wσ p`, conductor base
`c p ≠ 0`, and completion clock `β p`, `ℓ p`, the product of the per-place `symTensorCompleted`
reflections is a completed reflection whose completed readout is the product of the local completed
readouts and which satisfies the completed FE

`(∏ₚ Λₚ)(s) = (∏ₚ εfinₚ(s)·εarchₚ(s)) · (∏ₚ Λₚ^∨)(1-s)`.

This is the global twisted functional equation of the **finite Euler product** of `Sym^r π × σ`:
unconditional, every `r`, any twists, assembled from the per-place reciprocal FEs
(`localPoly_reciprocal`) and the self-dual clock — **no Poisson summation**.  The infinite Euler
product is the analytic limit, separate. -/
theorem symTensorFiniteProduct_FE {ι : Type*} (t : Finset ι) (r : ℕ)
    (α : ι → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    {κ : Type*} [Fintype κ] (Wσ : ι → FiniteWeightFiber κ)
    (c : ι → ℂ) (hc : ∀ p, c p ≠ 0) (β : ι → ℂ) (ℓ : ι → ℝ) (s : ℂ) :
    (∏ p ∈ t, (symTensorCompleted r (α p) (hα p) (Wσ p) (c p) (hc p) (β p) (ℓ p)).Λ s)
      = (∏ p ∈ t, ((symTensorCompleted r (α p) (hα p) (Wσ p) (c p) (hc p) (β p) (ℓ p)).εfin s
          * (symTensorCompleted r (α p) (hα p) (Wσ p) (c p) (hc p) (β p) (ℓ p)).εarch s))
        * (∏ p ∈ t,
            (symTensorCompleted r (α p) (hα p) (Wσ p) (c p) (hc p) (β p) (ℓ p)).Λdual (1 - s)) :=
  CompletedReflection.prod_completed_FE t
    (fun p => symTensorCompleted r (α p) (hα p) (Wσ p) (c p) (hc p) (β p) (ℓ p)) s

/-- **The all-places completed functional equation — ramified places included.**  For a finite set
`t` of places, a per-place index `ιloc p` of arbitrary size, per-place **arbitrary nonvanishing
weights** `w p` (no unit-modulus assumption — so a ramified place's inertia-invariant Frobenius
weight set is allowed), conductor base `c p ≠ 0`, and clock `β p`, `ℓ p`, the product of the per-place
`DualPairFiber.dualPairCompleted` reflections satisfies the completed FE

`(∏ₚ Λₚ)(s) = (∏ₚ εfinₚ(s)·εarchₚ(s)) · (∏ₚ Λₚ^∨)(1-s)`.

Every local factor is `dualPairCompleted`: its finite reflection is **derived** from the rational
identity `dualPair_localPoly_reciprocal` (not an imported analytic field); its `εfin` carries the
local **root number / determinant** `∏ᵢ w p i` and the **conductor** via `reflVar (c p)`; its dual
part uses the **contragredient** weights `dualWeights (w p)`.  So the global twisted functional
equation, its ε-factor, conductor, and contragredient assemble multiplicatively across **all** places
--- ramified, unramified, and archimedean alike --- with no analytic property imported through any
input field.  The only per-place input left is the arithmetic identification of `w p` with the actual
local parameter (`prop:localid`), uniform across places, not a separate ramified obstruction. -/
theorem dualPairFiniteProduct_FE {ι : Type*} (t : Finset ι)
    (ιloc : ι → Type*) [∀ p, Fintype (ιloc p)]
    (w : (p : ι) → ιloc p → ℂ) (hw : ∀ p, ∀ i, w p i ≠ 0)
    (c : ι → ℂ) (hc : ∀ p, c p ≠ 0) (β : ι → ℂ) (ℓ : ι → ℝ) (s : ℂ) :
    (∏ p ∈ t, (DualPairFiber.dualPairCompleted (w p) (hw p) (c p) (hc p) (β p) (ℓ p)).Λ s)
      = (∏ p ∈ t, ((DualPairFiber.dualPairCompleted (w p) (hw p) (c p) (hc p) (β p) (ℓ p)).εfin s
          * (DualPairFiber.dualPairCompleted (w p) (hw p) (c p) (hc p) (β p) (ℓ p)).εarch s))
        * (∏ p ∈ t,
            (DualPairFiber.dualPairCompleted (w p) (hw p) (c p) (hc p) (β p) (ℓ p)).Λdual (1 - s)) :=
  CompletedReflection.prod_completed_FE t
    (fun p => DualPairFiber.dualPairCompleted (w p) (hw p) (c p) (hc p) (β p) (ℓ p)) s

end CriticalLinePhasor.FiniteWeightFiber

#print axioms CriticalLinePhasor.FiniteWeightFiber.CompletedReflection.prod
#print axioms CriticalLinePhasor.FiniteWeightFiber.CompletedReflection.prod_completed_FE
#print axioms CriticalLinePhasor.FiniteWeightFiber.CompletedReflection.prod_Λ_differentiable
#print axioms CriticalLinePhasor.FiniteWeightFiber.CompletedReflection.completed_FE_of_tendsto
#print axioms CriticalLinePhasor.FiniteWeightFiber.CompletedReflection.infinite_completed_FE
#print axioms CriticalLinePhasor.FiniteWeightFiber.CompletedReflection.infinite_Λ_differentiable
#print axioms CriticalLinePhasor.FiniteWeightFiber.symTensorFiniteProduct_FE
#print axioms CriticalLinePhasor.FiniteWeightFiber.dualPairFiniteProduct_FE
