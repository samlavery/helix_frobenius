import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The carrier-manufactured continuation **is** the target — identity theorem, universal form

**Objection 4 (aristotle).**  A functional equation manufactured on the carrier produces an entire
function with a self-duality.  The decisive question is whether this constructed entire function
*is* the target completed Euler product `L(s, Sym^r π × τ)` — carrier construction and classical
global object are, a priori, two different functions, and `symTensorCompleted_FE` books the
identification as separate.

**The answer is the identity theorem, and it is unconditional and universal.**  The carrier supplies
an *entire* continuation `Λc` with its functional equation (Poisson/theta self-duality; no RH).  On
the **open** initial region — the half-plane where both the carrier bank and the target Dirichlet
series converge absolutely — agreement of `Λc` with the target `Λt` is *exactly* term-by-term
coefficient matching (`local_compatible` / `ArithmeticCPSCoefficientPassport`, and, for the compiled
Dirichlet fiber, `SpectralFiberIsLFunction`).  Two entire functions that agree on a nonempty open
set agree on the whole connected plane.  Hence `Λc = Λt` everywhere: the carrier object is **forced**
to be the target — there is no second continuation — and every functional equation proved for the
carrier is *verbatim* the target's functional equation.

This isolates the single genuine input with total precision — **coefficient matching on the initial
half-plane**, nothing else:

* No RH/GRH is used anywhere (the theorems below are pure identity-theorem statements).
* No property of the carrier beyond *entireness* is used; the initial agreement is the only bridge.
* The classical content is therefore *only* the coefficient identity `Λc = Λt` on the open initial
  region.  For `Sym^r π` this is Langlands functoriality: a **cited theorem** for `r ≤ 4`
  (Gelbart–Jacquet `Sym²`, Kim–Shahidi `Sym³`, Kim `Sym⁴`) and the **open functoriality conjecture**
  for `r ≥ 5`.  For a Dirichlet character it is discharged outright — `SpectralFiberIsLFunction`
  identifies the carrier readout with Mathlib's own `DirichletCharacter.LFunction`.

The identity theorem below is the same one the fiber files run throughout
(`LFunctionPhasor`, `FullFiber`, `HelixCollapseReality`, `AxisIdentityContinuation`); here it is
stated once, universally (any two entire functions), as the exact answer to objection 4.
-/

open Complex Set Filter Topology

namespace CriticalLinePhasor.CarrierTargetIdentification

/-- **Identity theorem, entire form.**  Two entire functions on `ℂ` that agree on a nonempty open
set are equal *everywhere*.  Fully universal: no hypothesis beyond entireness and open agreement,
no RH/GRH, no reference to any specific L-function. -/
theorem entire_eq_of_eqOn_isOpen {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hfg : Set.EqOn f g U) :
    f = g := by
  have hev : f =ᶠ[𝓝 z₀] g := hfg.eventuallyEq_of_mem (hU.mem_nhds hz₀)
  have heq : Set.EqOn f g Set.univ :=
    (analyticOnNhd_univ_iff_differentiable.mpr hf).eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_univ_iff_differentiable.mpr hg) isPreconnected_univ (Set.mem_univ z₀) hev
  funext s
  exact heq (Set.mem_univ s)

/-- **The carrier is the target, and the carrier functional equation transfers verbatim.**  Let the
carrier primal/dual continuations `Λcp, Λcd` and the target primal/dual completed readouts
`Λtp, Λtd` be entire.  If they agree on nonempty open initial regions `Up, Ud` — the *coefficient
matching* input — then `Λcp = Λtp`, `Λcd = Λtd` everywhere, and the carrier functional equation
`Λcp (k - s) = ε • Λcd s` holds *verbatim* for the target: `Λtp (k - s) = ε • Λtd s`.

Thus a functional equation "manufactured on the carrier" is not a coincidence about a different
function: given initial coefficient agreement, it *is* the target completed L-function's functional
equation, by uniqueness of analytic continuation. -/
theorem carrier_FE_transfers_to_target
    {Λcp Λtp Λcd Λtd : ℂ → ℂ}
    (hΛcp : Differentiable ℂ Λcp) (hΛtp : Differentiable ℂ Λtp)
    (hΛcd : Differentiable ℂ Λcd) (hΛtd : Differentiable ℂ Λtd)
    {Up Ud : Set ℂ} (hUp : IsOpen Up) (hUd : IsOpen Ud)
    {zp zd : ℂ} (hzp : zp ∈ Up) (hzd : zd ∈ Ud)
    (hap : Set.EqOn Λcp Λtp Up) (had : Set.EqOn Λcd Λtd Ud)
    {k ε : ℂ} (hFE : ∀ s, Λcp (k - s) = ε • Λcd s) :
    Λcp = Λtp ∧ Λcd = Λtd ∧ (∀ s, Λtp (k - s) = ε • Λtd s) := by
  have hidp : Λcp = Λtp := entire_eq_of_eqOn_isOpen hΛcp hΛtp hUp hzp hap
  have hidd : Λcd = Λtd := entire_eq_of_eqOn_isOpen hΛcd hΛtd hUd hzd had
  refine ⟨hidp, hidd, fun s => ?_⟩
  rw [← hidp, ← hidd]
  exact hFE s

/-- **Self-dual specialization.**  When the carrier's functional equation is a genuine
self-duality `Λc (k - s) = ε • Λc s`, initial agreement with an entire target `Λt` forces
`Λc = Λt` and the self-duality transfers verbatim to the target. -/
theorem carrier_selfdual_FE_transfers_to_target
    {Λc Λt : ℂ → ℂ}
    (hΛc : Differentiable ℂ Λc) (hΛt : Differentiable ℂ Λt)
    {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hagree : Set.EqOn Λc Λt U)
    {k ε : ℂ} (hFE : ∀ s, Λc (k - s) = ε • Λc s) :
    Λc = Λt ∧ (∀ s, Λt (k - s) = ε • Λt s) := by
  have hid : Λc = Λt := entire_eq_of_eqOn_isOpen hΛc hΛt hU hz₀ hagree
  refine ⟨hid, fun s => ?_⟩
  rw [← hid]
  exact hFE s

end CriticalLinePhasor.CarrierTargetIdentification

#print axioms CriticalLinePhasor.CarrierTargetIdentification.entire_eq_of_eqOn_isOpen
#print axioms CriticalLinePhasor.CarrierTargetIdentification.carrier_FE_transfers_to_target
#print axioms CriticalLinePhasor.CarrierTargetIdentification.carrier_selfdual_FE_transfers_to_target
