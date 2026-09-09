import RequestProject.FiniteCellSections
import RequestProject.GlobalHelixIntertwiner

/-!
The finite section count on the existing 3D double carrier.

The bank consists of N consecutive powers of the retained-height Cayley readout.
Its sections are polynomial readouts, with Taylor jets in that complex chart.
Distinct retained heights give distinct chart nodes. No injectivity is asserted
for projection on the whole 3D space: radius and phase remain in its loss ledger.
The existing global helix involution sends every node and every jet to its
complex conjugate, retaining all prescribed multiplicities.

Unfolded targets: for fibers c_i with distinct signed heights, dim ker E is
N - sum m_i, and E is onto when sum m_i <= N. Here E(P)_ij is the jth Taylor
coefficient at (height(c_i)-i)/(height(c_i)+i). Under the 3D involution,
E_anti(conjugate P)_ij = conjugate(E(P)_ij).

Strategies: `apply finrank_jetKernel` transports the divisor count; independently,
`rw [circleReadout_globalHelixInvolution, ← Polynomial.map_taylor]` transports
the actual Taylor constraints under the geometric involution.
Searches: `rg -n 'cayley.*inject|inject.*cayley|cayley.*eq.*iff|cayley.*inv'
RequestProject .lake/packages/mathlib/Mathlib`; `rg -n 'taylor.*map|map.*taylor|
taylor.*comp|coeff_map|conj.*Polynomial' .lake/packages/mathlib/Mathlib/Algebra/Polynomial`.
LeanSearch: Taylor expansion commutes with coefficient maps. Loogle:
`Polynomial.taylor, Polynomial.map`. Existing global symmetry and norm theorems
are audited in proof-drafts/2026-09-07/RouteAxiomAudit.lean.
-/

open Complex Polynomial ConeProjection

namespace CriticalLinePhasor.HelixCellSections3D

open Readout GlobalHelix FiniteCellSections

theorem cayley_real_injective : Function.Injective (fun h : ℝ => cayley (h : ℂ)) := by
  have hden (h : ℝ) : (h : ℂ) + I ≠ 0 := by
    intro heq
    have him := congrArg Complex.im heq
    norm_num at him
  intro h k heq
  have hcross := (div_eq_div_iff (hden h) (hden k)).mp heq
  have him := congrArg Complex.im hcross
  simp only [Complex.mul_im, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.I_re, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.I_im] at him
  linarith

theorem circleReadout_eq_iff (f g : Fiber) :
    circleReadout f = circleReadout g ↔ height f = height g := by
  exact cayley_real_injective.eq_iff

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem cellNodes_injective (c : ι → Fiber)
    (hc : Function.Injective (fun i => height (c i))) :
    Function.Injective (fun i => circleReadout (c i)) := by
  intro i j hij
  exact hc ((circleReadout_eq_iff _ _).mp hij)

/-- The N-mode Cayley bank, evaluated on the retained channel of the 3D carrier. -/
noncomputable def cellJets (c : ι → Fiber) (m : ι → ℕ) (N : ℕ) :=
  jetEvaluation (fun i => circleReadout (c i)) m N

omit [Fintype ι] in
theorem cellNodes_norm_one (c : ι → Fiber) (i : ι) :
    ‖circleReadout (c i)‖ = 1 := circleReadout_norm_one _

theorem finrank_cellJets_kernel (c : ι → Fiber)
    (hc : Function.Injective (fun i => height (c i))) (m : ι → ℕ) (N : ℕ) :
    Module.finrank ℂ (LinearMap.ker (cellJets c m N)) = N - ∑ i, m i :=
  finrank_jetKernel _ (cellNodes_injective c hc) m N

theorem cellJets_surjective (c : ι → Fiber)
    (hc : Function.Injective (fun i => height (c i))) (m : ι → ℕ) (N : ℕ)
    (hN : ∑ i, m i ≤ N) : Function.Surjective (cellJets c m N) :=
  jetEvaluation_surjective _ (cellNodes_injective c hc) m N hN

/-- Exact conjugacy at every jet order, before imposing vanishing. -/
theorem antiHelix_jet (P : ℂ[X]) (f : Fiber) (j : ℕ) :
    (Polynomial.taylor (circleReadout (globalHelixInvolution f))
      (P.map (starRingEnd ℂ))).coeff j =
      (starRingEnd ℂ) ((Polynomial.taylor (circleReadout f) P).coeff j) := by
  rw [circleReadout_globalHelixInvolution, ← Polynomial.map_taylor, Polynomial.coeff_map]

theorem antiHelix_jet_vanishes_iff (P : ℂ[X]) (f : Fiber) (j : ℕ) :
    (Polynomial.taylor (circleReadout (globalHelixInvolution f))
      (P.map (starRingEnd ℂ))).coeff j = 0 ↔
      (Polynomial.taylor (circleReadout f) P).coeff j = 0 := by
  rw [antiHelix_jet]
  simp

omit [Fintype ι] in
theorem antiHelix_height_injective (c : ι → Fiber)
    (hc : Function.Injective (fun i => height (c i))) :
    Function.Injective (fun i => height (globalHelixInvolution (c i))) := by
  intro i j hij
  apply hc
  exact neg_injective (by simpa only [height_globalHelixInvolution] using hij)

theorem finrank_antiHelix_kernel (c : ι → Fiber)
    (hc : Function.Injective (fun i => height (c i))) (m : ι → ℕ) (N : ℕ) :
    Module.finrank ℂ
      (LinearMap.ker (cellJets (fun i => globalHelixInvolution (c i)) m N)) =
      Module.finrank ℂ (LinearMap.ker (cellJets c m N)) := by
  rw [finrank_cellJets_kernel _ (antiHelix_height_injective c hc),
    finrank_cellJets_kernel c hc]

#print axioms finrank_cellJets_kernel
#print axioms cellJets_surjective
#print axioms antiHelix_jet
#print axioms finrank_antiHelix_kernel

end CriticalLinePhasor.HelixCellSections3D
