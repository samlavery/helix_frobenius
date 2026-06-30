import RequestProject.NoDoubleCancellation
import RequestProject.CancellationEquivalence

/-!
# GRH from a self-adjoint realization of the nontrivial cancellations

This file isolates the Hilbert–Pólya content cleanly and **unconditionally**: *if* every nontrivial
cancellation of `Lχ` is realized as a kernel of the fixed self-adjoint generator `Aχ`, *then* every
nontrivial zero lies on the critical line (GRH for `χ`).

The realization hypothesis is the genuine RH-strength input — it is isolated as an explicit
hypothesis, neither assumed globally nor proved here (proving it is GRH).  What *is* proved
unconditionally is the implication: a self-adjoint kernel forces the spectral height
`specHeight s = -i(s-1/2)` to be a **real** eigenvalue (von Neumann reality), hence `Re s = 1/2`.

* `nontrivial_Aχ_kernel_no_offline` — a nontrivial cancellation realized as an `Aχ`-kernel is on the
  critical line.
* `GRH_from_nontrivial_Aχ_realization` — the realization of *all* nontrivial cancellations as
  `Aχ`-kernels yields GRH for `χ`.

No `axiom`, no `sorry`.
-/

open Complex Filter Topology
open scoped BigOperators

namespace CriticalLinePhasor.SelfAdjointGenerator

open CriticalLinePhasor

/--
**A nontrivial cancellation realized by an `Aχ`-kernel is on the critical line.**

If a basis mode `single n 1` is a kernel vector of `specOp Aχ s`, then its real eigen-height
`logGen n` equals the spectral height `specHeight s`, forcing `specHeight s` real and hence
`Re s = 1/2`.  (The strip hypothesis is recorded but not needed for this geometric conclusion.)
-/
theorem nontrivial_Aχ_kernel_no_offline (s : ℂ)
    (h : (0 < s.re ∧ s.re < 1) ∧ ∃ n : ℕ, specOp Aχ s (Finsupp.single n 1) = 0) :
    s.re = 1 / 2 := by
  obtain ⟨_, n, hn⟩ := h
  rw [Aχ_single_kernel_iff] at hn
  have him : (specHeight s).im = 0 := by rw [← hn]; simp
  exact re_eq_half_of_specHeight_im_zero him

/--
**GRH for `χ` from a self-adjoint realization of the nontrivial cancellations.**

If every nontrivial cancellation of `Lχ` (a zero in the open critical strip) is realized as a kernel
of the fixed self-adjoint generator `Aχ`, then every nontrivial zero lies on the critical line — the
Generalized Riemann Hypothesis for `χ`.  The realization hypothesis `hrealize` is the isolated
RH-strength input; the implication itself is unconditional (von Neumann reality).
-/
theorem GRH_from_nontrivial_Aχ_realization
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hrealize :
      ∀ s : ℂ, SpectralFiber.NontrivialLCancellation χ s →
        ∃ n : ℕ, specOp Aχ s (Finsupp.single n 1) = 0) :
    ∀ s : ℂ, SpectralFiber.NontrivialLCancellation χ s → s.re = 1 / 2 := by
  intro s hs
  exact nontrivial_Aχ_kernel_no_offline s ⟨hs.2, hrealize s hs⟩

end CriticalLinePhasor.SelfAdjointGenerator
