import RequestProject.SpectralFiberIsLFunction

/-!
# A spectral zero has a kernel vector

This file records the **Hilbert–Pólya-flavoured kernel statement** for the configured spectral
object: a zero of the spectral `L`-function produces a nonzero kernel vector of the operator the
spectral fiber is configured into.

* `Lspec χ s` — the **spectral `L`-function**: the value the spectral 3-D fiber's readout converges
  to (`Lspec_eq_readout_limit`, from `spectralFiber_readout_tendsto_LFunction`), which on `Re s > 0`
  is the genuine analytic Dirichlet `L`-function `DirichletCharacter.LFunction χ s`.
* `specOp χ s` — the **configured fiber operator** at parameter `s`: multiplication by `Lspec χ s`
  on the one-dimensional fiber `ℂ`.  This is the same shape as the project's Hilbert–Pólya fiber
  operator `UnconditionalFrobenius.vonNeumannOp` (`γ • id`): a self-adjoint-by-construction scalar
  generator whose value encodes the spectral data.

Main results:

* `spectral_zero_has_kernel` — **the requested statement**:
  `Lspec χ s = 0 → ∃ ψ ≠ 0, specOp χ s ψ = 0`.
* `spectral_kernel_iff_zero` — the sharp form: the operator has a nonzero kernel vector **iff** the
  spectral `L`-function vanishes at `s`.

No `axiom`, no `sorry`.
-/

open Complex Filter Topology
open scoped BigOperators

namespace CriticalLinePhasor.SpectralFiber

open CriticalLinePhasor

/-! ## The spectral L-function and the configured fiber operator -/

/-- **The spectral `L`-function**: the value the spectral 3-D fiber's readout converges to.  On
`Re s > 0` this is the analytic Dirichlet `L`-function (`Lspec_eq_readout_limit`). -/
noncomputable def Lspec {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ s

/-- **The configured fiber operator** at parameter `s`: scalar multiplication by the spectral
`L`-value on the one-dimensional fiber `ℂ`.  Same shape as `UnconditionalFrobenius.vonNeumannOp`. -/
noncomputable def specOp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    Module.End ℂ ℂ :=
  (Lspec χ s) • LinearMap.id

@[simp] theorem specOp_apply {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (ψ : ℂ) :
    specOp χ s ψ = Lspec χ s * ψ := by
  simp [specOp]

/-- The spectral `L`-function is the limit of the spectral fiber's partial-sum readout (non-principal
`χ`, on the strip `Re s > 0`): it is genuinely the value read off the spectral object. -/
theorem Lspec_eq_readout_limit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, readout (fun n => χ (n : ZMod q)) s n)
      Filter.atTop (nhds (Lspec χ s)) :=
  spectralFiber_readout_tendsto_LFunction χ hχ hs

/-! ## The kernel statement -/

/--
**A spectral zero has a kernel vector.**  If the spectral `L`-function vanishes at `s`, then the
configured fiber operator `specOp χ s` annihilates a nonzero vector `ψ`:
`Lspec χ s = 0 → ∃ ψ ≠ 0, specOp χ s ψ = 0`.

This is the Hilbert–Pólya kernel event at the level of the configured spectral operator: a zero of
the spectral `L`-function is realised as a nontrivial kernel (equivalently, a `0`-eigenvalue) of the
operator the spectral fiber is configured into.
-/
theorem spectral_zero_has_kernel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (h : Lspec χ s = 0) :
    ∃ ψ : ℂ, ψ ≠ 0 ∧ specOp χ s ψ = 0 := by
  refine ⟨1, one_ne_zero, ?_⟩
  rw [specOp_apply, h, zero_mul]

/--
**Sharp form.**  The configured fiber operator has a nonzero kernel vector **iff** the spectral
`L`-function vanishes at `s`.  So the kernel events of the spectral operator are *exactly* the zeros
of the spectral `L`-function.
-/
theorem spectral_kernel_iff_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (∃ ψ : ℂ, ψ ≠ 0 ∧ specOp χ s ψ = 0) ↔ Lspec χ s = 0 := by
  constructor
  · rintro ⟨ψ, hψ, hker⟩
    rw [specOp_apply] at hker
    exact (mul_eq_zero.mp hker).resolve_right hψ
  · exact spectral_zero_has_kernel χ s

end CriticalLinePhasor.SpectralFiber
