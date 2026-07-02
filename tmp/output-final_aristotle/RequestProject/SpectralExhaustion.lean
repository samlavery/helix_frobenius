import RequestProject.NoDoubleCancellation
import RequestProject.CancellationEquivalence

/-!
# Nontrivial spectral cancellation and a real (self-adjoint) generator

The fully unrestricted realization "every nontrivial spectral cancellation is realized by a real
generator" is, by `SelfAdjointGenerator.specOp_kernel_iff_specBchan_zero` together with
`SelfAdjointGenerator.sign_flip_only_on_real_axis`, equivalent to `s.re = 1/2` for every nontrivial
zero — i.e. GRH for `χ` (an open problem), so it is not asserted here.  What **is** unconditional:

* `nontrivial_spectral_cancellation_to_real_generator_of_re_half` — **on the critical line** the
  realization holds outright (`γ = Im s`, `ψ = 1`).
* `realGeneratorCancellation_re_half` — conversely, a real-generator cancellation forces `Re s = 1/2`
  (von Neumann reality).
* `GRH_from_spectral_exhaustion` — GRH for `χ` follows from the isolated **spectral exhaustion**
  hypothesis (every nontrivial cancellation realized by a real generator); the hypothesis is the
  genuine RH-strength input, isolated, neither assumed globally nor proved.

No `axiom`, no `sorry`.
-/

open Complex Filter Topology
open scoped BigOperators

namespace CriticalLinePhasor.SpectralFiber

open CriticalLinePhasor CriticalLinePhasor.SelfAdjointGenerator
  CriticalLinePhasor.UnconditionalFrobenius

/-- **On the critical line, a nontrivial spectral cancellation is realized by a real generator.**
With `γ = Im s` and `ψ = 1`, the self-adjoint resolvent operator `specOp (vonNeumannOp γ) s`
annihilates `ψ`. -/
theorem nontrivial_spectral_cancellation_to_real_generator_of_re_half
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hline : s.re = 1 / 2) :
    NontrivialSpectralCancellation χ s →
      ∃ γ : ℝ, ∃ ψ : ℂ, ψ ≠ 0 ∧
        SelfAdjointGenerator.specOp (vonNeumannOp γ) s ψ = 0 := by
  intro _h
  refine ⟨s.im, ?_⟩
  have hb : specBchan s.im s = 0 := by
    apply Complex.ext
    · simp [specBchan_re]
    · simp [specBchan_im, hline]
  exact (specOp_kernel_iff_specBchan_zero s.im s).mpr hb

/-- **A real-generator cancellation** at `s`: a nonzero kernel vector of the self-adjoint resolvent
operator `specOp (vonNeumannOp γ) s` for some real `γ`. -/
def RealGeneratorCancellation (s : ℂ) : Prop :=
  ∃ γ : ℝ, ∃ ψ : ℂ, ψ ≠ 0 ∧
    SelfAdjointGenerator.specOp (vonNeumannOp γ) s ψ = 0

/-- **A real-generator cancellation forces the critical line.**  Von Neumann reality: the spectral
height `specHeight s` must be the real eigenvalue `γ`, so `Re s = 1/2`. -/
theorem realGeneratorCancellation_re_half {s : ℂ} :
    RealGeneratorCancellation s → s.re = 1 / 2 := by
  rintro ⟨γ, ψ, hψ, hker⟩
  exact SelfAdjointGenerator.spectral_cancellation_on_real_axis γ ⟨ψ, hψ, hker⟩

/-- **Spectral exhaustion** for `χ`: every nontrivial cancellation of `Lχ` is realized by a real
(self-adjoint) generator.  This is the isolated RH-strength hypothesis. -/
def SpectralExhaustion {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ s : ℂ, NontrivialLCancellation χ s → RealGeneratorCancellation s

/-- **GRH for `χ` from spectral exhaustion.**  If every nontrivial cancellation is realized by a real
generator, then every nontrivial zero lies on the critical line — GRH for `χ`.  The exhaustion
hypothesis is isolated (not assumed globally, not proved); the implication is unconditional. -/
theorem GRH_from_spectral_exhaustion
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hExh : SpectralExhaustion χ) :
    ∀ s : ℂ, NontrivialLCancellation χ s → s.re = 1 / 2 := by
  intro s hs
  exact realGeneratorCancellation_re_half (hExh s hs)

end CriticalLinePhasor.SpectralFiber
