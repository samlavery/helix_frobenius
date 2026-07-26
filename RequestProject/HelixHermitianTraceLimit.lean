import RequestProject.CaptureInterfaceAudit

/-!
# The Hermitian trace-limit reduction: the non-costume operator route to capture

`HelixSpectralLimit` audits its own `SpectralLimitCaptures` as a costume: quantifying arbitrary
real sequences pointwise re-encodes `Re ρ = ½` and gives the operator no work to do
(`spectralLimitCaptures_iff_grh`).  This file states the genuine reduction.

The object is a **Hermitian tower**: any sequence of Hermitian matrices `A n`, with the
*canonical* eigenvalue resolvent traces

  `T_n(z) = ∑ j, (z − μ_{n,j})⁻¹`,   `μ_{n,j} = (hA n).eigenvalues j : ℝ`.

Self-adjointness does genuine work at every stage: the spectrum is real, so each `T_n` is
holomorphic off the real axis (`hermitianResolventTrace_differentiableOn`) — a theorem, not a
hypothesis.  The **single open box** is one analytic statement, `hlim`: the tower's traces
converge locally uniformly, off the real axis, to the completed channel
`-Λ'/Λ(½ + i·)`.  Given it, Weierstrass makes the channel holomorphic off the real axis, the
compiled completed resonance (`completed_resonates_of_traceIdentity`) forbids that at any
off-line zero's pole parameter, and GRH follows (`grh_of_hermitian_traceLimit`).

Register, priced exactly: the hypothesis is a statement about the canonical traces of a
specific operator tower, uniform on compacts — not a per-zero re-encoding.  Its converse is
*not* provable by re-encoding: constructing from GRH a Hermitian tower whose traces converge to
the channel is the genuine Hilbert–Pólya construction problem, and no such construction is
claimed here.  This is the corrected form of the conclusion's "the one remaining closure step
is the operator": the remaining step is exactly `hlim`, with everything downstream compiled.
No RH/GRH is assumed anywhere in this file.
-/

open Filter Topology Complex DirichletCharacter

namespace CriticalLinePhasor.CaptureInterfaceAudit

variable {N : ℕ} [NeZero N]

/-- The canonical eigenvalue resolvent trace of a Hermitian matrix: the trace of the resolvent
`(z − A)⁻¹`, written on the real spectrum supplied by Hermitian reality. -/
noncomputable def hermitianResolventTrace {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (z : ℂ) : ℂ :=
  ∑ j, (z - ((hA.eigenvalues j : ℝ) : ℂ))⁻¹

/-- The off-real region of the spectral chart. -/
def offReal : Set ℂ := {z : ℂ | z.im ≠ 0}

lemma isOpen_offReal : IsOpen offReal :=
  isOpen_compl_singleton.preimage Complex.continuous_im

/-- **Each stage is holomorphic off the real axis — self-adjointness doing genuine work.**
The Hermitian spectrum is real, so every pole of the stage trace is real, and the trace is
differentiable on the off-real region.  This is a theorem about every stage of every Hermitian
tower; it is the per-stage content the costume interface discarded. -/
lemma hermitianResolventTrace_differentiableOn {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) :
    DifferentiableOn ℂ (hermitianResolventTrace hA) offReal := by
  unfold hermitianResolventTrace
  refine DifferentiableOn.fun_sum fun j _ => DifferentiableOn.inv ?_ ?_
  · exact (differentiable_id.sub_const _).differentiableOn
  · intro z hz h0
    have him : (z - ((hA.eigenvalues j : ℝ) : ℂ)).im = z.im := by
      simp
    rw [h0] at him
    exact hz (by simpa using him.symm)

/-- **The Hermitian trace-limit reduction.**  Let `A n` be any tower of Hermitian matrices whose
canonical eigenvalue resolvent traces converge locally uniformly, off the real axis, to the
completed channel `-Λ'/Λ(½ + i·)`.  Then GRH holds for `χ`.

The proof is unconditional given `hlim`: each stage is off-real holomorphic by Hermitian
reality; Weierstrass carries holomorphy to the limit; an off-line zero's pole parameter would be
an off-real point where the channel has a finite limit — contradicting the compiled completed
resonance.  The operator's reality is the entire mechanism; no positivity, no Weil/Li floor,
no per-zero data enters the hypothesis. -/
theorem grh_of_hermitian_traceLimit (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (k : ℕ → ℕ) (A : ∀ n, Matrix (Fin (k n)) (Fin (k n)) ℂ)
    (hA : ∀ n, (A n).IsHermitian) (T : ℂ → ℂ)
    (hid : ∀ z, T z = -logDeriv (completedLFunction χ) (1 / 2 + Complex.I * z))
    (hlim : TendstoLocallyUniformlyOn
      (fun n => hermitianResolventTrace (hA n)) T atTop offReal) :
    GRHSpectral.GRH χ := by
  intro ρ hρ
  by_contra hre
  have hz : HelixLimit.poleParam ρ ∈ offReal := by
    simp only [offReal, Set.mem_setOf_eq, HelixLimit.poleParam_im]
    intro h
    exact hre (by linarith)
  have hT : DifferentiableOn ℂ T offReal :=
    hlim.differentiableOn
      (Eventually.of_forall fun n => hermitianResolventTrace_differentiableOn (hA n))
      isOpen_offReal
  have hfin : ∃ L, Tendsto T (𝓝[≠] HelixLimit.poleParam ρ) (𝓝 L) := by
    refine ⟨T (HelixLimit.poleParam ρ), ?_⟩
    exact ((hT.differentiableAt
      (isOpen_offReal.mem_nhds hz)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  exact completed_resonates_of_traceIdentity hχ hid hρ hfin

/-- The trace-limit hypothesis is not a re-encoding: it implies the costume statement, but
through the operator — every pole parameter is forced real by the tower's reality, and the
constant sequence then witnesses the pointwise capture.  (The converse implication is exactly
what the costume audit showed carries no operator content.) -/
theorem spectralLimitCaptures_of_hermitian_traceLimit
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (k : ℕ → ℕ) (A : ∀ n, Matrix (Fin (k n)) (Fin (k n)) ℂ)
    (hA : ∀ n, (A n).IsHermitian) (T : ℂ → ℂ)
    (hid : ∀ z, T z = -logDeriv (completedLFunction χ) (1 / 2 + Complex.I * z))
    (hlim : TendstoLocallyUniformlyOn
      (fun n => hermitianResolventTrace (hA n)) T atTop offReal) :
    HelixLimit.SpectralLimitCaptures χ :=
  HelixLimit.spectralLimitCaptures_of_grh χ
    (grh_of_hermitian_traceLimit χ hχ k A hA T hid hlim)

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.hermitianResolventTrace_differentiableOn
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.grh_of_hermitian_traceLimit
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.spectralLimitCaptures_of_hermitian_traceLimit
