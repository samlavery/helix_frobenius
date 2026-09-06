import RequestProject.HelixLineTowerCapture

/-!
# Normalized trace capture on the open critical-strip chart

Unfolded target: the chart s = 1/2 + i z sends 0 < Re(s) < 1 to
-1/2 < Im(z) < 1/2. A locally uniform limit of finite real-spectrum
traces is holomorphic there off the real axis. Use i L'/L(s), whose
residue in z has the usual positive multiplicity normalization.

Expectation-free strategy A: `have hsub := hlim.differentiableOn ...`,
then take the punctured limit of the arithmetic channel. Strategy B:
`have hscaled := hL.const_mul I` transports the normalized channel's
limit to the existing -L'/L resonance theorem. Both steps occur below.

Searches: `rg -n -i 'trace.*(strip|domain|region)|re_half.*(on|of)|normalized.*(strip|domain)|offReal.*inter|stripOffReal|offRealStrip|strip_off_real|off_real_strip'
RequestProject -g '*Trace*.lean' -g '*Capture*.lean' -g '*Limit*.lean`;
`rg -n 'isOpen_Ioo|isOpen_setOf_lt|isOpen_inter|DifferentiableOn.mono|differentiableOn.*mono'
.lake/packages/mathlib/Mathlib/Topology/Order/OrderClosed.lean
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.
LeanSearch: locally uniform holomorphic limits on an open set.
Loogle: `IsOpen, Continuous, Set.Ioo`.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.CaptureInterfaceAudit

def stripOffReal : Set ℂ :=
  offReal ∩ Complex.im ⁻¹' Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

theorem isOpen_stripOffReal : IsOpen stripOffReal :=
  isOpen_offReal.inter (isOpen_Ioo.preimage Complex.continuous_im)

/-- Multiplicity-normalized logarithmic derivative in the spectral chart. -/
noncomputable def normalizedLTrace {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (z : ℂ) : ℂ :=
  I * logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + I * z)

theorem normalizedLTrace_resonates {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ¬ ∃ L, Tendsto (normalizedLTrace χ) (𝓝[≠] HelixLimit.poleParam ρ) (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hraw := HelixLimit.resonates_of_traceIdentity (χ := χ)
    (T := fun z => -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + I * z))
    (fun _ => rfl) hρ
  apply hraw
  refine ⟨I * L, ?_⟩
  have hscaled := hL.const_mul I
  simpa [normalizedLTrace, ← mul_assoc] using hscaled

/-- The strip chart is sufficient for every character's nontrivial zeros. -/
theorem grh_of_stripTraceLimit {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (d : ∀ n, ι n → ℝ) (c : ∀ n, ι n → ℂ) (E : ℂ → ℂ)
    (hE : DifferentiableOn ℂ E stripOffReal)
    (hlim : TendstoLocallyUniformlyOn
      (fun n => normalizedSpectrumTrace (d n) (c n))
      (fun z => normalizedLTrace χ z - E z) atTop stripOffReal) : GRHSpectral.GRH χ := by
  intro ρ hρ
  by_contra hre
  have hz : HelixLimit.poleParam ρ ∈ stripOffReal := by
    refine ⟨?_, ?_⟩
    · change (HelixLimit.poleParam ρ).im ≠ 0
      rw [HelixLimit.poleParam_im]
      intro h
      exact hre (by linarith)
    · change -(1 / 2 : ℝ) < (HelixLimit.poleParam ρ).im ∧
        (HelixLimit.poleParam ρ).im < 1 / 2
      rw [HelixLimit.poleParam_im]
      constructor <;> linarith [hρ.1, hρ.2.1]
  have hsub : DifferentiableOn ℂ (fun z => normalizedLTrace χ z - E z) stripOffReal :=
    hlim.differentiableOn
      (Eventually.of_forall fun n =>
        (normalizedSpectrumTrace_differentiableOn (d n) (c n)).mono
          (fun _ h => h.1)) isOpen_stripOffReal
  have hT : DifferentiableAt ℂ (normalizedLTrace χ) (HelixLimit.poleParam ρ) := by
    have h1 := hsub.differentiableAt (isOpen_stripOffReal.mem_nhds hz)
    have h2 := hE.differentiableAt (isOpen_stripOffReal.mem_nhds hz)
    have hsum : DifferentiableAt ℂ
        (fun z => (normalizedLTrace χ z - E z) + E z) (HelixLimit.poleParam ρ) := h1.add h2
    simpa only [sub_add_cancel] using hsum
  exact normalizedLTrace_resonates χ hρ
    ⟨normalizedLTrace χ (HelixLimit.poleParam ρ),
      hT.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.isOpen_stripOffReal
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.normalizedLTrace_resonates
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.grh_of_stripTraceLimit
