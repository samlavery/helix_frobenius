import RequestProject.StripTraceCapture

/-!
# A trace correction that extends through the real spectral axis

Unfolded target: the correction E is holomorphic on the entire open chart band,
including its real axis; the tower limit is only required off that axis. This
prevents taking E to be the arithmetic trace at any of its zero singularities.

Expectation-free route A: `apply grh_of_stripTraceLimit` and restrict the
correction's domain. Route B: `apply normalizedLTrace_resonates` to test the
proposed correction at a zero. Both checks are proved below.

Searches: `rg -n 'spectralStrip|stripChart|fullStripChart|normalizedLTrace.*differentiableAt|normalizedLTrace.*not|entireCorrection|regularCorrection' RequestProject --glob '*.lean'`;
Mathlib searches: `DifferentiableOn.mono`, `DifferentiableOn.differentiableAt`,
`IsOpen.mem_nhds`, `ContinuousAt.tendsto`, `nhdsWithin_le_nhds`.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.CaptureInterfaceAudit

def spectralStrip : Set ℂ := Complex.im ⁻¹' Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

theorem isOpen_spectralStrip : IsOpen spectralStrip :=
  isOpen_Ioo.preimage Complex.continuous_im

theorem normalizedLTrace_not_differentiableAt {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ¬ DifferentiableAt ℂ (normalizedLTrace χ) (HelixLimit.poleParam ρ) := by
  intro h
  exact normalizedLTrace_resonates χ hρ
    ⟨_, h.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩

theorem normalizedLTrace_not_regular_correction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ¬ DifferentiableOn ℂ (normalizedLTrace χ) spectralStrip := by
  intro h
  have hp : HelixLimit.poleParam ρ ∈ spectralStrip := by
    change -(1 / 2 : ℝ) < (HelixLimit.poleParam ρ).im ∧
      (HelixLimit.poleParam ρ).im < 1 / 2
    rw [HelixLimit.poleParam_im]
    constructor <;> linarith [hρ.1, hρ.2.1]
  exact normalizedLTrace_not_differentiableAt χ hρ
    (h.differentiableAt (isOpen_spectralStrip.mem_nhds hp))

theorem grh_of_regularCorrectionTraceLimit {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (d : ∀ n, ι n → ℝ) (c : ∀ n, ι n → ℂ) (E : ℂ → ℂ)
    (hE : DifferentiableOn ℂ E spectralStrip)
    (hlim : TendstoLocallyUniformlyOn
      (fun n => normalizedSpectrumTrace (d n) (c n))
      (fun z => normalizedLTrace χ z - E z) atTop stripOffReal) : GRHSpectral.GRH χ :=
  grh_of_stripTraceLimit χ d c E (hE.mono (fun _ h => h.2)) hlim

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.normalizedLTrace_not_regular_correction
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.grh_of_regularCorrectionTraceLimit
