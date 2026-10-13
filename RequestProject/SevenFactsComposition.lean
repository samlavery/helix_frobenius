import RequestProject.NativePencilSpectralSlot
import RequestProject.WarpFactorFocalLocus

/-!
# Composing the compiled facts: the literal remaining proposition (ledger 1211)

No new mechanism. The compiled facts are composed as they stand.

**The s-family side** (the two-lane pencil whose fiber lane is the Mellin readout, 2026-09-06 onward).
`sFamily_iff_zero`: on the open strip, the bundle "A_N(s) Hermitian for every N, native coupling → 0,
centered determinant → 0" holds at `s` exactly when `ζ(s) = 0`. Composing these facts returns the
analytic vanishing condition and nothing more. `stageA_isHermitian` holds at every complex `s`, so the
bundle carries no information about `Re s`.

**The native spectral side** (the original s-free helix pencil, `GeometricPhasorClosure`, spectral
variable the closure height). `helix_eigenheight_real_of_indep`: every generalized eigenheight is real.
`carrierScaleBalanced_iff`: the area law fixes the balanced exponent.

**The composition.** `ZerosAreNativeReadouts χ`: every nontrivial zero is `σ₀ + i·log μ`, where `μ` is a
generalized eigenheight of the native helix pencil and `σ₀` is a balanced exponent. This is a named
proposition, not assumed. `composition`: from it, every nontrivial zero has real part `½`. The proof
uses the reality of the eigenheight (self-adjointness), the area law, and `0 < Re ρ`. It inserts no ½,
FE, Γ or `1 − s`. `ZerosAreNativeReadouts` is the one proposition the compiled facts do not supply:
no compiled theorem relates the helix pencil's eigenheights to the zeros of ζ.
`ZerosAreNativeLimitReadouts` / `composition_limit`: the same with `μ` a limit of native eigenheights,
since exact eigenheights at a finite stage need not hit a zero height. Reality passes to the limit.

**Scope (cleanup, ledger 1237).** `ZerosAreNativeReadouts` and `ZerosAreNativeLimitReadouts` are observer-side
COVERAGE statements: they start from analytic zeros. They are not "the remaining theorem" and supersede nothing;
the sentence above calling it "the one proposition" is withdrawn. The repository records two disconnected forward
structures plus unresolved exhaustiveness, with no single predicate connecting them (see `Arrow1Graph` header).
-/

open Complex Filter Topology Matrix
open scoped Matrix

noncomputable section

namespace CriticalLinePhasor.SevenFacts

open CriticalLinePhasor CriticalLinePhasor.NativeSquare CriticalLinePhasor.Geometric
open CriticalLinePhasor.Pencil3D CriticalLinePhasor.NativeSpectralSlot CriticalLinePhasor.SpectralFiber
open CriticalLinePhasor.ThreeDFocal

/-! ## The s-family side composes to the analytic vanishing condition -/

/-- What the s-family facts give at `s`. -/
def SFamilyBundle (s : ℂ) : Prop :=
  (∀ N, (stageA etaW s N).IsHermitian) ∧
    Tendsto (nativeCoupling etaW s) atTop (𝓝 0) ∧
    Tendsto (fun N => (stageA etaW s N - (((N : ℂ) + 1) / 2) • stageB etaW s N).det) atTop (𝓝 0)

/-- **On the open strip the composed s-family facts are exactly `ζ(s) = 0`.** -/
theorem sFamily_iff_zero {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    SFamilyBundle s ↔ riemannZeta s = 0 := by
  constructor
  · rintro ⟨-, hC, -⟩
    exact (zeta_zero_iff_eta_coupling_tendsto_zero hs0 hs1).mpr hC
  · intro hz
    have hC := (zeta_zero_iff_eta_coupling_tendsto_zero hs0 hs1).mp hz
    refine ⟨fun N => stageA_isHermitian etaW s N, hC, ?_⟩
    simp_rw [stage_det_at_reference]
    have h := ((Complex.continuous_ofReal.tendsto _).comp (hC.norm.pow 2)).neg
    simpa using h

/-! ## The composition with the native spectral side -/

/-- `μ` is a generalized eigenheight of the native s-free helix pencil at some stage. -/
def IsNativeEigenheight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (μ : ℂ) : Prop :=
  ∃ N m : ℕ, Function.Injective (helixFeature χ N m).mulVec ∧
    ∃ v : Fin 6 × Fin m → ℂ, v ≠ 0 ∧
      (helixHeightA χ N m).mulVec v = μ • (helixMetricB χ N m).mulVec v

/-- **The one proposition the compiled facts do not supply**: every nontrivial zero is the readout
`σ₀ + i·log μ` of a native eigenheight `μ`, at a balanced exponent `σ₀`. Named, not assumed. -/
def ZerosAreNativeReadouts {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ ρ ∈ ZD.NontrivialZeros, ∃ μ : ℂ, IsNativeEigenheight χ μ ∧
    ∃ σ₀ : ℝ, CarrierScaleBalanced σ₀ ∧ ρ = (σ₀ : ℂ) + I * Complex.log μ

/-- **The composition.** Self-adjointness makes the eigenheight real, the area law makes the balanced
exponent `½`, and `0 < Re ρ` excludes the negative branch of the logarithm. -/
theorem composition {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : ZerosAreNativeReadouts χ) : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  intro ρ hρ
  obtain ⟨μ, ⟨N, m, hQ, v, hv, heig⟩, σ₀, hbal, hρeq⟩ := h ρ hρ
  have him : μ.im = 0 := helix_eigenheight_real_of_indep χ N m hQ μ v hv heig
  have hσ : σ₀ = 1 / 2 := (carrierScaleBalanced_iff σ₀).mp hbal
  have hre : ρ.re = σ₀ - Complex.arg μ := by
    rw [hρeq]
    simp [Complex.log_im]
    ring
  rcases le_or_gt 0 μ.re with hpos | hneg
  · have harg : Complex.arg μ = 0 := Complex.arg_eq_zero_iff.mpr ⟨hpos, him⟩
    rw [hre, harg, hσ]
    ring
  · have harg : Complex.arg μ = Real.pi := Complex.arg_eq_pi_iff.mpr ⟨hneg, him⟩
    have h0 := hρ.1
    rw [hre, harg, hσ] at h0
    linarith [Real.pi_gt_three]

/-- **The limit form**: every nontrivial zero is the readout of a limit of native eigenheights. The
stage form above asks for an exact eigenheight at a finite stage; this asks only for a limit. -/
def ZerosAreNativeLimitReadouts {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ ρ ∈ ZD.NontrivialZeros, ∃ μ : ℕ → ℂ, (∀ k, IsNativeEigenheight χ (μ k)) ∧
    ∃ μlim : ℂ, Tendsto μ atTop (𝓝 μlim) ∧
      ∃ σ₀ : ℝ, CarrierScaleBalanced σ₀ ∧ ρ = (σ₀ : ℂ) + I * Complex.log μlim

/-- **The composition, limit form.** Reality passes to the limit (the real axis is closed). -/
theorem composition_limit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : ZerosAreNativeLimitReadouts χ) : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  intro ρ hρ
  obtain ⟨μ, hμ, μlim, hlim, σ₀, hbal, hρeq⟩ := h ρ hρ
  have himk : ∀ k, (μ k).im = 0 := by
    intro k
    obtain ⟨N, m, hQ, v, hv, heig⟩ := hμ k
    exact helix_eigenheight_real_of_indep χ N m hQ (μ k) v hv heig
  have him : μlim.im = 0 := by
    have h := (Complex.continuous_im.tendsto μlim).comp hlim
    exact tendsto_nhds_unique h (by simp only [Function.comp_def, himk]; exact tendsto_const_nhds)
  have hσ : σ₀ = 1 / 2 := (carrierScaleBalanced_iff σ₀).mp hbal
  have hre : ρ.re = σ₀ - Complex.arg μlim := by
    rw [hρeq]
    simp [Complex.log_im]
    ring
  rcases le_or_gt 0 μlim.re with hpos | hneg
  · have harg : Complex.arg μlim = 0 := Complex.arg_eq_zero_iff.mpr ⟨hpos, him⟩
    rw [hre, harg, hσ]
    ring
  · have harg : Complex.arg μlim = Real.pi := Complex.arg_eq_pi_iff.mpr ⟨hneg, him⟩
    have h0 := hρ.1
    rw [hre, harg, hσ] at h0
    linarith [Real.pi_gt_three]

end CriticalLinePhasor.SevenFacts

end

#print axioms CriticalLinePhasor.SevenFacts.sFamily_iff_zero
#print axioms CriticalLinePhasor.SevenFacts.composition
#print axioms CriticalLinePhasor.SevenFacts.composition_limit
