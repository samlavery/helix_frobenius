import RequestProject.HelixSpectralLimit
import RequestProject.HelixSource
import RequestProject.HelixSourceMultiplicity
import RequestProject.SpectralSignFlip
import RequestProject.ThreeDFocalEvent
import RequestProject.Origination
import RequestProject.GradedModeDictionary
import RequestProject.HilbertPolya
import RequestProject.FocalResidualVanishes
import RequestProject.LimitDominance
import RequestProject.Faithfulness
import RequestProject.RoundTrip
import RequestProject.ShannonCascade
import RequestProject.FiniteWeightFiber
import RequestProject.FrobeniusSimilitude
import RequestProject.NoDoubleCancellation
import RequestProject.EulerMaclaurinDirichlet
import RequestProject.TransferContinuation
import RequestProject.ExportAdapter
import RequestProject.DifferencedResolvent

/-!
# Resolvent-trace Hilbert–Pólya capstone (multiplicity-aware, no positivity)

Two layers, plus the multiplicity obligation, all in the `z`-variable `s = ½ + i z` (so a **real**
spectral parameter is exactly the critical line):

* **Layer 1** (`HelixLimit.grh_of_selfAdjoint_spectral_capture`, in `HelixSpectralLimit`):
  *location capture ⟹ GRH*. `poleParam ρ ∈ spectrum ℂ a` for a self-adjoint `a` ⟹ `Re ρ = ½`,
  by spectral reality (`IsSelfAdjoint.im_eq_zero_of_mem_spectrum`). No positivity.
* **Layer 2** (`hcap_of_resolventTrace`, here): *resolvent-trace identity ⟹ location capture*. If a
  regularized resolvent trace `T` equals `−L'/L(½ + i·)` and is regular off `spectrum ℂ a`, then each
  zero's pole-parameter is in the spectrum. The singularity is inherited from `−L'/L`'s pole
  (`HelixSource.LFunction_logDeriv_not_tendsto`) by meromorphic equality — so it transfers *with
  multiplicity* — and "regular off the spectrum" forces it onto the spectrum. **Needs no
  self-adjointness.**
* **Capstone** (`grh_of_selfAdjoint_resolvent_capture`): Layer 1 ∘ Layer 2.

The local adapter consumes a **resolvent-trace identity** `hid` — the trace formula — kept
*local / principal-part* (regularity off the spectrum) rather than global trace-class. The Γ-factor,
trivial zeros, and `s = 1` pole live on the prime/archimedean side and are subtracted into the
regularizer `R₀` so the nontrivial-zero channel is clean; in the principal ξ channel and the
closed-form bridge this identity is discharged upstream and passed into this file as an ordinary
compiled theorem.

The **multiplicity layer** `multiplicityCapture_of_resolventTrace` is stated as the precise remaining
obligation (residue/principal-part equality), reducing to `HelixSource.LFunction_logDeriv_residue_eq_order`
(`residue_ρ(−L'/L) = mult_ρ L`) transported through `s = ½ + i z`.
-/

open Filter Topology

/-! ## Evidence-dossier propositions

Defined here, ahead of the machinery, so the conditional GRH proofs below can take the
**conjunction** `evidence ∧ conditional` as their single hypothesis.  The supporting dossiers are
proven unconditionally further down (`threeDRealEvidence`, `oneDChartEvidence`); the operative
1D correlation bridge is character-indexed and is consumed by the 1D theorem. -/
section EvidenceProps
open Complex CriticalLinePhasor CriticalLinePhasor.SourceHolonomy CriticalLinePhasor.HilbertPolya
open CriticalLinePhasor.GradedModes CriticalLinePhasor.ResidueJump CriticalLinePhasor.CarrierScale
open Faithful

namespace CriticalLinePhasor.RiemannEvidence

/-- A conjunction of internal 3D carrier, completed-readout, arithmetic, and general limit facts.
It contains no theorem mapping every analytic nontrivial zero to a completed physical-height
crossing; see
`NativeCarrierCoverage` for that separate statement. -/
abbrev ThreeDRealEvidence : Prop :=
    (∀ γ : ℝ, (UnconditionalFrobenius.vonNeumannOp γ).IsSymmetric)
    ∧ (∀ E : ℂ → ℂ, ThreeDExhaustive E)
    ∧ (∀ F : ℕ →₀ ℂ, CriticalLinePhasor.CupIdentity.Cup F F = 0 ↔ F = 0)
    ∧ (∀ m n : ℕ, m ≠ 0 → n ≠ 0 →
        Origination.windFromPrimes (m * n)
          = Origination.windFromPrimes m * Origination.windFromPrimes n)
    -- **Feynman's Quiver**: summability of phasors — the finite phasor bank converges to `L`.
    ∧ (∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (s : ℂ), 0 < s.re →
        Tendsto (DirichletPhasorCarrier.finiteCarrier χ s) atTop
          (nhds (DirichletCharacter.LFunction χ s)))
    -- **The phasor version of FTA**: all phasor heights are unique (`logGen` injective).
    ∧ (∀ (m n : ℕ), m ≠ n → SelfAdjointGenerator.logGen m ≠ SelfAdjointGenerator.logGen n)
    -- **No split focus**: at most one mode cancels at any spectral parameter.
    ∧ (∀ (s : ℂ), {n : ℕ |
        SelfAdjointGenerator.specOp SelfAdjointGenerator.Aχ s (Finsupp.single n 1) = 0}.Subsingleton)
    -- **Deligne's Pairs**: self-reciprocal local factor, Frobenius conjugate `det = 1`, weight
    -- product `= 1` (purity at the finite places).
    ∧ (∀ {ι : Type} [Fintype ι] (W : FiniteWeightFiber ι) (X : ℂ), X ≠ 0 →
        W.localPoly X = (-X) ^ (Fintype.card ι) * W.localPoly X⁻¹)
    ∧ (∀ (y : ℝ) (n : ℕ), (FrobeniusSimilitude.frobeniusBlock y n).det = 1)
    ∧ (∀ {ι : Type} [Fintype ι] (W : FiniteWeightFiber ι), ∏ i, W.weight i = 1)
    ∧ (∀ T : ℝ, (hpOperator T).IsHermitian)
    ∧ (∀ γ : ℝ, Module.finrank ℂ (ModeSpace γ) = eventOrder γ)
    -- **Exact harmonic vanishing**: the focal residual vanishes *exactly* iff the L-value does.
    ∧ (∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Z : ℝ),
        HarmonicCell.Dcell χ Z = 0
          ↔ DirichletCharacter.LFunction χ (HarmonicCell.reprPoint χ Z) = 0)
    ∧ (∀ {T : ℝ} (p : WindowIndex T), riemannZeta (line p.1.1) = 0)
    -- **Resolvent trace directly on the 3D modes**: the graded resolvent trace = residue sum.
    ∧ (∀ (w : ℂ) (T : ℝ), (∀ γ ∈ eventWindow T, w ≠ (γ : ℂ)) → ∀ (r : ℝ → ℂ),
        (∀ γ ∈ eventWindow T, Tendsto (fun s => (s - line γ) * logDeriv riemannZeta s)
            (𝓝[≠] line γ) (nhds (r γ))) →
        gradedResolventTrace w T = ∑ γ ∈ eventWindow T, r γ * ((γ : ℂ) - w)⁻¹)
    -- **Shannon Projection Dominance**: the highest level is the real one.
    ∧ (∀ (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (U : Set ℂ), IsOpen U →
        TendstoLocallyUniformlyOn F f atTop U → (∀ n, DifferentiableOn ℂ (F n) U) →
        ∀ (z₀ : ℂ), z₀ ∈ U → f z₀ = 0 → ¬ (∀ᶠ z in nhds z₀, f z = 0) →
        ∀ (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, ∃ z ∈ Metric.ball z₀ ε, F n z = 0)

/-- The conjunction of compiled chart-registration and transport facts.  `S(t)` is the global
coordinate map between the carrier-scale and unit-chart censuses.  Count and jump registration
does not itself establish a pointwise equivalence between completed physical-height crossings and
arbitrary Dirichlet L-zeros.  The character-indexed chart-to-kernel premise is
`OneDCorrelationEvidence`. -/
abbrev OneDChartEvidence : Prop :=
    (∀ t : ℝ, N_pi3 (Real.exp t) - N_1 (Real.exp t) = S t)
    ∧ (∀ T : ℝ, (Fintype.card (WindowIndex T) : ℝ) = 1 + theta T / Real.pi + Smult T)
    ∧ (∀ c y₁ y₂ : ℝ, ‖Complex.exp (-(c : ℂ) * (((1/2 : ℝ) : ℂ) + y₁ * Complex.I))‖
        = ‖Complex.exp (-(c : ℂ) * (((1/2 : ℝ) : ℂ) + y₂ * Complex.I))‖)
    ∧ (∀ y : ℝ, ‖1 - (((1/2 : ℝ) : ℂ) + y * Complex.I)⁻¹‖ = 1)
    ∧ Function.Bijective ConeProjection.record
    -- **Riemann's Fold**: `pipeline x = ½ ↔ x = ½` (real axis preserved across all dimensions).
    ∧ (∀ x : ℝ, ConeProjection.pipeline x = 1 / 2 ↔ x = 1 / 2)
    ∧ (∀ (γ : ℝ), (completedRiemannZeta (1 / 2 + (γ : ℂ) * Complex.I)).im = 0
        ∧ (EtaTrivial.Feta γ = 0 ↔ riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) = 0))
    ∧ (∀ (T γ : ℝ), 0 < γ → γ ≤ T →
        (riemannZeta (line γ) = 0 ↔ ∃ p : WindowIndex T, p.1.1 = γ))
    ∧ (∀ (γ : ℝ), 0 < γ →
        Tendsto (fun s => (s - line γ) * logDeriv riemannZeta s) (𝓝[≠] line γ)
          (𝓝 (eventOrder γ : ℂ)) ∧ HasJump Smult γ (eventOrder γ))
    -- **1D approximation via infinite analytic calculation**.
    ∧ (∀ (s : ℂ), 0 < s.re → s.re < 1 → s ≠ 1 →
        ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
          ‖GRH.SpiralInduction.S s N - riemannZeta s -
            (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ ≤ C * (↑N : ℝ) ^ (-s.re))
    -- **Faithful transport** (local correlation).
    ∧ (∀ (a : ℕ → ℂ) (Cc θ : ℝ), 0 ≤ θ →
        (∀ n : ℕ, ‖∑ k ∈ Finset.range n, a k‖ ≤ Cc * (n : ℝ) ^ θ) → ∀ (s : ℂ), θ < s.re →
        ∃ L : ℂ,
          Tendsto (fun N => ∑ n ∈ Finset.range N, a n * ((n + 1 : ℕ) : ℂ) ^ (-s)) atTop (nhds L))
    -- **Shannon Cascade**: an accumulation of stage features is a feature of the limit.
    ∧ (∀ (Cc : Cascade.MidpointCascade) (z : ℂ),
        (∀ ε > 0, ∀ᶠ n in atTop, ∃ w ∈ Metric.ball z ε, Cc.stage n w = 0) →
        XiChannel.xiSection z = 0)
    -- **S(t) detects every crossing**; every count-jump belongs entirely to S(t).
    ∧ (∀ (γ : ℝ), 0 < γ → (HasJump S γ 1 ↔ riemannZeta (line γ) = 0))
    ∧ (∀ (γ j : ℝ), HasJump (fun t => (zeroEventCount t : ℝ)) γ j ↔ HasJump S γ j)
    -- **The loss ledger**: radius/phase lost yet the chart chain injective.
    ∧ (∃ f₁ f₂ : ConeProjection.Fiber, ConeProjection.radial f₁ ≠ ConeProjection.radial f₂ ∧
        ConeProjection.realize f₁ ≠ ConeProjection.realize f₂ ∧
        ConeProjection.geomProj f₁ = ConeProjection.geomProj f₂)
    ∧ Function.Injective (fun y : ℝ => 1 - (((1/2 : ℝ) : ℂ) + y * Complex.I)⁻¹)
    -- **Native identification**: the π/3 native count equals the zero-event count.
    ∧ (∀ (t : ℝ), N_pi3 (Real.exp t) = (zeroEventCount t : ℝ))
    -- **Resolvent-trace `T→∞` limit (chart)**.
    ∧ (∀ (w : ℂ), Tendsto (fun T => windowedTrace (fun γ => ((γ : ℂ) - w)⁻¹ - (γ : ℂ)⁻¹) T)
        atTop (nhds (ResolventLimit.diffResolvent w)))

/-- The one-dimensional member of the correspondence: a chart-reported zero, with its ordinate. -/
def OneDChartZero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) : Prop :=
  DirichletCharacter.LFunction χ ρ = 0 ∧ ∃ γ : ℝ, γ = ρ.im

/-- The operative pointwise 1D premise for a character `χ`: every chart-reported analytic zero
realizes a nonzero scalar-fibre kernel at that same complex point.  Because the kernel equation
already forces the carrier abscissa, `grh_of_oneDCorrelationEvidence` shows that this premise alone
implies the critical-line conclusion. -/
def OneDCorrelationEvidence {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ⦃ρ : ℂ⦄, OneDChartZero χ ρ →
    ∃ γ : ℝ, ∃ ψ : ℂ, ψ ≠ 0 ∧
      SelfAdjointGenerator.specOp (UnconditionalFrobenius.vonNeumannOp γ) ρ ψ = 0 ∧ γ = ρ.im

end CriticalLinePhasor.RiemannEvidence
end EvidenceProps

namespace HelixLimit

variable {N : ℕ} [NeZero N]

/-- **Resonance lemma (principal-part).** The regularized resolvent trace `T = −L'/L(½+i·)` has **no
    finite limit** at `poleParam ρ` for every nontrivial zero `ρ` — it *resonates* (a pole) exactly at
    the zero parameters. Inherited from `−L'/L`'s pole at `ρ` (`HelixSource.LFunction_logDeriv_not_tendsto`)
    through the affine `s = ½ + i z`; meromorphic equality, so the resonance carries multiplicity. -/
theorem resonates_of_traceIdentity {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z))
    {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ¬ ∃ L, Tendsto T (𝓝[≠] (poleParam ρ)) (𝓝 L) := by
  have key : ∀ s : ℂ, (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) = s := fun s => by
    linear_combination (-(s - 1 / 2)) * Complex.I_sq
  have hhρ : -Complex.I * (ρ - 1 / 2) = poleParam ρ := by
    rw [poleParam]
    linear_combination Complex.I * Complex.re_add_im ρ - (ρ.im : ℂ) * Complex.I_sq
  rintro ⟨L, hL⟩
  refine HelixSource.LFunction_logDeriv_not_tendsto χ hρ ⟨L, ?_⟩
  have hcont : Tendsto (fun s : ℂ => -Complex.I * (s - 1 / 2)) (𝓝[≠] ρ)
      (𝓝[≠] (poleParam ρ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have hc : Continuous (fun s : ℂ => -Complex.I * (s - 1 / 2)) := by fun_prop
      have hct := hc.tendsto ρ
      rwa [hhρ] at hct
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro hc
      rw [← hhρ] at hc
      have h3 : -Complex.I * ((s - 1 / 2) - (ρ - 1 / 2)) = 0 := by linear_combination hc
      have h4 : (s - 1 / 2) - (ρ - 1 / 2) = 0 :=
        (mul_eq_zero.mp h3).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
      exact hs (by linear_combination h4)
  have hcomp := hL.comp hcont
  have heqfun : (fun s : ℂ => -logDeriv (DirichletCharacter.LFunction χ) s)
      = (T ∘ fun s : ℂ => -Complex.I * (s - 1 / 2)) := by
    funext s; simp only [Function.comp_apply, hid, key]
  rw [heqfun]; exact hcomp

/-- **Layer 2 — resolvent-trace ⟹ location capture** (self-adjointness *not* used). -/
theorem hcap_of_resolventTrace {A : Type*} [CStarAlgebra A] {a : A}
    (χ : DirichletCharacter ℂ N) (T : ℂ → ℂ)
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z))
    (hReg : ∀ z, z ∉ spectrum ℂ a → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)) :
    ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, poleParam ρ ∈ spectrum ℂ a := by
  intro ρ hρ
  by_contra hns
  exact resonates_of_traceIdentity hid hρ (hReg (poleParam ρ) hns)

/-- **Resolvent-trace capstone** = Layer 1 ∘ Layer 2. A self-adjoint channel whose regularized
    resolvent trace `T` equals `−L'/L(½ + i·)` (and is regular off its spectrum) forces GRH, by
    spectral reality alone — no positivity, no eigenvalue limit, multiplicity inherited from the
    meromorphic identity. -/
theorem grh_of_selfAdjoint_resolvent_capture
    {A : Type*} [CStarAlgebra A] [StarModule ℂ A] {a : A} (ha : IsSelfAdjoint a)
    (χ : DirichletCharacter ℂ N) (T : ℂ → ℂ)
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z))
    (hReg : ∀ z, z ∉ spectrum ℂ a → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)) :
    GRHSpectral.GRH χ :=
  grh_of_selfAdjoint_spectral_capture ha χ (hcap_of_resolventTrace χ T hid hReg)

/-- **The spectral-side dual receiver** (principal-part form — the proof object). A self-adjoint
    channel `a` *receives* `χ`'s zeros when its regularized resolvent trace `T`:
    * `regular_off_spectrum` — has a finite limit at every point **off** `spectrum ℂ a`; and
    * `resonates_at_zeros` — has **no** finite limit (a pole/resonance) at every zero parameter
      `poleParam ρ`.
    The zero **dips/resonances** are exactly the spectral singularities of `a`. Stated locally via
    principal parts: no global trace-class, no positivity. -/
structure ResolventReceiver {A : Type*} [CStarAlgebra A] (a : A)
    (χ : DirichletCharacter ℂ N) (T : ℂ → ℂ) : Prop where
  regular_off_spectrum : ∀ z, z ∉ spectrum ℂ a → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)
  resonates_at_zeros : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
    ¬ ∃ L, Tendsto T (𝓝[≠] (poleParam ρ)) (𝓝 L)

/-- A receiver captures every zero parameter into its spectrum (resonance ∧ regular-off-spectrum). -/
theorem ResolventReceiver.locationCapture {A : Type*} [CStarAlgebra A] {a : A}
    {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ} (h : ResolventReceiver a χ T) :
    ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, poleParam ρ ∈ spectrum ℂ a := by
  intro ρ hρ
  by_contra hns
  exact h.resonates_at_zeros ρ hρ (h.regular_off_spectrum (poleParam ρ) hns)

/-- **GRH from a self-adjoint receiver — the dual capstone.** A self-adjoint channel receiving `χ`'s
    zeros forces GRH, by spectral reality alone (no positivity). -/
theorem grh_of_resolventReceiver {A : Type*} [CStarAlgebra A] [StarModule ℂ A] {a : A}
    (ha : IsSelfAdjoint a) {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (h : ResolventReceiver a χ T) : GRHSpectral.GRH χ :=
  grh_of_selfAdjoint_spectral_capture ha χ h.locationCapture

/-- The meromorphic trace identity `T = −L'/L(½+i·)` (regular off the spectrum) **provides** a
    receiver: the resonances are `resonates_of_traceIdentity`. So discharging the global identity is
    one (stronger) way to realize the local principal-part object — the single remaining content is
    *"a self-adjoint channel whose resolvent trace resonates at the zeros."* -/
theorem ResolventReceiver.of_traceIdentity {A : Type*} [CStarAlgebra A] {a : A}
    {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z))
    (hReg : ∀ z, z ∉ spectrum ℂ a → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)) :
    ResolventReceiver a χ T where
  regular_off_spectrum := hReg
  resonates_at_zeros := fun ρ hρ => resonates_of_traceIdentity hid hρ

/-! ## Harmonic / boundary-value realization (continuous-spectrum compatible)

The "operator" is just the boundary trace `T : ℂ → ℂ` together with its limiting behaviour: its
spectrum is the **singular support** `{z | T has no finite limit at z}` — the absorption set. Stated by
`Tendsto`, so it covers **continuous spectrum** (Connes absorption), not only discrete atoms. The
self-adjointness becomes **reality of the boundary values** (`singular support ⊆ ℝ`), which is the
earned no-drift / conjugate-harmonic conservation — not a positivity floor and not an assumption that
the zeros are on the line. -/

/-- The **singular support** of a boundary trace `T`: where `T` has no finite limit (the absorption /
    resonance set). For a genuine resolvent trace this is the spectrum. -/
def SingularSupport (T : ℂ → ℂ) : Set ℂ := {z | ¬ ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)}

/-- **Harmonic-boundary capstone — real boundary values force the line.** If `T`'s singular support is
    **real** (`hreal`: the self-adjoint / conservative-harmonic condition — real boundary values) and
    `T` **resonates** at every zero parameter (`hres`), then GRH. The whole forcing is
    `singular support ⊆ ℝ`: `poleParam ρ` real ⟹ `σ = ½`. No C⋆-algebra, no discrete spectrum, no
    positivity — works for continuous-spectrum / Connes-absorption channels. `hreal` is the earned
    reality, *not* an assumption that the zeros are on-line. -/
theorem grh_of_realSingularSupport {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (hreal : ∀ z ∈ SingularSupport T, z.im = 0)
    (hres : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, poleParam ρ ∈ SingularSupport T) :
    GRHSpectral.GRH χ := by
  intro ρ hρ
  have him : (poleParam ρ).im = 0 := hreal (poleParam ρ) (hres ρ hρ)
  rw [poleParam_im] at him
  linarith

/-- The trace identity puts every zero parameter into the singular support: `T` resonates (absorbs)
    at each `poleParam ρ`. So discharging `hreal` (real boundary values) harmonically realizes the
    receiver and closes GRH via `grh_of_realSingularSupport`. -/
theorem zeros_subset_singularSupport_of_traceIdentity {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z)) :
    ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, poleParam ρ ∈ SingularSupport T :=
  fun ρ hρ => resonates_of_traceIdentity hid hρ

/-- **Self-adjoint receiver — boundary form, NOT "real boundary values".** `T` is a self-adjoint
    receiver when it is **regular off the real axis**: a finite limit at every `z` with `Im z ≠ 0`.
    This is the genuine self-adjoint content — the resolvent / bulk harmonic field is analytic off `ℝ`,
    equivalently `spectrum ⊆ ℝ` — and for a self-adjoint operator it is a *theorem* (resolvent set
    `⊇ ℂ∖ℝ`), **not** an assumption that the zeros are on-line. -/
def IsSelfAdjointReceiver (T : ℂ → ℂ) : Prop :=
  ∀ z, z.im ≠ 0 → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)

/-- **Earned reality (self-adjoint ⟹ real absorption).** A self-adjoint receiver's singular support is
    real: where it resonates/absorbs, the parameter lies on `ℝ`. This is the boundary form of
    `self-adjoint ⇒ spectrum ⊆ ℝ` — **derived from `IsSelfAdjointReceiver`, not assumed.** -/
theorem real_absorption_of_selfAdjoint {T : ℂ → ℂ} (hsa : IsSelfAdjointReceiver T) :
    ∀ z ∈ SingularSupport T, z.im = 0 := by
  intro z hz
  by_contra him
  exact hz (hsa z him)

/-- **(2a) — self-adjointness turns "regular off the spectrum" into a self-adjoint receiver.** A
    bounded self-adjoint `a` has real spectrum (`IsSelfAdjoint.im_eq_zero_of_mem_spectrum`), so any
    boundary trace `T` regular at every point **off the spectrum** is automatically regular off `ℝ` —
    an `IsSelfAdjointReceiver`. This is the earned reality `hsa` the harmonic capstone consumes:
    supplied by the operator's self-adjointness, with **no input about the zeros**. (`hReg` — regular
    off the spectrum — is the resolvent trace's own regularity; for the unbounded `gramOp` this lemma
    applies after passing to its bounded resolvent `(gramOp + 1)⁻¹`.) -/
theorem isSelfAdjointReceiver_of_regular_off_spectrum {A : Type*} [CStarAlgebra A] [StarModule ℂ A]
    {a : A} (ha : IsSelfAdjoint a) {T : ℂ → ℂ}
    (hReg : ∀ z, z ∉ spectrum ℂ a → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)) :
    IsSelfAdjointReceiver T :=
  fun z hz => hReg z fun hmem => hz (ha.im_eq_zero_of_mem_spectrum hmem)

/-- **Unitary receiver — the bounded 2D / Möbius-circle coordinate.** `T` has a finite limit at every
    `z` **off the unit circle** (`‖z‖ ≠ 1`). The bounded-operator analog of `IsSelfAdjointReceiver`,
    with the real axis replaced by the unit circle (the Cayley/Möbius image of `ℝ`, where `‖w‖ = 1 ⟺`
    on-line). This is the natural reality of the **bounded** loss-projection operator: no unbounded
    resolvent — the 2D shadow is compact. -/
def IsUnitaryReceiver (T : ℂ → ℂ) : Prop :=
  ∀ z, ‖z‖ ≠ 1 → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)

/-- **(2a), unitary form — unitarity turns "regular off the spectrum" into a unitary receiver.** A
    unitary `u` has spectrum on the unit circle (`spectrum.norm_eq_one_of_unitary`), so any trace `T`
    regular off the spectrum is regular off the circle. The earned reality of the **bounded** 2D
    loss-projection operator (its values are the Möbius circle), supplied by unitarity with **no input
    about the zeros** — the exact dual of `isSelfAdjointReceiver_of_regular_off_spectrum`. -/
theorem isUnitaryReceiver_of_regular_off_spectrum {A : Type*} [CStarAlgebra A]
    {u : A} (hu : u ∈ unitary A) {T : ℂ → ℂ}
    (hReg : ∀ z, z ∉ spectrum ℂ u → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)) :
    IsUnitaryReceiver T :=
  fun z hz => hReg z fun hmem => hz (spectrum.norm_eq_one_of_unitary hu hmem)

/-- **`hReg` is a theorem, not a hypothesis, for a bounded operator.** The resolvent
    `w ↦ resolvent a w` is differentiable — hence continuous — at every point of the resolvent set
    (`spectrum.hasDerivAt_resolvent`), i.e. **off the spectrum**. So any continuous scalar readout `φ`
    of it is regular off the spectrum, with the limit equal to the value. No hypotheses. -/
theorem regular_off_spectrum_of_resolvent {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (a : A) {φ : A → ℂ} (hφ : Continuous φ) :
    ∀ z, z ∉ spectrum ℂ a → ∃ L, Tendsto (fun w => φ (resolvent a w)) (𝓝[≠] z) (𝓝 L) := by
  intro z hz
  have hk : z ∈ resolventSet ℂ a := by by_contra h; exact hz h
  have hcont : ContinuousAt (fun w => φ (resolvent a w)) z :=
    hφ.continuousAt.comp (spectrum.hasDerivAt_resolvent_const_left hk).continuousAt
  exact ⟨_, hcont.tendsto.mono_left nhdsWithin_le_nhds⟩

/-- **Unconditional self-adjoint receiver — `hReg` discharged.** For a **bounded** self-adjoint `a`
    and any continuous readout `φ`, the resolvent trace `z ↦ φ(resolvent a z)` is an
    `IsSelfAdjointReceiver` — **no hypotheses beyond self-adjointness of the (bounded) operator.** The
    reality side is fully earned: self-adjoint spectrum (off ℝ) + resolvent continuity (off spectrum).
    The readout identification with `−L'/L` is supplied by the upstream closed-form / Hadamard trace
    bridge when this adapter is used in the full chain. -/
theorem isSelfAdjointReceiver_resolventReadout {A : Type*} [CStarAlgebra A] [StarModule ℂ A]
    {a : A} (ha : IsSelfAdjoint a) {φ : A → ℂ} (hφ : Continuous φ) :
    IsSelfAdjointReceiver (fun z => φ (resolvent a z)) :=
  isSelfAdjointReceiver_of_regular_off_spectrum ha (regular_off_spectrum_of_resolvent a hφ)

/-- **Unconditional unitary receiver — `hReg` discharged (the bounded 2D form).** For a unitary `u`
    (the bounded loss-projection operator's natural form) and any continuous readout `φ`, the resolvent
    trace `z ↦ φ(resolvent u z)` is an `IsUnitaryReceiver` — no hypotheses beyond unitarity. Earned
    reality on the compact circle; only the `−L'/L` identification remains. -/
theorem isUnitaryReceiver_resolventReadout {A : Type*} [CStarAlgebra A]
    {u : A} (hu : u ∈ unitary A) {φ : A → ℂ} (hφ : Continuous φ) :
    IsUnitaryReceiver (fun z => φ (resolvent u z)) :=
  isUnitaryReceiver_of_regular_off_spectrum hu (regular_off_spectrum_of_resolvent u hφ)

/-- **GRH from a self-adjoint harmonic receiver — the Connes/absorption capstone.** A self-adjoint
    receiver (regular off `ℝ`) whose singular support contains every zero parameter forces GRH:
    real absorption (earned) + resonance at the zeros ⟹ `poleParam ρ` real ⟹ `σ = ½`. No discrete
    spectrum, no positivity — continuous-spectrum compatible. -/
theorem grh_of_harmonicTraceReceiver {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (hsa : IsSelfAdjointReceiver T)
    (hres : ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, poleParam ρ ∈ SingularSupport T) :
    GRHSpectral.GRH χ :=
  grh_of_realSingularSupport (real_absorption_of_selfAdjoint hsa) hres

/-- **The harmonic capstone from the trace identity.** A self-adjoint receiver whose boundary trace
    equals `−L'/L(½+i·)` forces GRH: the zeros become boundary absorption resonances
    (`zeros_subset_singularSupport_of_traceIdentity`), and self-adjoint reality puts them on `ℝ`.
    In the full chain the boundary identity is supplied by the closed-form / Hadamard trace bridge;
    self-adjointness is `regular off ℝ`. -/
theorem grh_of_harmonicTraceReceiver_traceIdentity {χ : DirichletCharacter ℂ N} {T : ℂ → ℂ}
    (hsa : IsSelfAdjointReceiver T)
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z)) :
    GRHSpectral.GRH χ :=
  grh_of_harmonicTraceReceiver hsa (zeros_subset_singularSupport_of_traceIdentity hid)

/-- **GRH from a self-adjoint operator whose resolvent readout is `−L'/L`.** The on-line forcing is
    entirely **self-adjointness**: `isSelfAdjointReceiver_resolventReadout` is unconditional — a
    self-adjoint spectrum is real, so the resolvent is regular off `ℝ`. The *only* input is the trace
    identity `hid` (the operator's resolvent readout equals `−L'/L(½+i·)`), supplied upstream by the
    closed-form / Hadamard trace bridge and read in operator form. Self-adjointness ⟹ on-line;
    energy cancellation ⟹ the trace identity consumed here. -/
theorem grh_of_selfAdjoint_resolventReadout {A : Type*} [CStarAlgebra A] [StarModule ℂ A]
    {a : A} (ha : IsSelfAdjoint a) {φ : A → ℂ} (hφ : Continuous φ)
    {χ : DirichletCharacter ℂ N}
    (hid : ∀ z, φ (resolvent a z)
        = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z)) :
    GRHSpectral.GRH χ :=
  grh_of_harmonicTraceReceiver_traceIdentity (isSelfAdjointReceiver_resolventReadout ha hφ) hid

/-- **Multiplicity layer — the resolvent trace's residue at `poleParam ρ` is the zero multiplicity.**
    From the meromorphic identity `T = −L'/L(½+i·)`, the principal part of `T` at `z = poleParam ρ` is

    `T z = (i · n) · (z − poleParam ρ)⁻¹ + G z`,  `G` analytic at `poleParam ρ`, `n = mult_ρ(L) ≥ 1`.

    So `T` has a **simple pole** there with **residue `i · n`** — the resolvent-trace residue equals the
    zero multiplicity, up to the change-of-variable Jacobian `ds/dz = i`. (For a genuine resolvent
    trace `Tr((a−z)⁻¹)` the residue at an eigenvalue is its spectral multiplicity, so this is
    `spectralMultiplicity a (poleParam ρ) = mult_ρ(L)`.) Built by transporting
    `HelixSource.LFunction_logDeriv_residue_eq_order` through `s = ½ + i z`. No positivity, no
    self-adjointness — pure meromorphic equality, so multiplicity rides along linearly. -/
theorem multiplicityCapture_of_resolventTrace {A : Type*} [CStarAlgebra A] {a : A}
    (χ : DirichletCharacter ℂ N) (T : ℂ → ℂ)
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ) (1 / 2 + Complex.I * z))
    {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ∃ (n : ℕ) (G : ℂ → ℂ), 1 ≤ n ∧ AnalyticAt ℂ G (poleParam ρ) ∧
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ = (n : ℕ∞) ∧
      ∀ᶠ z in 𝓝[≠] (poleParam ρ),
        T z = Complex.I * (n : ℂ) * (z - poleParam ρ)⁻¹ + G z := by
  obtain ⟨n, g, hn, hg, hgne, hord, hform⟩ := HelixSource.LFunction_logDeriv_residue_eq_order χ hρ
  -- change of variable `w z = ½ + i z`, with `w (poleParam ρ) = ρ` and `w z − ρ = i (z − poleParam ρ)`
  have key : ∀ s : ℂ, (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) = s := fun s => by
    linear_combination (-(s - 1 / 2)) * Complex.I_sq
  have hhρ : -Complex.I * (ρ - 1 / 2) = poleParam ρ := by
    rw [poleParam]
    linear_combination Complex.I * Complex.re_add_im ρ - (ρ.im : ℂ) * Complex.I_sq
  have hwρ : (1 : ℂ) / 2 + Complex.I * poleParam ρ = ρ := by rw [← hhρ]; exact key ρ
  have hwsub : ∀ z : ℂ, (1 : ℂ) / 2 + Complex.I * z - ρ = Complex.I * (z - poleParam ρ) :=
    fun z => by linear_combination hwρ
  refine ⟨n, fun z => -(deriv g (1 / 2 + Complex.I * z) / g (1 / 2 + Complex.I * z)),
    hn, ?_, hord, ?_⟩
  · -- analyticity of the holomorphic part `G`
    have haff : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) / 2 + Complex.I * z) (poleParam ρ) := by
      apply analyticAt_const.add
      exact analyticAt_const.mul analyticAt_id
    have hdgg : AnalyticAt ℂ (fun s : ℂ => deriv g s / g s) ρ := (hg.deriv).div hg hgne
    have hcomp : AnalyticAt ℂ
        ((fun s : ℂ => deriv g s / g s) ∘ fun z : ℂ => (1 : ℂ) / 2 + Complex.I * z)
        (poleParam ρ) := by
      refine AnalyticAt.comp ?_ haff
      rw [hwρ]
      exact hdgg
    exact hcomp.neg
  · -- the principal-part identity, transported through `w`
    have htendsto : Tendsto (fun z : ℂ => (1 : ℂ) / 2 + Complex.I * z) (𝓝[≠] (poleParam ρ))
        (𝓝[≠] ρ) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
        have hc : Continuous (fun z : ℂ => (1 : ℂ) / 2 + Complex.I * z) := by fun_prop
        have hct := hc.tendsto (poleParam ρ)
        rwa [show (1 : ℂ) / 2 + Complex.I * poleParam ρ = ρ from hwρ] at hct
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
        intro hc
        have h3 : Complex.I * (z - poleParam ρ) = 0 := by
          rw [← hwsub]; linear_combination hc
        exact hz (by
          have h4 := (mul_eq_zero.mp h3).resolve_left Complex.I_ne_zero
          linear_combination h4)
    filter_upwards [htendsto.eventually hform, self_mem_nhdsWithin] with z hPz hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    rw [hid z, hPz, hwsub z, mul_inv, Complex.inv_I]
    ring

/-! ## Local principal parts ⟹ global trace identity — the entire-error kill

`hcap`/`ResolventReceiver` only need the *local* resonance (same poles). Upgrading the **local**
principal-part equality to the **global** meromorphic identity `T_spec = T_L` is the entire-error step:
the difference has no surviving poles, hence is entire, and a growth/normalization bound kills it
(Liouville). -/

/-- **Entire from cancelled principal parts.** A function meromorphic *and continuous* at every point
    is entire: where the principal parts cancel (the difference is continuous), the meromorphic
    singularities are removable. -/
theorem differentiable_of_meromorphic_continuous {D : ℂ → ℂ}
    (hMero : ∀ z, MeromorphicAt D z) (hCont : Continuous D) : Differentiable ℂ D :=
  fun z => ((hMero z).analyticAt hCont.continuousAt).differentiableAt

/-- **Entire-error kill (Liouville / decay).** An entire function tending to `0` at infinity
    (`cocompact`) is identically `0`. -/
theorem eq_zero_of_entire_tendsto_zero {D : ℂ → ℂ} (hD : Differentiable ℂ D)
    (hdecay : Tendsto D (Filter.cocompact ℂ) (𝓝 0)) : D = 0 := by
  funext z; simpa using hD.apply_eq_of_tendsto_cocompact z hdecay

/-- **Local ⟹ global trace identity.** If `Tspec` and `TL` are meromorphic, their difference is
    continuous (principal parts equal — *no surviving poles*) and decays at infinity
    (growth/normalization kill), then `Tspec = TL` globally. This is the exact local-to-global
    transition: same poles + same residues, upgraded past the entire error. Feeding `Tspec` = a
    self-adjoint channel's resolvent trace and `TL = −L'/L(½+i·)` gives the `hid` of the capstone. -/
theorem global_traceIdentity_of_local {Tspec TL : ℂ → ℂ}
    (hspec : ∀ z, MeromorphicAt Tspec z) (hL : ∀ z, MeromorphicAt TL z)
    (hCont : Continuous (Tspec - TL))
    (hdecay : Tendsto (Tspec - TL) (Filter.cocompact ℂ) (𝓝 0)) :
    Tspec = TL :=
  sub_eq_zero.mp <| eq_zero_of_entire_tendsto_zero
    (differentiable_of_meromorphic_continuous (fun z => (hspec z).sub (hL z)) hCont) hdecay

/-! ## RH from the GRH capstone at the trivial character

The principal-character (mod 1) L-function **is** `riemannZeta`
(`DirichletCharacter.LFunction_modOne_eq`, Mathlib, definitional).  So the GRH capstone
of this file, read at `χ = 1`, is RH: the strip zeros it places are ζ's own.  The GRH
part is `grh_of_harmonicTraceReceiver` — a self-adjoint receiver (regular off `ℝ`, the
earned reality) that resonates at the zeros.  The out-of-strip cases (`Re ≥ 1`
nonvanishing; `Re ≤ 0` trivial zeros via the completed-ζ functional equation) are
Mathlib.  Self-adjointness places the strip zeros; the FE and non-vanishing dispatch the
rest. -/

/-- **RH from the GRH capstone at the trivial character.**  For the character mod 1, a
self-adjoint receiver `T` (regular off `ℝ`) that resonates at every nontrivial-zero
parameter yields Mathlib's `RiemannHypothesis`.  The GRH is
`grh_of_harmonicTraceReceiver`; the trivial-character bridge is
`LFunction_modOne_eq`.  **Pure and unconditional** — `rh_from_grh`: no operator, no
receiver, no conditional beyond GRH itself.  The two GRH routes below (identity and
correlation, each with its own isolated conditional) feed it. -/
theorem RH_of_GRH_Trivial_Char (χ₁ : DirichletCharacter ℂ 1)
    (hgrh : GRHSpectral.GRH χ₁) :
    RiemannHypothesis := by
  -- the strip-zero placement, transported to ζ through `LFunction χ₁ = riemannZeta`
  have hline : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → ρ.re = 1 / 2 := by
    intro ρ h0 h1 hz
    refine hgrh ρ ⟨h0, h1, ?_⟩
    simp only [DirichletCharacter.LFunction_modOne_eq]
    exact hz
  -- the Mathlib-only out-of-strip bridge
  intro s hs hnt hne1
  by_cases h1 : 1 ≤ s.re
  · exact absurd hs (riemannZeta_ne_zero_of_one_le_re h1)
  push_neg at h1
  by_cases h0 : 0 < s.re
  · exact hline s h0 h1 hs
  push_neg at h0
  exfalso
  have hne0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp [riemannZeta_zero] at hs
  have hdef : completedRiemannZeta s / s.Gammaℝ = 0 :=
    (riemannZeta_def_of_ne_zero hne0).symm.trans hs
  rw [div_eq_zero_iff] at hdef
  have hξ : completedRiemannZeta s = 0 := by
    rcases hdef with h | h
    · exact h
    · exfalso
      simp only [Complex.Gammaℝ] at h
      have hpi : (↑Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_pos.ne'))
      have hΓ : Complex.Gamma (s / 2) = 0 :=
        (mul_eq_zero.mp h).resolve_left hpi
      rw [Complex.Gamma_eq_zero_iff] at hΓ
      obtain ⟨m, hm⟩ := hΓ
      have hs_eq : s = -2 * (m : ℂ) := by linear_combination 2 * hm
      rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
      · rw [hm0] at hs_eq; simp at hs_eq; exact hne0 hs_eq
      · apply hnt
        refine ⟨m - 1, ?_⟩
        have hcast : ((m - 1 : ℕ) : ℂ) + 1 = (m : ℂ) := by
          have h : (m - 1 : ℕ) + 1 = m := Nat.sub_add_cancel hm_pos
          exact_mod_cast h
        rw [hs_eq, ← hcast]
  have hξ1 : completedRiemannZeta (1 - s) = 0 :=
    (completedRiemannZeta_one_sub s).trans hξ
  have hne1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
  have hζ1s : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_def_of_ne_zero hne1', hξ1, zero_div]
  exact riemannZeta_ne_zero_of_one_le_re
    (by simp only [Complex.sub_re, Complex.one_re]; linarith) hζ1s

/-! ## Logical audit of the worked GRH interfaces

The carrier midpoint is derived in `ThreeDFocalEvent`: `carrierAbscissa` is selected by the
unique unit-gauge area-law balance condition, and only then normalized to `1 / 2`.  The scalar
fibre operator `vonNeumannOp γ = γ • id` is a local coordinate detector: its kernel calculation
shows that a point already represented at real height `γ` has the carrier's derived abscissa.  It
does not identify the analytic zero set with the native focal-event set.

The declarations below expose that identification boundary exactly.

* `NativeCarrierCoverage χ` is midpoint-free: it says an analytic zero produces a completed
  fibre crossing at physical height `exp ρ.im`, whose ordinate is `ρ.im`.
* `threeDCrossings_iff_grh_and_nativeCarrierCoverage` proves that the older identity premise is
  precisely the conjunction of the critical-line conclusion and midpoint-free coverage.
* `oneD_zeta_zero_correlated_proved` proves the disjunctive routing proposition unconditionally;
  `grh_of_oneDCorrelationEvidence` shows that the separate chart-to-kernel evidence is the
  substantive 1D identification premise.

Thus the two legacy implication names remain API-compatible, but their proofs now call the
minimal premise directly.  The independent operator interface earlier in this file is
`grh_of_selfAdjoint_resolvent_capture`: it takes a fixed self-adjoint operator together with a
proved analytic-zero-to-spectrum capture map. -/

open CriticalLinePhasor.SelfAdjointGenerator CriticalLinePhasor.UnconditionalFrobenius
  CriticalLinePhasor.ThreeDFocal in
/-- Legacy identity premise in physical-height coordinates.  A completed fibre crossing occurs
by focal cancellation at a positive helix height `Z`; its analytic ordinate is `y = log Z`.  The equality
`ρ = carrierPointAtHeight Z` also includes the critical-line conclusion. -/
def ThreeD_crossings_are_real_zeros {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∃ Z : ℝ,
    CompletedThreeDZeroAtHeight χ Z ∧ ρ = carrierPointAtHeight Z

open CriticalLinePhasor.ThreeDFocal in
/-- Midpoint-free analytic coverage in physical-height coordinates: the zero with ordinate
`ρ.im` produces a completed fibre event at helix height `Z = exp ρ.im`, so `log Z = ρ.im`.
This proposition contains neither `carrierPointAtHeight` nor an equality fixing the real part. -/
def NativeCarrierCoverage {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
    CompletedThreeDZeroAtHeight χ (Real.exp ρ.im)

open CriticalLinePhasor.ThreeDFocal in
/-- The exact logical content of the identity premise: native-event coverage does not select an
abscissa, while `GRH χ` supplies the analytic-zero identification with the area-law carrier. -/
theorem threeDCrossings_iff_grh_and_nativeCarrierCoverage {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    ThreeD_crossings_are_real_zeros χ ↔ GRHSpectral.GRH χ ∧ NativeCarrierCoverage χ := by
  constructor
  · intro h
    constructor
    · intro ρ hρ
      obtain ⟨Z, _hzero, hrepr⟩ := h ρ hρ
      rw [hrepr]
      simp [carrierPointAtHeight]
    · intro ρ hρ
      obtain ⟨Z, hzero, hrepr⟩ := h ρ hρ
      have hy : ρ.im = Real.log Z := by
        rw [hrepr]
        simp
      have hZ : Real.exp ρ.im = Z := by
        rw [hy, Real.exp_log hzero.1]
      simpa only [hZ] using hzero
  · rintro ⟨hgrh, hcoverage⟩ ρ hρ
    have hzero := hcoverage ρ hρ
    refine ⟨Real.exp ρ.im, hzero, ?_⟩
    rw [carrierPointAtHeight_exp]
    apply Complex.ext
    · simpa using hgrh ρ hρ
    · simp

open CriticalLinePhasor.ThreeDFocal in
/-- The identity premise directly contains the critical-line conclusion through its carrier
equality; no fibre-operator or focal-cancellation fact is needed for this implication. -/
theorem grh_of_threeDCrossings {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : ThreeD_crossings_are_real_zeros χ) : GRHSpectral.GRH χ := by
  exact (threeDCrossings_iff_grh_and_nativeCarrierCoverage χ).1 h |>.1

open CriticalLinePhasor.SelfAdjointGenerator CriticalLinePhasor.UnconditionalFrobenius
  CriticalLinePhasor.ThreeDFocal in
/-- Legacy disjunctive routing proposition.  Its right branch merely records an analytic zero
and chooses its own imaginary part as ordinate, so the proposition is proved unconditionally by
`oneD_zeta_zero_correlated_proved`.  The separate `OneDCorrelationEvidence χ` is the premise that
places a kernel at the analytic zero. -/
def OneD_zeta_zero_correlated {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
    -- 3D primary: the completed fibre has a focal cancellation at physical height `Z`,
    -- whose chart ordinate is `log Z`.
    (∃ Z : ℝ, CompletedThreeDZeroAtHeight χ Z ∧ ρ = carrierPointAtHeight Z)
    ∨
    -- 3D NOT primary → 1D primary: the chart reports a zero and its ordinate.  The operative
    -- evidence `OneDCorrelationEvidence χ` realizes this report as the von Neumann kernel.
    CriticalLinePhasor.RiemannEvidence.OneDChartZero χ ρ

/-- The routing proposition is unconditional: every member of `NontrivialZeros χ` satisfies
the right branch because `OneDChartZero` records only the defining L-value equation and its own
imaginary coordinate. -/
theorem oneD_zeta_zero_correlated_proved {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : OneD_zeta_zero_correlated χ := by
  intro ρ hρ
  right
  exact ⟨hρ.2.2, ρ.im, rfl⟩

open CriticalLinePhasor.SelfAdjointGenerator in
/-- The operative 1D evidence alone implies the critical-line conclusion: its kernel assertion
at the analytic zero is the substantive identification; the disjunctive routing proposition is
not used. -/
theorem grh_of_oneDCorrelationEvidence {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (h : CriticalLinePhasor.RiemannEvidence.OneDCorrelationEvidence χ) :
    GRHSpectral.GRH χ := by
  intro ρ hρ
  have hchart : CriticalLinePhasor.RiemannEvidence.OneDChartZero χ ρ :=
    ⟨hρ.2.2, ρ.im, rfl⟩
  obtain ⟨γ, ψ, hψ, hker, _hγ⟩ := h hchart
  exact spectral_cancellation_on_real_axis γ ⟨ψ, hψ, hker⟩

open CriticalLinePhasor.SelfAdjointGenerator CriticalLinePhasor.UnconditionalFrobenius
  CriticalLinePhasor.ThreeDFocal in
/-- Legacy 3D implication.  The evidence component is redundant here; the conclusion follows
directly from the carrier equality inside `ThreeD_crossings_are_real_zeros χ`. -/
theorem grh_of_resolvant_trace_3D_real {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : CriticalLinePhasor.RiemannEvidence.ThreeDRealEvidence
          ∧ ThreeD_crossings_are_real_zeros χ) : GRHSpectral.GRH χ :=
  grh_of_threeDCrossings χ h.2

open CriticalLinePhasor.SelfAdjointGenerator CriticalLinePhasor.UnconditionalFrobenius
  CriticalLinePhasor.ThreeDFocal in
/-- Legacy 1D implication.  The routing component is redundant; the conclusion follows from
`OneDCorrelationEvidence χ`, which asserts a fibre kernel at every analytic chart zero. -/
theorem grh_of_resolvant_trace_1D_correlation {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : CriticalLinePhasor.RiemannEvidence.OneDCorrelationEvidence χ
          ∧ OneD_zeta_zero_correlated χ) : GRHSpectral.GRH χ :=
  grh_of_oneDCorrelationEvidence χ h.1

/-- **RH — 3D-real reading** — `rh_from_grh ∘ grh_of_resolvant_trace_3D_real`; depends on the
conjunction `ThreeDRealEvidence ∧ ThreeD_crossings_are_real_zeros χ₁`. -/
theorem RH_of_resolvant_trace_3D_real (χ₁ : DirichletCharacter ℂ 1)
    (h : CriticalLinePhasor.RiemannEvidence.ThreeDRealEvidence
          ∧ ThreeD_crossings_are_real_zeros χ₁) : RiemannHypothesis :=
  RH_of_GRH_Trivial_Char χ₁ (grh_of_resolvant_trace_3D_real χ₁ h)

/-- **RH — 1D-correlation reading** — `rh_from_grh ∘ grh_of_resolvant_trace_1D_correlation`;
depends on the conjunction `OneDCorrelationEvidence χ₁ ∧ OneD_zeta_zero_correlated χ₁`. -/
theorem RH_of_resolvant_trace_1D_correlation (χ₁ : DirichletCharacter ℂ 1)
    (h : CriticalLinePhasor.RiemannEvidence.OneDCorrelationEvidence χ₁
          ∧ OneD_zeta_zero_correlated χ₁) : RiemannHypothesis :=
  RH_of_GRH_Trivial_Char χ₁ (grh_of_resolvant_trace_1D_correlation χ₁ h)

/-- **GRH — the conjecture itself, identity reading.**  Adopting the identity reading at every
modulus — every nontrivial zero of every Dirichlet `L(s,χ)` is a real-height crossing — yields,
with the unconditional 3D-real evidence, the full `GRHSpectral.GRHComplete`: every Dirichlet
L-function, every modulus, every character, principal included. -/
theorem grhComplete_of_resolvant_trace_3D_real
    (hev : CriticalLinePhasor.RiemannEvidence.ThreeDRealEvidence)
    (hall : ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M),
      ThreeD_crossings_are_real_zeros χ) :
    GRHSpectral.GRHComplete :=
  fun M _ χ => grh_of_resolvant_trace_3D_real χ ⟨hev, hall M χ⟩

/-- **GRH — the conjecture itself, correlation reading.**  Adopting the operative,
character-indexed correlation evidence and the correlation reading at every modulus yields the
full `GRHSpectral.GRHComplete`. -/
theorem grhComplete_of_resolvant_trace_1D_correlation
    (hall : ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M),
      CriticalLinePhasor.RiemannEvidence.OneDCorrelationEvidence χ
        ∧ OneD_zeta_zero_correlated χ) :
    GRHSpectral.GRHComplete :=
  fun M _ χ => grh_of_resolvant_trace_1D_correlation χ (hall M χ)

end HelixLimit

#print axioms HelixLimit.RH_of_GRH_Trivial_Char
#print axioms HelixLimit.threeDCrossings_iff_grh_and_nativeCarrierCoverage
#print axioms HelixLimit.grh_of_threeDCrossings
#print axioms HelixLimit.oneD_zeta_zero_correlated_proved
#print axioms HelixLimit.grh_of_oneDCorrelationEvidence
#print axioms HelixLimit.grh_of_resolvant_trace_3D_real
#print axioms HelixLimit.grh_of_resolvant_trace_1D_correlation
#print axioms HelixLimit.RH_of_resolvant_trace_3D_real
#print axioms HelixLimit.RH_of_resolvant_trace_1D_correlation
#print axioms HelixLimit.grhComplete_of_resolvant_trace_3D_real
#print axioms HelixLimit.grhComplete_of_resolvant_trace_1D_correlation
#print axioms HelixLimit.hcap_of_resolventTrace
#print axioms HelixLimit.grh_of_selfAdjoint_resolvent_capture
#print axioms HelixLimit.multiplicityCapture_of_resolventTrace
#print axioms HelixLimit.grh_of_resolventReceiver
#print axioms HelixLimit.ResolventReceiver.of_traceIdentity
#print axioms HelixLimit.differentiable_of_meromorphic_continuous
#print axioms HelixLimit.eq_zero_of_entire_tendsto_zero
#print axioms HelixLimit.global_traceIdentity_of_local
#print axioms HelixLimit.grh_of_realSingularSupport
#print axioms HelixLimit.real_absorption_of_selfAdjoint
#print axioms HelixLimit.isSelfAdjointReceiver_of_regular_off_spectrum
#print axioms HelixLimit.isUnitaryReceiver_of_regular_off_spectrum
#print axioms HelixLimit.regular_off_spectrum_of_resolvent
#print axioms HelixLimit.isSelfAdjointReceiver_resolventReadout
#print axioms HelixLimit.isUnitaryReceiver_resolventReadout
#print axioms HelixLimit.grh_of_harmonicTraceReceiver_traceIdentity
#print axioms HelixLimit.grh_of_selfAdjoint_resolventReadout

/-! # The Riemann evidence dossiers and the combined readings

Two bundles of unconditionally proven internal facts.  Each dossier is a single theorem whose
conjuncts are kernel-clean, but inhabiting a dossier does not compose those conjuncts into an
analytic-zero-to-native-event map.  The exact missing interfaces are exposed above:
`NativeCarrierCoverage` for midpoint-free 3D coverage, and `OneDCorrelationEvidence χ` for the
pointwise chart-to-kernel assertion.  The older 3D identity premise is decomposed by
`threeDCrossings_iff_grh_and_nativeCarrierCoverage`; the older 1D routing proposition is proved
unconditionally by `oneD_zeta_zero_correlated_proved`.

The author's assignment of evidence to readings, cast leads in **bold**:

* **`threeDRealEvidence`** — internal carrier and readout support.  **Feynman's Quiver** (the
  winding is prime-generated by FTA, the
  phasor bank is *summable*, the phasor-version-of-FTA uniqueness, no split focus), **Deligne's
  Pairs** (the det-1 self-reciprocal local factor, the Frobenius conjugate `det = 1`, the fiber
  weight product `= 1` — purity at the finite places), local scalar-fibre symmetry, real-height
  exhaustion, chart-indexed multiplicity, represented-point harmonic vanishing, the
  graded 3D-mode resolvent, and **Shannon Projection Dominance** (in projection geometry the
  highest level is the real one).

* **`oneDChartEvidence`** — the 1D chart dossier supporting the correlation reading.  **S(t)**
  (the global registration binding), the
  no-radial-drift fidelity, the on-circle placement and the lossless round-trip projection
  (**Shannon** — the collapse never counterfeits), **Riemann's Fold** (a real-axis projection
  crossing multiple dimensions lands at the real axis for all of them, and only the real axis
  does), the real-on-line faithful projection, the coincidence, residue = jump(S), the 1D
  infinite-continuation approximation, faithful transport, the **Shannon Cascade** convergence,
  S(t) detecting every crossing, the loss ledger, native identification, and the chart resolvent
  limit.

The operative `OneDCorrelationEvidence χ` is separate: it maps a reported 1D chart-zero event
for `χ` to a scalar-fibre kernel at that same complex point, and by itself supplies the
critical-line conclusion.  The dossiers are machine-checked at the standard axioms. -/

open Complex Filter Topology
open CriticalLinePhasor CriticalLinePhasor.SourceHolonomy CriticalLinePhasor.HilbertPolya
open CriticalLinePhasor.GradedModes CriticalLinePhasor.ResidueJump CriticalLinePhasor.CarrierScale
open Faithful

namespace CriticalLinePhasor.RiemannEvidence

/-- **The internal 3D support dossier holds unconditionally.**  It contains local scalar-fibre
symmetry, real-height exhaustion with no spurious state zeros,
**Feynman's Quiver** (FTA generation, phasor summability, phasor-FTA uniqueness, no split focus),
**Deligne's Pairs** (self-reciprocal, Frobenius conjugate `det = 1`, weight product `= 1`), the
chart-indexed multiplicity, represented-point harmonic vanishing, the graded mode resolvent, and
**Shannon Projection Dominance**.  Inhabiting `ThreeDRealEvidence` certifies every conjunct but
does not prove `NativeCarrierCoverage`. -/
theorem threeDRealEvidence : ThreeDRealEvidence := by
  refine ⟨UnconditionalFrobenius.vonNeumannOp_isSymmetric, threeD_exhaustive,
    threeD_metric_no_zeros, fun m n hm hn => Origination.windFromPrimes_mul hm hn,
    fun χ hχ _ hs => fiber_accumulates_to_L χ hχ hs,
    fun _ _ hmn => SelfAdjointGenerator.heights_distinct hmn,
    SelfAdjointGenerator.cancellation_modes_subsingleton,
    fun W X hX => W.localPoly_reciprocal hX,
    FrobeniusSimilitude.frobeniusBlock_det_one, fun W => W.fiber_det_one,
    hpOperator_isHermitian, finrank_modeSpace,
    fun χ Z => HarmonicCell.focal_residual_zero_iff_L_zero χ Z, ?_,
    fun w T hw r hr => gradedResolventTrace_eq_residue_sum w T hw r hr, ?_⟩
  · intro T p
    exact eigenheight_is_exact_vanishing p
  · exact fun _ _ _ hU hconv hdiff _ hz₀ hf0 hnz _ hε =>
      CriticalLinePhasor.LimitDominance.limit_dominance hU hconv hdiff hz₀ hf0 hnz hε

/-- **The 1D chart dossier holds unconditionally.**  It records chart-side infrastructure:
**S(t)** as the global coordinate/registration map, no radial
drift, on-circle placement, the lossless round-trip projection (**Shannon** — the collapse never
counterfeits), **Riemann's Fold** (the real axis is preserved across all crossed dimensions), the
real-on-line faithful projection, the coincidence, residue = jump(S), the 1D infinite-continuation
approximation, faithful transport, the **Shannon Cascade** convergence, S(t) detecting every
crossing, the loss ledger, native identification, and the chart resolvent limit.  Inhabiting
`OneDChartEvidence` certifies every conjunct; it does not prove the pointwise
`OneDCorrelationEvidence χ` premise. -/
theorem oneDChartEvidence : OneDChartEvidence := by
  refine ⟨carrier_scale_compensation_S, hpDimension_eq_registration,
    no_radial_drift_on_helix, midpoint_entry_on_circle,
    ConeProjection.record_bijective, ConeProjection.pipeline_midpoint_iff,
    Faithful.faithful_projection_zeta,
    fun T γ h0 hT => chartZero_iff_eigenheight h0 hT, residue_eq_Smult_jump,
    fun s hσ hσ1 hs1 => GRH.EulerMaclaurinDirichlet.euler_maclaurin_dirichlet s hσ hσ1 hs1,
    fun a Cc θ hθ hA s hs => TransferContinuation.transfer_tendsto a Cc θ hθ hA s hs,
    fun Cc z hacc => Cascade.limit_zero_of_stage_accumulation Cc hacc,
    fun γ hγ => S_jump_detects_event hγ,
    count_hasJump_iff_S_hasJump,
    ConeProjection.radial_lost,
    projection_bijective_loss_ledger,
    native_identification',
    ResolventLimit.windowedDiffResolvent_tendsto⟩

/-! ## Each reading, combined: its evidence with its conditional GRH proof

The conditionality lives entirely at the **GRH** level: each reading's GRH proof depends on its
listed inputs (self-adjointness discharged), and **RH follows from GRH
unconditionally** via `HelixLimit.RH_of_GRH_Trivial_Char` (`rh_from_grh`).  So each combined
theorem bundles the reading's **unconditional evidence** (left — proven, its presence certifies
every fact) with the reading's **conditional GRH proof** (right — `evidence ∧ conditional → GRH`,
the conjunction on which GRH depends; the conditional is the single first-of-kind hypothesis,
isolated and asserted by no one). -/

/-- **The 3D-real (identity) reading, combined.**  The unconditional evidence `threeDRealEvidence`,
together with the GRH proof — every modulus and character — depending on the **conjunction**
`ThreeDRealEvidence ∧ ThreeD_crossings_are_real_zeros χ` (`grh_of_resolvant_trace_3D_real`,
self-adjoint discharged).  RH then follows from GRH unconditionally (`RH_of_GRH_Trivial_Char`). -/
theorem threeD_real_case :
    ThreeDRealEvidence
      ∧ (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
          ThreeDRealEvidence ∧ HelixLimit.ThreeD_crossings_are_real_zeros χ
            → GRHSpectral.GRH χ) :=
  ⟨threeDRealEvidence, fun _ _ χ h => HelixLimit.grh_of_resolvant_trace_3D_real χ h⟩

/-- **The 1D-correlation (coincidence) reading, combined.**  The unconditional chart dossier
`oneDChartEvidence`, together with the GRH proof — every modulus and character — depending on
the **conjunction** `OneDCorrelationEvidence χ ∧ OneD_zeta_zero_correlated χ`
(`grh_of_resolvant_trace_1D_correlation`, whose 1D branch consumes the correlation bridge).
RH then follows from GRH
unconditionally (`RH_of_GRH_Trivial_Char`). -/
theorem oneD_correlation_case :
    OneDChartEvidence
      ∧ (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
          OneDCorrelationEvidence χ ∧ HelixLimit.OneD_zeta_zero_correlated χ
            → GRHSpectral.GRH χ) :=
  ⟨oneDChartEvidence, fun _ _ χ h => HelixLimit.grh_of_resolvant_trace_1D_correlation χ h⟩

end CriticalLinePhasor.RiemannEvidence

#print axioms CriticalLinePhasor.RiemannEvidence.threeDRealEvidence
#print axioms CriticalLinePhasor.RiemannEvidence.oneDChartEvidence
#print axioms CriticalLinePhasor.RiemannEvidence.threeD_real_case
#print axioms CriticalLinePhasor.RiemannEvidence.oneD_correlation_case
