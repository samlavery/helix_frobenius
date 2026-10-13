import RequestProject.WarpFactorFocalLocus

/-!
# Transverse rigidity of the harmonic pencil under `D_δ` (ledger 1199)

The proposed theorem: the native harmonic pencil, deformed transversally by `D_δ`, drops rank only
at `δ = 0`. This file compiles what the house pencil gives for it.

* `pencil_rigidity_iff_channel`: for every calibration family `(A, μ, λ)` with `A ≠ 0`, `λ ≠ μ`,
  allowed to depend on `δ` and `y`, transverse rigidity of the finite `D`-image pencil is transverse
  rigidity of its signed channel. The calibration is where area-law data could be placed, and it
  drops out (`harmonicGram_rank_drop_iff_channel_zero`).
* `eta_dilate_offNative_rankDrop`: for every reference exponent `σ₀`, the normalized limit pencil of
  the `D_{1−σ₀}`-image of the η fiber at height `2π/log 2` converges to a singular pencil, and
  `ζ ≠ 0` there. For `σ₀ ≠ 1` this is a limit rank drop at `δ = 1 − σ₀ ≠ 0`, through the dyadic
  factor `1 − 2^{1−s}` of the η routing (`etaFactorEvent`, ledger 1156). The statement
  "rank drop ⇒ `δ = 0`" is false for the η-routed pencil without a strip restriction.
  Scope (cleanup, ledger 1237): this rank drop is FACTOR-INDUCED (the conductor's dyadic multiplier, with
  `ζ ≠ 0`; `EtaFactorAudit.eta_event_dichotomy`). It lives in the weak asymptotic type and is not a physical
  focal event, so it is no counterexample to rigidity claims about physical focal events or the ζ subclass.
* `strip_rigidity_iff`: in the open strip `0 < σ₀ + δ < 1`, transverse rigidity of the η-routed
  limit pencil at reference exponent `σ₀` holds iff every nontrivial ζ zero has real part `σ₀`.
-/

open Complex Filter Topology
open scoped Matrix

noncomputable section

namespace CriticalLinePhasor.PencilRigidity

open CriticalLinePhasor CriticalLinePhasor.FiberDetectorChain CriticalLinePhasor.HarmonicCell
open CriticalLinePhasor.LimitFocalEventNS CriticalLinePhasor.EisensteinWheelBank
open CriticalLinePhasor.WarpFactorLocus

/-- **The calibration drops out.** Transverse rigidity of the `D`-image pencil, for any calibration
family with `A ≠ 0` and `λ ≠ μ`, is transverse rigidity of the signed channel. -/
theorem pencil_rigidity_iff_channel (w : ℕ → ℂ) (Z σ₀ : ℝ) (A μ lam : ℝ → ℝ → ℂ)
    (hA : ∀ δ y, A δ y ≠ 0) (hlam : ∀ δ y, lam δ y ≠ μ δ y) :
    (∀ δ y : ℝ, ((harmonicPencil (A δ y) (dilateFiber w Z ((σ₀ : ℂ) + (y : ℂ) * I) δ) (μ δ y)
        (lam δ y))ᴴ * harmonicPencil (A δ y) (dilateFiber w Z ((σ₀ : ℂ) + (y : ℂ) * I) δ)
        (μ δ y) (lam δ y)).det = 0 → δ = 0) ↔
      (∀ δ y : ℝ, dilateFiber w Z ((σ₀ : ℂ) + (y : ℂ) * I) δ = 0 → δ = 0) := by
  refine forall_congr' fun δ => forall_congr' fun y => ?_
  rw [harmonicGram_rank_drop_iff_channel_zero _ _ _ _ (hA δ y) (hlam δ y)]

/-- **An off-native limit rank drop of the η-routed pencil.** For every reference exponent `σ₀`, the
normalized pencil of the `D_{1−σ₀}`-image of the η fiber at height `2π/log 2` converges to a singular
pencil, at a point where `ζ ≠ 0`. Factor-induced (dyadic multiplier); not a physical focal event. -/
theorem eta_dilate_offNative_rankDrop (σ₀ : ℝ) (μ lam : ℂ) :
    Tendsto (fun Z => harmonicPencil 1
        (dilateFiber Routing.eta.coeff Z ((σ₀ : ℂ) + (dyadicOrdinate : ℂ) * I) (1 - σ₀)) μ lam)
        atTop (𝓝 (harmonicPencil 1 0 μ lam)) ∧
      ((harmonicPencil 1 0 μ lam)ᴴ * harmonicPencil 1 0 μ lam).det = 0 ∧
      riemannZeta ((σ₀ : ℂ) + (dyadicOrdinate : ℂ) * I + ((1 - σ₀ : ℝ) : ℂ)) ≠ 0 := by
  refine ⟨normalizedDetector_tendsto
    (WarpFactorLocus.LimitFocalEvent.dilate_image etaFactorEvent σ₀) μ lam,
    limit_pencil_singular μ lam, ?_⟩
  have h : (σ₀ : ℂ) + (dyadicOrdinate : ℂ) * I + ((1 - σ₀ : ℝ) : ℂ) =
      (etaFactorEvent.σ : ℂ) + (etaFactorEvent.y : ℂ) * I := by
    show _ = ((1 : ℝ) : ℂ) + (dyadicOrdinate : ℂ) * I
    push_cast
    ring
  rw [h]
  exact etaFactorEvent_not_zeta_zero

/-- **In the open strip, transverse rigidity of the η-routed limit pencil at `σ₀` is the statement
that every nontrivial ζ zero has real part `σ₀`.** -/
theorem strip_rigidity_iff (σ₀ : ℝ) :
    (∀ δ y : ℝ, 0 < σ₀ + δ → σ₀ + δ < 1 →
        Tendsto (fun Z => dilateFiber Routing.eta.coeff Z ((σ₀ : ℂ) + (y : ℂ) * I) δ) atTop (𝓝 0) →
          δ = 0) ↔
      ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = σ₀ := by
  have hpt : ∀ δ y : ℝ, (σ₀ : ℂ) + (y : ℂ) * I + (δ : ℂ) = ((σ₀ + δ : ℝ) : ℂ) + (y : ℂ) * I := by
    intro δ y
    push_cast
    ring
  constructor
  · intro h ρ hρ
    obtain ⟨h0, h1, hz⟩ := hρ
    have hre : (((σ₀ + (ρ.re - σ₀) : ℝ) : ℂ) + (ρ.im : ℂ) * I) = ρ := by
      rw [show σ₀ + (ρ.re - σ₀) = ρ.re by ring]
      exact Complex.re_add_im ρ
    have hδ := h (ρ.re - σ₀) ρ.im (by linarith) (by linarith) (by
      simp_rw [dilateFiber_eq, hpt, hre]
      exact (limit_chain_eta h0 h1 0 1 one_ne_zero).1.mpr hz)
    linarith
  · intro h δ y h0 h1 hT
    simp_rw [dilateFiber_eq, hpt] at hT
    have hs0 : 0 < (((σ₀ + δ : ℝ) : ℂ) + (y : ℂ) * I).re := by simpa using h0
    have hs1 : (((σ₀ + δ : ℝ) : ℂ) + (y : ℂ) * I).re < 1 := by simpa using h1
    have hz := (limit_chain_eta hs0 hs1 0 1 one_ne_zero).1.mp hT
    have hre := h _ ⟨hs0, hs1, hz⟩
    simp at hre
    linarith

end CriticalLinePhasor.PencilRigidity

end

#print axioms CriticalLinePhasor.PencilRigidity.pencil_rigidity_iff_channel
#print axioms CriticalLinePhasor.PencilRigidity.eta_dilate_offNative_rankDrop
#print axioms CriticalLinePhasor.PencilRigidity.strip_rigidity_iff
