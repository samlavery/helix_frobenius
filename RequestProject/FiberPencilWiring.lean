import RequestProject.CancellationEquivalence
import RequestProject.GlobalHelixOddSpectralPencil

/-!
# Wiring the spectral-fiber cancellation into the generic harmonic pencil (ledger 909)

The concrete `HarmonicCell.Bchan` is `Ucell · Φ`, with `Φ χ Z = L(½ + i log Z)`: it is already read
at the critical readout.  The generic pencil `HarmonicCell.harmonicPencil A B μ λ` and the odd
spectral coordinate `GlobalHelix.oddSpectralCoordinate B` accept an arbitrary signed channel `B`.
This file feeds them the spectral fiber's own resultant at an arbitrary chart point `s`, with no
`reprPoint`, no `criticalReadout`, and no hypothesis on `Re s`.

* `fiberResultant w s` — the limit of the readout partial sums of `spectralFiber w s`;
  `fiberResultant_eq_LFunction` (`χ ≠ 1`, `Re s > 0`) and `fiberResultant_eta_eq` (the η-configured
  fiber, `(1 − 2^{1−s}) ζ(s)`).
* Wiring: `spectralCancellation_iff_resultant_zero`, `spectralCancellation_iff_harmonicGram_rankDrop`,
  `spectralCancellation_iff_specGram_rankDrop`, `spectralCancellation_iff_oddCoordinate`,
  `zeta_zero_etaResultant_harmonicGram_rankDrop`.
* What the pencil coordinate carries: `oddSpectralCoordinate_eq` (`= ½ − i·B`, a function of the
  value alone); `oddCoordinate_constant_on_cancellations` (the same point at every cancellation);
  `oddCoordinate_eq_carrierPoint_height_iff` (it registers a cancellation at the carrier point of the
  cancellation's own height only when that height is `0`).
* The naive carrying equality `s = oddSpectralCoordinate (fiberResultant _ s)` is named
  (`NaiveOddCoordinateCarried`), never assumed, and shown to collapse every cancellation to the
  single point `carrierPoint 0` (`naiveOddCoordinateCarried_collapses`).
* The obligation that does carry `s`: `CancellationOnCarrier` — every strip cancellation sits at the
  carrier point of its own height.  Named, never assumed.  Per point it is `Re s = carrierAbscissa`
  (`eq_carrierPoint_im_iff`); `cancellationOnCarrier_re` records what it would deliver.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology
open scoped Matrix

namespace CriticalLinePhasor.FiberPencilWiring

open CriticalLinePhasor.HarmonicCell CriticalLinePhasor.GlobalHelix

variable {q : ℕ} [NeZero q]

/-! ## 1. The fiber's own resultant -/

/-- The resultant of the spectral fiber at `s`: the limit of its readout partial sums. -/
noncomputable def fiberResultant (w : ℕ → ℂ) (s : ℂ) : ℂ :=
  limUnder atTop (fun N : ℕ => ∑ n ∈ Finset.range N, SpectralFiber.readout w s n)

/-- For a non-principal character on `Re s > 0`, the resultant is the L-value. -/
theorem fiberResultant_eq_LFunction (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) :
    fiberResultant (fun n => χ (n : ZMod q)) s = DirichletCharacter.LFunction χ s :=
  (SpectralFiber.spectralFiber_readout_tendsto_LFunction χ hχ hs).limUnder_eq

/-- For the η-configured fiber on `Re s > 0`, `s ≠ 1`, the resultant is `(1 − 2^{1−s}) ζ(s)`. -/
theorem fiberResultant_eta_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    fiberResultant SpectralFiber.etaW s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s :=
  (SpectralFiber.etaSpectralFiber_readout_tendsto_zeta hs hs1).limUnder_eq

/-! ## 2. The wiring -/

/-- A spectral cancellation at `s` is exactly the vanishing of the fiber's own resultant. -/
theorem spectralCancellation_iff_resultant_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    SpectralFiber.SpectralCancellation χ s ↔ fiberResultant (fun n => χ (n : ZMod q)) s = 0 := by
  rw [SpectralFiber.cancellation_sets_coincide, fiberResultant_eq_LFunction χ hχ hs]
  exact Iff.rfl

/-- The generic harmonic Gram with signed channel `B` rank-drops exactly when `B = 0`. -/
theorem harmonicGram_rankDrop_iff (A B μ lam : ℂ) (hA : A ≠ 0) (hlam : lam ≠ μ) :
    ((harmonicPencil A B μ lam)ᴴ * harmonicPencil A B μ lam).det = 0 ↔ B = 0 := by
  rw [gram_rank_drop_iff_det_cell_zero, harmonicPencil_det]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd (sub_eq_zero.mp h2) hlam
      · exact absurd h2 hA
    · exact h1
  · intro h
    rw [h, mul_zero]

/-- **Wiring 1.**  The fiber cancellation drives the generic harmonic Gram pencil at every `s`
with `Re s > 0`. -/
theorem spectralCancellation_iff_harmonicGram_rankDrop (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) (A μ lam : ℂ) (hA : A ≠ 0) (hlam : lam ≠ μ) :
    SpectralFiber.SpectralCancellation χ s ↔
      ((harmonicPencil A (fiberResultant (fun n => χ (n : ZMod q)) s) μ lam)ᴴ *
        harmonicPencil A (fiberResultant (fun n => χ (n : ZMod q)) s) μ lam).det = 0 := by
  rw [harmonicGram_rankDrop_iff _ _ _ _ hA hlam]
  exact spectralCancellation_iff_resultant_zero χ hχ hs

/-- **Wiring 2.**  The same event is the rank drop of the self-adjoint spectral Gram at the odd
coordinate of the fiber's resultant. -/
theorem spectralCancellation_iff_specGram_rankDrop (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) (μ lam : ℂ) (hlam : lam ≠ μ) :
    SpectralFiber.SpectralCancellation χ s ↔
      (SelfAdjointGenerator.specGram 0
        (oddSpectralCoordinate (fiberResultant (fun n => χ (n : ZMod q)) s)) μ lam).det = 0 := by
  rw [specGram_oddSpectralCoordinate_rankDrop_iff _ μ lam hlam]
  exact spectralCancellation_iff_resultant_zero χ hχ hs

/-- **Wiring 3.**  The same event is the odd coordinate registering at `carrierPoint 0`. -/
theorem spectralCancellation_iff_oddCoordinate (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    SpectralFiber.SpectralCancellation χ s ↔
      oddSpectralCoordinate (fiberResultant (fun n => χ (n : ZMod q)) s) =
        ThreeDFocal.carrierPoint 0 := by
  rw [oddSpectralCoordinate_eq_carrierPoint_zero_iff]
  exact spectralCancellation_iff_resultant_zero χ hχ hs

/-- The ζ instance through the η-configured fiber: a zeta zero in the half-plane `Re s > 0`
(`s ≠ 1`) makes the fiber's resultant vanish, hence the generic harmonic Gram rank-drop. -/
theorem zeta_zero_etaResultant_harmonicGram_rankDrop {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (A μ lam : ℂ) (hA : A ≠ 0) (hlam : lam ≠ μ) :
    fiberResultant SpectralFiber.etaW s = 0 ∧
      ((harmonicPencil A (fiberResultant SpectralFiber.etaW s) μ lam)ᴴ *
        harmonicPencil A (fiberResultant SpectralFiber.etaW s) μ lam).det = 0 := by
  have h0 : fiberResultant SpectralFiber.etaW s = 0 := by
    rw [fiberResultant_eta_eq hs hs1, hz, mul_zero]
  exact ⟨h0, (harmonicGram_rankDrop_iff _ _ _ _ hA hlam).mpr h0⟩

/-! ## 3. What the pencil coordinate carries -/

/-- The odd coordinate is `½ − i·B`: an affine function of the signed value alone. -/
theorem oddSpectralCoordinate_eq (B : ℂ) : oddSpectralCoordinate B = 1 / 2 - I * B := by
  apply Complex.ext
  · rw [oddSpectralCoordinate_re]
    simp [Complex.sub_re, Complex.mul_re]
  · rw [oddSpectralCoordinate_im]
    simp [Complex.sub_im, Complex.mul_im]

/-- **The odd coordinate forgets the zero**: every cancellation registers at the same point. -/
theorem oddCoordinate_constant_on_cancellations (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s₁ s₂ : ℂ} (h₁ : 0 < s₁.re) (h₂ : 0 < s₂.re)
    (c₁ : SpectralFiber.SpectralCancellation χ s₁) (c₂ : SpectralFiber.SpectralCancellation χ s₂) :
    oddSpectralCoordinate (fiberResultant (fun n => χ (n : ZMod q)) s₁) =
      oddSpectralCoordinate (fiberResultant (fun n => χ (n : ZMod q)) s₂) := by
  rw [(spectralCancellation_iff_oddCoordinate χ hχ h₁).mp c₁,
    (spectralCancellation_iff_oddCoordinate χ hχ h₂).mp c₂]

/-- At a cancellation, the odd coordinate is the carrier point of the cancellation's own height
only when that height is `0`: the pencil registers every cancellation at height zero. -/
theorem oddCoordinate_eq_carrierPoint_height_iff (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) (c : SpectralFiber.SpectralCancellation χ s) :
    oddSpectralCoordinate (fiberResultant (fun n => χ (n : ZMod q)) s) =
        ThreeDFocal.carrierPoint s.im ↔ s.im = 0 := by
  rw [(spectralCancellation_iff_oddCoordinate χ hχ hs).mp c]
  constructor
  · intro h
    have him := congrArg Complex.im h
    rw [ThreeDFocal.carrierPoint_im, ThreeDFocal.carrierPoint_im] at him
    exact him.symm
  · intro h
    rw [h]

/-! ## 4. The obligations, named and never assumed -/

/-- The naive carrying equality: each cancellation is its own odd coordinate. -/
def NaiveOddCoordinateCarried (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ s : ℂ, 0 < s.re → SpectralFiber.SpectralCancellation χ s →
    s = oddSpectralCoordinate (fiberResultant (fun n => χ (n : ZMod q)) s)

/-- The naive equality would collapse every cancellation to the single point `carrierPoint 0`. -/
theorem naiveOddCoordinateCarried_collapses (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (h : NaiveOddCoordinateCarried χ) {s : ℂ} (hs : 0 < s.re)
    (c : SpectralFiber.SpectralCancellation χ s) :
    s = ThreeDFocal.carrierPoint 0 := by
  rw [h s hs c]
  exact (spectralCancellation_iff_oddCoordinate χ hχ hs).mp c

/-- **The remaining obligation, correctly typed**: every cancellation in the strip sits at the
carrier point of its own height. -/
def CancellationOnCarrier (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → SpectralFiber.SpectralCancellation χ s →
    s = ThreeDFocal.carrierPoint s.im

/-- Per point, sitting at the carrier point of one's own height is having the carrier abscissa. -/
theorem eq_carrierPoint_im_iff (s : ℂ) :
    s = ThreeDFocal.carrierPoint s.im ↔ s.re = ThreeDFocal.carrierAbscissa := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    rwa [ThreeDFocal.carrierPoint_re] at hre
  · intro h
    apply Complex.ext
    · rw [ThreeDFocal.carrierPoint_re, h]
    · rw [ThreeDFocal.carrierPoint_im]

/-- What the obligation would deliver: every zero of `L(·, χ)` in the strip on the carrier abscissa. -/
theorem cancellationOnCarrier_re (χ : DirichletCharacter ℂ q) (h : CancellationOnCarrier χ)
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hL : DirichletCharacter.LFunction χ s = 0) :
    s.re = 1 / 2 := by
  have c : SpectralFiber.SpectralCancellation χ s :=
    (SpectralFiber.cancellation_sets_coincide χ s).mpr hL
  rw [← ThreeDFocal.carrierAbscissa_eq_half]
  exact (eq_carrierPoint_im_iff s).mp (h s h0 h1 c)

end CriticalLinePhasor.FiberPencilWiring

#print axioms CriticalLinePhasor.FiberPencilWiring.fiberResultant_eq_LFunction
#print axioms CriticalLinePhasor.FiberPencilWiring.fiberResultant_eta_eq
#print axioms CriticalLinePhasor.FiberPencilWiring.spectralCancellation_iff_harmonicGram_rankDrop
#print axioms CriticalLinePhasor.FiberPencilWiring.spectralCancellation_iff_specGram_rankDrop
#print axioms CriticalLinePhasor.FiberPencilWiring.spectralCancellation_iff_oddCoordinate
#print axioms CriticalLinePhasor.FiberPencilWiring.zeta_zero_etaResultant_harmonicGram_rankDrop
#print axioms CriticalLinePhasor.FiberPencilWiring.oddSpectralCoordinate_eq
#print axioms CriticalLinePhasor.FiberPencilWiring.oddCoordinate_constant_on_cancellations
#print axioms CriticalLinePhasor.FiberPencilWiring.oddCoordinate_eq_carrierPoint_height_iff
#print axioms CriticalLinePhasor.FiberPencilWiring.naiveOddCoordinateCarried_collapses
#print axioms CriticalLinePhasor.FiberPencilWiring.eq_carrierPoint_im_iff
#print axioms CriticalLinePhasor.FiberPencilWiring.cancellationOnCarrier_re
