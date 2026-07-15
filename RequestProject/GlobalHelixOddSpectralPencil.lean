import RequestProject.GlobalHelixFixedBankReflection
import RequestProject.ThreeDFocalEvent

/-!
# Spectral pencil of the global-helix odd channel

Every complex signed channel has a canonical spectral coordinate.  Applied to the global 3D odd
bank, this identifies its harmonic Gram pencil literally with the self-adjoint-generator spectral
Gram pencil.  Thus the remaining extinction step is an exact registration of that coordinate with
the carrier's marked real spectral point.
-/

open Complex Matrix

namespace CriticalLinePhasor.GlobalHelix

open CriticalLinePhasor.HarmonicCell CriticalLinePhasor.SelfAdjointGenerator

/-- The unique affine spectral coordinate whose signed mode at eigenheight zero is `B`. -/
noncomputable def oddSpectralCoordinate (B : ℂ) : ℂ :=
  ((1 / 2 + B.im : ℝ) : ℂ) - Complex.I * (B.re : ℂ)

theorem oddSpectralCoordinate_re (B : ℂ) :
    (oddSpectralCoordinate B).re = 1 / 2 + B.im := by
  simp [oddSpectralCoordinate]

theorem oddSpectralCoordinate_im (B : ℂ) :
    (oddSpectralCoordinate B).im = -B.re := by
  simp [oddSpectralCoordinate]

/-- The spectral signed mode reconstructs the supplied complex channel exactly. -/
theorem specBchan_oddSpectralCoordinate (B : ℂ) :
    specBchan 0 (oddSpectralCoordinate B) = B := by
  apply Complex.ext
  · rw [CriticalLinePhasor.SelfAdjointGenerator.specBchan_re,
      oddSpectralCoordinate_im]
    simp
  · rw [CriticalLinePhasor.SelfAdjointGenerator.specBchan_im,
      oddSpectralCoordinate_re]
    simp

/-- The spectral pencil at the canonical odd coordinate is literally the channel-agnostic harmonic
pencil with signed channel `B`. -/
theorem specHarmonicPencil_oddSpectralCoordinate (B μ lam : ℂ) :
    specHarmonicPencil 0 (oddSpectralCoordinate B) μ lam =
      harmonicPencil 1 B μ lam := by
  rw [specHarmonicPencil, specBchan_oddSpectralCoordinate]

/-- The corresponding Gram matrices agree exactly. -/
theorem specGram_oddSpectralCoordinate (B μ lam : ℂ) :
    specGram 0 (oddSpectralCoordinate B) μ lam =
      (harmonicPencil 1 B μ lam)ᴴ * harmonicPencil 1 B μ lam := by
  rw [specGram, specHarmonicPencil_oddSpectralCoordinate]

/-- Rank drop of the self-adjoint spectral Gram at the global odd coordinate is exactly extinction
of that odd channel. -/
theorem specGram_oddSpectralCoordinate_rankDrop_iff
    (B μ lam : ℂ) (hlam : lam ≠ μ) :
    (specGram 0 (oddSpectralCoordinate B) μ lam).det = 0 ↔ B = 0 := by
  rw [specGram_det_zero_iff 0 _ hlam, specBchan_oddSpectralCoordinate]

/-- The odd coordinate registers at the marked zero-height carrier point exactly when the signed
channel vanishes. -/
theorem oddSpectralCoordinate_eq_carrierPoint_zero_iff (B : ℂ) :
    oddSpectralCoordinate B = CriticalLinePhasor.ThreeDFocal.carrierPoint 0 ↔ B = 0 := by
  constructor
  · intro h
    have hs : specBchan 0 (oddSpectralCoordinate B) = 0 := by
      rw [h]
      simp [CriticalLinePhasor.ThreeDFocal.carrierPoint, specBchan, specHeight]
    simpa [specBchan_oddSpectralCoordinate] using hs
  · intro h
    subst B
    simp [oddSpectralCoordinate, CriticalLinePhasor.ThreeDFocal.carrierPoint]

/-- Pointwise specialization to the fixed-kernel global 3D bank. -/
theorem fixedBankOddChannel_rankDrop_iff
    (μs : List ℂ) (a : ℕ → ℂ) (η : ℂ) (κ x : ℝ)
    (μ lam : ℂ) (hlam : lam ≠ μ) :
    (specGram 0 (oddSpectralCoordinate (fixedBankOddChannel μs a η κ x)) μ lam).det = 0 ↔
      fixedBankOddChannel μs a η κ x = 0 :=
  specGram_oddSpectralCoordinate_rankDrop_iff _ μ lam hlam

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.specBchan_oddSpectralCoordinate
#print axioms CriticalLinePhasor.GlobalHelix.specHarmonicPencil_oddSpectralCoordinate
#print axioms CriticalLinePhasor.GlobalHelix.specGram_oddSpectralCoordinate
#print axioms CriticalLinePhasor.GlobalHelix.specGram_oddSpectralCoordinate_rankDrop_iff
#print axioms CriticalLinePhasor.GlobalHelix.oddSpectralCoordinate_eq_carrierPoint_zero_iff
#print axioms CriticalLinePhasor.GlobalHelix.fixedBankOddChannel_rankDrop_iff
