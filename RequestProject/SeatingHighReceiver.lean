import RequestProject.SeatingLadderFold
import RequestProject.HilbertPolyaCapstone

/-!
# The localized Hilbert–Pólya receiver: regularity above the ladder suffices

The absorption argument of the compiled HP capstone is pointwise, and the DVP
ladder settles all ordinates `|γ| ≤ 1269/2`.  So the self-adjoint-receiver
regularity of the ξ spectral trace is needed only on the HIGH spectral band:

  `rh_of_high_receiver` — **RH ⟸ the ξ spectral trace has boundary limits at
  the off-real points with `|Re z| > 634.5` alone.**

The HP target and the seating target are now localized identically — the two
registers' residuals coincide above the same compiled ladder height.

No `sorry`, no `axiom`.
-/

open Complex Filter

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

open CriticalLinePhasor CriticalLinePhasor.HilbertPolya

/-- **RH from the high receiver**: boundary regularity of the ξ spectral trace
only at off-real points of the high band `|Re z| > 1269/2`. -/
theorem rh_of_high_receiver
    (hsa : ∀ z : ℂ, z.im ≠ 0 → 1269/2 < |z.re| →
      ∃ L, Tendsto xiSpectralTrace (nhdsWithin z {z}ᶜ) (nhds L)) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2 := by
  intro ρ hρ
  by_cases hlow : |ρ.im| ≤ 1269/2
  · exact CriticalLinePhasor.DVP.online_below_1269o2 ρ hρ hlow
  · push_neg at hlow
    by_contra hre
    have hmem := xi_spectralCoord_mem_singularSupport hρ
    have him : (spectralCoord ρ).im ≠ 0 := by
      have hcalc : (spectralCoord ρ).im = -(ρ.re - 1/2) := by
        simp [spectralCoord, Complex.mul_im, Complex.sub_re, Complex.sub_im]
      rw [hcalc]
      intro h
      exact hre (by linarith)
    have hhigh : 1269/2 < |(spectralCoord ρ).re| := by
      have hcalc : (spectralCoord ρ).re = ρ.im := by
        simp [spectralCoord, Complex.mul_re, Complex.sub_re, Complex.sub_im]
      rw [hcalc]
      exact hlow
    exact hmem (hsa _ him hhigh)

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.rh_of_high_receiver
