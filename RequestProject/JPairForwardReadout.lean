import RequestProject.JPairIdentificationStatus

/-!
# The forward readout of a physical J-pair: the pre-registered binary test (ledger 911)

The test, as specified: take a physical fiber state `f` and its J-image `J f`, push each member
forward through the readout without introducing an analytic parameter first, and read off the two
Mellin abscissae.  Decision rule, fixed before the run: amplitudes `n^{-σ}` and `n^{-(1-σ)}` on the two
ends → the radial argument goes through; two equal amplitudes with phase conjugation → it does not.

* The existing chart readout does not read the radial channel. `stripReadout_eq_of_height_eq`: two
  states of equal height have equal readout, whatever their radii. `stripReadout_re`: the real part is
  the constant `½`.  On this image J acts both as conjugation and as `s ↦ 1 − s`, because the image has
  real part `½` by definition, not because any radius was compared.
* Any readout that does see the radial channel, i.e. any function of the phasor's length, takes the same
  value on both ends of a physical J-pair (`jPair_magnitude_readout`).  In particular the Mellin
  abscissa of the amplitude, `amplitudeAbscissa v n = −log‖v‖ / log n`, is equal on the two ends
  (`amplitudeAbscissa_jPair`), and their plane components are conjugate (`jPair_plane_conj`).
* On the actual spectral fiber this abscissa is `Re s` (`amplitudeAbscissa_spectralFiber`).  The J-end of
  the phasor at `(s, n)` reads at `Re s` with the conjugate plane component (`jPair_forward_abscissae`);
  the reflected end at `(1 − s, n)` reads at `1 − Re s`; the two agree exactly when `Re s = ½`
  (`jEnd_eq_reflected_abscissa_iff`).

Outcome: equal amplitudes with phase conjugation.  No zero premise and no analytic parameter enter the
statements about physical pairs.  No `sorry`, no `axiom`.
-/

noncomputable section
open Complex ConeProjection

namespace CriticalLinePhasor.GlobalHelix

open Phasor3D SpectralFiber

/-! ## 1. The existing chart readout of a physical state -/

/-- The strip readout does not read the radial channel: equal heights give equal readouts. -/
theorem stripReadout_eq_of_height_eq (f g : Fiber) (h : height f = height g) :
    stripReadout f = stripReadout g := by
  unfold stripReadout
  rw [analyticOrdinate_eq_height, analyticOrdinate_eq_height, h]

/-- The real part of the strip readout is the constant `½`, for every physical state. -/
theorem stripReadout_re (f : Fiber) : (stripReadout f).re = 1 / 2 := by
  simp [stripReadout]

/-! ## 2. Readouts that see the radial channel, on a physical J-pair -/

/-- Any readout of the phasor's length takes the same value on both ends of a physical J-pair. -/
theorem jPair_magnitude_readout {v w : Vec3} {f : Fiber} (Φ : ℝ → ℝ)
    (hH : realize f = (v.1.re, v.1.im, v.2))
    (hJ : realize (globalHelixInvolution f) = (w.1.re, w.1.im, w.2)) :
    Φ (mag3 w) = Φ (mag3 v) := by
  rw [mag3_eq_of_realize_j_pair hH hJ]

/-- The Mellin abscissa read from the amplitude of a 3D phasor at site `n`. -/
noncomputable def amplitudeAbscissa (v : Vec3) (n : ℕ) : ℝ := -Real.log (mag3 v) / Real.log n

/-- The two ends of any physical J-pair read at the same amplitude abscissa. -/
theorem amplitudeAbscissa_jPair {v w : Vec3} {f : Fiber} (n : ℕ)
    (hH : realize f = (v.1.re, v.1.im, v.2))
    (hJ : realize (globalHelixInvolution f) = (w.1.re, w.1.im, w.2)) :
    amplitudeAbscissa w n = amplitudeAbscissa v n :=
  jPair_magnitude_readout (fun m => -Real.log m / Real.log n) hH hJ

/-- The plane components of the two ends of a physical J-pair are conjugate. -/
theorem jPair_plane_conj {v w : Vec3} {f : Fiber}
    (hH : realize f = (v.1.re, v.1.im, v.2))
    (hJ : realize (globalHelixInvolution f) = (w.1.re, w.1.im, w.2)) :
    w.1 = (starRingEnd ℂ) v.1 := by
  have h := hJ.symm.trans (realize_globalHelixInvolution f)
  rw [hH] at h
  have hx := congrArg (fun t : ℝ × ℝ × ℝ => t.1) h
  have hy := congrArg (fun t : ℝ × ℝ × ℝ => t.2.1) h
  apply Complex.ext
  · simpa using hx
  · simpa using hy

/-! ## 3. On the actual spectral fiber -/

variable {q : ℕ} [NeZero q]

/-- On the actual spectral fiber the amplitude abscissa is `Re s`. -/
theorem amplitudeAbscissa_spectralFiber (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic)
    (s : ℂ) (n : ℕ) (hn : 1 < n) :
    amplitudeAbscissa (spectralFiber (fun k => χ k) s n) n = s.re := by
  unfold amplitudeAbscissa spectralFiber
  rw [phasor3D_mag3 χ hq _ _ n (by omega)]
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log n ≠ 0 := (Real.log_pos hn').ne'
  rw [Real.log_rpow (by linarith), neg_mul, neg_neg, mul_div_assoc, div_self hlog, mul_one]

/-- **The binary test on the actual fiber.**  The physical J-image of the fiber phasor at `(s, n)`
reads at amplitude abscissa `Re s`, with plane component the conjugate. -/
theorem jPair_forward_abscissae (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) (s : ℂ) (n : ℕ)
    (hn : 1 < n) (hcharged : χ n = 1 ∨ χ n = -1) :
    ∃ w : Vec3,
      (∃ f : Fiber,
        realize f = ((spectralFiber (fun k => χ k) s n).1.re,
          (spectralFiber (fun k => χ k) s n).1.im, (spectralFiber (fun k => χ k) s n).2) ∧
        realize (globalHelixInvolution f) = (w.1.re, w.1.im, w.2)) ∧
      amplitudeAbscissa w n = s.re ∧
      w.1 = (starRingEnd ℂ) (spectralFiber (fun k => χ k) s n).1 := by
  obtain ⟨f, hH, hJ⟩ := actual_jPair χ s n hcharged
  refine ⟨spectralFiber (fun k => χ k) ((starRingEnd ℂ) s) n, ⟨f, hH, hJ⟩, ?_, ?_⟩
  · rw [amplitudeAbscissa_jPair n hH hJ, amplitudeAbscissa_spectralFiber χ hq s n hn]
  · exact jPair_plane_conj hH hJ

/-- The J-end and the reflected end read at the same amplitude abscissa exactly when `Re s = ½`. -/
theorem jEnd_eq_reflected_abscissa_iff (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) (s : ℂ)
    (n : ℕ) (hn : 1 < n) :
    amplitudeAbscissa (spectralFiber (fun k => χ k) ((starRingEnd ℂ) s) n) n =
        amplitudeAbscissa (spectralFiber (fun k => χ k) (1 - s) n) n ↔ s.re = 1 / 2 := by
  rw [amplitudeAbscissa_spectralFiber χ hq _ n hn, amplitudeAbscissa_spectralFiber χ hq _ n hn,
    Complex.conj_re, Complex.sub_re, Complex.one_re]
  constructor <;> intro h <;> linarith

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.stripReadout_eq_of_height_eq
#print axioms CriticalLinePhasor.GlobalHelix.stripReadout_re
#print axioms CriticalLinePhasor.GlobalHelix.jPair_magnitude_readout
#print axioms CriticalLinePhasor.GlobalHelix.amplitudeAbscissa_jPair
#print axioms CriticalLinePhasor.GlobalHelix.jPair_plane_conj
#print axioms CriticalLinePhasor.GlobalHelix.amplitudeAbscissa_spectralFiber
#print axioms CriticalLinePhasor.GlobalHelix.jPair_forward_abscissae
#print axioms CriticalLinePhasor.GlobalHelix.jEnd_eq_reflected_abscissa_iff
