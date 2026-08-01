import Mathlib

/-!
# The Gaussian clock is forced: self-duality pins `e^{-πx²}`, and its
# Mellin transform is the completion factor

The hostile-reader lemma for the carrier's completion clock, in two exact
statements:

* `gaussianClock_selfDual_iff` — among the Gaussian clocks
  `x ↦ exp(-π b x²)` (`Re b > 0`), the Fourier transform fixes EXACTLY the
  one with `b = 1`: the coefficient `π` and the normalization of the
  completion kernel are FORCED by self-duality (the scalar readout of the
  carrier's two-lane exchange), not chosen by convention and not imported
  from any functional equation.
* `gaussianClock_mellin` — the Mellin transform of that unique self-dual
  clock is `(1/2)·Γℝ(s) = (1/2)·π^{-s/2}Γ(s/2)`: the completion factor of
  the completed readout, hence the `ϑ(t)`-phase and the smooth counting
  clock `1 + ϑ(t)/π`, derive from the carrier's quadratic clock with no
  classical counting formula supplied as input.

Everything is consumed from Mathlib's exact identities
(`fourier_gaussian_pi`, `mellin_comp_rpow`, `mellin_comp_mul_left`,
`Complex.Gamma_eq_integral`); the numerical theta verifications in the
papers are thereby calibration of proven statements, never their proof.
-/

open Complex Real MeasureTheory
open scoped FourierTransform

namespace CriticalLinePhasor.GaussianClock

/-- The candidate Gaussian clocks: `x ↦ exp(-π b x²)`. -/
noncomputable def gaussianClock (b : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-π * b * x ^ 2)

/-- **Self-duality forces the clock**: the Fourier transform fixes the
Gaussian clock iff `b = 1` — the coefficient `π` is pinned by the exchange
symmetry, not by convention. -/
theorem gaussianClock_selfDual_iff {b : ℂ} (hb : 0 < b.re) :
    𝓕 (gaussianClock b) = gaussianClock b ↔ b = 1 := by
  constructor
  · intro h
    have hb0 : b ≠ 0 := fun h0 => by simp [h0] at hb
    rw [show 𝓕 (gaussianClock b) = 𝓕 fun x : ℝ => cexp (-π * b * x ^ 2)
        from rfl, fourier_gaussian_pi hb] at h
    have h0 := congrFun h 0
    simp only [gaussianClock] at h0
    norm_num at h0
    -- h0 : 1 / b ^ (1/2 : ℂ) = 1  (after the exponentials evaluate at 0)
    have hroot : b ^ (1 / 2 : ℂ) = 1 := by
      field_simp at h0
      exact h0
    calc b = b ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ) := by
              rw [← Complex.cpow_add _ _ hb0]
              norm_num
    _ = 1 := by rw [hroot, one_mul]
  · rintro rfl
    rw [show 𝓕 (gaussianClock 1) = 𝓕 fun x : ℝ => cexp (-π * 1 * x ^ 2)
        from rfl, fourier_gaussian_pi (by norm_num)]
    funext t
    simp [gaussianClock]

/-- Mellin of the plain exponential is `Γ` (Euler's integral, order
adjusted to the Mellin convention). -/
theorem mellin_exp_neg {w : ℂ} (hw : 0 < w.re) :
    mellin (fun t : ℝ => (rexp (-t) : ℂ)) w = Complex.Gamma w := by
  rw [Complex.Gamma_eq_integral hw]
  simp only [mellin, Complex.GammaIntegral, smul_eq_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-- **The Mellin of the self-dual clock is the completion factor**:
`∫₀^∞ e^{-πt²} t^{s-1} dt = ½ π^{-s/2} Γ(s/2) = ½ Γℝ(s)`. -/
theorem gaussianClock_mellin {s : ℂ} (hs : 0 < s.re) :
    mellin (gaussianClock 1) s = (1 / 2 : ℂ) * Complex.Gammaℝ s := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  -- rewrite the clock through rpow so the composition lemmas apply
  have hfun : gaussianClock 1 = fun t : ℝ =>
      (fun u : ℝ => (rexp (-(π * u)) : ℂ)) (t ^ (2:ℝ)) := by
    funext t
    have h2' : t ^ ((2:ℝ)) = t ^ (2:ℕ) := by
      rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    simp only [gaussianClock, mul_one, h2']
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hmul : (fun u : ℝ => (rexp (-(π * u)) : ℂ))
      = fun u : ℝ => (fun v : ℝ => (rexp (-v) : ℂ)) (π * u) := by
    funext u
    simp
  have hre : 0 < ((s / ((2:ℝ):ℂ))).re := by
    rw [Complex.div_ofReal_re]
    positivity
  rw [hfun, mellin_comp_rpow (fun u : ℝ => (rexp (-(π * u)) : ℂ)) s 2,
    hmul, mellin_comp_mul_left (fun v : ℝ => (rexp (-v) : ℂ)) _ hpi,
    mellin_exp_neg hre, Complex.Gammaℝ_def]
  rw [Complex.real_smul, smul_eq_mul]
  push_cast
  rw [show -(s / 2) = -s / 2 by ring]
  ring_nf
  push_cast
  ring

end CriticalLinePhasor.GaussianClock

#print axioms CriticalLinePhasor.GaussianClock.gaussianClock_selfDual_iff
#print axioms CriticalLinePhasor.GaussianClock.gaussianClock_mellin
