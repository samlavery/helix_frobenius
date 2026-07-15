import RequestProject.GeneralLatticeTheta
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# The rail decomposition of the general lattice bank

Brick (iii-b).  The lattice bank at `z` decomposes into `m`-indexed rails: the inner `n`-sum of
each rail is a two-variable Jacobi theta with characteristic — the dressed-rail form.  Exactly:

  `Θ_z(t) = ∑_m  e^{-πt m²|z|²/y} · θ₂( i·t·m·x/y , i·t/y )`,

with the rail shift carrying the Gram value of the rail's base point and the characteristic
carrying the off-diagonal coupling.  This is the structural input of the general-`z` functional
equation: the `τ → -1/τ` transformation of `θ₂` (Mathlib, compiled) acts railwise, and the
re-summation over `m` reassembles the dual bank.  All exponent algebra closes by the
`I² = -1` `linear_combination` discipline.  No RH/GRH.
-/

open Complex UpperHalfPlane
open scoped Real

namespace CriticalLinePhasor.EpsteinTheta

/-- The rail shift: the Gram weight of the `m`-th rail. -/
noncomputable def railShift (z : ℍ) (t : ℝ) (m : ℤ) : ℂ :=
  Complex.exp (((-(π * t * (m : ℝ) ^ 2 * (z.re ^ 2 + z.im ^ 2) / z.im)) : ℝ) : ℂ)

/-- The rail characteristic: the off-diagonal coupling of the `m`-th rail. -/
noncomputable def railChar (z : ℍ) (t : ℝ) (m : ℤ) : ℂ :=
  Complex.I * (t * m * z.re / z.im)

/-- The rail modulus. -/
noncomputable def railTau (z : ℍ) (t : ℝ) : ℂ := Complex.I * (t / z.im)

lemma railTau_im (z : ℍ) {t : ℝ} (ht : 0 < t) : 0 < (railTau z t).im := by
  have hy := z.im_pos
  have hcast : railTau z t = Complex.I * (((t / z.im : ℝ)) : ℂ) := by
    rw [railTau]
    push_cast
    ring
  rw [hcast]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, one_mul, mul_zero, zero_add]
  positivity

/-- **The per-term rail identity**: each bank phasor factors as rail shift times a
two-variable-theta term. -/
lemma term_rail (z : ℍ) (t : ℝ) (m n : ℤ) :
    ((Real.exp (-(π * t) * gram z (m, n)) : ℝ) : ℂ) =
      railShift z t m * jacobiTheta₂_term n (railChar z t m) (railTau z t) := by
  rw [railShift, jacobiTheta₂_term, railChar, railTau, ← Complex.exp_add,
    Complex.ofReal_exp]
  congr 1
  rw [gram]
  push_cast
  linear_combination (-(2 * π * t * (m : ℂ) * (n : ℂ) * (z.re : ℂ) + π * t * (n : ℂ) ^ 2) /
    (z.im : ℂ)) * Complex.I_sq

/-- The rail form of the bank is summable over the full lattice. -/
lemma summable_rail_terms (z : ℍ) {t : ℝ} (ht : 0 < t) :
    Summable fun p : ℤ × ℤ =>
      railShift z t p.1 * jacobiTheta₂_term p.2 (railChar z t p.1) (railTau z t) := by
  have hreal : Summable fun p : ℤ × ℤ => ((Real.exp (-(π * t) * gram z p) : ℝ) : ℂ) :=
    Complex.summable_ofReal.mpr (summable_latticeTheta_term z ht)
  exact hreal.congr fun p => term_rail z t p.1 p.2

/-- **The rail decomposition of the bank**: the general lattice theta is the `m`-indexed sum
of rail shifts times two-variable Jacobi thetas with characteristic — the dressed-rail form of
the carrier bank at `z`. -/
theorem latticeTheta_rails (z : ℍ) {t : ℝ} (ht : 0 < t) :
    (latticeTheta z t : ℂ) =
      ∑' m : ℤ, railShift z t m * jacobiTheta₂ (railChar z t m) (railTau z t) := by
  rw [latticeTheta, Complex.ofReal_tsum]
  calc ∑' p : ℤ × ℤ, ((Real.exp (-(π * t) * gram z p) : ℝ) : ℂ)
      = ∑' p : ℤ × ℤ,
          railShift z t p.1 * jacobiTheta₂_term p.2 (railChar z t p.1) (railTau z t) :=
        tsum_congr fun p => term_rail z t p.1 p.2
    _ = ∑' m : ℤ, ∑' n : ℤ,
          railShift z t m * jacobiTheta₂_term n (railChar z t m) (railTau z t) :=
        (summable_rail_terms z ht).tsum_prod' fun m =>
          (summable_rail_terms z ht).prod_factor m
    _ = ∑' m : ℤ, railShift z t m * jacobiTheta₂ (railChar z t m) (railTau z t) := by
        refine tsum_congr fun m => ?_
        rw [tsum_mul_left]
        rfl

end CriticalLinePhasor.EpsteinTheta

#print axioms CriticalLinePhasor.EpsteinTheta.term_rail
#print axioms CriticalLinePhasor.EpsteinTheta.latticeTheta_rails
