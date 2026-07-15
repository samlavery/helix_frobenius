import RequestProject.HeckeCancellation
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# The Gaussian-lattice theta functional equation

The first brick of the Eisenstein/Rankin error-term chain — the `r = 2` instance of the
fixed-kernel functional equation.  At `z = i` the lattice `ℤ·z + ℤ` is `ℤ[i]` with Gram form
`m² + n²`, and the two-dimensional lattice theta is the *square* of the one-variable Jacobi
theta (Cauchy product — the identification is the named next brick; this file delivers the
analytic law).  The weight-one functional equation `Θ(1/t) = t·Θ(t)` falls out of Mathlib's
`jacobiTheta_S_smul` composed with the compiled vertical-line inversion (`Sgl_smul_vert`): the
two-dimensional Poisson input obtained by squaring the one-dimensional one.  Fed to the abstract
functional-equation machinery this yields the Epstein zeta continuation at the Gaussian point.
No RH/GRH.
-/

open Complex UpperHalfPlane
open scoped Real

namespace CriticalLinePhasor.EpsteinTheta

open CriticalLinePhasor.HeckeCancellation

/-- The two-dimensional lattice theta at the Gaussian point: the square of the Jacobi theta on
the vertical line. -/
noncomputable def thetaSq (t : ℝ) : ℂ := jacobiTheta ((t : ℂ) * Complex.I) ^ 2

/-- **The weight-one functional equation of the Gaussian lattice theta**:
`Θ(1/t) = t·Θ(t)`. -/
theorem thetaSq_inv {t : ℝ} (ht : 0 < t) :
    thetaSq t⁻¹ = (t : ℂ) * thetaSq t := by
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hSv : ModularGroup.S • vert t ht = vert t⁻¹ (inv_pos.mpr ht) := by
    show Sgl • vert t ht = vert t⁻¹ (inv_pos.mpr ht)
    exact Sgl_smul_vert t ht
  have hS := jacobiTheta_S_smul (vert t ht)
  rw [hSv, vert_coe, vert_coe] at hS
  have harg : -Complex.I * ((t : ℂ) * Complex.I) = (t : ℂ) := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-(t : ℂ)) * hI
  rw [harg] at hS
  unfold thetaSq
  push_cast at hS ⊢
  rw [hS, mul_pow, pow_two ((t : ℂ) ^ (1 / 2 : ℂ)), ← Complex.cpow_add _ _ htne]
  norm_num

/-- Each Gaussian phasor is a real exponential: the bank's terms at the Gaussian point. -/
lemma term_eq_real {t : ℝ} (n : ℤ) :
    Complex.exp (π * Complex.I * (n : ℂ) ^ 2 * ((t : ℂ) * Complex.I)) =
      ((Real.exp (-(π * t * (n : ℝ) ^ 2)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (π * (t : ℂ) * (n : ℂ) ^ 2) * Complex.I_sq

/-- The complex phasor bank at the Gaussian point is summable. -/
lemma summable_term {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℤ =>
      Complex.exp (π * Complex.I * (n : ℂ) ^ 2 * ((t : ℂ) * Complex.I)) := by
  have him : 0 < ((t : ℂ) * Complex.I).im := by simpa using ht
  have h := (hasSum_jacobiTheta₂_term 0 him).summable
  apply h.congr
  intro n
  simp [jacobiTheta₂_term]

/-- The phasor bank is norm-summable: each phasor is a positive real exponential. -/
lemma summable_norm_term {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℤ =>
      ‖Complex.exp (π * Complex.I * (n : ℂ) ^ 2 * ((t : ℂ) * Complex.I))‖ := by
  have h := summable_term ht
  simp_rw [term_eq_real] at h
  rw [Complex.summable_ofReal] at h
  exact h.congr fun n => by
    rw [term_eq_real, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]

/-- **The lattice identification**: the squared theta is the phasor bank of the Gaussian
lattice `ℤ[i]` — the two-dimensional carrier bank whose heights are the Gram-form values
`m² + n²`, with the functional equation `thetaSq_inv` as its weld reflection and the `(0,0)`
term as the DC channel. -/
theorem thetaSq_eq_double {t : ℝ} (ht : 0 < t) :
    thetaSq t = ∑' p : ℤ × ℤ,
      Complex.exp (π * Complex.I * ((p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2) *
        ((t : ℂ) * Complex.I)) := by
  have hjt : jacobiTheta ((t : ℂ) * Complex.I) =
      ∑' n : ℤ, Complex.exp (π * Complex.I * (n : ℂ) ^ 2 * ((t : ℂ) * Complex.I)) := rfl
  rw [thetaSq, pow_two, hjt,
    tsum_mul_tsum_of_summable_norm (summable_norm_term ht) (summable_norm_term ht)]
  apply tsum_congr
  intro p
  rw [← Complex.exp_add]
  congr 1
  ring

end CriticalLinePhasor.EpsteinTheta

#print axioms CriticalLinePhasor.EpsteinTheta.thetaSq_inv
#print axioms CriticalLinePhasor.EpsteinTheta.thetaSq_eq_double
#print axioms CriticalLinePhasor.EpsteinTheta.summable_norm_term
