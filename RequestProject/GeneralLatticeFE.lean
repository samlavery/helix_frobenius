import RequestProject.GeneralLatticeRails

/-!
# The general-z functional equation of the lattice bank

Brick (iii-c), closing brick (iii) of the Eisenstein chain.  The weight-one functional equation
`Θ_z(1/t) = t·Θ_z(t)` holds at **every** point `z` of the upper half plane, not only at the
Gaussian point.  Route: the compiled rail decomposition (`latticeTheta_rails`) writes the bank
as `m`-indexed rails; Mathlib's two-variable Jacobi theta transformation
(`jacobiTheta₂_functional_equation`) acts railwise and lands each rail on the *diagonal-dual*
form `√(y/t)·∑_n exp(2πi·mn·x − πt·m²y − π·n²y/t)`; the resulting double sum is symmetric
under the `(m,n)`-swap composed with `t ↦ 1/t`, and that exact swap symmetry — the two lattice
axes exchanging roles through Poisson — is the weld reflection.  Determinant one enters as
`√(ty)·√(y/t)⁻¹ = t`: the det-1 normalization is what makes the reflected bank land on itself
with weight one.  All exponent algebra closes by the `I² = -1` `linear_combination` discipline.
No RH/GRH.
-/

open Complex UpperHalfPlane
open scoped Real

namespace CriticalLinePhasor.EpsteinTheta

/-- The diagonal-dual term: the rail-transformed phasor, symmetric in the two lattice axes
through `t ↦ 1/t`. -/
noncomputable def dualTerm (z : ℍ) (t : ℝ) (p : ℤ × ℤ) : ℂ :=
  Complex.exp (2 * π * Complex.I * p.1 * p.2 * z.re - π * t * p.1 ^ 2 * z.im -
    π * p.2 ^ 2 * z.im / t)

/-- The dual term splits into a unit phase and a real Gaussian. -/
lemma dualTerm_eq (z : ℍ) (t : ℝ) (p : ℤ × ℤ) :
    dualTerm z t p =
      Complex.exp (((2 * π * (p.1 : ℝ) * (p.2 : ℝ) * z.re : ℝ) : ℂ) * Complex.I) *
        ((Real.exp (-(π * (t * z.im) * (p.1 : ℝ) ^ 2) +
          -(π * (z.im / t) * (p.2 : ℝ) ^ 2)) : ℝ) : ℂ) := by
  rw [dualTerm, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The dual term's norm is the product Gaussian. -/
lemma norm_dualTerm (z : ℍ) (t : ℝ) (p : ℤ × ℤ) :
    ‖dualTerm z t p‖ =
      Real.exp (-(π * (t * z.im) * (p.1 : ℝ) ^ 2)) *
        Real.exp (-(π * (z.im / t) * (p.2 : ℝ) ^ 2)) := by
  rw [dualTerm_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, Real.abs_exp, Real.exp_add]

/-- The diagonal-dual bank is summable. -/
lemma summable_dualTerm (z : ℍ) {t : ℝ} (ht : 0 < t) : Summable (dualTerm z t) := by
  have hy : (0 : ℝ) < z.im := z.im_pos
  have hg1 := summable_gaussian_real (c := t * z.im) (by positivity)
  have hg2 := summable_gaussian_real (c := z.im / t) (by positivity)
  have hg1n : Summable fun n : ℤ => ‖Real.exp (-(π * (t * z.im) * (n : ℝ) ^ 2))‖ :=
    hg1.congr fun n => (Real.norm_of_nonneg (Real.exp_pos _).le).symm
  have hg2n : Summable fun n : ℤ => ‖Real.exp (-(π * (z.im / t) * (n : ℝ) ^ 2))‖ :=
    hg2.congr fun n => (Real.norm_of_nonneg (Real.exp_pos _).le).symm
  exact Summable.of_norm
    ((summable_mul_of_summable_norm' hg1n hg1 hg2n hg2).congr fun p =>
      (norm_dualTerm z t p).symm)

/-- **The swap symmetry of the dual bank**: exchanging the two lattice axes inverts the
height — the reflection that carries the weld. -/
lemma tsum_dualTerm_inv (z : ℍ) (t : ℝ) :
    ∑' p : ℤ × ℤ, dualTerm z t⁻¹ p = ∑' p : ℤ × ℤ, dualTerm z t p := by
  rw [← (Equiv.prodComm ℤ ℤ).tsum_eq (dualTerm z t)]
  refine tsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply]
  rw [dualTerm, dualTerm]
  simp only [Prod.fst_swap, Prod.snd_swap]
  congr 1
  push_cast
  simp only [div_eq_mul_inv, inv_inv]
  ring

lemma railTau_ne_zero (z : ℍ) {t : ℝ} (ht : 0 < t) : railTau z t ≠ 0 := by
  intro h
  have him := railTau_im z ht
  rw [h] at him
  simp at him

/-- The dual modulus: minus one over the rail modulus. -/
lemma railTau_neg_inv (z : ℍ) (t : ℝ) :
    -1 / railTau z t = Complex.I * ((z.im / t : ℝ) : ℂ) := by
  rw [railTau]
  push_cast
  rw [show Complex.I * ((t : ℂ) / (z.im : ℂ)) = ((t : ℂ) / (z.im : ℂ)) * Complex.I from
    mul_comm _ _, neg_div, div_eq_mul_inv, one_mul, mul_inv, Complex.inv_I]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- Each dual term is the rail Gaussian times a two-variable-theta term at the dual
modulus. -/
lemma dualTerm_rail (z : ℍ) (t : ℝ) (m n : ℤ) :
    dualTerm z t (m, n) =
      ((Real.exp (-(π * (t * z.im) * (m : ℝ) ^ 2)) : ℝ) : ℂ) *
        jacobiTheta₂_term n (((m : ℝ) * z.re : ℝ) : ℂ)
          (Complex.I * ((z.im / t : ℝ) : ℂ)) := by
  rw [dualTerm, jacobiTheta₂_term, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (-((π : ℂ) * (n : ℂ) ^ 2 * (z.im : ℂ) / (t : ℂ))) * Complex.I_sq

/-- **The railwise transformation**: the two-variable theta law carries each rail of the bank
to its diagonal-dual slice, with the det-1 prefactor `√(y/t)`. -/
lemma rail_transform (z : ℍ) {t : ℝ} (ht : 0 < t) (m : ℤ) :
    railShift z t m * jacobiTheta₂ (railChar z t m) (railTau z t) =
      (((z.im / t) ^ (2⁻¹ : ℝ) : ℝ) : ℂ) * ∑' n : ℤ, dualTerm z t (m, n) := by
  have hy : (0 : ℝ) < z.im := z.im_pos
  have hτne := railTau_ne_zero z ht
  have hpre : (1 : ℂ) / (-Complex.I * railTau z t) ^ (1 / 2 : ℂ) =
      (((z.im / t) ^ (2⁻¹ : ℝ) : ℝ) : ℂ) := by
    have h1 : -Complex.I * railTau z t = ((t / z.im : ℝ) : ℂ) := by
      rw [railTau]
      push_cast
      linear_combination (-((t : ℂ) / (z.im : ℂ))) * Complex.I_sq
    rw [h1, show (1 / 2 : ℂ) = ((2⁻¹ : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity) (2⁻¹ : ℝ), one_div, ← Complex.ofReal_inv,
      ← Real.inv_rpow (by positivity), inv_div]
  have hdiv : railChar z t m / railTau z t = (((m : ℝ) * z.re : ℝ) : ℂ) := by
    rw [div_eq_iff hτne, railChar, railTau]
    push_cast
    ring
  have hgauss : railShift z t m *
      Complex.exp (-π * Complex.I * railChar z t m ^ 2 / railTau z t) =
      ((Real.exp (-(π * (t * z.im) * (m : ℝ) ^ 2)) : ℝ) : ℂ) := by
    have hB : -π * Complex.I * railChar z t m ^ 2 / railTau z t =
        ((π * t * (m : ℝ) ^ 2 * z.re ^ 2 / z.im : ℝ) : ℂ) := by
      rw [div_eq_iff hτne, railChar, railTau]
      push_cast
      linear_combination
        (-((π : ℂ) * (t : ℂ) ^ 2 * (m : ℂ) ^ 2 * (z.re : ℂ) ^ 2 / (z.im : ℂ) ^ 2 *
          Complex.I)) * Complex.I_sq
    rw [railShift, hB, ← Complex.exp_add, ← Complex.ofReal_add, Complex.ofReal_exp]
    congr 2
    field_simp
    ring
  rw [jacobiTheta₂_functional_equation (railChar z t m) (railTau z t), hpre, hdiv,
    railTau_neg_inv, tsum_congr (fun n => dualTerm_rail z t m n), tsum_mul_left,
    show (∑' n : ℤ, jacobiTheta₂_term n (((m : ℝ) * z.re : ℝ) : ℂ)
      (Complex.I * ((z.im / t : ℝ) : ℂ))) =
      jacobiTheta₂ (((m : ℝ) * z.re : ℝ) : ℂ) (Complex.I * ((z.im / t : ℝ) : ℂ)) from rfl,
    ← hgauss]
  ring

/-- **The bank in diagonal-dual form**: the general lattice theta is `√(y/t)` times the
symmetric dual bank. -/
lemma latticeTheta_eq_dual (z : ℍ) {t : ℝ} (ht : 0 < t) :
    (latticeTheta z t : ℂ) =
      (((z.im / t) ^ (2⁻¹ : ℝ) : ℝ) : ℂ) * ∑' p : ℤ × ℤ, dualTerm z t p := by
  rw [latticeTheta_rails z ht, tsum_congr (fun m => rail_transform z ht m), tsum_mul_left,
    ← (summable_dualTerm z ht).tsum_prod' fun m => (summable_dualTerm z ht).prod_factor m]

/-- **The general-z functional equation of the lattice bank**: `Θ_z(1/t) = t·Θ_z(t)` at every
point of the upper half plane — the weld reflection of the carrier bank, with weight one forced
by the determinant-one normalization.  Proven for the full two-parameter family in one stroke;
the Gaussian-point law `thetaSq_inv` is its `z = i` reading.  No RH/GRH. -/
theorem latticeTheta_inv (z : ℍ) {t : ℝ} (ht : 0 < t) :
    latticeTheta z t⁻¹ = t * latticeTheta z t := by
  have hy : (0 : ℝ) < z.im := z.im_pos
  have hscalar : (z.im / t⁻¹) ^ (2⁻¹ : ℝ) = t * (z.im / t) ^ (2⁻¹ : ℝ) := by
    have h1 : z.im / t⁻¹ = t ^ 2 * (z.im / t) := by
      rw [div_eq_mul_inv, inv_inv]
      field_simp
    rw [h1, Real.mul_rpow (sq_nonneg t) (by positivity),
      ← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le,
      show ((2 : ℕ) : ℝ) * 2⁻¹ = 1 by norm_num, Real.rpow_one]
  have hC : (latticeTheta z t⁻¹ : ℂ) = ((t * latticeTheta z t : ℝ) : ℂ) := by
    rw [latticeTheta_eq_dual z (inv_pos.mpr ht), tsum_dualTerm_inv, Complex.ofReal_mul,
      latticeTheta_eq_dual z ht, hscalar]
    push_cast
    ring
  exact_mod_cast hC

end CriticalLinePhasor.EpsteinTheta

#print axioms CriticalLinePhasor.EpsteinTheta.rail_transform
#print axioms CriticalLinePhasor.EpsteinTheta.latticeTheta_inv
