import Mathlib
import RequestProject.ThetaWronskianSuzukiGram

/-!
# The Jensen ladder at degree two

For a real sequence `γ` the degree-`d` Jensen polynomial at the centre is
`J^{d,0}(X) = ∑_{j ≤ d} (d choose j) γ_j X^j`; at `d = 2` it is
`γ₂X² + 2γ₁X + γ₀`.

This file makes the `d = 2` rung standalone.  With no hypothesis beyond
positivity of the leading coefficient, hyperbolicity of the degree-two Jensen
polynomial is *exactly* the central Turán inequality `γ₀γ₂ ≤ γ₁²`
(`jensenTwo_allRootsReal_iff`).  The equivalence is then instantiated at the
actual Xi central coefficients — unconditionally, in both the central
normalization (`xiJensenTwo_allRootsReal_iff`) and the raw moment
normalization (`xiJensenTwo_allRootsReal_iff_moments`) — and the one-way arrow
from the compiled theta-kernel gate is recorded
(`xiJensenTwo_allRootsReal_of_numerator_pos`).

Two further unconditional facts about the actual rung: its real roots are
strictly negative (`xiJensenTwo_root_neg`), and its leading and constant
coefficients are positive, so the rung is a genuine quadratic and the
equivalence above is not vacuous.

Scope: `d = 2` alone is one rung.  Nothing here climbs the ladder.

Search record used before construction:

* repository: `rg -n "Jensen|jensen|hyperbolic|AllZerosImaginary|discrim"`
* Mathlib names: `rg -n "discrim|quadratic_eq_zero_iff|Polynomial.roots_quadratic"`
* the existing central-coefficient layer of `ThetaWronskianSuzukiGram`
  (`xiCentralCoeff`, `xiCentralCoeff_zero_one_two`, `xiCentralTuran_of_numerator_pos`)
-/

open Polynomial

noncomputable section

namespace CriticalLinePhasor.JensenRungTwo

open CriticalLinePhasor.ThetaWronskianSuzukiGram

/-- A real polynomial is hyperbolic: every complex root is real.  Companion of
`AllZerosImaginary` in `ThetaWronskianSuzukiGram`, with the other axis. -/
def AllRootsReal (p : ℝ[X]) : Prop :=
  ∀ z : ℂ, Polynomial.eval₂ Complex.ofRealHom z p = 0 → z.im = 0

/-- The degree-two Jensen polynomial `γ₂X² + 2γ₁X + γ₀`. -/
def jensenTwo (g0 g1 g2 : ℝ) : ℝ[X] :=
  C g2 * X ^ 2 + C (2 * g1) * X + C g0

theorem jensenTwo_eval₂ (g0 g1 g2 : ℝ) (z : ℂ) :
    Polynomial.eval₂ Complex.ofRealHom z (jensenTwo g0 g1 g2)
      = (g2 : ℂ) * z ^ 2 + 2 * (g1 : ℂ) * z + (g0 : ℂ) := by
  simp [jensenTwo]

theorem jensenTwo_eval (g0 g1 g2 r : ℝ) :
    Polynomial.eval r (jensenTwo g0 g1 g2) = g2 * r ^ 2 + 2 * g1 * r + g0 := by
  simp [jensenTwo]

/-- The real and imaginary parts of the defining equation of a complex root. -/
theorem jensenTwo_root_re_im {g0 g1 g2 : ℝ} {z : ℂ}
    (hz : Polynomial.eval₂ Complex.ofRealHom z (jensenTwo g0 g1 g2) = 0) :
    g2 * (z.re ^ 2 - z.im ^ 2) + 2 * g1 * z.re + g0 = 0 ∧
      2 * z.im * (g2 * z.re + g1) = 0 := by
  rw [jensenTwo_eval₂, Complex.ext_iff] at hz
  obtain ⟨hre, him⟩ := hz
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    pow_two, Complex.ofReal_re, Complex.ofReal_im] at hre him
  constructor
  · nlinarith [hre]
  · nlinarith [him]

/-- Converse of `jensenTwo_root_re_im`: the two real equations produce a root. -/
theorem jensenTwo_root_of_re_im {g0 g1 g2 : ℝ} {z : ℂ}
    (h1 : g2 * (z.re ^ 2 - z.im ^ 2) + 2 * g1 * z.re + g0 = 0)
    (h2 : 2 * z.im * (g2 * z.re + g1) = 0) :
    Polynomial.eval₂ Complex.ofRealHom z (jensenTwo g0 g1 g2) = 0 := by
  rw [jensenTwo_eval₂, Complex.ext_iff]
  refine ⟨?_, ?_⟩
  · simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      pow_two, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [h1]
  · simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      pow_two, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [h2]

/-- **The rung, standalone.**  For a positive leading coefficient the degree-two
Jensen polynomial is hyperbolic exactly when the central Turán inequality
holds. -/
theorem jensenTwo_allRootsReal_iff {g0 g1 g2 : ℝ} (hg2 : 0 < g2) :
    AllRootsReal (jensenTwo g0 g1 g2) ↔ g0 * g2 ≤ g1 ^ 2 := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    set D : ℝ := (g0 * g2 - g1 ^ 2) / g2 ^ 2 with hDdef
    have hg2ne : g2 ≠ 0 := ne_of_gt hg2
    have hDpos : 0 < D := by
      apply div_pos (by linarith) (by positivity)
    set b : ℝ := Real.sqrt D with hbdef
    have hbpos : 0 < b := Real.sqrt_pos.mpr hDpos
    have hbsq : b ^ 2 = D := Real.sq_sqrt hDpos.le
    set z : ℂ := ⟨-g1 / g2, b⟩ with hzdef
    have hzre : z.re = -g1 / g2 := rfl
    have hzim : z.im = b := rfl
    have hre_eq : g2 * (z.re ^ 2 - z.im ^ 2) + 2 * g1 * z.re + g0 = 0 := by
      rw [hzre, hzim, hbsq, hDdef]
      field_simp
      ring
    have him_eq : 2 * z.im * (g2 * z.re + g1) = 0 := by
      rw [hzre, hzim]
      field_simp
      ring
    have := h z (jensenTwo_root_of_re_im hre_eq him_eq)
    rw [hzim] at this
    exact absurd this (ne_of_gt hbpos)
  · intro h z hz
    obtain ⟨hre, him⟩ := jensenTwo_root_re_im hz
    by_contra hy
    have hlin : g2 * z.re + g1 = 0 := by
      rcases mul_eq_zero.mp him with h2 | h3
      · exact absurd (show z.im = 0 by linarith) hy
      · exact h3
    have himsq : 0 < z.im ^ 2 := by
      rcases lt_trichotomy z.im 0 with hlt | heq | hgt
      · nlinarith
      · exact absurd heq hy
      · nlinarith
    have hg1 : g1 = -(g2 * z.re) := by linarith
    subst hg1
    nlinarith [hre, h, mul_pos (mul_pos hg2 hg2) himsq]

/-! ## Non-vacuity: the predicate separates

`AllRootsReal` is neither vacuous nor trivially true on the family, and the
equivalence decides both cases correctly. -/

example : AllRootsReal (jensenTwo 1 2 1) :=
  (jensenTwo_allRootsReal_iff one_pos).mpr (by norm_num)

example : ¬ AllRootsReal (jensenTwo 1 0 1) := by
  intro h
  have := (jensenTwo_allRootsReal_iff one_pos).mp h
  norm_num at this

/-! ## Instantiation at the actual Xi central coefficients -/

theorem xiCentralCoeff_zero_pos : 0 < xiCentralCoeff 0 := by
  rcases xiCentralCoeff_zero_one_two with ⟨h0, _, _⟩
  rw [h0]; exact xiThetaMoment_pos 0

theorem xiCentralCoeff_one_pos : 0 < xiCentralCoeff 1 := by
  rcases xiCentralCoeff_zero_one_two with ⟨_, h1, _⟩
  rw [h1]; have := xiThetaMoment_pos 2; linarith

theorem xiCentralCoeff_two_pos : 0 < xiCentralCoeff 2 := by
  rcases xiCentralCoeff_zero_one_two with ⟨_, _, h2⟩
  rw [h2]; have := xiThetaMoment_pos 4; linarith

/-- The actual degree-two Jensen polynomial of Riemann's Xi kernel. -/
def xiJensenTwo : ℝ[X] :=
  jensenTwo (xiCentralCoeff 0) (xiCentralCoeff 1) (xiCentralCoeff 2)

/-- **The rung at the actual object, unconditionally**: hyperbolicity of the
degree-two Jensen polynomial of the Xi kernel is equivalent to the central
Turán inequality. -/
theorem xiJensenTwo_allRootsReal_iff :
    AllRootsReal xiJensenTwo ↔
      xiCentralCoeff 0 * xiCentralCoeff 2 ≤ xiCentralCoeff 1 ^ 2 :=
  jensenTwo_allRootsReal_iff xiCentralCoeff_two_pos

/-- The same equivalence in the raw moment normalization. -/
theorem xiJensenTwo_allRootsReal_iff_moments :
    AllRootsReal xiJensenTwo ↔
      xiThetaMoment 0 * xiThetaMoment 4 ≤ 3 * xiThetaMoment 2 ^ 2 := by
  rw [xiJensenTwo_allRootsReal_iff]
  rcases xiCentralCoeff_zero_one_two with ⟨h0, h1, h2⟩
  rw [h0, h1, h2]
  constructor <;> intro h <;> nlinarith

/-- **The one-way arrow.**  Positivity of the theta-kernel concavity numerator
— the gate of `ThetaWronskianSuzukiGram` — makes the degree-two Jensen
polynomial of the Xi kernel hyperbolic. -/
theorem xiJensenTwo_allRootsReal_of_numerator_pos
    (hpos : ∀ u : ℝ, 0 < u → 0 < xiRadialConcavityNumerator u) :
    AllRootsReal xiJensenTwo :=
  xiJensenTwo_allRootsReal_iff.mpr (xiCentralTuran_of_numerator_pos hpos).le

/-- Unconditionally, every real root of the actual rung is strictly negative:
the sign structure the Laguerre--Pólya class requires, with no gate input. -/
theorem xiJensenTwo_root_neg {r : ℝ} (hr : Polynomial.eval r xiJensenTwo = 0) :
    r < 0 := by
  rw [xiJensenTwo, jensenTwo_eval] at hr
  by_contra hcon
  push_neg at hcon
  nlinarith [xiCentralCoeff_zero_pos, xiCentralCoeff_one_pos,
    xiCentralCoeff_two_pos, sq_nonneg r, mul_nonneg xiCentralCoeff_one_pos.le hcon,
    mul_nonneg xiCentralCoeff_two_pos.le (sq_nonneg r)]

/-- The rung is a genuine quadratic: its degree is exactly two. -/
theorem xiJensenTwo_natDegree : xiJensenTwo.natDegree = 2 := by
  have h2 : xiCentralCoeff 2 ≠ 0 := ne_of_gt xiCentralCoeff_two_pos
  rw [xiJensenTwo, jensenTwo]
  compute_degree!

end CriticalLinePhasor.JensenRungTwo

section AxiomAudit

#print axioms CriticalLinePhasor.JensenRungTwo.jensenTwo_allRootsReal_iff
#print axioms CriticalLinePhasor.JensenRungTwo.xiJensenTwo_allRootsReal_iff
#print axioms CriticalLinePhasor.JensenRungTwo.xiJensenTwo_allRootsReal_iff_moments
#print axioms CriticalLinePhasor.JensenRungTwo.xiJensenTwo_allRootsReal_of_numerator_pos
#print axioms CriticalLinePhasor.JensenRungTwo.xiJensenTwo_root_neg
#print axioms CriticalLinePhasor.JensenRungTwo.xiJensenTwo_natDegree

end AxiomAudit
