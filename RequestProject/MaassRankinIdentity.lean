import RequestProject.MaassRankinEvaluation
import RequestProject.StripFubini

/-!
# The Rankin--Selberg identity for a Maass form, unconditional

The two halves meet.  `maass_rs_unfolding_unconditional` turns the strip integral into the
Eisenstein pairing over the fundamental domain; `mellin_maassEnergy` turns it into arithmetic times
archimedean.  The bridge between them is Fubini on the strip, and — for the sixth time in this
chain — the corpus's transport is form-independent: `StripFubini.strip_integral_eq_iterated`
consumes an arbitrary `G : ℍ → ℂ`, so the Maass case needs no new measure theory, only the
product-integrability already proved.

The exponent bookkeeping is the same scale fact as before, read from the other side: the hyperbolic
density contributes `y^{-2}`, so the strip integral at `s` is the Mellin transform of the energy at
`s - 1`, and `mellin_maassEnergy` then shifts back to `s`.  The two shifts cancel exactly, which is
the arithmetic reason the Rankin--Selberg series appears at the same `s` as the Eisenstein height.

Result: `maass_rankinSelberg_identity` — for a genuine level-one Maass cusp form,

  `∑'_q ∫_𝒟 ‖u‖²·Im(γ_q·z)^s = ½·(∑ₙ|λₙ|²(n+1)^{-s})·A(s)`

with no side condition on the half-plane `Re s > 2(E₀+2)+1`.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Filter
open scoped Real MatrixGroups Pointwise Topology

set_option maxHeartbeats 1000000

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-- **The strip integral is the Mellin transform of the horizontal energy**, at the exponent the
hyperbolic density `y^{-2}` dictates. -/
theorem maass_strip_side_mellin (M : GenuineMaassCuspForm3D) {s : ℂ} (hs : 1 < s.re) :
    ∫ z in strip, maassRsIntegrand M s z ∂(volume : Measure ℍ) =
      mellin (fun y : ℝ => ((maassEnergy M y : ℝ) : ℂ)) (s - 1) := by
  rw [strip_integral_eq_iterated (maassRsIntegrand M s)
    (maassRsIntegrand_product_integrable M hs), mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0:ℝ) < y := hy
  have hyne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy0.ne'
  have hpoint : ∀ x : ℝ, ((y ^ 2)⁻¹ : ℝ) •
      maassRsIntegrand M s (UpperHalfPlane.ofComplex
        (Complex.measurableEquivRealProd.symm (x, y))) =
      ((((y ^ 2)⁻¹ : ℝ) : ℂ) * (y : ℂ) ^ s) *
        ((‖maassWaveCoordinates M.eigenData M.radialKernel x y‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have hmk : Complex.measurableEquivRealProd.symm (x, y) = (x : ℂ) + y * Complex.I := by
      rw [Complex.measurableEquivRealProd_symm_apply]
      exact Complex.mk_eq_add_mul_I x y
    have him : (0 : ℝ) < ((x : ℂ) + y * Complex.I).im := by simpa using hy0
    have him2 : (⟨(x : ℂ) + y * Complex.I, him⟩ : ℍ).im = y := by
      simp [UpperHalfPlane.im]
    have hwave : maassWave M.eigenData M.radialKernel ⟨(x : ℂ) + y * Complex.I, him⟩ =
        maassWaveCoordinates M.eigenData M.radialKernel x y := by
      rw [maassWave_eq_coords, him2]
      norm_num
    rw [hmk, ofComplex_apply_of_im_pos him, maassRsIntegrand, maassP, him2, hwave,
      Complex.real_smul]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ico fun x _ => hpoint x,
    MeasureTheory.integral_const_mul, integral_complex_ofReal, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, smul_eq_mul, maassEnergy]
  congr 1
  have hzp : (y : ℝ) ^ (-2 : ℤ) = (y ^ 2)⁻¹ := by
    rw [zpow_neg, zpow_two, pow_two]
  rw [show s - 1 - 1 = ((-2 : ℤ) : ℂ) + s by push_cast; ring,
    Complex.cpow_add _ _ hyne, Complex.cpow_intCast, ← Complex.ofReal_zpow, hzp]

/-- **The strip side is the Rankin--Selberg series.**  The two exponent shifts — the density's
`y^{-2}` and Parseval's `y/2` — cancel exactly. -/
theorem maass_strip_side_rankinSelberg (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < s.re) :
    ∫ z in strip, maassRsIntegrand M s z ∂(volume : Measure ℍ) =
      (2 : ℂ)⁻¹ * ((∑' n : ℕ, rankinSelbergTerm M s n) * archimedeanFactor M s) := by
  have hE : (0:ℝ) ≤ 2 * (M.eigenData.E₀ + 2) := by positivity
  have hs1 : 1 < s.re := by linarith
  have hshift : s - 1 + 1 = s := by ring
  have hre : ((s - 1) + 1).re = s.re := by rw [hshift]
  rw [maass_strip_side_mellin M hs1, mellin_maassEnergy M (s := s - 1) (by rw [hre]; exact hs),
    hshift]

/-- **The Rankin--Selberg identity for a genuine level-one Maass cusp form, unconditional.**
The Eisenstein pairing over the fundamental domain equals half the arithmetic series times the
archimedean factor, with no side condition. -/
theorem maass_rankinSelberg_identity (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < s.re) :
    ∑' q : CosetQ, ∫ z in ModularGroup.fd,
        (maassP M z : ℂ) * (((rep q • z).im : ℝ) : ℂ) ^ s ∂(volume : Measure ℍ) =
      (2 : ℂ)⁻¹ * ((∑' n : ℕ, rankinSelbergTerm M s n) * archimedeanFactor M s) := by
  have hE : (0:ℝ) ≤ 2 * (M.eigenData.E₀ + 2) := by positivity
  have hs1 : 1 < s.re := by linarith
  rw [← maass_rs_unfolding_unconditional M hs1]
  exact maass_strip_side_rankinSelberg M hs

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maass_strip_side_mellin
#print axioms CriticalLinePhasor.Unfolding.maass_strip_side_rankinSelberg
#print axioms CriticalLinePhasor.Unfolding.maass_rankinSelberg_identity
