import RequestProject.StripFubini

/-!
# The strip side of the Rankin–Selberg integral: the Mellin transform of the energy readout

Slice five (c) of brick (iv).  Instantiating the compiled strip Fubini at the RS integrand:
the inner horizontal integral at height `y` is *exactly* the smoothed second moment (the
compiled `rankin_energy_exact`), and the outer integral is a Mellin transform, so

  `∫_{strip} P·(Im)^s dμ_ℍ  =  mellin R (s+k-1)`,   `R(y) = ∑' n, ‖a_n‖²·e^{-4πny}`

(`rs_strip_side`), whence by the compiled Mellin identification (`rankin_mellin_eq`), for
`Re s > 2`:

  `∫_{strip} P·(Im)^s dμ_ℍ  =  Γ(s+k-1) · ∑' n, ‖a_n‖²/(4πn)^{s+k-1}`

(`rs_strip_side_eq_dirichlet`) — the strip side of the unfolded Rankin–Selberg integral IS the
completed Rankin–Selberg Dirichlet series, compiled end to end; combined with `rs_unfolding`
this equates the Dirichlet series to the Petersson–Eisenstein pairing, the engine of its
continuation.  Integrability of the RS integrand on the strip is the carried hypothesis,
discharged with the convergence bounds in the next slice.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups Pointwise NNReal

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- **The strip side is the Mellin transform of the exact energy readout.** -/
theorem rs_strip_side (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) (s : ℂ)
    (hInt : Integrable (fun p : ℝ × ℝ => ((p.2 ^ 2)⁻¹ : ℝ) •
        rsIntegrand f s (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm p)))
      ((volume.restrict (Set.Ico (0:ℝ) 1)).prod (volume.restrict (Set.Ioi (0:ℝ))))) :
    ∫ z in strip, rsIntegrand f s z ∂(volume : Measure ℍ) =
      mellin (fun y : ℝ => ((∑' n : ℕ,
        ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) : ℝ) : ℂ))
        (s + k - 1) := by
  rw [strip_integral_eq_iterated (rsIntegrand f s) hInt, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have hyne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy0.ne'
  -- the integrand at height y, pointwise in x
  have hpoint : ∀ x : ℝ, ((y ^ 2)⁻¹ : ℝ) •
      rsIntegrand f s (UpperHalfPlane.ofComplex
        (Complex.measurableEquivRealProd.symm (x, y))) =
      ((((y ^ 2)⁻¹ * y ^ k : ℝ) : ℂ) * (y : ℂ) ^ s) *
        ((‖f (⟨(x : ℂ) + y * Complex.I, by simpa using hy0⟩ : ℍ)‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have hmk : Complex.measurableEquivRealProd.symm (x, y) = (x : ℂ) + y * Complex.I := by
      rw [Complex.measurableEquivRealProd_symm_apply]
      exact Complex.mk_eq_add_mul_I x y
    have him : (0 : ℝ) < ((x : ℂ) + y * Complex.I).im := by simpa using hy0
    rw [hmk, ofComplex_apply_of_im_pos him, rsIntegrand]
    have him2 : (⟨(x : ℂ) + y * Complex.I, him⟩ : ℍ).im = y := by
      simp [UpperHalfPlane.im]
    rw [P, him2, Complex.normSq_eq_norm_sq]
    rw [Complex.real_smul]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ico fun x _ => hpoint x,
    MeasureTheory.integral_const_mul, integral_complex_ofReal, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, ← rankin_energy_exact f hk hy0]
  -- the scalar: ↑((y²)⁻¹·y^k)·y^s = y^{(s+k-1)-1}
  rw [smul_eq_mul]
  congr 1
  have hzp : (y : ℝ) ^ (k - 2 : ℤ) = (y ^ 2)⁻¹ * y ^ k := by
    rw [zpow_sub₀ hy0.ne', div_eq_mul_inv, mul_comm, zpow_two, pow_two]
  rw [show s + (k : ℂ) - 1 - 1 = ((k - 2 : ℤ) : ℂ) + s by push_cast; ring,
    Complex.cpow_add _ _ hyne, Complex.cpow_intCast, ← Complex.ofReal_zpow, hzp]

/-- **The strip side is the completed Rankin–Selberg Dirichlet series** on `Re s > 2`. -/
theorem rs_strip_side_eq_dirichlet (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re)
    (hInt : Integrable (fun p : ℝ × ℝ => ((p.2 ^ 2)⁻¹ : ℝ) •
        rsIntegrand f s (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm p)))
      ((volume.restrict (Set.Ico (0:ℝ) 1)).prod (volume.restrict (Set.Ioi (0:ℝ))))) :
    ∫ z in strip, rsIntegrand f s z ∂(volume : Measure ℍ) =
      Complex.Gamma (s + k - 1) * ∑' n : ℕ,
        ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) /
          ((4 * π * n : ℝ) : ℂ) ^ (s + k - 1) := by
  rw [rs_strip_side f hk s hInt]
  apply rankin_mellin_eq f hk
  have hre : (s + (k : ℂ) - 1).re = s.re + (k : ℝ) - 1 := by
    simp
  rw [hre]
  linarith

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.rs_strip_side
#print axioms CriticalLinePhasor.Unfolding.rs_strip_side_eq_dirichlet
