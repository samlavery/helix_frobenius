import RequestProject.GlobalHelixCPSFixedCompletion
import RequestProject.GlobalHelixCompletionGammaProduct
import RequestProject.CarrierThetaDecay

/-!
# Full fixed completion of polynomial CPS Satake banks

This file combines the actual primal/contragredient Euler coefficients with a nonempty prescribed
archimedean shift list and a positive conductor scale.  The banks are defined on the 3D carrier;
their projections are coefficient theta functions, whose Mellin transforms are exactly the full
Gamma-completed Dirichlet readouts in the initial half-plane.
-/

open Complex Set MeasureTheory Filter Asymptotics

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection

noncomputable def cpsPolynomialFullPrimal3DBankReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μs : List ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor (coefficientFiber (cpsPolynomialPrimalCoeff W) n x) *
      conductorScaledCompletionKernelLog C μs
        (multiplicativeHeight (coefficientFiber (cpsPolynomialPrimalCoeff W) n x))

noncomputable def cpsPolynomialFullDual3DTransformedReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μs : List ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor
        (reciprocalCoefficientFiber
          (fun j => (starRingEnd ℂ) (cpsPolynomialDualCoeff W j)) n x) *
      conductorScaledCompletionKernelLog C μs
        (multiplicativeHeight
          (reciprocalCoefficientFiber
            (fun j => (starRingEnd ℂ) (cpsPolynomialDualCoeff W j)) n x))

theorem cpsPolynomialFullPrimal3DBankReadout_eq_theta
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μs : List ℂ) {x : ℝ} (hx : 0 < x) :
    cpsPolynomialFullPrimal3DBankReadout W C μs x =
      CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
        (conductorScaledCompletionKernelLog C μs) x := by
  unfold cpsPolynomialFullPrimal3DBankReadout CarrierTheta.theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_coefficientFiber,
    multiplicativeHeight_coefficientFiber (cpsPolynomialPrimalCoeff W) n hx]

theorem cpsPolynomialFullDual3DTransformedReadout_eq_theta_one_div
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μs : List ℂ) {x : ℝ} (hx : 0 < x) :
    cpsPolynomialFullDual3DTransformedReadout W C μs x =
      CarrierTheta.theta (cpsPolynomialDualCoeff W)
        (conductorScaledCompletionKernelLog C μs) (1 / x) := by
  unfold cpsPolynomialFullDual3DTransformedReadout CarrierTheta.theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_reciprocalCoefficientFiber_conj,
    multiplicativeHeight_reciprocalCoefficientFiber _ n hx]
  simp [div_eq_mul_inv]

/-- The prescribed primal coefficient-theta bank is locally integrable on the positive carrier.
This is derived from one convergent Gamma-product Mellin weight, not included as source data. -/
theorem cpsPolynomialFullPrimalTheta_locallyIntegrableOn
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ []) :
    LocallyIntegrableOn
      (CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
        (conductorScaledCompletionKernelLog C μs)) (Ioi 0) := by
  let A : ℝ := (Fintype.card ι + W.primalExponent : ℕ)
  obtain ⟨σ, hσA, hσμ⟩ :=
    exists_weight_gt_neg_and_shifts (-(A + 1)) μs
  have hA : A + 1 < ((σ : ℂ).re) := by
    simpa using hσA
  have hμ : ∀ μ ∈ μs, 0 < (((σ : ℂ) + μ).re) := by
    intro μ hμs
    simp only [add_re, ofReal_re]
    linarith [hσμ μ hμs]
  have ha : ∀ n : ℕ, ‖cpsPolynomialPrimalCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialPrimalCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialPrimalCoeff_norm_le W n
  have hg := conductorScaledCompletionKernelLog_hasMellin
    C hC μs hne (σ : ℂ) hμ
  have htheta := CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialPrimalCoeff W) (conductorScaledCompletionKernelLog C μs)
      (σ : ℂ) 1 A hg.1 ha hA
  exact CarrierTheta.locallyIntegrableOn_of_mellinConvergent _ _ htheta.1

/-- The prescribed contragredient coefficient-theta bank is locally integrable on the positive
carrier, by the same independently chosen Gamma-product Mellin weight. -/
theorem cpsPolynomialFullDualTheta_locallyIntegrableOn
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ []) :
    LocallyIntegrableOn
      (CarrierTheta.theta (cpsPolynomialDualCoeff W)
        (conductorScaledCompletionKernelLog C μs)) (Ioi 0) := by
  let A : ℝ := (Fintype.card ι + W.dualExponent : ℕ)
  obtain ⟨σ, hσA, hσμ⟩ :=
    exists_weight_gt_neg_and_shifts (-(A + 1)) μs
  have hA : A + 1 < ((σ : ℂ).re) := by
    simpa using hσA
  have hμ : ∀ μ ∈ μs, 0 < (((σ : ℂ) + μ).re) := by
    intro μ hμs
    simp only [add_re, ofReal_re]
    linarith [hσμ μ hμs]
  have ha : ∀ n : ℕ, ‖cpsPolynomialDualCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialDualCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialDualCoeff_norm_le W n
  have hg := conductorScaledCompletionKernelLog_hasMellin
    C hC μs hne (σ : ℂ) hμ
  have htheta := CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialDualCoeff W) (conductorScaledCompletionKernelLog C μs)
      (σ : ℂ) 1 A hg.1 ha hA
  exact CarrierTheta.locallyIntegrableOn_of_mellinConvergent _ _ htheta.1

/-- The literal primal 3D bank projection inherits local integrability from its exact positive-axis
coefficient-theta readout. -/
theorem cpsPolynomialFullPrimal3DBankReadout_locallyIntegrableOn
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ []) :
    LocallyIntegrableOn (cpsPolynomialFullPrimal3DBankReadout W C μs) (Ioi 0) := by
  apply LocallyIntegrableOn.congr _
    (cpsPolynomialFullPrimalTheta_locallyIntegrableOn W C hC μs hne)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (cpsPolynomialFullPrimal3DBankReadout_eq_theta W C μs hx).symm

/-- After reciprocal-height transformation, the literal dual 3D bank projection is exactly the
locally integrable contragredient coefficient-theta bank on the positive carrier. -/
theorem cpsPolynomialFullDual3DReflectedReadout_locallyIntegrableOn
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ []) :
    LocallyIntegrableOn
      (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x))
      (Ioi 0) := by
  apply LocallyIntegrableOn.congr _
    (cpsPolynomialFullDualTheta_locallyIntegrableOn W C hC μs hne)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := Set.mem_Ioi.mp hx
  rw [cpsPolynomialFullDual3DTransformedReadout_eq_theta_one_div W C μs
    (one_div_pos.mpr hxpos)]
  simp

/-- The literal prescribed primal 3D bank decreases faster than every real power at positive
infinity.  Polynomial coefficient growth is absorbed by the rapid Gamma-product kernel. -/
theorem cpsPolynomialFullPrimal3DBankReadout_rapid
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) :
    ∀ q : ℝ, cpsPolynomialFullPrimal3DBankReadout W C μs =O[atTop]
      (fun x : ℝ => x ^ q) := by
  let A : ℝ := (Fintype.card ι + W.primalExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialPrimalCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialPrimalCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialPrimalCoeff_norm_le W n
  have htheta := CarrierTheta.theta_rapid_of_polynomial_of_kernel_rapid
    (cpsPolynomialPrimalCoeff W) (conductorScaledCompletionKernelLog C μs)
      1 A zero_le_one ha (conductorScaledCompletionKernelLog_rapid C hC μs)
  intro q
  have heq :
      CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
          (conductorScaledCompletionKernelLog C μs) =ᶠ[atTop]
        cpsPolynomialFullPrimal3DBankReadout W C μs := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (cpsPolynomialFullPrimal3DBankReadout_eq_theta W C μs hx).symm
  simpa using (htheta q).congr' heq Filter.EventuallyEq.rfl

/-- The reciprocal-height transformed prescribed dual 3D bank is rapidly decreasing at positive
infinity, because it is exactly the contragredient coefficient theta on that ray. -/
theorem cpsPolynomialFullDual3DReflectedReadout_rapid
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) :
    ∀ q : ℝ,
      (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x))
        =O[atTop] (fun x : ℝ => x ^ q) := by
  let A : ℝ := (Fintype.card ι + W.dualExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialDualCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialDualCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialDualCoeff_norm_le W n
  have htheta := CarrierTheta.theta_rapid_of_polynomial_of_kernel_rapid
    (cpsPolynomialDualCoeff W) (conductorScaledCompletionKernelLog C μs)
      1 A zero_le_one ha (conductorScaledCompletionKernelLog_rapid C hC μs)
  intro q
  have heq :
      CarrierTheta.theta (cpsPolynomialDualCoeff W)
          (conductorScaledCompletionKernelLog C μs) =ᶠ[atTop]
        (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [cpsPolynomialFullDual3DTransformedReadout_eq_theta_one_div W C μs
      (one_div_pos.mpr hx)]
    simp
  simpa using (htheta q).congr' heq Filter.EventuallyEq.rfl

noncomputable def cpsPolynomialFullPrimalCompletedReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μs : List ℂ) (s : ℂ) : ℂ :=
  (C : ℂ) ^ s * (μs.map fun μ => Complex.Gammaℂ (s + μ)).prod *
    CarrierTheta.dirichlet (cpsPolynomialPrimalCoeff W) s

noncomputable def cpsPolynomialFullDualCompletedReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μs : List ℂ) (s : ℂ) : ℂ :=
  (C : ℂ) ^ s * (μs.map fun μ => Complex.Gammaℂ (s + μ)).prod *
    CarrierTheta.dirichlet (cpsPolynomialDualCoeff W) s

theorem cpsPolynomialFullPrimal_initialIdentification
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hμ : ∀ μ ∈ μs, 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin
        (CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
          (conductorScaledCompletionKernelLog C μs)) s =
      cpsPolynomialFullPrimalCompletedReadout W C μs s := by
  let A : ℝ := (Fintype.card ι + W.primalExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialPrimalCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialPrimalCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialPrimalCoeff_norm_le W n
  have hg := conductorScaledCompletionKernelLog_hasMellin C hC μs hne s hμ
  have h := CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialPrimalCoeff W) (conductorScaledCompletionKernelLog C μs)
      s 1 A hg.1 ha (by simpa [A] using hs)
  rw [h.2, hg.2]
  unfold cpsPolynomialFullPrimalCompletedReadout
  ring

theorem cpsPolynomialFullDual_initialIdentification
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hμ : ∀ μ ∈ μs, 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.dualExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin
        (CarrierTheta.theta (cpsPolynomialDualCoeff W)
          (conductorScaledCompletionKernelLog C μs)) s =
      cpsPolynomialFullDualCompletedReadout W C μs s := by
  let A : ℝ := (Fintype.card ι + W.dualExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialDualCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialDualCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialDualCoeff_norm_le W n
  have hg := conductorScaledCompletionKernelLog_hasMellin C hC μs hne s hμ
  have h := CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialDualCoeff W) (conductorScaledCompletionKernelLog C μs)
      s 1 A hg.1 ha (by simpa [A] using hs)
  rw [h.2, hg.2]
  unfold cpsPolynomialFullDualCompletedReadout
  ring

theorem cpsPolynomialFullPrimal3DBankReadout_mellin_eq_theta
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μs : List ℂ) (s : ℂ) :
    mellin (cpsPolynomialFullPrimal3DBankReadout W C μs) s =
      mellin (CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
        (conductorScaledCompletionKernelLog C μs)) s := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [cpsPolynomialFullPrimal3DBankReadout_eq_theta W C μs (Set.mem_Ioi.mp hx)]

/-- Complete fixed Gamma-product identification from the 3D CPS bank itself. -/
theorem cpsPolynomialFullPrimal3D_initialIdentification
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hμ : ∀ μ ∈ μs, 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin (cpsPolynomialFullPrimal3DBankReadout W C μs) s =
      cpsPolynomialFullPrimalCompletedReadout W C μs s := by
  rw [cpsPolynomialFullPrimal3DBankReadout_mellin_eq_theta W C μs s]
  exact cpsPolynomialFullPrimal_initialIdentification W C hC μs hne s hμ hs

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullPrimal3DBankReadout_eq_theta
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullDual3DTransformedReadout_eq_theta_one_div
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullPrimalTheta_locallyIntegrableOn
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullDualTheta_locallyIntegrableOn
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullPrimal3DBankReadout_locallyIntegrableOn
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullDual3DReflectedReadout_locallyIntegrableOn
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullPrimal3DBankReadout_rapid
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullDual3DReflectedReadout_rapid
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullPrimal_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullDual_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullPrimal3D_initialIdentification
