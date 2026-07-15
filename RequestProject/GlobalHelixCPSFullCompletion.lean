import RequestProject.GlobalHelixCPSFixedCompletion
import RequestProject.GlobalHelixCompletionGammaProduct

/-!
# Full fixed completion of polynomial CPS Satake banks

This file combines the actual primal/contragredient Euler coefficients with a nonempty prescribed
archimedean shift list and a positive conductor scale.  The banks are defined on the 3D carrier;
their projections are coefficient theta functions, whose Mellin transforms are exactly the full
Gamma-completed Dirichlet readouts in the initial half-plane.
-/

open Complex Set MeasureTheory

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
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullPrimal_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullDual_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullPrimal3D_initialIdentification
