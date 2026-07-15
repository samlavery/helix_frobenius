import RequestProject.GlobalHelixCPSPolynomialDualPair
import RequestProject.GlobalHelixFixedBankReflection
import RequestProject.GlobalHelixFixedCompletionMellin

/-!
# CPS Satake banks with a prescribed archimedean completion

The primal and contragredient coefficient banks are placed on the three-dimensional carrier first.
The completion clock is fixed by its archimedean shift and is independent of both banks.  Projection
then gives the corresponding coefficient theta, and its Mellin transform is the Dirichlet readout
times the prescribed Deligne Gamma factor in the initial half-plane.
-/

open Complex Set MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection

/-- The primal polynomial CPS bank with one prescribed complex-place completion clock. -/
noncomputable def cpsPolynomialFixedPrimal3DBankReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (μ : ℂ) (x : ℝ) : ℂ :=
  fixedPrimalBankReadout [μ] (cpsPolynomialPrimalCoeff W) x

/-- The sheared anti-helix bank carrying the actual contragredient coefficients. -/
noncomputable def cpsPolynomialFixedDual3DTransformedReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (μ : ℂ) (x : ℝ) : ℂ :=
  fixedTransformedDualBankReadout [μ]
    (fun n => (starRingEnd ℂ) (cpsPolynomialDualCoeff W n)) x

/-- Projection of the primal 3D bank is its fixed-completion theta. -/
theorem cpsPolynomialFixedPrimal3DBankReadout_eq_theta
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (μ : ℂ) {x : ℝ} (hx : 0 < x) :
    cpsPolynomialFixedPrimal3DBankReadout W μ x =
      CarrierTheta.theta (cpsPolynomialPrimalCoeff W) (completionKernel [μ]) x := by
  exact fixedPrimalBankReadout_eq_theta [μ] (cpsPolynomialPrimalCoeff W) hx

/-- Projection of the transformed dual 3D bank is the contragredient theta at reciprocal height. -/
theorem cpsPolynomialFixedDual3DTransformedReadout_eq_theta_one_div
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (μ : ℂ) {x : ℝ} (hx : 0 < x) :
    cpsPolynomialFixedDual3DTransformedReadout W μ x =
      CarrierTheta.theta (cpsPolynomialDualCoeff W) (completionKernel [μ]) (1 / x) := by
  exact fixedTransformedConjugateDualBankReadout_eq_theta_one_div
    [μ] (cpsPolynomialDualCoeff W) hx

/-- The primal fixed clock reads exactly `Gamma_C(s+μ)` times the CPS Dirichlet series. -/
theorem cpsPolynomialPrimal_fixedGamma_initialIdentification
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (μ s : ℂ) (hμ : 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin
        (CarrierTheta.theta (cpsPolynomialPrimalCoeff W) (completionKernel [μ])) s =
      CarrierTheta.dirichlet (cpsPolynomialPrimalCoeff W) s *
        Complex.Gammaℂ (s + μ) := by
  let A : ℝ := (Fintype.card ι + W.primalExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialPrimalCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialPrimalCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialPrimalCoeff_norm_le W n
  have hg : MellinConvergent (completionKernel [μ]) s :=
    (completionKernel_singleton_hasMellin μ s hμ).1
  have h := CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialPrimalCoeff W) (completionKernel [μ]) s 1 A hg ha
      (by simpa [A] using hs)
  rw [h.2, (completionKernel_singleton_hasMellin μ s hμ).2]

/-- The contragredient fixed clock has the same exact initial-half-plane identification. -/
theorem cpsPolynomialDual_fixedGamma_initialIdentification
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (μ s : ℂ) (hμ : 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.dualExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin
        (CarrierTheta.theta (cpsPolynomialDualCoeff W) (completionKernel [μ])) s =
      CarrierTheta.dirichlet (cpsPolynomialDualCoeff W) s *
        Complex.Gammaℂ (s + μ) := by
  let A : ℝ := (Fintype.card ι + W.dualExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialDualCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialDualCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialDualCoeff_norm_le W n
  have hg : MellinConvergent (completionKernel [μ]) s :=
    (completionKernel_singleton_hasMellin μ s hμ).1
  have h := CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialDualCoeff W) (completionKernel [μ]) s 1 A hg ha
      (by simpa [A] using hs)
  rw [h.2, (completionKernel_singleton_hasMellin μ s hμ).2]

/-- The prescribed-completion 3D odd channel for a primal/contragredient CPS pair. -/
noncomputable def cpsPolynomialFixed3DOddChannel
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (μ : ℂ) (η : ℂ) (κ : ℝ) (x : ℝ) : ℂ :=
  cpsPolynomialFixedPrimal3DBankReadout W μ x -
    (η * (x ^ κ : ℝ)) • cpsPolynomialFixedDual3DTransformedReadout W μ x

/-- Vanishing of the 3D odd channel is exactly the fixed primal/contragredient theta reflection. -/
theorem cpsPolynomialFixed3DOddChannel_eq_zero_iff_theta_reflection
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (μ : ℂ) (η : ℂ) (κ : ℝ) {x : ℝ} (hx : 0 < x) :
    cpsPolynomialFixed3DOddChannel W μ η κ x = 0 ↔
      CarrierTheta.theta (cpsPolynomialPrimalCoeff W) (completionKernel [μ]) x =
        (η * (x ^ κ : ℝ)) •
          CarrierTheta.theta (cpsPolynomialDualCoeff W) (completionKernel [μ]) (1 / x) := by
  rw [cpsPolynomialFixed3DOddChannel,
    cpsPolynomialFixedPrimal3DBankReadout_eq_theta W μ hx,
    cpsPolynomialFixedDual3DTransformedReadout_eq_theta_one_div W μ hx]
  exact sub_eq_zero

/-! ## Conductor-scaled fixed completion, still constructed in 3D first -/

/-- The primal CPS bank with the conductor scale carried by the third coordinate's clock readout. -/
noncomputable def cpsPolynomialConductorPrimal3DBankReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μ : ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor (coefficientFiber (cpsPolynomialPrimalCoeff W) n x) *
      conductorScaledGammaClockReadout C μ
        (coefficientFiber (cpsPolynomialPrimalCoeff W) n x)

/-- The conductor-scaled transformed contragredient bank on the anti-helix. -/
noncomputable def cpsPolynomialConductorDual3DTransformedReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μ : ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor
        (reciprocalCoefficientFiber
          (fun j => (starRingEnd ℂ) (cpsPolynomialDualCoeff W j)) n x) *
      conductorScaledGammaClockReadout C μ
        (reciprocalCoefficientFiber
          (fun j => (starRingEnd ℂ) (cpsPolynomialDualCoeff W j)) n x)

theorem cpsPolynomialConductorPrimal3DBankReadout_eq_theta
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μ : ℂ) {x : ℝ} (hx : 0 < x) :
    cpsPolynomialConductorPrimal3DBankReadout W C μ x =
      CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
        (conductorScaledGammaClock C μ) x := by
  unfold cpsPolynomialConductorPrimal3DBankReadout CarrierTheta.theta
    conductorScaledGammaClockReadout
  apply tsum_congr
  intro n
  rw [fiberPhasor_coefficientFiber,
    multiplicativeHeight_coefficientFiber (cpsPolynomialPrimalCoeff W) n hx]

theorem cpsPolynomialConductorDual3DTransformedReadout_eq_theta_one_div
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μ : ℂ) {x : ℝ} (hx : 0 < x) :
    cpsPolynomialConductorDual3DTransformedReadout W C μ x =
      CarrierTheta.theta (cpsPolynomialDualCoeff W)
        (conductorScaledGammaClock C μ) (1 / x) := by
  unfold cpsPolynomialConductorDual3DTransformedReadout CarrierTheta.theta
    conductorScaledGammaClockReadout
  apply tsum_congr
  intro n
  rw [fiberPhasor_reciprocalCoefficientFiber_conj,
    multiplicativeHeight_reciprocalCoefficientFiber _ n hx]
  simp [div_eq_mul_inv]

/-- The completed primal CPS Dirichlet readout with geometric conductor scale `C`. -/
noncomputable def cpsPolynomialPrimalCompletedReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μ s : ℂ) : ℂ :=
  (C : ℂ) ^ s * Complex.Gammaℂ (s + μ) *
    CarrierTheta.dirichlet (cpsPolynomialPrimalCoeff W) s

/-- The completed contragredient CPS Dirichlet readout. -/
noncomputable def cpsPolynomialDualCompletedReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μ s : ℂ) : ℂ :=
  (C : ℂ) ^ s * Complex.Gammaℂ (s + μ) *
    CarrierTheta.dirichlet (cpsPolynomialDualCoeff W) s

/-- Initial-half-plane identification of the conductor-scaled fixed theta with the completed
primal CPS Dirichlet readout. -/
theorem cpsPolynomialPrimal_conductorGamma_initialIdentification
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μ s : ℂ) (hμ : 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin
        (CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
          (conductorScaledGammaClock C μ)) s =
      cpsPolynomialPrimalCompletedReadout W C μ s := by
  let A : ℝ := (Fintype.card ι + W.primalExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialPrimalCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialPrimalCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialPrimalCoeff_norm_le W n
  have hg := conductorScaledGammaClock_mellinConvergent C hC μ s hμ
  have h := CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialPrimalCoeff W) (conductorScaledGammaClock C μ) s 1 A hg ha
      (by simpa [A] using hs)
  rw [h.2, conductorScaledGammaClock_mellin C hC μ s hμ]
  unfold cpsPolynomialPrimalCompletedReadout
  ring

/-- Initial-half-plane identification for the conductor-scaled contragredient readout. -/
theorem cpsPolynomialDual_conductorGamma_initialIdentification
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μ s : ℂ) (hμ : 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.dualExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin
        (CarrierTheta.theta (cpsPolynomialDualCoeff W)
          (conductorScaledGammaClock C μ)) s =
      cpsPolynomialDualCompletedReadout W C μ s := by
  let A : ℝ := (Fintype.card ι + W.dualExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialDualCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialDualCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialDualCoeff_norm_le W n
  have hg := conductorScaledGammaClock_mellinConvergent C hC μ s hμ
  have h := CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialDualCoeff W) (conductorScaledGammaClock C μ) s 1 A hg ha
      (by simpa [A] using hs)
  rw [h.2, conductorScaledGammaClock_mellin C hC μ s hμ]
  unfold cpsPolynomialDualCompletedReadout
  ring

/-- The primal and contragredient E5 identifications, exposed as one CPS completion payload.
This is the initial-half-plane bridge from the two coefficient banks to their prescribed
Gamma/conductor completed Dirichlet readouts. -/
theorem cpsPolynomialConductor_initialIdentification_pair
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μ s : ℂ) (hμ : 0 < (s + μ).re)
    (hsPrimal : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re)
    (hsDual : ((Fintype.card ι + W.dualExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin
        (CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
          (conductorScaledGammaClock C μ)) s =
        cpsPolynomialPrimalCompletedReadout W C μ s ∧
      mellin
        (CarrierTheta.theta (cpsPolynomialDualCoeff W)
          (conductorScaledGammaClock C μ)) s =
        cpsPolynomialDualCompletedReadout W C μ s :=
  ⟨cpsPolynomialPrimal_conductorGamma_initialIdentification
      W C hC μ s hμ hsPrimal,
    cpsPolynomialDual_conductorGamma_initialIdentification
      W C hC μ s hμ hsDual⟩

/-- Mellin projection of the 3D primal bank is the fixed theta transform. -/
theorem cpsPolynomialConductorPrimal3DBankReadout_mellin_eq_theta
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μ s : ℂ) :
    mellin (cpsPolynomialConductorPrimal3DBankReadout W C μ) s =
      mellin (CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
        (conductorScaledGammaClock C μ)) s := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [cpsPolynomialConductorPrimal3DBankReadout_eq_theta W C μ (Set.mem_Ioi.mp hx)]

/-- The full initial-half-plane CPS completion is the Mellin projection of the 3D primal bank. -/
theorem cpsPolynomialConductorPrimal3D_initialIdentification
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μ s : ℂ) (hμ : 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re) :
    mellin (cpsPolynomialConductorPrimal3DBankReadout W C μ) s =
      cpsPolynomialPrimalCompletedReadout W C μ s := by
  rw [cpsPolynomialConductorPrimal3DBankReadout_mellin_eq_theta W C μ s]
  exact cpsPolynomialPrimal_conductorGamma_initialIdentification W C hC μ s hμ hs

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFixedPrimal3DBankReadout_eq_theta
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFixedDual3DTransformedReadout_eq_theta_one_div
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialPrimal_fixedGamma_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialDual_fixedGamma_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFixed3DOddChannel_eq_zero_iff_theta_reflection
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialConductorPrimal3DBankReadout_eq_theta
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialConductorDual3DTransformedReadout_eq_theta_one_div
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialPrimal_conductorGamma_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialDual_conductorGamma_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialConductor_initialIdentification_pair
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialConductorPrimal3D_initialIdentification
