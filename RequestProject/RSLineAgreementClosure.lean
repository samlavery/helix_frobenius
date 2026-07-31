import RequestProject.CPSCompletedVerticalIntegrable
import RequestProject.CPSWeakProfileCoupling3D
import RequestProject.RSPairInterface
import RequestProject.RSAveragedContinuity

/-!
# Line agreement closes the r = 2 house coupling

Two tiers, both driven by the same 3D fact: the inverse-Mellin reconstruction of a bank
readout reads the transform only along one vertical line of the chart.

* **Tier 1** (`eqOn_pos_of_mellin_eqOn_line`) — Mellin uniqueness on the positive ray from
  agreement of the two transforms on the single line `Re s = σ`.  This is
  `eqOn_pos_of_mellin_eq` (CPSMellinBasicIdentity) with the plane-wide transform equality
  weakened to its σ-line values: `mellinInv_mellin_eq` consumes only those values, and the
  second function's vertical integrability transfers along the line by integrability
  congruence.

* **Tier 2** (`rsCoupling_of_lineAgreement`) — the r = 2 house-coupling closure engine: the
  identification layer of the rung reduced to one vertical-line agreement per side.  Given
  the σ-line agreement of the prescribed bank readouts with the Petersson-averaged lattice
  profile `θ̄_f − ‖f‖²` (`hlineP`, `hlineD`), the two pointwise readout identifications of
  `rsAveragedProfileCoupling` are recovered by Tier 1, and the weak coupling
  `WeakBankThetaProfileCoupling3D` is inhabited.  Bank-side side conditions are the compiled
  discharge layer (`cpsPolynomialFullPrimal3DBankReadout_mellinConvergent`, `_continuousAt`,
  `mellinPrimal_verticalIntegrable`); the dual side's vertical integrability transfers along
  the line from the compiled primal one.  The line agreement itself — Γ-chart registration
  and coefficient identification — is not proven in this file.  The profile-side Mellin
  convergence and positive-ray continuity and the dual-side Mellin convergence are inputs
  (`hprofConv`, `hprofCont`, `hdualConv`): the planned supplier files `RSPairInterface.lean`
  and `RSAveragedContinuity.lean` are not present in `RequestProject/` at the time of
  writing (checked by directory listing), so those regularity facts are not proven in this
  file either.

`Re s = σ` is the chart's readout line; every input lives at the Mellin-line or regularity
level — none restates the pointwise identification being concluded.
-/

open Complex MeasureTheory Set

namespace CriticalLinePhasor.ThreeDConverse

/-- **Line-restricted Mellin uniqueness on the positive ray.**  Two readouts agree at every
positive height at which both are continuous, as soon as their Mellin transforms agree on
the single vertical line `Re s = σ`: the inverse-Mellin reconstruction
(`mellinInv_mellin_eq`) reads the transform only along that line, and `g`'s vertical
integrability transfers from `f`'s along the line by integrability congruence.
Line-restricted variant of `eqOn_pos_of_mellin_eq`. -/
theorem eqOn_pos_of_mellin_eqOn_line {f g : ℝ → ℂ} {σ : ℝ}
    (hfC : MellinConvergent f σ) (hgC : MellinConvergent g σ)
    (hV : VerticalIntegrable (mellin f) σ volume)
    (hline : ∀ τ : ℝ, mellin f ((σ : ℂ) + (τ : ℂ) * Complex.I)
      = mellin g ((σ : ℂ) + (τ : ℂ) * Complex.I))
    {x : ℝ} (hx : 0 < x) (hfc : ContinuousAt f x) (hgc : ContinuousAt g x) :
    f x = g x := by
  have hgV : VerticalIntegrable (mellin g) σ volume := by
    unfold Complex.VerticalIntegrable at hV ⊢
    exact hV.congr (Filter.Eventually.of_forall fun τ => hline τ)
  have hinv : mellinInv σ (mellin f) x = mellinInv σ (mellin g) x := by
    unfold mellinInv
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun τ => by simp only [hline τ])
  calc f x = mellinInv σ (mellin f) x := (mellinInv_mellin_eq σ f hx hfC hV hfc).symm
    _ = mellinInv σ (mellin g) x := hinv
    _ = g x := mellinInv_mellin_eq σ g hx hgC hgV hgc

end CriticalLinePhasor.ThreeDConverse

namespace CriticalLinePhasor.GlobalHelix

open CriticalLinePhasor.CarrierTheta

/-- The transformed dual bank readout at the inverted height is continuous at every positive
height: the M-test continuity of the dual theta (`theta_continuousAt_of_polynomial`)
transported through the compiled chart identification
(`cpsPolynomialFullDual3DTransformedReadout_eq_theta_one_div`). -/
theorem cpsPolynomialFullDual3DTransformedReadout_one_div_continuousAt
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ)
    (hgc : ContinuousOn (conductorScaledCompletionKernelLog C μs) (Ioi 0))
    {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (fun x : ℝ =>
      cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)) x₀ := by
  let A : ℝ := (Fintype.card ι + W.dualExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialDualCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialDualCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialDualCoeff_norm_le W n
  have htheta := CarrierTheta.theta_continuousAt_of_polynomial
    (cpsPolynomialDualCoeff W) (conductorScaledCompletionKernelLog C μs)
    1 A one_pos.le (by positivity) ha hgc
    (conductorScaledCompletionKernelLog_rapid C hC μs (-(A + 2))) hx₀
  refine htheta.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hx₀] with x hx
  rw [cpsPolynomialFullDual3DTransformedReadout_eq_theta_one_div W C μs
    (one_div_pos.mpr hx), one_div_one_div]

end CriticalLinePhasor.GlobalHelix

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.HeckeSupBound
open CriticalLinePhasor.ThreeDConverse CriticalLinePhasor.CarrierTheta
open UpperHalfPlane ModularGroup Filter
open scoped Real MatrixGroups Topology

/-- **The r = 2 house-coupling closure engine.**  The identification layer of the r = 2
rung reduced to one vertical-line agreement per side: given the σ-line agreement of the
primal bank readout (`hlineP`) and of the transformed dual readout (`hlineD`) with the
Petersson-averaged lattice profile `θ̄_f − ‖f‖²`, both pointwise readout identifications of
`rsAveragedProfileCoupling` are recovered by `eqOn_pos_of_mellin_eqOn_line`, inhabiting the
weak coupling.  Bank-side Mellin convergence, continuity, and vertical integrability are
the compiled discharge layer; the dual side's vertical integrability transfers along the
line from the primal one, so every hypothesis lives at the Mellin-line or regularity level
and none restates the pointwise identification.  The line agreement itself (Γ-chart
registration + coefficient identification) is not proven in this file; the profile-side
Mellin convergence and continuity (`hprofConv`, `hprofCont`) and the dual-side Mellin
convergence (`hdualConv`) are likewise inputs — their planned suppliers
`RSPairInterface.lean` / `RSAveragedContinuity.lean` are not present in `RequestProject/`
at the time of writing. -/
noncomputable def rsCoupling_of_lineAgreement
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ [])
    (hgc : ContinuousOn (conductorScaledCompletionKernelLog C μs) (Ioi 0))
    (σ : ℝ) (hσμ : ∀ μ ∈ μs, 0 < ((σ : ℂ) + μ).re)
    (hσ : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < σ)
    {k : ℤ} (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k)
    (hdualConv : MellinConvergent
      (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)) σ)
    (hlineP : ∀ τ : ℝ,
      mellin (cpsPolynomialFullPrimal3DBankReadout W C μs)
          ((σ : ℂ) + (τ : ℂ) * Complex.I)
        = mellin (fun t : ℝ => averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ))
            ((σ : ℂ) + (τ : ℂ) * Complex.I))
    (hlineD : ∀ τ : ℝ,
      mellin (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x))
          ((σ : ℂ) + (τ : ℂ) * Complex.I)
        = mellin (fun t : ℝ => averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ))
            ((σ : ℂ) + (τ : ℂ) * Complex.I)) :
    WeakBankThetaProfileCoupling3D W C μs := by
  have hbankConv : MellinConvergent (cpsPolynomialFullPrimal3DBankReadout W C μs) σ :=
    cpsPolynomialFullPrimal3DBankReadout_mellinConvergent W C hC μs hne (σ : ℂ) hσμ
      (by simpa using hσ)
  have hbankV : VerticalIntegrable
      (mellin (cpsPolynomialFullPrimal3DBankReadout W C μs)) σ volume :=
    mellinPrimal_verticalIntegrable W C hC μs hne σ hσμ hσ
  have hdualV : VerticalIntegrable
      (mellin (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)))
      σ volume := by
    unfold Complex.VerticalIntegrable at hbankV ⊢
    exact hbankV.congr (Filter.Eventually.of_forall fun τ =>
      (hlineP τ).trans (hlineD τ).symm)
  exact rsAveragedProfileCoupling W C μs f
    (fun x hx =>
      eqOn_pos_of_mellin_eqOn_line hbankConv hprofConv hbankV hlineP hx
        (cpsPolynomialFullPrimal3DBankReadout_continuousAt W C hC μs hgc hx)
        (hprofCont x hx))
    (fun x hx =>
      eqOn_pos_of_mellin_eqOn_line hdualConv hprofConv hdualV hlineD hx
        (cpsPolynomialFullDual3DTransformedReadout_one_div_continuousAt W C hC μs hgc hx)
        (hprofCont x hx))

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.ThreeDConverse.eqOn_pos_of_mellin_eqOn_line
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullDual3DTransformedReadout_one_div_continuousAt
#print axioms CriticalLinePhasor.Unfolding.rsCoupling_of_lineAgreement
