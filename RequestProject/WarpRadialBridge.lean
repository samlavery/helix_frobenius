import RequestProject.WarpNoResidue
import RequestProject.RadialCellBalance

/-!
The local pole cancellation and the radial window ledger use different residues.
This file connects them by retaining the residues of the actual warp correction.
No definition of the seat, crossing ledger, or radial log-mass is changed.
-/

set_option autoImplicit false

open Complex Filter Topology MeasureTheory Set
open scoped BigOperators
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.ResidueJump
open CriticalLinePhasor.DVP CriticalLinePhasor.CarrierHeadFiniteFiber

namespace CriticalLinePhasor.WarpNoResidue

/-- The pole coefficient of the correction already present in `warpedSeat`. -/
noncomputable def warpCorrectionResidue (L : ℝ) (ρ : ℂ) : ℂ :=
  limUnder (𝓝[≠] ρ) (fun s => (s - ρ) *
    (warpedSeat L ρ s - logDeriv ZD.riemannXi s))

/-- The correction retains minus the full analytic multiplicity. -/
theorem warpCorrectionResidue_eq {L : ℝ} (hL : L ≠ 0) (ρ : ℂ) :
    warpCorrectionResidue L ρ = -(ZD.xiOrderNat ρ : ℂ) := by
  have h := (kernel_residue hL ρ).const_mul (ZD.xiOrderNat ρ : ℂ)
  have ht : Tendsto (fun s => (s - ρ) *
      (warpedSeat L ρ s - logDeriv ZD.riemannXi s))
      (𝓝[≠] ρ) (𝓝 (-(ZD.xiOrderNat ρ : ℂ))) := by
    convert h using 1 <;> first | (ext s; simp [warpedSeat]; ring) | simp
  exact ht.limUnder_eq

/-- The full seat's cancelled pole and the correction's retained mass are both exact. -/
theorem local_seat_and_correction {L : ℝ} (hL : L ≠ 0) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) :
    limUnder (𝓝[≠] ρ) (fun s => (s - ρ) * warpedSeat L ρ s) = 0 ∧
      warpCorrectionResidue L ρ = -(ZD.xiOrderNat ρ : ℂ) :=
  ⟨(warpedSeat_no_residue hL hρ).limUnder_eq, warpCorrectionResidue_eq hL ρ⟩

/-- Summing the actual correction residues over the off-line strip window gives its ledger. -/
theorem sum_offLine_warpCorrectionResidue {L : ℝ} (hL : L ≠ 0) (T : ℝ) :
    (∑ ρ ∈ (stripZeroFinset T).filter (fun ρ => ρ.re ≠ 1 / 2),
      (warpCorrectionResidue L ρ).re) = -(offLineStripZeroCountMult T : ℝ) := by
  classical
  simp [warpCorrectionResidue_eq hL, offLineStripZeroCountMult, Nat.cast_sum,
    Finset.sum_neg_distrib]

/-- The exact connection to the existing radial residue, including every correction mass. -/
theorem radialResidue_eq_integrated_warpCorrections {L : ℝ} (hL : L ≠ 0)
    {a b : ℝ} (ha : GoodHeight a) (hb : GoodHeight b) (hab : a ≤ b) :
    radialResidue a b = Real.pi * ∫ t in a..b,
      ∑ ρ ∈ (stripZeroFinset t).filter (fun ρ => ρ.re ≠ 1 / 2),
        (warpCorrectionResidue L ρ).re := by
  simp_rw [sum_offLine_warpCorrectionResidue hL]
  rw [intervalIntegral.integral_neg, mul_neg]
  exact radialResidue_eq_neg_defect ha hb hab

/-- The carrier supplies a nonzero front parameter at every nonnegative height. -/
theorem carrier_front_ne_zero {y : ℝ} (hy : 0 ≤ y) :
    Real.log (physicalHead y) ≠ 0 := by
  have h9 := physicalHead_lower y
  have he : 1 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hgt : 1 < physicalHead y := by nlinarith [Real.exp_pos y]
  exact (Real.log_pos hgt).ne'

/-- The same bridge uses the carrier's own varying head inside the height integral. -/
theorem radialResidue_eq_integrated_carrierCorrections
    {a b : ℝ} (ha : GoodHeight a) (hb : GoodHeight b) (hab : a ≤ b) :
    radialResidue a b = Real.pi * ∫ t in a..b,
      ∑ ρ ∈ (stripZeroFinset t).filter (fun ρ => ρ.re ≠ 1 / 2),
        (warpCorrectionResidue (Real.log (physicalHead t)) ρ).re := by
  rw [radialResidue_eq_neg_defect ha hb hab]
  have hi : (∫ t in a..b,
      ∑ ρ ∈ (stripZeroFinset t).filter (fun ρ => ρ.re ≠ 1 / 2),
        (warpCorrectionResidue (Real.log (physicalHead t)) ρ).re) =
      ∫ t in a..b, -(offLineStripZeroCountMult t : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hat : a ≤ t := (uIcc_of_le hab ▸ ht).1
    exact sum_offLine_warpCorrectionResidue (carrier_front_ne_zero (ha.1.le.trans hat)) t
  rw [hi, intervalIntegral.integral_neg, mul_neg]

end CriticalLinePhasor.WarpNoResidue

#print axioms CriticalLinePhasor.WarpNoResidue.warpCorrectionResidue_eq
#print axioms CriticalLinePhasor.WarpNoResidue.local_seat_and_correction
#print axioms CriticalLinePhasor.WarpNoResidue.radialResidue_eq_integrated_warpCorrections
#print axioms CriticalLinePhasor.WarpNoResidue.radialResidue_eq_integrated_carrierCorrections
