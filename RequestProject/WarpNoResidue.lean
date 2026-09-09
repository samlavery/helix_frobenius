import RequestProject.TruncatedExplicitFormula
import RequestProject.SeatingRDefect
import RequestProject.CarrierHeadFiniteFiber

/-!
# Primes fuel S, S fuels the warp, the warp on the fiber with the scaling of the carrier gives no residue at
# vanishing points (ledger 689)

* **Primes fuel S** — `primes_fuel_seat`: at a growth front `x = e^L` the seat `ξ′/ξ`, warped at every zero by the
  front kernel `K_L`, equals the prime side plus the arch: the compiled truncated explicit formula.
* **S fuels the warp** — the warp is the front kernel `K_L(ρ − s₀) = G_L(ρ − s₀)/(ρ − s₀)` with `G_L(0) = 1`
  (`cubicG_zero`); `kernel_residue`: the warp carries residue `−1` at each vanishing point.
* **No residue at vanishing points** — `warpedSeat_no_residue`: at every zero `ρ` and every front `L ≠ 0`, the warped
  seat `ξ′/ξ(s₀) + m_ρ K_L(ρ − s₀)` has residue `0` at `s₀ = ρ`: the seat's pole (residue `m_ρ`, `xi_logDeriv_residue`)
  is cancelled exactly by the warp.
* **The scaling of the carrier** — `warpedSeat_no_residue_at_carrier_head`: the same at the front the carrier itself
  supplies, `L = log W(y)` (`physicalHead`), for every ordinate `y`; hence at every front and in the limit.
-/

open Complex Filter Topology
open scoped Real
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.SeatingLedger
open CriticalLinePhasor.CarrierHeadFiniteFiber

namespace CriticalLinePhasor.WarpNoResidue

/-- **Primes fuel S**: the front-warped seat equals the prime side plus the arch (the compiled truncated explicit
formula, restated under this name). -/
theorem primes_fuel_seat {L : ℝ} (hL : 0 < L) {s₀ : ℂ} (hs₀ : s₀ ∉ ZD.NontrivialZeros) {a b : ℝ}
    (ha : a < 0) (hb : 1 < b) (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) :
    logDeriv ZD.riemannXi s₀ + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * cubicKernel L (ρ.val - s₀)
      = (1 / (2 * π)) * ((∫ t : ℝ, cubicKernel L ((b : ℂ) + t * I - s₀) * weilArch ((b : ℂ) + t * I))
          + (∫ t : ℝ, cubicKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I))))
        - ∑' n : ℕ, (cubicProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n :=
  truncated_explicit_formula_cubic hL hs₀ ha hb hs₀a hs₀b

/-- The seat warped by the front kernel at the vanishing point `ρ`. -/
noncomputable def warpedSeat (L : ℝ) (ρ s₀ : ℂ) : ℂ :=
  logDeriv ZD.riemannXi s₀ + (ZD.xiOrderNat ρ : ℂ) * cubicKernel L (ρ - s₀)

/-- **S fuels the warp**: the front kernel carries residue `−1` at the vanishing point. -/
theorem kernel_residue {L : ℝ} (hL : L ≠ 0) (ρ : ℂ) :
    Tendsto (fun s₀ : ℂ => (s₀ - ρ) * cubicKernel L (ρ - s₀)) (𝓝[≠] ρ) (𝓝 (-1)) := by
  have hcont : Tendsto (fun s₀ : ℂ => -cubicG L (ρ - s₀)) (𝓝[≠] ρ) (𝓝 (-1)) := by
    have h1 : Tendsto (fun s₀ : ℂ => -cubicG L (ρ - s₀)) (𝓝 ρ) (𝓝 (-cubicG L (ρ - ρ))) := by
      have hc : Continuous (cubicG L) := (cubicG_differentiable L).continuous
      exact ((hc.comp (continuous_const.sub continuous_id)).neg).tendsto ρ
    rw [sub_self, cubicG_zero hL] at h1
    exact tendsto_nhdsWithin_of_tendsto_nhds h1
  refine hcont.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s₀ hs₀
  have hne : ρ - s₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hs₀)
  unfold cubicKernel
  field_simp
  ring

/-- **No residue at vanishing points**: the seat's residue `m_ρ` is cancelled by the warp's `−m_ρ`. -/
theorem warpedSeat_no_residue {L : ℝ} (hL : L ≠ 0) {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    Tendsto (fun s₀ : ℂ => (s₀ - ρ) * warpedSeat L ρ s₀) (𝓝[≠] ρ) (𝓝 0) := by
  have h1 := xi_logDeriv_residue hρ
  have h2 := (kernel_residue hL ρ).const_mul ((ZD.xiOrderNat ρ : ℂ))
  have h := h1.add h2
  rw [show ((ZD.xiOrderNat ρ : ℂ)) + (ZD.xiOrderNat ρ : ℂ) * (-1) = 0 by ring] at h
  refine h.congr' (Eventually.of_forall fun s₀ => ?_)
  unfold warpedSeat
  ring

/-- **The scaling of the carrier**: the front is the carrier's own head `W(y)`; the warped seat has no residue at any
vanishing point at every ordinate `y`. -/
theorem warpedSeat_no_residue_at_carrier_head {y : ℝ} (hy : 0 ≤ y) {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    Tendsto (fun s₀ : ℂ => (s₀ - ρ) * warpedSeat (Real.log (physicalHead y)) ρ s₀) (𝓝[≠] ρ) (𝓝 0) := by
  apply warpedSeat_no_residue _ hρ
  have h9 : 9 * Real.exp y ^ 2 ≤ physicalHead y := physicalHead_lower y
  have he : 1 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hgt : 1 < physicalHead y := by nlinarith [Real.exp_pos y]
  exact (Real.log_pos hgt).ne'

end CriticalLinePhasor.WarpNoResidue

#print axioms CriticalLinePhasor.WarpNoResidue.primes_fuel_seat
#print axioms CriticalLinePhasor.WarpNoResidue.kernel_residue
#print axioms CriticalLinePhasor.WarpNoResidue.warpedSeat_no_residue
#print axioms CriticalLinePhasor.WarpNoResidue.warpedSeat_no_residue_at_carrier_head
