import RequestProject.FocalHeightPencil
import RequestProject.CarrierHelixGenerator

/-!
# The physical height law of the scaled carrier (ledger 1219)

On the scaled carrier `(p, r) = (1, 3)` the helix is `k ↦ (3k cos 2πk, 3k sin 2πk, k)`, so a site's
physical height is exactly its cylindrical radius divided by `3`.

* `carrierSiteHeight_eq`: `h_n = R_n / 3`, with `h_n = carrierSiteHeight n`, `R_n = carrierRadius 1 3 n`.
* `carrierSiteHeight_sq_div_tendsto`: `h_n² / n → 1/9` (from the area law `R_n²/n → 1`).
* `driftFree_mul_height`: the drift-free amplitude `1/R_n` times the physical height is exactly `1/3`.
* `warp_eq_height_power`: `n^{−δ} = (3h_n)^{−2δ} · (R_n²/n)^δ`; the Mellin warp is a power of physical
  height up to a factor that tends to `1`.
* `driftFreeBank`, `driftFree_momentA`, `driftFree_momentB`: on the drift-free bank the height row of the
  focal-height pencil is `1/3` of the phase-only channels.
-/

open Complex Filter Topology Finset

noncomputable section

namespace CriticalLinePhasor.PhysicalHeight

open CriticalLinePhasor CriticalLinePhasor.Geometry CriticalLinePhasor.HarmonicCell
open CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.FocalHeightPencil

/-- **Physical height is radius over three** on the scaled carrier. -/
theorem carrierSiteHeight_eq (n : ℕ) : carrierSiteHeight n = carrierRadius 1 3 n / 3 := by
  have hR : carrierRadius 1 3 n = 3 * windParameter 1 3 (spinAngle n) :=
    windIntegerSite_cyl_radius 1 3 (by norm_num) n
  rw [hR, carrierSiteHeight, windIntegerSite, helix]
  ring

/-- **The height law**: `h_n² / n → 1/9`. -/
theorem carrierSiteHeight_sq_div_tendsto :
    Tendsto (fun n : ℕ => carrierSiteHeight n ^ 2 / (n : ℝ)) atTop (𝓝 (1 / 9)) := by
  have h := carrierRadius_sq_div_tendsto 1 3 (by norm_num)
  have hc : (3 : ℝ) * (Real.pi / 3) / Real.pi = 1 := by field_simp
  rw [hc] at h
  have h9 := h.div_const 9
  rw [show (1 : ℝ) / 9 = 1 / 9 from rfl] at h9
  refine h9.congr' (Eventually.of_forall fun n => ?_)
  simp only [carrierSiteHeight_eq]
  ring

/-- **The drift-free amplitude times the physical height is `1/3`.** -/
theorem driftFree_mul_height {n : ℕ} (hn : 1 ≤ n) :
    (carrierRadius 1 3 n)⁻¹ * carrierSiteHeight n = 1 / 3 := by
  have hR : 0 < carrierRadius 1 3 n := CarrierHelixGenerator.carrierRadius_pos 1 3 (by norm_num) hn
  rw [carrierSiteHeight_eq]
  field_simp

/-- **The Mellin warp as a power of physical height**: `n^{−δ} = (3h_n)^{−2δ}·(R_n²/n)^δ`. -/
theorem warp_eq_height_power {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) :
    (n : ℝ) ^ (-δ) = (3 * carrierSiteHeight n) ^ (-2 * δ) * (carrierRadius 1 3 n ^ 2 / n) ^ δ := by
  have hR : 0 < carrierRadius 1 3 n := CarrierHelixGenerator.carrierRadius_pos 1 3 (by norm_num) hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [carrierSiteHeight_eq, show 3 * (carrierRadius 1 3 n / 3) = carrierRadius 1 3 n by ring,
    Real.div_rpow (by positivity) hnp.le, show (-2 * δ) = 2 * (-δ) by ring, Real.rpow_mul hR.le,
    show carrierRadius 1 3 n ^ (2 : ℝ) = carrierRadius 1 3 n ^ (2 : ℕ) by norm_cast,
    Real.rpow_neg (x := carrierRadius 1 3 n ^ 2) (by positivity), Real.rpow_neg hnp.le]
  have h1 : 0 < (carrierRadius 1 3 n ^ 2) ^ δ := by positivity
  field_simp

/-- The drift-free bank: amplitude `1/R_n`, Mellin phase, cutoff `N`. -/
def driftFreeBank (N : ℕ) (hN : 1 ≤ N) : FocalBank where
  amplitude n := (carrierRadius 1 3 n)⁻¹
  phase := carrierPhase
  cutoff := N
  cutoff_pos := hN
  amplitude_one_pos := inv_pos.mpr (CarrierHelixGenerator.carrierRadius_pos 1 3 (by norm_num) le_rfl)
  amplitude_nonneg n := inv_nonneg.mpr (carrierRadius_nonneg 1 3 n)

/-- **Unsigned height row of the drift-free bank**: `A_h = (1/3)·Σ_{n ≤ N} ‖χ(n)‖`. -/
theorem driftFree_momentA {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) (hN : 1 ≤ N) :
    momentA χ (driftFreeBank N hN) carrierSiteHeight =
      (1 / 3) * ∑ n ∈ Icc 1 N, ‖χ (n : ZMod q)‖ := by
  unfold momentA finiteA
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  show ‖χ (n : ZMod q)‖ * ((carrierRadius 1 3 n)⁻¹ * carrierSiteHeight n) = _
  rw [driftFree_mul_height hn1]
  ring

/-- **Signed height row of the drift-free bank**: `B_h = (1/3)·Σ_{n ≤ N} χ(n)·e^{iφ_y(n)}`, the
phase-only channel. -/
theorem driftFree_momentB {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) (hN : 1 ≤ N)
    (y : ℝ) :
    momentB χ (driftFreeBank N hN) carrierSiteHeight y =
      (1 / 3 : ℂ) * ∑ n ∈ Icc 1 N, χ (n : ZMod q) * Complex.exp ((carrierPhase y n : ℂ) * I) := by
  unfold momentB finiteB
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  show χ (n : ZMod q) * (((carrierRadius 1 3 n)⁻¹ * carrierSiteHeight n : ℝ) : ℂ) *
      Complex.exp ((carrierPhase y n : ℂ) * I) = _
  rw [driftFree_mul_height hn1]
  push_cast
  ring

end CriticalLinePhasor.PhysicalHeight

end

#print axioms CriticalLinePhasor.PhysicalHeight.carrierSiteHeight_eq
#print axioms CriticalLinePhasor.PhysicalHeight.carrierSiteHeight_sq_div_tendsto
#print axioms CriticalLinePhasor.PhysicalHeight.driftFree_mul_height
#print axioms CriticalLinePhasor.PhysicalHeight.warp_eq_height_power
#print axioms CriticalLinePhasor.PhysicalHeight.driftFree_momentA
#print axioms CriticalLinePhasor.PhysicalHeight.driftFree_momentB
