import RequestProject.GrownFiberEvolution
import RequestProject.CarrierHelixGenerator
import RequestProject.ThreeDFocalEvent

/-!
# Where the carrier's radial datum is fixed (ledger 913)

Constructor audit of the chain `Geometry.helix → arclength → windParameter → windIntegerSite →
carrierRadius → sigma_half_is_scale_critical → carrierAbscissa → carrierPoint → heat`.

* The native state type has one real parameter: `CarrierState3D p r ≃ ℝ` through the ordinate
  (`carrierState3DEquiv`).  There is no radial field.
* The configurable radial knobs of the helix, the pitch `p` and the growth rate `r`, do not move the
  balanced exponent (`scaleBalance_gauge_free`).  The exponent `½` comes from the Archimedean profile
  `radius = r·k` of `Geometry.helix` under arclength-uniform winding.
* The free variable before `carrierAbscissa` is chosen is the trial exponent `σ` of
  `CarrierScaleBalanced σ`: an amplitude law tested against the fixed radius.  Moving it by a real
  `δ` multiplies the site-scale product by `(k+1)^{−δ}` (`siteScaleProduct_add_real`), which is
  `e^{−δ·logWeight k}`, the eigenvalue of the heat semigroup at real time `δ` on the `k`-th phasor
  (`rpow_neg_eq_exp_logWeight`).  Measured in the carrier's own radius, through the helix-native
  generator `A = log R²`, the same drift is `R^{−2δ}` (`areaWarp_drift`).
* On native states the drift is zero: the site-scale product at `carrierPoint y` is the fixed
  geometric sequence `R_{k+1}/√(k+1)` at every height (`siteScaleProduct_carrierPoint`); on the heat
  orbit it is that sequence times `(k+1)^{−δ}` (`siteScaleProduct_heatOrbit`).

So the downstream heat time `δ` is a drift of the fiber's amplitude against a fixed carrier radius.
No constructor in this chain deforms the carrier radially.

No `sorry`, no `axiom`.
-/

noncomputable section
open Filter Topology

namespace CriticalLinePhasor.CarrierRadialDegree

open CriticalLinePhasor CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.GrownFiberEvolution

/-! ## 1. The native state type has one real parameter -/

/-- A native carrier state is determined by its ordinate: the state type is a copy of `ℝ`. -/
def carrierState3DEquiv (p r : ℝ) : CarrierState3D p r ≃ ℝ where
  toFun s := s.ordinate
  invFun y := carrierState3D p r y
  left_inv s := by
    obtain ⟨point, ordinate, h⟩ := s
    subst h
    rfl
  right_inv _ := rfl

/-! ## 2. The configurable radial knobs do not carry the exponent -/

/-- **Gauge-free balance.**  Two helices with growth rates `r, r' > 0` and any pitches balance the
same trial exponents: the pitch and the growth rate never move the balanced abscissa. -/
theorem scaleBalance_gauge_free (p r p' r' : ℝ) (hr : 0 < r) (hr' : 0 < r') (σ : ℝ) :
    (∃ L : ℝ, 0 < L ∧
        Tendsto (fun n : ℕ => (n : ℝ) ^ (-σ) * Geometry.carrierRadius p r n) atTop (𝓝 L)) ↔
      (∃ L : ℝ, 0 < L ∧
        Tendsto (fun n : ℕ => (n : ℝ) ^ (-σ) * Geometry.carrierRadius p' r' n) atTop (𝓝 L)) := by
  rw [Geometry.sigma_half_is_scale_critical p r hr σ,
    Geometry.sigma_half_is_scale_critical p' r' hr' σ]

/-! ## 3. The trial exponent is the heat time -/

/-- **The drift of the trial exponent.**  Moving the abscissa by a real `δ` multiplies the
site-scale product by `(k+1)^{−δ}`. -/
theorem siteScaleProduct_add_real (s : ℂ) (δ : ℝ) (k : ℕ) :
    siteScaleProduct (s + (δ : ℂ)) k = siteScaleProduct s k * ((k : ℝ) + 1) ^ (-δ) := by
  rw [siteScaleProduct_eq, siteScaleProduct_eq]
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hre : (s + (δ : ℂ)).re = s.re + δ := by simp
  rw [hre, show (1 / 2 : ℝ) - (s.re + δ) = (1 / 2 - s.re) + -δ by ring, Real.rpow_add hpos]
  ring

/-- The drift factor is the heat semigroup's eigenvalue at real time `δ` on the `k`-th phasor. -/
theorem rpow_neg_eq_exp_logWeight (δ : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) ^ (-δ) = Real.exp (-δ * CarrierReadout.logWeight k) := by
  rw [Real.rpow_def_of_pos (by positivity)]
  simp only [CarrierReadout.logWeight]
  congr 1
  ring

/-- **The drift in the carrier's own radius.**  With the helix-native generator `A = log R²`, the
state at abscissa `½ + δ` times the wound radius is `R^{−2δ}`, exactly, at every site. -/
theorem areaWarp_drift (δ : ℝ) (n : ℕ) :
    Real.exp (-(1 / 2 + δ) * CarrierHelixGenerator.areaLogWeight n) *
        Geometry.carrierRadius 1 3 (n + 1) =
      Geometry.carrierRadius 1 3 (n + 1) ^ (-2 * δ) := by
  have hR := CarrierHelixGenerator.carrierRadius_pos 1 3 (by norm_num) (Nat.le_add_left 1 n)
  rw [CarrierHelixGenerator.areaLogWeight_eq_two_log n, Real.rpow_def_of_pos hR]
  calc Real.exp (-(1 / 2 + δ) * (2 * Real.log (Geometry.carrierRadius 1 3 (n + 1)))) *
        Geometry.carrierRadius 1 3 (n + 1)
      = Real.exp (-(1 / 2 + δ) * (2 * Real.log (Geometry.carrierRadius 1 3 (n + 1)))) *
          Real.exp (Real.log (Geometry.carrierRadius 1 3 (n + 1))) := by rw [Real.exp_log hR]
    _ = Real.exp (Real.log (Geometry.carrierRadius 1 3 (n + 1)) * (-2 * δ)) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-! ## 4. Native states carry no drift; the heat orbit carries exactly the heat time -/

/-- **Native states.**  At the carrier point of every height the site-scale product is the fixed
geometric sequence `R_{k+1}/√(k+1)`; it does not depend on the height. -/
theorem siteScaleProduct_carrierPoint (y : ℝ) (k : ℕ) :
    siteScaleProduct (carrierPoint y) k =
      Geometry.carrierRadius 1 3 (k + 1) / Real.sqrt ((k : ℝ) + 1) := by
  rw [siteScaleProduct_eq, carrierPoint_re, carrierAbscissa_eq_half, sub_self, Real.rpow_zero,
    mul_one]

/-- **The heat orbit.**  At the carrier point shifted by a real `δ`, the site-scale product is the
native sequence times the heat eigenvalue `(k+1)^{−δ}`. -/
theorem siteScaleProduct_heatOrbit (y δ : ℝ) (k : ℕ) :
    siteScaleProduct (carrierPoint y + (δ : ℂ)) k =
      Geometry.carrierRadius 1 3 (k + 1) / Real.sqrt ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ (-δ) := by
  rw [siteScaleProduct_add_real, siteScaleProduct_carrierPoint]

end CriticalLinePhasor.CarrierRadialDegree

#print axioms CriticalLinePhasor.CarrierRadialDegree.carrierState3DEquiv
#print axioms CriticalLinePhasor.CarrierRadialDegree.scaleBalance_gauge_free
#print axioms CriticalLinePhasor.CarrierRadialDegree.siteScaleProduct_add_real
#print axioms CriticalLinePhasor.CarrierRadialDegree.rpow_neg_eq_exp_logWeight
#print axioms CriticalLinePhasor.CarrierRadialDegree.areaWarp_drift
#print axioms CriticalLinePhasor.CarrierRadialDegree.siteScaleProduct_carrierPoint
#print axioms CriticalLinePhasor.CarrierRadialDegree.siteScaleProduct_heatOrbit
