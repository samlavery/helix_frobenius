import RequestProject.FrobeniusSimilitude
import RequestProject.DVPCarrierOrderedSum

/-!
# The carrier-driven stateful fiber, and the scale/warp balance in geometric variables

Built from the carrier and fiber definitions only.  Not used anywhere in this file: the `ζ`/`L`
identities, the functional equation, the explicit formula, the primes, any zero set.

## 1. The balance equation before the abscissa

The carrier's scaling law is the area law: the cylindrical radius of the wound site `n` is
`Geometry.carrierRadius p r n = r · k_n` (`carrierRadius_eq`), positive from site `1` on
(`carrierRadius_pos`), with `carrierRadius / √n → √(rΔ/π)`
(`Geometry.carrierRadius_div_sqrt_tendsto`).  The exponent `½` is a theorem of the arclength
geometry; the gauge `(p, r)` fixes only the prefactor.

The fiber's warp is the heat semigroup `e^{−sH}` of the carrier Hamiltonian
(`CarrierHamiltonian.heat s`), acting on the `n`-th phasor by `(n+1)^{−s}`
(`CarrierHamiltonian.heat_phasor`).  Its amplitude profile is
`heatAmplitude s n = (n+1)^{−Re s}` (`heatAmplitude_eq`).

`GeometricScaleWarpBalance p r a` says that a warp amplitude profile `a` and the carrier radius
have a positive finite conserved product.  It contains no abscissa.
* With the power-law profile it is *definitionally* `FrobeniusSimilitude.ScaleBalanced p r σ`
  (`geometricScaleWarpBalance_rpow_iff`, proof `Iff.rfl`).
* With the heat profile it is `ScaleBalanced p r (Re s)` (`geometricScaleWarpBalance_heat_iff`).
* It is the additive-log (cocycle) statement `log a_n + log r_n → ℓ`
  (`geometricScaleWarpBalance_iff_log`).
So `scaleBalanced_iff : ScaleBalanced p r σ ↔ σ = ½` is the coordinate reading of
"warp amplitude exponent = carrier growth exponent", and the `½` on its right is the carrier's.

## 2. The carrier-driven accumulator

`DVP.etaPartial s N` is the ordered accumulator: `S₀ = 0` (`etaPartial_zero`) and
`S_{N+1} = S_N + (−1)^N (N+1)^{−s}` (`etaPartial_succ`, `etaTerm_eq`).  The transition is
additive; the warp acts once, on the incoming phasor at its entry (`norm_etaTerm`), never on the
accumulated state.  The conjugate stream is the conjugate accumulator (`etaPartial_conj`).
The grown fiber at head `Z` is the window-weighted average of the ordered partial readouts
(`GrownFiber.finiteFiber_eq_avg`): a functional of the path, not of its endpoint.

## 3. An exact one-ended endpoint closure off balance

`S₂(s) = 1 − 2^{−s}` (`etaPartial_two`) vanishes at `s₀ = 2πi/log 2`, whose real part is `0`
(`etaPartial_two_offBalance`, `offBalancePoint_re`), while the reflected stream at the same head
takes the value `½` (`etaPartial_two_reflected`).  The one-ended finite closure event therefore
carries no balance information by itself (`offBalance_endpoint_closure`); whatever rigidity the
geometry has must come from the coupling of the two ends.
-/

open Filter Topology Finset
open CriticalLinePhasor

noncomputable section

namespace CriticalLinePhasor.CarrierDrivenFiber

/-! ## 1. The carrier's scaling: the area-law radius is positive from site 1 -/

/-- The area-law radius at site `n` is `r · k_n`, `k_n` the wind parameter of arclength `nπ/3`. -/
theorem carrierRadius_eq (p r : ℝ) (hr : 0 < r) (n : ℕ) :
    Geometry.carrierRadius p r n = r * Geometry.windParameter p r (Geometry.spinAngle n) := by
  unfold Geometry.carrierRadius
  exact Geometry.windIntegerSite_cyl_radius p r hr n

theorem arclength_zero (p r : ℝ) : Geometry.arclength p r 0 = 0 := by
  unfold Geometry.arclength
  simp

theorem spinAngle_pos {n : ℕ} (hn : 1 ≤ n) : 0 < Geometry.spinAngle n := by
  unfold Geometry.spinAngle
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos hn' (by positivity)

/-- The carrier radius is positive at every site `n ≥ 1`. -/
theorem carrierRadius_pos (p r : ℝ) (hr : 0 < r) {n : ℕ} (hn : 1 ≤ n) :
    0 < Geometry.carrierRadius p r n := by
  rw [carrierRadius_eq p r hr n]
  obtain ⟨hk0, hk⟩ := Geometry.windParameter_spec p r _ hr (Geometry.spinAngle_nonneg n)
  refine mul_pos hr (lt_of_le_of_ne hk0 ?_)
  intro h0
  rw [← h0, arclength_zero] at hk
  exact (spinAngle_pos hn).ne' hk.symm

/-! ## 2. The balance equation before the abscissa -/

/-- **Geometric scale/warp balance.**  A fiber whose warp amplitude at site `n` is `a n`
balances the carrier `(p, r)` when the product of the warp amplitude and the area-law carrier
radius converges to a positive conserved value.  No abscissa appears. -/
def GeometricScaleWarpBalance (p r : ℝ) (a : ℕ → ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ Tendsto (fun n : ℕ => a n * Geometry.carrierRadius p r n) atTop (𝓝 L)

/-- The amplitude profile of the heat warp `e^{−sH}`: the modulus of its eigenvalue `(n+1)^{−s}`
on the `n`-th phasor (`CarrierHamiltonian.heat_phasor`). -/
def heatAmplitude (s : ℂ) (n : ℕ) : ℝ := ‖((n : ℂ) + 1) ^ (-s)‖

theorem heatAmplitude_eq (s : ℂ) (n : ℕ) : heatAmplitude s n = ((n : ℝ) + 1) ^ (-s.re) := by
  unfold heatAmplitude
  have h : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]

theorem heatAmplitude_pos (s : ℂ) (n : ℕ) : 0 < heatAmplitude s n := by
  rw [heatAmplitude_eq]
  positivity

/-- (a) With the power-law profile `n^{−σ}`, geometric balance IS `ScaleBalanced`: definitional. -/
theorem geometricScaleWarpBalance_rpow_iff (p r σ : ℝ) :
    GeometricScaleWarpBalance p r (fun n : ℕ => (n : ℝ) ^ (-σ))
      ↔ FrobeniusSimilitude.ScaleBalanced p r σ :=
  Iff.rfl

theorem tendsto_div_add_one_rpow (σ : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) / ((n : ℝ) + 1)) ^ (-σ)) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hc : ContinuousAt (fun x : ℝ => x ^ (-σ)) 1 :=
    Real.continuousAt_rpow_const 1 (-σ) (Or.inl one_ne_zero)
  have := hc.tendsto.comp h
  rw [Real.one_rpow] at this
  exact this

theorem tendsto_add_one_div_rpow (σ : ℝ) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1) / (n : ℝ)) ^ (-σ)) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
    have h1 := (tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀ one_ne_zero
    rw [inv_one] at h1
    refine h1.congr' (Eventually.of_forall fun n => ?_)
    simp only [inv_div]
  have hc : ContinuousAt (fun x : ℝ => x ^ (-σ)) 1 :=
    Real.continuousAt_rpow_const 1 (-σ) (Or.inl one_ne_zero)
  have := hc.tendsto.comp h
  rw [Real.one_rpow] at this
  exact this

/-- (b) **The heat warp balances the carrier iff `ScaleBalanced (Re s)`.**  The abscissa of the
warp rate is the only datum of the warp that the balance sees. -/
theorem geometricScaleWarpBalance_heat_iff (p r : ℝ) (s : ℂ) :
    GeometricScaleWarpBalance p r (heatAmplitude s)
      ↔ FrobeniusSimilitude.ScaleBalanced p r s.re := by
  unfold GeometricScaleWarpBalance FrobeniusSimilitude.ScaleBalanced
  have e1 : ∀ n : ℕ, 1 ≤ n →
      heatAmplitude s n = (n : ℝ) ^ (-s.re) * (((n : ℝ) + 1) / (n : ℝ)) ^ (-s.re) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [heatAmplitude_eq,
      ← Real.mul_rpow (x := (n : ℝ)) (y := ((n : ℝ) + 1) / (n : ℝ)) hn0.le (by positivity)]
    congr 1
    field_simp
  have e2 : ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ (-s.re) = heatAmplitude s n * ((n : ℝ) / ((n : ℝ) + 1)) ^ (-s.re) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [heatAmplitude_eq,
      ← Real.mul_rpow (x := (n : ℝ) + 1) (y := (n : ℝ) / ((n : ℝ) + 1)) (by positivity)
        (by positivity)]
    congr 1
    field_simp
  constructor
  · rintro ⟨L, hL, hT⟩
    refine ⟨L, hL, ?_⟩
    have h := (tendsto_div_add_one_rpow s.re).mul hT
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [e2 n hn]
    ring
  · rintro ⟨L, hL, hT⟩
    refine ⟨L, hL, ?_⟩
    have h := (tendsto_add_one_div_rpow s.re).mul hT
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [e1 n hn]
    ring

/-- (c) **The additive-log form of the balance**: for a positive amplitude profile, balance is the
convergence of `log a_n + log r_n` — "log W + log C = const", the cocycle form. -/
theorem geometricScaleWarpBalance_iff_log (p r : ℝ) (hr : 0 < r) {a : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) :
    GeometricScaleWarpBalance p r a ↔
      ∃ ℓ : ℝ, Tendsto (fun n : ℕ => Real.log (a n) + Real.log (Geometry.carrierRadius p r n))
        atTop (𝓝 ℓ) := by
  constructor
  · rintro ⟨L, hL, hT⟩
    refine ⟨Real.log L, ?_⟩
    have h := (Real.continuousAt_log hL.ne').tendsto.comp hT
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp]
    rw [Real.log_mul (ha n).ne' (carrierRadius_pos p r hr hn).ne']
  · rintro ⟨ℓ, hT⟩
    refine ⟨Real.exp ℓ, Real.exp_pos ℓ, ?_⟩
    have h := (Real.continuous_exp.tendsto ℓ).comp hT
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp]
    rw [Real.exp_add, Real.exp_log (ha n), Real.exp_log (carrierRadius_pos p r hr hn)]

/-! ## 3. The carrier-driven accumulator: `S₀` and the transition law -/

/-- `S₀ = 0`. -/
theorem etaPartial_zero (s : ℂ) : DVP.etaPartial s 0 = 0 := by
  simp [DVP.etaPartial]

/-- **The transition law is additive**: `S_{N+1} = S_N + v_N`. -/
theorem etaPartial_succ (s : ℂ) (N : ℕ) :
    DVP.etaPartial s (N + 1) = DVP.etaPartial s N + DVP.etaTerm s N := by
  unfold DVP.etaPartial
  exact Finset.sum_range_succ _ N

/-- The incoming phasor is the sign of the site times the heat-warp eigenvalue at the site:
the warp acts on the input once, at entry. -/
theorem etaTerm_eq (s : ℂ) (n : ℕ) : DVP.etaTerm s n = (-1) ^ n * ((n : ℂ) + 1) ^ (-s) := by
  unfold DVP.etaTerm
  rw [Complex.cpow_neg, div_eq_mul_inv]

/-- The modulus of the incoming phasor is the heat amplitude at its site. -/
theorem norm_etaTerm (s : ℂ) (n : ℕ) : ‖DVP.etaTerm s n‖ = heatAmplitude s n := by
  rw [etaTerm_eq, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rfl

theorem etaTerm_conj (s : ℂ) (n : ℕ) :
    DVP.etaTerm ((starRingEnd ℂ) s) n = (starRingEnd ℂ) (DVP.etaTerm s n) := by
  rw [etaTerm_eq, etaTerm_eq, map_mul, map_pow, map_neg, map_one]
  congr 1
  have hx : ((n : ℂ) + 1).arg ≠ Real.pi := by
    have h : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [h, Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm
  have h := Complex.conj_cpow ((n : ℂ) + 1) (-(starRingEnd ℂ) s) hx
  rw [map_neg, Complex.conj_conj] at h
  have hc : (starRingEnd ℂ) ((n : ℂ) + 1) = (n : ℂ) + 1 := by
    rw [map_add, map_natCast, map_one]
  rw [hc] at h
  exact h

/-- **The conjugate stream is the conjugate accumulator**: the anti-helix end (opposite spin,
same amplitudes) carries the same state, conjugated. -/
theorem etaPartial_conj (s : ℂ) (N : ℕ) :
    DVP.etaPartial ((starRingEnd ℂ) s) N = (starRingEnd ℂ) (DVP.etaPartial s N) := by
  unfold DVP.etaPartial
  rw [map_sum]
  exact Finset.sum_congr rfl (fun n _ => etaTerm_conj s n)

/-! ## 4. An exact one-ended endpoint closure off balance -/

theorem etaPartial_two (s : ℂ) : DVP.etaPartial s 2 = 1 - (2 : ℂ) ^ (-s) := by
  rw [etaPartial_succ, etaPartial_succ, etaPartial_zero, etaTerm_eq, etaTerm_eq]
  simp only [Nat.cast_zero, zero_add, Complex.one_cpow, pow_zero, pow_one, Nat.cast_one,
    one_add_one_eq_two]
  ring

/-- The off-balance readout point `s₀ = 2πi / log 2`. -/
def offBalancePoint : ℂ := ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I

theorem offBalancePoint_re : offBalancePoint.re = 0 := by
  rw [offBalancePoint, Complex.mul_I_re, Complex.ofReal_im, neg_zero]

theorem two_cpow_neg_offBalancePoint : (2 : ℂ) ^ (-offBalancePoint) = 1 := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hl : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    have := Complex.ofReal_log (x := 2) (by norm_num)
    push_cast at this
    exact this.symm
  rw [Complex.cpow_def_of_ne_zero two_ne_zero, hl]
  unfold offBalancePoint
  have hlog2' : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog2
  have h : ((Real.log 2 : ℝ) : ℂ) * -(((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I)
      = -(2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    linear_combination (-(2 * (Real.pi : ℂ) * Complex.I)) * mul_inv_cancel₀ hlog2'
  rw [h, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

/-- **A legal one-ended closure off balance**: the ordered stream with warp rate `s₀` closes at
head `2`, and `Re s₀ = 0`. -/
theorem etaPartial_two_offBalance : DVP.etaPartial offBalancePoint 2 = 0 := by
  rw [etaPartial_two, two_cpow_neg_offBalancePoint, sub_self]

/-- The reflected stream at the same head does not close: `S₂(1 − s₀) = ½`. -/
theorem etaPartial_two_reflected : DVP.etaPartial (1 - offBalancePoint) 2 = 1 / 2 := by
  rw [etaPartial_two]
  have h : (2 : ℂ) ^ (-(1 - offBalancePoint))
      = (2 : ℂ) ^ offBalancePoint * (2 : ℂ) ^ (-(1 : ℂ)) := by
    rw [← Complex.cpow_add _ _ two_ne_zero]
    congr 1
    ring
  have h2 : (2 : ℂ) ^ offBalancePoint = 1 := by
    have := two_cpow_neg_offBalancePoint
    rw [Complex.cpow_neg, inv_eq_one] at this
    exact this
  rw [h, h2, Complex.cpow_neg_one, one_mul]
  norm_num

/-- The one-ended finite closure event carries no balance information: it occurs at a legal
warp rate of abscissa `0`, and the reflected end is open there. -/
theorem offBalance_endpoint_closure :
    DVP.etaPartial offBalancePoint 2 = 0 ∧ offBalancePoint.re ≠ 1 / 2 ∧
      DVP.etaPartial (1 - offBalancePoint) 2 ≠ 0 :=
  ⟨etaPartial_two_offBalance, by rw [offBalancePoint_re]; norm_num,
    by rw [etaPartial_two_reflected]; norm_num⟩

end CriticalLinePhasor.CarrierDrivenFiber
