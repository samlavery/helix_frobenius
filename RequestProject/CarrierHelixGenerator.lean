import RequestProject.AreaLaw
import RequestProject.LogWeightOperator

/-!
# The helix and the log-weight generator

Audit and promotion of the link "helix geometry → arclength/scale law → generator spectrum →
height-flow phases" (`tmp/campaign_r22_a_sitelink.lean`).  Imports: `AreaLaw` (helix, arclength,
winding, wound radius) and `LogWeightOperator` (`H`, `H_Δ` on `ℓ²(ℕ, ℂ)`).  Provenance scan of the
transitive constant closure (`tmp/campaign_r23_helixgen_draft.lean`): the only house constants
consumed are `CriticalLinePhasor.Geometry.*` (ClosedForm, AreaLaw) and `CarrierReadout.*`
(LogWeightOperator); no ζ, L-series, zero-set or functional-equation constant occurs.

## 1. The arclength reading of `H` is the tick rule

The wound site `n` is defined as the helix parameter whose arclength is the tick `n·π/3`
(`Geometry.windIntegerSite`, `Geometry.windParameter`, `Geometry.windParameter_spec`).  So:

* `carrierLogWeight_eq_log_of_section`: for any `L : ℝ → ℝ` and any `w` with `L (w s) = s` on
  `s ≥ 0`, `log L(w(Δ(n+1))) = log(Δ(n+1))`.  No property of any curve is used.
* `carrierLogWeight_eq_log_arclength` (R22A2, promoted) is proved as the instance
  `L = arclength p r`, `w = windParameter p r`.
* `log_arclength_site_gauge_free`: the value does not depend on the gauge `(p, r)`.
* `helix_rail_same_siteLaw`: every helix with `r > 0` and the straight rail `r = 0` read the same
  site arclength at the eigenvalue of `H_{π/3}`.
* `HΔ_phasor_eq_log_arclength`: the eigenvalue of `H_{π/3}` on the `n`-th phasor is the
  log-arclength of the wound site `n+1`.

`log(arclength of site n+1) = log(Δ(n+1))` therefore holds by definition of the ticks; the helix
enters only through the existence of its arclength parametrisation.  The form `log` is forced by
scale covariance (`CarrierReadout.gaugeWeight_eq_log`, `RequestProject/CarrierRegistration.lean`),
not by the helix.

## 2. The helix-native generator: log of the squared wound radius

The helix does determine a spectrum of its own, through the wound radius `R_n = r·k_n`.  In the
unit gauge `(p, r) = (1, 3)` set `A_n = log R_{n+1}²` (`areaLogWeight`; on `ℓ²` the
multiplication operator is self-adjoint with the phasors as eigenvectors,
`areaGenerator_isSelfAdjoint`, `areaGenerator_phasor`).

* `areaLogWeight_eq`: `A_n = log(n+1) + log(R_{n+1}²/(n+1))`, exactly;
* `areaRatio_eq`: `R_{n+1}²/(n+1) = 3π k²/S(k)`, the leading area term over the full arclength at
  the wound parameter `k` of site `n+1`;
* `areaLogWeight_lt`: `A_n < log(n+1)` at every site (the `arsinh` term of the closed form is
  positive, `arclengthClosed_strict_lower`);
* `tendsto_areaDefect`: `A_n − log(n+1) → 0` (area law);
* `areaLogWeight_not_affine`: `A ≠ a·H + c` for all real `a, c`.

So `H` is the common mode of `A`; the remainder `E = A − H`, with `E < 0` and `E → 0`, is evaluated
exactly from the closed-form arclength.

## 3. Height flow

`heightFlow w y n = exp(−i·y·w_n)`: unimodular (`norm_heightFlow`), a one-parameter group
(`heightFlow_add`), angular velocity `w_n` (`hasDerivAt_heightFlow`).  With `w = log(Δ(n+1))`,
`Δ = π/3`, it is `(arclength of site n+1)^{−iy}` (`heightFlow_carrierLogWeight_eq_cpow`).  The
`A`-flow is the `H`-flow times the `E`-flow (`heightFlow_area_factor`), and at each fixed `y` the
`E`-flow tends to `1` along the sites (`tendsto_heightFlow_areaDefect`).

## 4. The abscissa read from the helix-native generator

* `areaWarp_balance_iff`: `e^{−σ A_n}·R_{n+1} = 1` at every site iff `σ = ½`.  For `σ ≠ ½` the warp
  `e^{−σA}` is DEFORMED: it fails the balance at site `1`.
* `areaState_eq`: `exp(−(½ + iy)·A_n) = R_{n+1}^{−1}·exp(−iy·A_n)`.
* `heatWarp_not_sitewise_balanced`: for the log-arclength generator no `σ` gives
  `(n+1)^{−σ}·R_{n+1} = 1` at every site (site `1` fails), so its balance with the radius is the
  limit statement `Geometry.sigma_half_is_scale_critical`.
-/

open Filter Topology
open CriticalLinePhasor

noncomputable section

namespace CriticalLinePhasor.CarrierHelixGenerator

/-! ### 1. The arclength reading is the tick rule -/

/-- The arclength of the wound site `n` is its tick `n·π/3`: the defining property of the
winding. -/
theorem arclength_windParameter_spinAngle (p r : ℝ) (hr : 0 < r) (n : ℕ) :
    Geometry.arclength p r (Geometry.windParameter p r (Geometry.spinAngle n))
      = Geometry.spinAngle n :=
  (Geometry.windParameter_spec p r _ hr (Geometry.spinAngle_nonneg n)).2

theorem spinAngle_succ_pos (n : ℕ) : 0 < Geometry.spinAngle (n + 1) := by
  unfold Geometry.spinAngle
  positivity

/-- **The site law is a section identity.**  For any function `L` and any `w` with `L (w s) = s`
for `s ≥ 0`, the log of `L` at `w(Δ(n+1))` is the eigenvalue `log(Δ(n+1))` of `H_Δ`.  No
property of any curve is used. -/
theorem carrierLogWeight_eq_log_of_section (L w : ℝ → ℝ)
    (hsec : ∀ s : ℝ, 0 ≤ s → L (w s) = s) (Δ : ℝ) (hΔ : 0 ≤ Δ) (n : ℕ) :
    CarrierReadout.carrierLogWeight Δ n = Real.log (L (w (Δ * ((n : ℝ) + 1)))) := by
  show Real.log (Δ * ((n : ℝ) + 1)) = _
  rw [hsec (Δ * ((n : ℝ) + 1)) (mul_nonneg hΔ (by positivity))]

/-- At `Δ = π/3` the eigenvalue of `H_Δ` at index `n` is the log of the helix arclength of the
wound site `n + 1`, for every gauge `(p, r)` with `r > 0`.  Proved as the instance
`L = arclength p r` of `carrierLogWeight_eq_log_of_section`. -/
theorem carrierLogWeight_eq_log_arclength (p r : ℝ) (hr : 0 < r) (n : ℕ) :
    CarrierReadout.carrierLogWeight (Real.pi / 3) n
      = Real.log (Geometry.arclength p r
          (Geometry.windParameter p r (Geometry.spinAngle (n + 1)))) := by
  have hsite : Real.pi / 3 * ((n : ℝ) + 1) = Geometry.spinAngle (n + 1) := by
    unfold Geometry.spinAngle
    push_cast
    ring
  rw [carrierLogWeight_eq_log_of_section (Geometry.arclength p r) (Geometry.windParameter p r)
    (fun s hs => (Geometry.windParameter_spec p r s hr hs).2) (Real.pi / 3) (by positivity) n,
    hsite]

/-- **The helix is inert in the site law.**  The log-arclength of the wound site does not depend
on the gauge `(p, r)`. -/
theorem log_arclength_site_gauge_free (p r p' r' : ℝ) (hr : 0 < r) (hr' : 0 < r') (n : ℕ) :
    Real.log (Geometry.arclength p r (Geometry.windParameter p r (Geometry.spinAngle n)))
      = Real.log (Geometry.arclength p' r'
          (Geometry.windParameter p' r' (Geometry.spinAngle n))) := by
  rw [arclength_windParameter_spinAngle p r hr n, arclength_windParameter_spinAngle p' r' hr' n]

/-- **Helix and straight rail read the same site law.**  The arclength of the wound site `n+1` on
any helix with `r > 0` equals the arclength reached on the straight rail `r = 0` by the climber at
the ordinate `carrierLogWeight (π/3) n`. -/
theorem helix_rail_same_siteLaw (p r : ℝ) (hp : 0 < p) (hr : 0 < r) (n : ℕ) :
    Geometry.arclength p r (Geometry.windParameter p r (Geometry.spinAngle (n + 1)))
      = Geometry.arclength p 0
          (Geometry.kClimb p (CarrierReadout.carrierLogWeight (Real.pi / 3) n)) := by
  rw [arclength_windParameter_spinAngle p r hr (n + 1), Geometry.arclength_r_zero p _ hp.le,
    ← Geometry.height_eq_p_mul_kClimb p _ hp.ne']
  have hx : (0 : ℝ) < Real.pi / 3 * ((n : ℝ) + 1) := by positivity
  simp only [CarrierReadout.carrierLogWeight, Geometry.spinAngle]
  rw [Real.exp_log hx]
  push_cast
  ring

/-- The eigenvalue of `H_{π/3}` on the `n`-th phasor is the log-arclength of the wound site
`n + 1`. -/
theorem HΔ_phasor_eq_log_arclength (p r : ℝ) (hr : 0 < r) (n : ℕ) :
    CarrierReadout.HΔ (Real.pi / 3)
        ⟨CarrierReadout.phasor n, CarrierReadout.phasor_mem_weightDomain _ n⟩
      = ((Real.log (Geometry.arclength p r
            (Geometry.windParameter p r (Geometry.spinAngle (n + 1)))) : ℝ) : ℂ)
          • CarrierReadout.phasor n := by
  rw [← carrierLogWeight_eq_log_arclength p r hr n]
  exact CarrierReadout.weightMul_phasor _ n

/-! ### 2. The helix-native generator: log of the squared wound radius -/

/-- The wound radius at site `n` is `r · k_n`. -/
theorem carrierRadius_eq_mul (p r : ℝ) (hr : 0 < r) (n : ℕ) :
    Geometry.carrierRadius p r n = r * Geometry.windParameter p r (Geometry.spinAngle n) := by
  unfold Geometry.carrierRadius
  exact Geometry.windIntegerSite_cyl_radius p r hr n

theorem windParameter_pos (p r : ℝ) (hr : 0 < r) {n : ℕ} (hn : 1 ≤ n) :
    0 < Geometry.windParameter p r (Geometry.spinAngle n) := by
  obtain ⟨hk0, hk⟩ := Geometry.windParameter_spec p r _ hr (Geometry.spinAngle_nonneg n)
  refine lt_of_le_of_ne hk0 ?_
  intro h0
  rw [← h0, Geometry.arclength_zero p r hr] at hk
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Geometry.spinAngle n := by
    unfold Geometry.spinAngle
    exact mul_pos hn' (by positivity)
  linarith

theorem carrierRadius_pos (p r : ℝ) (hr : 0 < r) {n : ℕ} (hn : 1 ≤ n) :
    0 < Geometry.carrierRadius p r n := by
  rw [carrierRadius_eq_mul p r hr n]
  exact mul_pos hr (windParameter_pos p r hr hn)

/-- Strict area-law bound `π r k² < S(k)` for `k > 0`: the `arsinh` term is positive. -/
theorem arclengthClosed_strict_lower (p r k : ℝ) (hr : 0 < r) (hk : 0 < k) :
    Real.pi * r * k ^ 2 < Geometry.arclengthClosed p r k := by
  unfold Geometry.arclengthClosed
  have h2 : 0 ≤ 2 * Real.pi * r * k := by positivity
  have hsqrtA : 2 * Real.pi * r * k
      ≤ Real.sqrt (p ^ 2 + r ^ 2 + 4 * Real.pi ^ 2 * r ^ 2 * k ^ 2) := by
    rw [show 2 * Real.pi * r * k = Real.sqrt ((2 * Real.pi * r * k) ^ 2) from
      (Real.sqrt_sq h2).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hterm1 : Real.pi * r * k ^ 2
      ≤ k / 2 * Real.sqrt (p ^ 2 + r ^ 2 + 4 * Real.pi ^ 2 * r ^ 2 * k ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hsqrtA (show (0:ℝ) ≤ k / 2 by positivity)]
  have hterm2 : 0 < (p ^ 2 + r ^ 2) / (4 * Real.pi * r)
      * Real.arsinh (2 * Real.pi * r * k / Real.sqrt (p ^ 2 + r ^ 2)) := by
    apply mul_pos (by positivity)
    exact Real.arsinh_pos_iff.mpr (by positivity)
  linarith

/-- In the unit gauge `(1, 3)` the squared wound radius of site `n+1` is strictly below `n+1`. -/
theorem carrierRadius_sq_lt (n : ℕ) :
    Geometry.carrierRadius 1 3 (n + 1) ^ 2 < (n : ℝ) + 1 := by
  have hk := windParameter_pos 1 3 (by norm_num) (Nat.le_add_left 1 n)
  have hS := arclength_windParameter_spinAngle 1 3 (by norm_num) (n + 1)
  have hlt := arclengthClosed_strict_lower 1 3 _ (by norm_num) hk
  rw [← Geometry.arclength_closed_form 1 3 _ (by norm_num), hS] at hlt
  rw [carrierRadius_eq_mul 1 3 (by norm_num) (n + 1)]
  set k := Geometry.windParameter 1 3 (Geometry.spinAngle (n + 1)) with hkdef
  have hsa : Geometry.spinAngle (n + 1) = ((n : ℝ) + 1) * (Real.pi / 3) := by
    rw [Geometry.spinAngle, Nat.cast_add, Nat.cast_one]
  rw [hsa] at hlt
  have hπ := Real.pi_pos
  have h9 : Real.pi * (9 * k ^ 2) < Real.pi * ((n : ℝ) + 1) := by linarith
  have h9' := lt_of_mul_lt_mul_left h9 hπ.le
  calc (3 * k) ^ 2 = 9 * k ^ 2 := by ring
    _ < (n : ℝ) + 1 := h9'

/-- **The helix-native log-weight** of the `n`-th phasor (site `n+1`), unit gauge `(1, 3)`: the
logarithm of the squared wound radius. -/
def areaLogWeight (n : ℕ) : ℝ := Real.log (Geometry.carrierRadius 1 3 (n + 1) ^ 2)

theorem areaLogWeight_eq_two_log (n : ℕ) :
    areaLogWeight n = 2 * Real.log (Geometry.carrierRadius 1 3 (n + 1)) := by
  simp [areaLogWeight, Real.log_pow]

/-- Exact decomposition: `A_n = log(n+1) + log(R_{n+1}²/(n+1))`. -/
theorem areaLogWeight_eq (n : ℕ) :
    areaLogWeight n = CarrierReadout.logWeight n
      + Real.log (Geometry.carrierRadius 1 3 (n + 1) ^ 2 / ((n : ℝ) + 1)) := by
  have hR := carrierRadius_pos 1 3 (by norm_num) (Nat.le_add_left 1 n)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.log_div (pow_pos hR 2).ne' hn.ne']
  simp only [areaLogWeight, CarrierReadout.logWeight]
  ring

/-- The ratio in the defect is the leading area term `π r k²` (`r = 3`) over the full arclength
`S(k)`, at the wound parameter `k` of site `n+1`. -/
theorem areaRatio_eq (n : ℕ) :
    Geometry.carrierRadius 1 3 (n + 1) ^ 2 / ((n : ℝ) + 1)
      = Real.pi * 3 * Geometry.windParameter 1 3 (Geometry.spinAngle (n + 1)) ^ 2
          / Geometry.arclength 1 3
              (Geometry.windParameter 1 3 (Geometry.spinAngle (n + 1))) := by
  rw [arclength_windParameter_spinAngle 1 3 (by norm_num) (n + 1),
    carrierRadius_eq_mul 1 3 (by norm_num) (n + 1)]
  set k := Geometry.windParameter 1 3 (Geometry.spinAngle (n + 1)) with hkdef
  have hsa : Geometry.spinAngle (n + 1) = ((n : ℝ) + 1) * (Real.pi / 3) := by
    rw [Geometry.spinAngle, Nat.cast_add, Nat.cast_one]
  rw [hsa]
  have hb : (n : ℝ) + 1 ≠ 0 := by positivity
  have hd : ((n : ℝ) + 1) * (Real.pi / 3) ≠ 0 := by positivity
  rw [div_eq_div_iff hb hd]
  ring

/-- The helix-native weight lies strictly below the log-arclength weight at every site. -/
theorem areaLogWeight_lt (n : ℕ) : areaLogWeight n < CarrierReadout.logWeight n := by
  have hR := carrierRadius_pos 1 3 (by norm_num) (Nat.le_add_left 1 n)
  show Real.log (Geometry.carrierRadius 1 3 (n + 1) ^ 2) < Real.log ((n : ℝ) + 1)
  exact Real.log_lt_log (pow_pos hR 2) (carrierRadius_sq_lt n)

/-- The defect `A_n − log(n+1)` tends to `0` (area law). -/
theorem tendsto_areaDefect :
    Tendsto (fun n : ℕ => areaLogWeight n - CarrierReadout.logWeight n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => Geometry.carrierRadius 1 3 n ^ 2 / (n : ℝ)) atTop (𝓝 1) :=
    Geometry.windIntegerSite_radius_sq_tendsto_unit_gauge
  have h1 : Tendsto (fun n : ℕ => Geometry.carrierRadius 1 3 (n + 1) ^ 2 / ((n : ℝ) + 1))
      atTop (𝓝 1) := by
    refine ((tendsto_add_atTop_iff_nat 1).mpr h).congr (fun n => ?_)
    simp only [Nat.cast_add, Nat.cast_one]
  have h2 := h1.log one_ne_zero
  rw [Real.log_one] at h2
  refine h2.congr (fun n => ?_)
  rw [areaLogWeight_eq n]
  ring

theorem tendsto_logWeight_atTop :
    Tendsto (fun n : ℕ => CarrierReadout.logWeight n) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact Real.tendsto_log_atTop.comp h

/-- The helix-native weight is not an affine function of the log-arclength weight. -/
theorem areaLogWeight_not_affine :
    ¬ ∃ a c : ℝ, ∀ n : ℕ, areaLogWeight n = a * CarrierReadout.logWeight n + c := by
  rintro ⟨a, c, hac⟩
  have hE := tendsto_areaDefect
  have hEq : ∀ n : ℕ, areaLogWeight n - CarrierReadout.logWeight n
      = (a - 1) * CarrierReadout.logWeight n + c := fun n => by rw [hac n]; ring
  by_cases ha : a = 1
  · subst ha
    have hc : ∀ n : ℕ, areaLogWeight n - CarrierReadout.logWeight n = c := fun n => by
      rw [hEq n]; ring
    have hc0 : c = 0 := by
      have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 0) := hE.congr hc
      exact tendsto_nhds_unique tendsto_const_nhds hconst
    have h0 := areaLogWeight_lt 0
    have h1 := hc 0
    linarith
  · have hne : a - 1 ≠ 0 := sub_ne_zero.mpr ha
    have hconv : Tendsto (fun n : ℕ => CarrierReadout.logWeight n) atTop
        (𝓝 ((0 - c) / (a - 1))) := by
      refine ((hE.sub_const c).div_const (a - 1)).congr (fun n => ?_)
      show (areaLogWeight n - CarrierReadout.logWeight n - c) / (a - 1)
        = CarrierReadout.logWeight n
      rw [hEq n, eq_comm, eq_div_iff hne]
      ring
    exact not_tendsto_nhds_of_tendsto_atTop tendsto_logWeight_atTop _ hconv

/-- The helix-native generator on `ℓ²`, multiplication by `A_n = log R_{n+1}²` on its maximal
domain, is self-adjoint. -/
theorem areaGenerator_isSelfAdjoint :
    IsSelfAdjoint (CarrierReadout.weightMul areaLogWeight) :=
  CarrierReadout.weightMul_isSelfAdjoint areaLogWeight

/-- The phasors are its eigenvectors, with eigenvalue `A_n`. -/
theorem areaGenerator_phasor (n : ℕ) :
    CarrierReadout.weightMul areaLogWeight
        ⟨CarrierReadout.phasor n, CarrierReadout.phasor_mem_weightDomain areaLogWeight n⟩
      = (areaLogWeight n : ℂ) • CarrierReadout.phasor n :=
  CarrierReadout.weightMul_phasor areaLogWeight n

/-! ### 3. Height flow -/

/-- The phase of site `n` at ordinate `y` under the generator with weights `w`:
`exp(−i·y·w_n)`. -/
def heightFlow (w : ℕ → ℝ) (y : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((-(y * w n)) : ℝ) * Complex.I)

theorem norm_heightFlow (w : ℕ → ℝ) (y : ℝ) (n : ℕ) : ‖heightFlow w y n‖ = 1 := by
  unfold heightFlow
  exact Complex.norm_exp_ofReal_mul_I _

theorem heightFlow_add (w : ℕ → ℝ) (y y' : ℝ) (n : ℕ) :
    heightFlow w (y + y') n = heightFlow w y n * heightFlow w y' n := by
  unfold heightFlow
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The angular velocity of site `n` in the height flow is its weight `w_n`. -/
theorem hasDerivAt_heightFlow (w : ℕ → ℝ) (y : ℝ) (n : ℕ) :
    HasDerivAt (fun t : ℝ => heightFlow w t n)
      (-((w n : ℝ) : ℂ) * Complex.I * heightFlow w y n) y := by
  have h1 : HasDerivAt (fun t : ℝ => -(t * w n)) (-(1 * w n)) y :=
    ((hasDerivAt_id y).mul_const (w n)).neg
  have h2 := (h1.ofReal_comp.mul_const Complex.I).cexp
  unfold heightFlow
  convert h2 using 1
  push_cast
  ring

/-- With the carrier weights at `Δ = π/3`, the height-flow phase of site `n` is
`(arclength of the wound site n+1)^{−iy}`. -/
theorem heightFlow_carrierLogWeight_eq_cpow (p r : ℝ) (hr : 0 < r) (y : ℝ) (n : ℕ) :
    heightFlow (CarrierReadout.carrierLogWeight (Real.pi / 3)) y n
      = ((Geometry.arclength p r
            (Geometry.windParameter p r (Geometry.spinAngle (n + 1))) : ℝ) : ℂ)
          ^ (-(y : ℂ) * Complex.I) := by
  have hlog := carrierLogWeight_eq_log_arclength p r hr n
  rw [arclength_windParameter_spinAngle p r hr (n + 1)] at hlog ⊢
  have hx := spinAngle_succ_pos n
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le]
  unfold heightFlow
  rw [hlog]
  congr 1
  push_cast
  ring

/-- The `A`-flow is the `H`-flow times the defect flow. -/
theorem heightFlow_area_factor (y : ℝ) (n : ℕ) :
    heightFlow areaLogWeight y n
      = heightFlow CarrierReadout.logWeight y n
          * heightFlow (fun m => areaLogWeight m - CarrierReadout.logWeight m) y n := by
  unfold heightFlow
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- At every fixed ordinate the defect flow tends to `1` along the sites. -/
theorem tendsto_heightFlow_areaDefect (y : ℝ) :
    Tendsto (fun n : ℕ =>
        heightFlow (fun m => areaLogWeight m - CarrierReadout.logWeight m) y n)
      atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ =>
      (((-(y * (areaLogWeight n - CarrierReadout.logWeight n))) : ℝ) : ℂ) * Complex.I)
      atTop (𝓝 ((((-(y * 0)) : ℝ) : ℂ) * Complex.I)) :=
    ((Complex.continuous_ofReal.tendsto _).comp
      ((tendsto_areaDefect.const_mul y).neg)).mul_const Complex.I
  have h1 := h0.cexp
  rw [show ((((-(y * 0)) : ℝ) : ℂ) * Complex.I) = 0 by simp, Complex.exp_zero] at h1
  exact h1

/-! ### 4. The abscissa read from the helix-native generator -/

/-- At abscissa `½` the helix-native state has amplitude exactly the reciprocal wound radius. -/
theorem areaState_eq (y : ℝ) (n : ℕ) :
    Complex.exp (-(((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) * (areaLogWeight n : ℂ))
      = (((Geometry.carrierRadius 1 3 (n + 1))⁻¹ : ℝ) : ℂ) * heightFlow areaLogWeight y n := by
  have hR := carrierRadius_pos 1 3 (by norm_num) (Nat.le_add_left 1 n)
  have hamp : Real.exp (-(1 / 2) * areaLogWeight n)
      = (Geometry.carrierRadius 1 3 (n + 1))⁻¹ := by
    rw [areaLogWeight_eq_two_log n,
      show -(1 / 2 : ℝ) * (2 * Real.log (Geometry.carrierRadius 1 3 (n + 1)))
        = -Real.log (Geometry.carrierRadius 1 3 (n + 1)) by ring,
      Real.exp_neg, Real.exp_log hR]
  rw [← hamp, Complex.ofReal_exp]
  unfold heightFlow
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Exact sitewise balance.**  The warp `e^{−σA}` reciprocates the wound radius at every site
iff `σ = ½`. -/
theorem areaWarp_balance_iff (σ : ℝ) :
    (∀ n : ℕ, Real.exp (-σ * areaLogWeight n) * Geometry.carrierRadius 1 3 (n + 1) = 1)
      ↔ σ = 1 / 2 := by
  have hexp : ∀ n : ℕ,
      Real.exp (-σ * areaLogWeight n) * Geometry.carrierRadius 1 3 (n + 1)
        = Real.exp ((1 - 2 * σ) * Real.log (Geometry.carrierRadius 1 3 (n + 1))) := by
    intro n
    have hR := carrierRadius_pos 1 3 (by norm_num) (Nat.le_add_left 1 n)
    calc Real.exp (-σ * areaLogWeight n) * Geometry.carrierRadius 1 3 (n + 1)
        = Real.exp (-σ * (2 * Real.log (Geometry.carrierRadius 1 3 (n + 1))))
            * Real.exp (Real.log (Geometry.carrierRadius 1 3 (n + 1))) := by
          rw [areaLogWeight_eq_two_log n, Real.exp_log hR]
      _ = Real.exp ((1 - 2 * σ) * Real.log (Geometry.carrierRadius 1 3 (n + 1))) := by
          rw [← Real.exp_add]
          congr 1
          ring
  constructor
  · intro h
    have h0 := h 0
    rw [hexp 0, Real.exp_eq_one_iff] at h0
    have hR1 := carrierRadius_pos 1 3 (by norm_num) (Nat.le_add_left 1 0)
    have hlt : Geometry.carrierRadius 1 3 (0 + 1) ^ 2 < 1 := by
      have := carrierRadius_sq_lt 0
      rwa [Nat.cast_zero, zero_add (1 : ℝ)] at this
    have hR1lt : Geometry.carrierRadius 1 3 (0 + 1) < 1 := by nlinarith
    have hlog : Real.log (Geometry.carrierRadius 1 3 (0 + 1)) < 0 := Real.log_neg hR1 hR1lt
    rcases mul_eq_zero.mp h0 with h1 | h1
    · linarith
    · linarith
  · rintro rfl n
    rw [hexp n]
    norm_num

/-- For the log-arclength generator no exponent balances the wound radius at every site: site `1`
already fails. -/
theorem heatWarp_not_sitewise_balanced (σ : ℝ) :
    ¬ ∀ n : ℕ, ((n : ℝ) + 1) ^ (-σ) * Geometry.carrierRadius 1 3 (n + 1) = 1 := by
  intro h
  have h0 := h 0
  rw [Nat.cast_zero, zero_add (1 : ℝ), Real.one_rpow, one_mul] at h0
  have hlt : Geometry.carrierRadius 1 3 (0 + 1) ^ 2 < 1 := by
    have := carrierRadius_sq_lt 0
    rwa [Nat.cast_zero, zero_add (1 : ℝ)] at this
  rw [h0] at hlt
  norm_num at hlt

end CriticalLinePhasor.CarrierHelixGenerator

#print axioms CriticalLinePhasor.CarrierHelixGenerator.arclength_windParameter_spinAngle
#print axioms CriticalLinePhasor.CarrierHelixGenerator.spinAngle_succ_pos
#print axioms CriticalLinePhasor.CarrierHelixGenerator.carrierLogWeight_eq_log_of_section
#print axioms CriticalLinePhasor.CarrierHelixGenerator.carrierLogWeight_eq_log_arclength
#print axioms CriticalLinePhasor.CarrierHelixGenerator.log_arclength_site_gauge_free
#print axioms CriticalLinePhasor.CarrierHelixGenerator.helix_rail_same_siteLaw
#print axioms CriticalLinePhasor.CarrierHelixGenerator.HΔ_phasor_eq_log_arclength
#print axioms CriticalLinePhasor.CarrierHelixGenerator.carrierRadius_eq_mul
#print axioms CriticalLinePhasor.CarrierHelixGenerator.windParameter_pos
#print axioms CriticalLinePhasor.CarrierHelixGenerator.carrierRadius_pos
#print axioms CriticalLinePhasor.CarrierHelixGenerator.arclengthClosed_strict_lower
#print axioms CriticalLinePhasor.CarrierHelixGenerator.carrierRadius_sq_lt
#print axioms CriticalLinePhasor.CarrierHelixGenerator.areaLogWeight_eq_two_log
#print axioms CriticalLinePhasor.CarrierHelixGenerator.areaLogWeight_eq
#print axioms CriticalLinePhasor.CarrierHelixGenerator.areaRatio_eq
#print axioms CriticalLinePhasor.CarrierHelixGenerator.areaLogWeight_lt
#print axioms CriticalLinePhasor.CarrierHelixGenerator.tendsto_areaDefect
#print axioms CriticalLinePhasor.CarrierHelixGenerator.tendsto_logWeight_atTop
#print axioms CriticalLinePhasor.CarrierHelixGenerator.areaLogWeight_not_affine
#print axioms CriticalLinePhasor.CarrierHelixGenerator.areaGenerator_isSelfAdjoint
#print axioms CriticalLinePhasor.CarrierHelixGenerator.areaGenerator_phasor
#print axioms CriticalLinePhasor.CarrierHelixGenerator.norm_heightFlow
#print axioms CriticalLinePhasor.CarrierHelixGenerator.heightFlow_add
#print axioms CriticalLinePhasor.CarrierHelixGenerator.hasDerivAt_heightFlow
#print axioms CriticalLinePhasor.CarrierHelixGenerator.heightFlow_carrierLogWeight_eq_cpow
#print axioms CriticalLinePhasor.CarrierHelixGenerator.heightFlow_area_factor
#print axioms CriticalLinePhasor.CarrierHelixGenerator.tendsto_heightFlow_areaDefect
#print axioms CriticalLinePhasor.CarrierHelixGenerator.areaState_eq
#print axioms CriticalLinePhasor.CarrierHelixGenerator.areaWarp_balance_iff
#print axioms CriticalLinePhasor.CarrierHelixGenerator.heatWarp_not_sitewise_balanced
