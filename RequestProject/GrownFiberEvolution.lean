import RequestProject.GrownFiberConverges
import RequestProject.AreaLaw
import RequestProject.LogWeightOperator

/-!
# The carrier-driven grown fiber: normalization, head-evolution law, carrier scale inside the term

Everything is derived from the house definitions `finiteFiber`, `smoothEntry`, `physicalHead`,
`weight`, `partialReadout` (CarrierHeadFiniteFiber, GrownFiberConverges), the carrier radius
(AreaLaw) and the carrier log-weights (LogWeightOperator).  No `ζ`/`L` identity, functional
equation, explicit formula, prime, zero set, or RH-equivalent statement is used in any proof.

## 1. Normalization
`G_Z(s) = Σ_{k<⌈Z⌉₊} K_Z(k) · V_s(k)` with the carrier/head window `K_Z(k) = ψ((k+1)/Z)`
(`headWindow`) and the warped input `V_s(k) = (−1)^k (k+1)^{−s}` (`inputPhasor`):
`finiteFiber_eq_window_input`.  History form: `GrownFiber.finiteFiber_eq_avg`, with the
window weights `weight Z i ≥ 0` summing to `ψ(1/Z)` (`weight_sum`), which tends to `1`
(`tendsto_smoothEntry_one_div`).

## 2. The exact head-advance law
`G_{Z'} = G_Z + B(Z, Z', s)`, `B` the re-weighting of the whole history by the moved window
(`finiteFiber_advance`, `finiteFiber_advance_avg`): `A = 1`, and `B` does not depend on whether
`G_Z` vanishes.  The grown fiber is differentiable in the head at every `Z > 0`, thresholds
included, with derivative the same input bank re-windowed by the growth kernel `κ(u) = −u ψ′(u)`
and divided by `Z` (`hasDerivAt_finiteFiber_head`); in log-head time the `1/Z` disappears
(`hasDerivAt_finiteFiber_logHead`); in the carrier's ordinate the head advances at the rate
`speed·e^y/Δ` (`physicalHead_hasDerivAt`, `hasDerivAt_carrierHeadFiber`).

## 3. The carrier scale inside the term
The fiber rides the carrier; the phasors ride on the fiber.  The relative scale of carrier and
fiber at site `k+1`, the carrier's radius there times the warp amplitude of the phasor the fiber
carries there, factorizes as `A_{k+1} · (k+1)^{½ − Re s}` with `A_n = carrierRadius 1 3 n / √n → 1`
(`siteScaleProduct_eq`, `tendsto_carrierRadius_div_sqrt`).  The energy of the grown state
factorizes through the head law as `E_Z(σ) = Z^{1−2σ} · R_Z(σ)` (`energy_eq`), and its flux per
unit log-head is `Z^{1−2σ} · Φ_Z(σ)` (`hasDerivAt_energy_logHead`): the combined exponent
`1 − 2σ = 2(½ − σ)` sits inside the actual evolution.

## 4. Carrier gauge covariance
Reading the phasors through the carrier-scaled log-weights `CarrierReadout.carrierLogWeight Δ k = log(Δ(k+1))`
multiplies the grown state by the global factor `Δ^{−s}` (`gaugedFiber_eq`): the vanishing locus
is invariant under the harmonic scaling of the carrier for every warp rate.
-/

open Complex Filter Topology Finset
open CriticalLinePhasor
open CriticalLinePhasor.CarrierHeadFiniteFiber
open CriticalLinePhasor.GrownFiber

noncomputable section

namespace CriticalLinePhasor.GrownFiberEvolution

/-! ## 1. Normalization: window × input -/

/-- The carrier/head window at head `Z`: the entry weight of the `k`-th phasor (site `k+1`). -/
def headWindow (Z : ℝ) (k : ℕ) : ℝ := smoothEntry (((k + 1 : ℕ) : ℝ) / Z)

/-- The `k`-th carrier-generated warped phasor: the sign of the site times the heat-warp
eigenvalue `(k+1)^{−s}`. -/
def inputPhasor (s : ℂ) (k : ℕ) : ℂ := (-1 : ℂ) ^ k * ((k : ℂ) + 1) ^ (-s)

theorem inputPhasor_zero (s : ℂ) : inputPhasor s 0 = 1 := by
  simp [inputPhasor]

theorem norm_inputPhasor (s : ℂ) (k : ℕ) : ‖inputPhasor s k‖ = ((k : ℝ) + 1) ^ (-s.re) := by
  unfold inputPhasor
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have h : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]

/-- **Normalization.** `G_Z(s) = Σ_{k<⌈Z⌉₊} K_Z(k) · V_s(k)`. -/
theorem finiteFiber_eq_window_input (Z : ℝ) (s : ℂ) :
    finiteFiber Z s = ∑ k ∈ range ⌈Z⌉₊, ((headWindow Z k : ℝ) : ℂ) * inputPhasor s k := by
  unfold finiteFiber headWindow inputPhasor
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [exp_neg_log_eq_cpow]
  ring

/-- Phasors beyond the head have not entered: their window weight is `0`. -/
theorem headWindow_eq_zero {Z : ℝ} (hZ : 0 < Z) {k : ℕ} (hk : ⌈Z⌉₊ ≤ k) :
    headWindow Z k = 0 := by
  unfold headWindow
  apply smoothEntry_of_one_le
  rw [le_div_iff₀ hZ, one_mul]
  have h1 : Z ≤ ⌈Z⌉₊ := Nat.le_ceil Z
  have h2 : (⌈Z⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
  push_cast
  linarith

/-- The grown state may be written over any range past the head. -/
theorem finiteFiber_eq_sum_of_le {Z : ℝ} (hZ : 0 < Z) (s : ℂ) {M : ℕ} (hM : ⌈Z⌉₊ ≤ M) :
    finiteFiber Z s = ∑ k ∈ range M, ((headWindow Z k : ℝ) : ℂ) * inputPhasor s k := by
  rw [finiteFiber_eq_window_input]
  apply Finset.sum_subset (Finset.range_subset_range.mpr hM)
  intro k _ hk
  rw [Finset.mem_range, not_lt] at hk
  rw [headWindow_eq_zero hZ hk]
  simp

/-! ## 2. The exact head-advance law -/

/-- **Head advance, input form.**  `G_{Z'} = G_Z + B`, `B` the re-weighting of the entire
history by the moved window: `A = 1`, and `B` is the same expression whether or not `G_Z = 0`. -/
theorem finiteFiber_advance {Z Z' : ℝ} (hZ : 0 < Z) (hZZ' : Z ≤ Z') (s : ℂ) :
    finiteFiber Z' s = finiteFiber Z s +
      ∑ k ∈ range ⌈Z'⌉₊, ((headWindow Z' k - headWindow Z k : ℝ) : ℂ) * inputPhasor s k := by
  rw [finiteFiber_eq_sum_of_le hZ s (Nat.ceil_mono hZZ'), finiteFiber_eq_window_input,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem weight_eq_zero_of_le {Z : ℝ} (hZ : 0 < Z) {i : ℕ} (hi : ⌈Z⌉₊ - 1 ≤ i) :
    weight Z i = 0 := by
  have hc : 1 ≤ ⌈Z⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hZ).ne'
  have h1 : ⌈Z⌉₊ ≤ i + 1 := by omega
  have h2 : ⌈Z⌉₊ ≤ i + 2 := by omega
  have hZc : Z ≤ ⌈Z⌉₊ := Nat.le_ceil Z
  have h1' : (⌈Z⌉₊ : ℝ) ≤ (i : ℝ) + 1 := by exact_mod_cast h1
  have h2' : (⌈Z⌉₊ : ℝ) ≤ (i : ℝ) + 2 := by exact_mod_cast h2
  unfold weight
  rw [smoothEntry_of_one_le, smoothEntry_of_one_le, sub_zero]
  all_goals (rw [le_div_iff₀ hZ, one_mul]; linarith)

theorem finiteFiber_eq_avg_of_le {Z : ℝ} (hZ : 0 < Z) (s : ℂ) {M : ℕ} (hM : ⌈Z⌉₊ - 1 ≤ M) :
    finiteFiber Z s = ∑ i ∈ range M, ((weight Z i : ℝ) : ℂ) * partialReadout (i + 1) s := by
  rw [finiteFiber_eq_avg hZ s]
  apply Finset.sum_subset (Finset.range_subset_range.mpr hM)
  intro i _ hi
  rw [Finset.mem_range, not_lt] at hi
  rw [weight_eq_zero_of_le hZ hi]
  simp

/-- **Head advance, history form.**  The moved window re-weights every ordered partial readout. -/
theorem finiteFiber_advance_avg {Z Z' : ℝ} (hZ : 0 < Z) (hZZ' : Z ≤ Z') (s : ℂ) :
    finiteFiber Z' s = finiteFiber Z s +
      ∑ i ∈ range (⌈Z'⌉₊ - 1), ((weight Z' i - weight Z i : ℝ) : ℂ) * partialReadout (i + 1) s := by
  rw [finiteFiber_eq_avg_of_le hZ s (Nat.sub_le_sub_right (Nat.ceil_mono hZZ') 1),
    finiteFiber_eq_avg (hZ.trans_le hZZ') s, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- **Normalization of the history weights**: they sum to `ψ(1/Z)`, the entry weight of site 1. -/
theorem weight_sum {Z : ℝ} (hZ : 0 < Z) :
    ∑ i ∈ range (⌈Z⌉₊ - 1), weight Z i = smoothEntry (1 / Z) := by
  have hc : 1 ≤ ⌈Z⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hZ).ne'
  rw [Finset.range_eq_Ico, sum_weight_Ico Z (Nat.zero_le _)]
  have hcast : (((⌈Z⌉₊ - 1 : ℕ) : ℝ) + 1) = (⌈Z⌉₊ : ℝ) := by
    rw [Nat.cast_sub hc]; push_cast; ring
  have htop : (1 : ℝ) ≤ (⌈Z⌉₊ : ℝ) / Z := by
    rw [le_div_iff₀ hZ, one_mul]; exact Nat.le_ceil Z
  rw [hcast, smoothEntry_of_one_le htop]
  simp

/-- The total history weight tends to `1` as the head climbs. -/
theorem tendsto_smoothEntry_one_div :
    Tendsto (fun Z : ℝ => smoothEntry (1 / Z)) atTop (𝓝 1) := by
  have hlow : Tendsto (fun Z : ℝ => 1 - 2 * (1 / Z) ^ 2) atTop (𝓝 1) := by
    have h : Tendsto (fun Z : ℝ => 1 / Z) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have := ((h.pow 2).const_mul 2).const_sub 1
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with Z hZ
    have hZ0 : 0 < Z := by linarith
    have hu : 1 / Z ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hZ
    have := one_sub_smoothEntry_le (by positivity) hu
    linarith
  · filter_upwards [eventually_gt_atTop 0] with Z hZ
    exact smoothEntry_le_one (by positivity)

/-! ## 3. The entry profile is the smooth glue; the head-derivative laws -/

/-- On the physical range the entry profile is `e · expNegInvGlue (1 − u²)`. -/
theorem smoothEntry_eq_glue {u : ℝ} (hu : -1 < u) :
    smoothEntry u = Real.exp 1 * expNegInvGlue (1 - u ^ 2) := by
  unfold smoothEntry expNegInvGlue
  by_cases h : u < 1
  · have hpos : 0 < 1 - u ^ 2 := by nlinarith
    rw [if_pos h, if_neg (not_le.mpr hpos), ← Real.exp_add]
    congr 1
    rw [sub_eq_add_neg, one_div]
  · have h1 : 1 ≤ u := not_lt.mp h
    have hle : 1 - u ^ 2 ≤ 0 := by nlinarith
    rw [if_neg h, if_pos hle, mul_zero]

theorem glue_hasDerivAt (x : ℝ) :
    HasDerivAt expNegInvGlue (deriv expNegInvGlue x) x :=
  ((expNegInvGlue.contDiff (n := 1)).differentiable (by simp) x).hasDerivAt

theorem smoothEntry_hasDerivAt {u : ℝ} (hu : -1 < u) :
    HasDerivAt smoothEntry
      (Real.exp 1 * (deriv expNegInvGlue (1 - u ^ 2) * (-(2 * u)))) u := by
  have hin : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-(2 * u)) u := by
    have := (hasDerivAt_pow 2 u).const_sub 1
    simpa using this
  have h := ((glue_hasDerivAt (1 - u ^ 2)).comp u hin).const_mul (Real.exp 1)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact smoothEntry_eq_glue hv

/-- The growth kernel `κ(u) = −u ψ′(u)`: the rate at which the window releases the phasor at
relative position `u = site/head`, per unit log-head. -/
def growthKernel (u : ℝ) : ℝ := -u * deriv smoothEntry u

theorem hasDerivAt_headWindow (k : ℕ) {Z : ℝ} (hZ : 0 < Z) :
    HasDerivAt (fun Z : ℝ => headWindow Z k)
      (deriv smoothEntry (((k + 1 : ℕ) : ℝ) / Z) * (-(((k + 1 : ℕ) : ℝ) / Z ^ 2))) Z := by
  unfold headWindow
  have hu : -1 < ((k + 1 : ℕ) : ℝ) / Z := by
    have : 0 < ((k + 1 : ℕ) : ℝ) / Z := by positivity
    linarith
  have hin : HasDerivAt (fun Z : ℝ => ((k + 1 : ℕ) : ℝ) / Z) (-(((k + 1 : ℕ) : ℝ) / Z ^ 2)) Z := by
    have h := (hasDerivAt_inv hZ.ne').const_mul ((k + 1 : ℕ) : ℝ)
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with v
      rw [div_eq_mul_inv]
    · rw [div_eq_mul_inv]; ring
  have hψ : HasDerivAt smoothEntry (deriv smoothEntry (((k + 1 : ℕ) : ℝ) / Z))
      (((k + 1 : ℕ) : ℝ) / Z) :=
    (smoothEntry_hasDerivAt hu).differentiableAt.hasDerivAt
  exact hψ.comp Z hin

/-- **The head-evolution law.**  At every head `Z > 0`, thresholds included, the grown fiber is
differentiable in the head; its derivative is the same input bank re-windowed by the growth
kernel, divided by `Z`.  New sites enter through `κ`, which vanishes at and beyond the head. -/
theorem hasDerivAt_finiteFiber_head (s : ℂ) {Z : ℝ} (hZ : 0 < Z) :
    HasDerivAt (fun Z : ℝ => finiteFiber Z s)
      (((1 / Z : ℝ) : ℂ) * ∑ k ∈ range (⌈Z⌉₊ + 1),
        ((growthKernel (((k + 1 : ℕ) : ℝ) / Z) : ℝ) : ℂ) * inputPhasor s k) Z := by
  have hlt : Z < ((⌈Z⌉₊ + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil Z
    push_cast
    linarith
  have hnhds : (fun Z' : ℝ => finiteFiber Z' s) =ᶠ[𝓝 Z]
      (fun Z' : ℝ => ∑ k ∈ range (⌈Z⌉₊ + 1), ((headWindow Z' k : ℝ) : ℂ) * inputPhasor s k) := by
    filter_upwards [Ioi_mem_nhds hZ, Iio_mem_nhds hlt] with Z' h1 h2
    exact finiteFiber_eq_sum_of_le h1 s (Nat.ceil_le.mpr h2.le)
  have hsum : HasDerivAt
      (fun Z' : ℝ => ∑ k ∈ range (⌈Z⌉₊ + 1), ((headWindow Z' k : ℝ) : ℂ) * inputPhasor s k)
      (∑ k ∈ range (⌈Z⌉₊ + 1),
        ((deriv smoothEntry (((k + 1 : ℕ) : ℝ) / Z) * (-(((k + 1 : ℕ) : ℝ) / Z ^ 2)) : ℝ) : ℂ)
          * inputPhasor s k) Z := by
    apply HasDerivAt.fun_sum
    intro k _
    exact ((hasDerivAt_headWindow k hZ).ofReal_comp).mul_const (inputPhasor s k)
  refine (hsum.congr_of_eventuallyEq hnhds).congr_deriv ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold growthKernel
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  push_cast
  field_simp

theorem continuousAt_finiteFiber_head (s : ℂ) {Z : ℝ} (hZ : 0 < Z) :
    ContinuousAt (fun Z : ℝ => finiteFiber Z s) Z :=
  (hasDerivAt_finiteFiber_head s hZ).continuousAt

/-- The head-evolution law in log-head time `τ = log Z`: `dG/dτ = Σ_k κ((k+1)/Z) V_s(k)`. -/
theorem hasDerivAt_finiteFiber_logHead (s : ℂ) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => finiteFiber (Real.exp τ) s)
      (∑ k ∈ range (⌈Real.exp τ⌉₊ + 1),
        ((growthKernel (((k + 1 : ℕ) : ℝ) / Real.exp τ) : ℝ) : ℂ) * inputPhasor s k) τ := by
  have h := (hasDerivAt_finiteFiber_head s (Real.exp_pos τ)).scomp τ (Real.hasDerivAt_exp τ)
  refine h.congr_deriv ?_
  rw [Complex.real_smul]
  have hne : (Real.exp τ : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos τ).ne'
  push_cast
  field_simp

/-- **The carrier-head law is differentiable in the ordinate**, with rate `speed · e^y / Δ > 0`. -/
theorem physicalHead_hasDerivAt (y : ℝ) :
    HasDerivAt physicalHead (Geometry.speed 1 3 (Real.exp y) * Real.exp y / Geometry.Delta) y := by
  have h1 := (Geometry.arclength_hasDerivAt 1 3 (Real.exp y)).comp y (Real.hasDerivAt_exp y)
  have h2 := h1.div_const Geometry.Delta
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards with v
  simp [physicalHead, Geometry.Nindex, Geometry.kClimb]

theorem physicalHead_pos (y : ℝ) : 0 < physicalHead y :=
  lt_of_lt_of_le (by positivity) (physicalHead_lower y)

/-- **Evolution in the carrier's ordinate.**  As the carrier advances by `dy`, the grown fiber
at the carrier's own head changes by the head rate times the head-evolution law. -/
theorem hasDerivAt_carrierHeadFiber (s : ℂ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => carrierHeadFiber y s)
      ((Geometry.speed 1 3 (Real.exp y) * Real.exp y / Geometry.Delta) •
        (((1 / physicalHead y : ℝ) : ℂ) * ∑ k ∈ range (⌈physicalHead y⌉₊ + 1),
          ((growthKernel (((k + 1 : ℕ) : ℝ) / physicalHead y) : ℝ) : ℂ) * inputPhasor s k)) y :=
  (hasDerivAt_finiteFiber_head s (physicalHead_pos y)).scomp y (physicalHead_hasDerivAt y)

/-! ## 4. The carrier scale inside the term -/

/-- The relative scale of carrier and fiber at site `k+1`: the carrier's radius at the site times
the warp amplitude of the phasor the fiber carries there.  (The fiber rides the carrier; the
phasors ride on the fiber.  This product compares the two scales at one site; it does not place a
phasor at the carrier's radius.) -/
def siteScaleProduct (s : ℂ) (k : ℕ) : ℝ :=
  Geometry.carrierRadius 1 3 (k + 1) * ‖inputPhasor s k‖

/-- **Factorization exposing `δ = ½ − Re s`**: site scale product `= A_{k+1} · (k+1)^{½−Re s}`. -/
theorem siteScaleProduct_eq (s : ℂ) (k : ℕ) :
    siteScaleProduct s k =
      (Geometry.carrierRadius 1 3 (k + 1) / Real.sqrt ((k : ℝ) + 1)) *
        ((k : ℝ) + 1) ^ (1 / 2 - s.re) := by
  unfold siteScaleProduct
  rw [norm_inputPhasor]
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have e : ((k : ℝ) + 1) ^ (1 / 2 - s.re) = Real.sqrt ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ (-s.re) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos]
    congr 1; try ring
  rw [e]
  have hs : Real.sqrt ((k : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  field_simp

/-- On the `(1,3)` carrier the prefactor tends to `1`: `carrierRadius 1 3 n / √n → 1`. -/
theorem tendsto_carrierRadius_div_sqrt :
    Tendsto (fun n : ℕ => Geometry.carrierRadius 1 3 n / Real.sqrt n) atTop (𝓝 1) := by
  have h := Geometry.carrierRadius_div_sqrt_tendsto 1 3 (by norm_num)
  have hc : Real.sqrt (3 * (Real.pi / 3) / Real.pi) = 1 := by
    rw [show (3 : ℝ) * (Real.pi / 3) / Real.pi = 1 by field_simp, Real.sqrt_one]
  rwa [hc] at h

/-! ## 5. The energy of the grown state and its head-law scaling -/

/-- The energy of the grown state: the sum of the squared moduli of its windowed phasors. -/
def energy (Z : ℝ) (σ : ℝ) : ℝ :=
  ∑ k ∈ range ⌈Z⌉₊, headWindow Z k ^ 2 * ((k : ℝ) + 1) ^ (-(2 * σ))

theorem energy_eq_sum_norm_sq (Z : ℝ) (s : ℂ) :
    energy Z s.re = ∑ k ∈ range ⌈Z⌉₊, ‖((headWindow Z k : ℝ) : ℂ) * inputPhasor s k‖ ^ 2 := by
  unfold energy
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, norm_inputPhasor, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast; ring

/-- The relative-position shape of the energy: a Riemann sum over `u = site/head`. -/
def energyShape (Z : ℝ) (σ : ℝ) : ℝ :=
  (1 / Z) * ∑ k ∈ range ⌈Z⌉₊, headWindow Z k ^ 2 * (((k + 1 : ℕ) : ℝ) / Z) ^ (-(2 * σ))

/-- **Head-law factorization of the energy**: `E_Z(σ) = Z^{1−2σ} · R_Z(σ)`.  The carrier's head
exponent `1` (sites accumulate linearly in the head) and the warp's energy exponent `−2σ`
combine into `1 − 2σ = 2(½ − σ)`. -/
theorem energy_eq (σ : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    energy Z σ = Z ^ (1 - 2 * σ) * energyShape Z σ := by
  unfold energy energyShape
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [Real.div_rpow hk.le hZ.le, Real.rpow_neg hZ.le, Real.rpow_sub hZ, Real.rpow_one]
  have h2 : Z ^ (2 * σ) ≠ 0 := (Real.rpow_pos_of_pos hZ _).ne'
  have hZ0 : Z ≠ 0 := hZ.ne'
  push_cast
  field_simp

theorem hasDerivAt_energy_head (σ : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    HasDerivAt (fun Z : ℝ => energy Z σ)
      ((1 / Z) * ∑ k ∈ range (⌈Z⌉₊ + 1),
        2 * headWindow Z k * growthKernel (((k + 1 : ℕ) : ℝ) / Z) * ((k : ℝ) + 1) ^ (-(2 * σ))) Z := by
  have hlt : Z < ((⌈Z⌉₊ + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil Z
    push_cast
    linarith
  have hnhds : (fun Z' : ℝ => energy Z' σ) =ᶠ[𝓝 Z]
      (fun Z' : ℝ => ∑ k ∈ range (⌈Z⌉₊ + 1), headWindow Z' k ^ 2 * ((k : ℝ) + 1) ^ (-(2 * σ))) := by
    filter_upwards [Ioi_mem_nhds hZ, Iio_mem_nhds hlt] with Z' h1 h2
    unfold energy
    apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.ceil_le.mpr (Set.mem_Iio.mp h2).le))
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rw [headWindow_eq_zero h1 hk]
    simp
  have hsum : HasDerivAt
      (fun Z' : ℝ => ∑ k ∈ range (⌈Z⌉₊ + 1), headWindow Z' k ^ 2 * ((k : ℝ) + 1) ^ (-(2 * σ)))
      (∑ k ∈ range (⌈Z⌉₊ + 1),
        (2 * headWindow Z k *
          (deriv smoothEntry (((k + 1 : ℕ) : ℝ) / Z) * (-(((k + 1 : ℕ) : ℝ) / Z ^ 2))))
          * ((k : ℝ) + 1) ^ (-(2 * σ))) Z := by
    apply HasDerivAt.fun_sum
    intro k _
    have h := ((hasDerivAt_headWindow k hZ).pow 2).mul_const (((k : ℝ) + 1) ^ (-(2 * σ)))
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    try ring
  refine (hsum.congr_of_eventuallyEq hnhds).congr_deriv ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold growthKernel
  have hZ0 : Z ≠ 0 := hZ.ne'
  field_simp

/-- The flux shape: the Riemann sum of `2 ψ κ u^{−2σ}` over `u = site/head`. -/
def fluxShape (Z σ : ℝ) : ℝ :=
  (1 / Z) * ∑ k ∈ range (⌈Z⌉₊ + 1),
    2 * headWindow Z k * growthKernel (((k + 1 : ℕ) : ℝ) / Z) * (((k + 1 : ℕ) : ℝ) / Z) ^ (-(2 * σ))

/-- **The energy flux per unit log-head carries exactly the factor `Z^{1−2σ} = Z^{2δ}`.**
This is the carrier scale (head law) and the fiber warp in one evolution equation. -/
theorem hasDerivAt_energy_logHead (σ τ : ℝ) :
    HasDerivAt (fun τ : ℝ => energy (Real.exp τ) σ)
      (Real.exp τ ^ (1 - 2 * σ) * fluxShape (Real.exp τ) σ) τ := by
  have h := (hasDerivAt_energy_head σ (Real.exp_pos τ)).comp τ (Real.hasDerivAt_exp τ)
  refine h.congr_deriv ?_
  unfold fluxShape
  have hZ : 0 < Real.exp τ := Real.exp_pos τ
  have hZ0 : Real.exp τ ≠ 0 := hZ.ne'
  have h2 : Real.exp τ ^ (2 * σ) ≠ 0 := (Real.rpow_pos_of_pos hZ _).ne'
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [Real.div_rpow hk.le hZ.le, Real.rpow_neg hZ.le, Real.rpow_sub hZ, Real.rpow_one]
  push_cast
  field_simp

/-! ## 6. Carrier gauge covariance -/

/-- The grown fiber read through the carrier-scaled log-weights `CarrierReadout.carrierLogWeight Δ k`. -/
def gaugedFiber (Δ Z : ℝ) (s : ℂ) : ℂ :=
  ∑ k ∈ range ⌈Z⌉₊, ((headWindow Z k : ℝ) : ℂ) *
    ((-1 : ℂ) ^ k * Complex.exp (-s * (CarrierReadout.carrierLogWeight Δ k : ℂ)))

/-- **Gauge covariance**: the harmonic scaling of the carrier by `Δ` multiplies the grown state
by the global factor `Δ^{−s}`; the vanishing locus is gauge-invariant for every warp rate. -/
theorem gaugedFiber_eq {Δ : ℝ} (hΔ : 0 < Δ) (Z : ℝ) (s : ℂ) :
    gaugedFiber Δ Z s = (Δ : ℂ) ^ (-s) * finiteFiber Z s := by
  unfold gaugedFiber
  rw [finiteFiber_eq_window_input, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold inputPhasor CarrierReadout.carrierLogWeight
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hΔc : (Δ : ℂ) ^ (-s) = Complex.exp (-s * (Real.log Δ : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hΔ.ne'), ← Complex.ofReal_log hΔ.le]
    congr 1; ring
  have hkc : ((k : ℂ) + 1) ^ (-s) = Complex.exp (-s * (Real.log ((k : ℝ) + 1) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hk.ne'),
      show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log hk.le]
    congr 1; ring
  rw [hΔc, hkc, Real.log_mul hΔ.ne' hk.ne']
  push_cast
  rw [show -s * ((Real.log Δ : ℂ) + (Real.log ((k : ℝ) + 1) : ℂ))
      = -s * (Real.log Δ : ℂ) + -s * (Real.log ((k : ℝ) + 1) : ℂ) by ring, Complex.exp_add]
  ring

end CriticalLinePhasor.GrownFiberEvolution
