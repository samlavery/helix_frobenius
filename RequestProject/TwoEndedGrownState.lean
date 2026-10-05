import RequestProject.GrownFiberEvolution

/-!
# The grown state as a transition, its two ends, and the zero equality case

Built on `GrownFiberEvolution` (window × input normalization, exact head-advance law).  No `ζ`/`L`
identity, functional equation, explicit formula, prime, zero set or zero-location statement is
used in any proof.

## A. Anatomy of the transition
Old-state transport is diagonal and real: each attached phasor is multiplied by the growth factor
`ψ((k+1)/Z')/ψ((k+1)/Z) ≥ 1` (`transport_multiplier`, `one_le_transport_multiplier`); its warp
amplitude and its spin are untouched.  The new input attaches flat: at the head the window weight
is `0` and the growth kernel is `0` (`newInput_flat`, via `smoothEntry_deriv_one`), so the boundary
contribution vanishes to first order and the whole first-order change is transport.  In the
carrier's own ordinate the actual state `carrierState σ y = finiteFiber (physicalHead y) (σ + iy)`
has two channels: the carrier's supply (growth kernel, coefficient head-rate/head) and the
carrier's rotation (the log-weights, coefficient `−i`) (`hasDerivAt_carrierState`).

## B. The two ends
The 3D end swap J is conjugation phasor by phasor and preserves every magnitude
(`norm_inputPhasor_conj`, `norm_finiteFiber_conj`).  The chart's reflected end `1 − s` carries the
reciprocal amplitude law: relative scale `(k+1)^{2 Re s − 1} = (k+1)^{−2δ}` (`end_scale_ratio`).
The two agree exactly at balance: equal end magnitudes at one site `≥ 2` force `Re s = ½`
(`re_eq_half_of_end_norms_eq`), and `1 − s = conj s ↔ Re s = ½` (`one_sub_eq_conj_iff`).  The
transition preserves end equality site by site (`transport_preserves_end_equality`).

## C. The opposed channels the one-branch state has, and the zero
`finiteFiber Z s = P − M` (odd sites minus even sites, `finiteFiber_eq_P_sub_M`); the zero is
exactly channel equality `P = M` (`finiteFiber_eq_zero_iff_channels_eq`).  The negative channel is
the whole unsigned fiber at half head, scaled by the warp's response `2^{−s}` to the carrier's
doubling (`negativeChannel_eq_unsigned_half`), so at a zero the unsigned fiber is dyadically
covariant with factor `2^{1−s}` (`unsigned_doubling_of_zero`): the `2` is the carrier's site count
under doubling, the `2^{−s}` the warp.  In modulus the two opposed channels have relative scale
`2^{1 − Re s}`, equal exactly at `Re s = 1` (`norm_unsigned_doubling_of_zero`,
`channel_scale_eq_one_iff`), not at `½`.
-/

open Complex Filter Topology Finset
open CriticalLinePhasor
open CriticalLinePhasor.CarrierHeadFiniteFiber
open CriticalLinePhasor.GrownFiber
open CriticalLinePhasor.GrownFiberEvolution

noncomputable section

namespace CriticalLinePhasor.TwoEndedGrownState

/-! ## A. Anatomy of the transition -/

theorem headWindow_nonneg (Z : ℝ) (k : ℕ) : 0 ≤ headWindow Z k :=
  smoothEntry_nonneg _

/-- Attached phasors only grow as the head advances. -/
theorem headWindow_mono {Z Z' : ℝ} (hZ : 0 < Z) (hZZ' : Z ≤ Z') (k : ℕ) :
    headWindow Z k ≤ headWindow Z' k := by
  unfold headWindow
  have hZ' : 0 < Z' := hZ.trans_le hZZ'
  have hab : ((k + 1 : ℕ) : ℝ) / Z' ≤ ((k + 1 : ℕ) : ℝ) / Z :=
    div_le_div_of_nonneg_left (by positivity) hZ hZZ'
  exact smoothEntry_antitoneOn (by simp only [Set.mem_Ici]; positivity)
    (by simp only [Set.mem_Ici]; positivity) hab

/-- **Old-state transport is diagonal and real**: the attached phasor at site `k+1` is multiplied
by `ψ((k+1)/Z')/ψ((k+1)/Z)`; spin and warp amplitude are untouched. -/
theorem transport_multiplier {Z Z' : ℝ} (s : ℂ) {k : ℕ} (hk : headWindow Z k ≠ 0) :
    ((headWindow Z' k : ℝ) : ℂ) * inputPhasor s k =
      ((headWindow Z' k / headWindow Z k : ℝ) : ℂ) *
        (((headWindow Z k : ℝ) : ℂ) * inputPhasor s k) := by
  have h : (headWindow Z k : ℂ) ≠ 0 := by exact_mod_cast hk
  push_cast
  field_simp

theorem one_le_transport_multiplier {Z Z' : ℝ} (hZ : 0 < Z) (hZZ' : Z ≤ Z') {k : ℕ}
    (hk : 0 < headWindow Z k) : 1 ≤ headWindow Z' k / headWindow Z k :=
  (one_le_div hk).mpr (headWindow_mono hZ hZZ' k)

theorem glue_deriv_zero : deriv expNegInvGlue 0 = 0 := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) 0
  have h' : HasDerivAt expNegInvGlue
      (((Polynomial.X ^ 2 * ((1 : Polynomial ℝ) - Polynomial.derivative (R := ℝ) 1)).eval
        (0 : ℝ)⁻¹) * expNegInvGlue 0) 0 := by
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with x
    simp
  rw [h'.deriv, expNegInvGlue.zero, mul_zero]

/-- The entry profile is flat at the head: `ψ′(1) = 0`. -/
theorem smoothEntry_deriv_one : deriv smoothEntry 1 = 0 := by
  rw [(smoothEntry_hasDerivAt (by norm_num : (-1 : ℝ) < 1)).deriv]
  simp [glue_deriv_zero]

theorem growthKernel_one : growthKernel 1 = 0 := by
  simp [growthKernel, smoothEntry_deriv_one]

/-- **The new input attaches flat**: the phasor whose site is the head has window weight `0` and
growth rate `0`.  The boundary contribution to the transition vanishes to first order. -/
theorem newInput_flat {Z : ℝ} (hZ : 0 < Z) {k : ℕ} (hk : ((k + 1 : ℕ) : ℝ) = Z) :
    headWindow Z k = 0 ∧ growthKernel (((k + 1 : ℕ) : ℝ) / Z) = 0 := by
  constructor
  · unfold headWindow
    rw [hk, div_self hZ.ne']
    exact smoothEntry_of_one_le le_rfl
  · rw [hk, div_self hZ.ne']
    exact growthKernel_one

/-! ## B. The two ends -/

/-- The 3D end swap J is conjugation phasor by phasor: it preserves every phasor magnitude. -/
theorem norm_inputPhasor_conj (s : ℂ) (k : ℕ) :
    ‖inputPhasor ((starRingEnd ℂ) s) k‖ = ‖inputPhasor s k‖ := by
  rw [norm_inputPhasor, norm_inputPhasor, Complex.conj_re]

/-- J preserves the magnitude of the whole grown state. -/
theorem norm_finiteFiber_conj (Z : ℝ) (s : ℂ) :
    ‖finiteFiber Z ((starRingEnd ℂ) s)‖ = ‖finiteFiber Z s‖ := by
  rw [finiteFiber_conj, Complex.norm_conj]

/-- The chart's reflected end `1 − s` carries the reciprocal amplitude law. -/
theorem norm_inputPhasor_reflect (s : ℂ) (k : ℕ) :
    ‖inputPhasor (1 - s) k‖ = ((k : ℝ) + 1) ^ (-(1 - s.re)) := by
  rw [norm_inputPhasor, Complex.sub_re, Complex.one_re]

/-- Relative scale of the two chart ends at site `k+1`: `(k+1)^{2 Re s − 1} = (k+1)^{−2δ}`. -/
theorem end_scale_ratio (s : ℂ) (k : ℕ) :
    ‖inputPhasor (1 - s) k‖ = ((k : ℝ) + 1) ^ (2 * s.re - 1) * ‖inputPhasor s k‖ := by
  rw [norm_inputPhasor_reflect, norm_inputPhasor, ← Real.rpow_add (by positivity)]
  congr 1; ring

/-- **The equality case.**  Equal magnitudes of the two chart ends at one site `k+1 ≥ 2` force
`Re s = ½`. -/
theorem re_eq_half_of_end_norms_eq {s : ℂ} {k : ℕ} (hk : 1 ≤ k)
    (h : ‖inputPhasor (1 - s) k‖ = ‖inputPhasor s k‖) : s.re = 1 / 2 := by
  rw [norm_inputPhasor_reflect, norm_inputPhasor] at h
  have hb : (1 : ℝ) < (k : ℝ) + 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have := (Real.strictMono_rpow_of_base_gt_one hb).injective h
  linarith

theorem end_norms_eq_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) (k : ℕ) :
    ‖inputPhasor (1 - s) k‖ = ‖inputPhasor s k‖ := by
  rw [norm_inputPhasor_reflect, norm_inputPhasor, hs]
  norm_num

/-- On the line the chart's reflected end is the conjugate end, and only there. -/
theorem one_sub_eq_conj_iff (s : ℂ) : 1 - s = (starRingEnd ℂ) s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  · intro h
    apply Complex.ext
    · simp; linarith
    · simp

/-- The transition preserves end equality site by site: the growth multiplier is a common real
factor. -/
theorem transport_preserves_end_equality (Z : ℝ) (s : ℂ) (k : ℕ) :
    ‖((headWindow Z k : ℝ) : ℂ) * inputPhasor (1 - s) k‖
        = ‖((headWindow Z k : ℝ) : ℂ) * inputPhasor s k‖
      ↔ headWindow Z k = 0 ∨ ‖inputPhasor (1 - s) k‖ = ‖inputPhasor s k‖ := by
  rw [norm_mul, norm_mul, Complex.norm_real]
  constructor
  · intro h
    by_cases hw : headWindow Z k = 0
    · exact Or.inl hw
    · right
      have : ‖headWindow Z k‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      exact mul_left_cancel₀ this h
  · rintro (hw | h)
    · simp [hw]
    · rw [h]

/-! ## C. The opposed channels inside the one-branch state, and the zero -/

/-- The unsigned grown fiber over all sites at head `W`. -/
def unsignedFiber (W : ℝ) (s : ℂ) : ℂ :=
  ∑ k ∈ range ⌈W⌉₊, ((headWindow W k : ℝ) : ℂ) * ((k : ℂ) + 1) ^ (-s)

theorem unsignedFiber_eq_sum_of_le {W : ℝ} (hW : 0 < W) (s : ℂ) {M : ℕ} (hM : ⌈W⌉₊ ≤ M) :
    unsignedFiber W s = ∑ k ∈ range M, ((headWindow W k : ℝ) : ℂ) * ((k : ℂ) + 1) ^ (-s) := by
  unfold unsignedFiber
  apply Finset.sum_subset (Finset.range_subset_range.mpr hM)
  intro k _ hk
  rw [Finset.mem_range, not_lt] at hk
  rw [headWindow_eq_zero hW hk]
  simp

/-- The positive channel: the odd sites `2j+1`. -/
def positiveChannel (Z : ℝ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ range N, ((headWindow Z (2 * j) : ℝ) : ℂ) * (((2 * j : ℕ) : ℂ) + 1) ^ (-s)

/-- The negative channel: the even sites `2j+2`. -/
def negativeChannel (Z : ℝ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ range N, ((headWindow Z (2 * j + 1) : ℝ) : ℂ) * (((2 * j + 1 : ℕ) : ℂ) + 1) ^ (-s)

theorem sum_range_two_mul (f : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ range (2 * N), f k = ∑ j ∈ range N, f (2 * j) + ∑ j ∈ range N, f (2 * j + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- **The one-branch grown state is `P − M`.** -/
theorem finiteFiber_eq_P_sub_M {Z : ℝ} (hZ : 0 < Z) (s : ℂ) {N : ℕ} (hN : ⌈Z⌉₊ ≤ 2 * N) :
    finiteFiber Z s = positiveChannel Z s N - negativeChannel Z s N := by
  rw [finiteFiber_eq_sum_of_le hZ s hN, sum_range_two_mul]
  unfold positiveChannel negativeChannel inputPhasor
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_mul]
    simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ, pow_mul]
    simp

theorem unsignedFiber_eq_P_add_M {Z : ℝ} (hZ : 0 < Z) (s : ℂ) {N : ℕ} (hN : ⌈Z⌉₊ ≤ 2 * N) :
    unsignedFiber Z s = positiveChannel Z s N + negativeChannel Z s N := by
  rw [unsignedFiber_eq_sum_of_le hZ s hN, sum_range_two_mul]
  rfl

/-- **The zero is channel equality**: `G_Z(s) = 0 ↔ P = M`. -/
theorem finiteFiber_eq_zero_iff_channels_eq {Z : ℝ} (hZ : 0 < Z) (s : ℂ) {N : ℕ}
    (hN : ⌈Z⌉₊ ≤ 2 * N) :
    finiteFiber Z s = 0 ↔ positiveChannel Z s N = negativeChannel Z s N := by
  rw [finiteFiber_eq_P_sub_M hZ s hN, sub_eq_zero]

/-- The negative channel is the whole fiber at half head, scaled by the warp's response `2^{−s}`
to the carrier's doubling of the sites. -/
theorem negativeChannel_eq (Z : ℝ) (s : ℂ) (N : ℕ) :
    negativeChannel Z s N = (2 : ℂ) ^ (-s) *
      ∑ j ∈ range N, ((headWindow (Z / 2) j : ℝ) : ℂ) * ((j : ℂ) + 1) ^ (-s) := by
  unfold negativeChannel headWindow
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hw : (((2 * j + 1 + 1 : ℕ) : ℝ) / Z) = ((j + 1 : ℕ) : ℝ) / (Z / 2) := by
    push_cast
    rw [div_div_eq_mul_div]
    ring
  have hc : (((2 * j + 1 : ℕ) : ℂ) + 1) ^ (-s) = (2 : ℂ) ^ (-s) * ((j : ℂ) + 1) ^ (-s) := by
    have h2 : (((2 * j + 1 : ℕ) : ℂ) + 1) = ((2 : ℝ) : ℂ) * (((j : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h2, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    push_cast
    rfl
  rw [hw, hc]
  ring

theorem negativeChannel_eq_unsigned_half {Z : ℝ} (hZ : 0 < Z) (s : ℂ) {N : ℕ}
    (hN : ⌈Z⌉₊ ≤ 2 * N) :
    negativeChannel Z s N = (2 : ℂ) ^ (-s) * unsignedFiber (Z / 2) s := by
  have hZ2 : Z ≤ 2 * N := (Nat.le_ceil Z).trans (by exact_mod_cast hN)
  have hM : ⌈Z / 2⌉₊ ≤ N := Nat.ceil_le.mpr (by linarith)
  rw [negativeChannel_eq Z s N, unsignedFiber_eq_sum_of_le (by positivity : 0 < Z / 2) s hM]

/-- **The zero as dyadic covariance of the unsigned fiber**: `U_Z(s) = 2^{1−s} · U_{Z/2}(s)`.
The `2` is the carrier's site count under doubling; the `2^{−s}` is the warp's response. -/
theorem unsigned_doubling_of_zero {Z : ℝ} (hZ : 0 < Z) {s : ℂ} {N : ℕ} (hN : ⌈Z⌉₊ ≤ 2 * N)
    (h0 : finiteFiber Z s = 0) :
    unsignedFiber Z s = (2 : ℂ) ^ (1 - s) * unsignedFiber (Z / 2) s := by
  have hPM := (finiteFiber_eq_zero_iff_channels_eq hZ s hN).mp h0
  rw [unsignedFiber_eq_P_add_M hZ s hN, hPM, negativeChannel_eq_unsigned_half hZ s hN, ← two_mul,
    ← mul_assoc]
  congr 1
  rw [show (1 : ℂ) - s = 1 + -s by ring, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]

/-- In modulus: at a zero the two opposed channels have relative scale `2^{1 − Re s}`. -/
theorem norm_unsigned_doubling_of_zero {Z : ℝ} (hZ : 0 < Z) {s : ℂ} {N : ℕ} (hN : ⌈Z⌉₊ ≤ 2 * N)
    (h0 : finiteFiber Z s = 0) :
    ‖unsignedFiber Z s‖ = (2 : ℝ) ^ (1 - s.re) * ‖unsignedFiber (Z / 2) s‖ := by
  rw [unsigned_doubling_of_zero hZ hN h0, norm_mul]
  congr 1
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  simp

/-- The two opposed channels have equal scale exactly at `Re s = 1`, not at `½`. -/
theorem channel_scale_eq_one_iff (σ : ℝ) : (2 : ℝ) ^ (1 - σ) = 1 ↔ σ = 1 := by
  constructor
  · intro h
    have h1 : (2 : ℝ) ^ (1 - σ) = (2 : ℝ) ^ (0 : ℝ) := by rw [h, Real.rpow_zero]
    have := (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective h1
    linarith
  · intro h
    rw [h, sub_self, Real.rpow_zero]

/-! ## D. The actual state in the carrier's ordinate: two channels, supply and rotation -/

/-- The actual carrier-driven state at ordinate `y`: head `physicalHead y`, spin at ordinate `y`,
warp exponent `σ`. -/
def carrierState (σ y : ℝ) : ℂ := finiteFiber (physicalHead y) ((σ : ℂ) + Complex.I * (y : ℂ))

theorem hasDerivAt_cpow_neg_ordinate (k : ℕ) (σ y : ℝ) :
    HasDerivAt (fun y : ℝ => ((k : ℂ) + 1) ^ (-((σ : ℂ) + Complex.I * (y : ℂ))))
      (-(Complex.I * (Real.log ((k : ℝ) + 1) : ℂ)) *
        ((k : ℂ) + 1) ^ (-((σ : ℂ) + Complex.I * (y : ℂ)))) y := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hne : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast hk.ne'
  have hlog : Complex.log ((k : ℂ) + 1) = (Real.log ((k : ℝ) + 1) : ℂ) := by
    rw [show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_log hk.le]
  have hy : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := (hasDerivAt_id y).ofReal_comp
  have h1 : HasDerivAt (fun y : ℝ => Complex.log ((k : ℂ) + 1) * -((σ : ℂ) + Complex.I * (y : ℂ)))
      (-(Complex.I * (Real.log ((k : ℝ) + 1) : ℂ))) y := by
    have := (((hy.const_mul Complex.I).const_add (σ : ℂ)).neg).const_mul (Complex.log ((k : ℂ) + 1))
    refine this.congr_deriv ?_
    rw [hlog]; ring
  have h2 := (Complex.hasDerivAt_exp _).comp y h1
  refine (h2.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with t
    simp only [Function.comp]
    rw [Complex.cpow_def_of_ne_zero hne]
  · rw [Complex.cpow_def_of_ne_zero hne]
    ring

/-- **The actual transition in the carrier's ordinate.**  Two channels: the carrier's supply
(growth kernel, coefficient head-rate/head) and the carrier's rotation (the log-weights,
coefficient `−i`). -/
theorem hasDerivAt_carrierState (σ y : ℝ) :
    HasDerivAt (fun y : ℝ => carrierState σ y)
      (((Geometry.speed 1 3 (Real.exp y) * Real.exp y / Geometry.Delta / physicalHead y : ℝ) : ℂ) *
          ∑ k ∈ range (⌈physicalHead y⌉₊ + 1),
            ((growthKernel (((k + 1 : ℕ) : ℝ) / physicalHead y) : ℝ) : ℂ) *
              inputPhasor ((σ : ℂ) + Complex.I * (y : ℂ)) k
        + ∑ k ∈ range (⌈physicalHead y⌉₊ + 1),
            ((headWindow (physicalHead y) k : ℝ) : ℂ) *
              (-(Complex.I * (Real.log ((k : ℝ) + 1) : ℂ)) *
                inputPhasor ((σ : ℂ) + Complex.I * (y : ℂ)) k)) y := by
  set Z := physicalHead y with hZdef
  have hZ : 0 < Z := physicalHead_pos y
  set M : ℕ := ⌈Z⌉₊ + 1 with hMdef
  have hlt : Z < (M : ℝ) := by
    have := Nat.le_ceil Z
    rw [hMdef]; push_cast; linarith
  have hcont : ContinuousAt physicalHead y := (physicalHead_hasDerivAt y).continuousAt
  have hnhds : (fun y' : ℝ => carrierState σ y') =ᶠ[𝓝 y]
      (fun y' : ℝ => ∑ k ∈ range M, ((headWindow (physicalHead y') k : ℝ) : ℂ) *
        inputPhasor ((σ : ℂ) + Complex.I * (y' : ℂ)) k) := by
    filter_upwards [hcont.tendsto.eventually (Iio_mem_nhds hlt)] with y' hy'
    exact finiteFiber_eq_sum_of_le (physicalHead_pos y') _ (Nat.ceil_le.mpr (Set.mem_Iio.mp hy').le)
  have hsum : HasDerivAt
      (fun y' : ℝ => ∑ k ∈ range M, ((headWindow (physicalHead y') k : ℝ) : ℂ) *
        inputPhasor ((σ : ℂ) + Complex.I * (y' : ℂ)) k)
      (∑ k ∈ range M,
        ((((deriv smoothEntry (((k + 1 : ℕ) : ℝ) / Z) * (-(((k + 1 : ℕ) : ℝ) / Z ^ 2))) *
            (Geometry.speed 1 3 (Real.exp y) * Real.exp y / Geometry.Delta) : ℝ) : ℂ) *
              inputPhasor ((σ : ℂ) + Complex.I * (y : ℂ)) k
          + ((headWindow Z k : ℝ) : ℂ) *
            ((-1 : ℂ) ^ k * (-(Complex.I * (Real.log ((k : ℝ) + 1) : ℂ)) *
              ((k : ℂ) + 1) ^ (-((σ : ℂ) + Complex.I * (y : ℂ))))))) y := by
    apply HasDerivAt.fun_sum
    intro k _
    have hc0 : HasDerivAt ((fun Z : ℝ => headWindow Z k) ∘ physicalHead)
        ((deriv smoothEntry (((k + 1 : ℕ) : ℝ) / Z) * (-(((k + 1 : ℕ) : ℝ) / Z ^ 2))) *
          (Geometry.speed 1 3 (Real.exp y) * Real.exp y / Geometry.Delta)) y :=
      (hasDerivAt_headWindow k hZ).comp y (physicalHead_hasDerivAt y)
    have hc : HasDerivAt (fun y' : ℝ => ((headWindow (physicalHead y') k : ℝ) : ℂ))
        ((((deriv smoothEntry (((k + 1 : ℕ) : ℝ) / Z) * (-(((k + 1 : ℕ) : ℝ) / Z ^ 2))) *
            (Geometry.speed 1 3 (Real.exp y) * Real.exp y / Geometry.Delta) : ℝ) : ℂ)) y :=
      hc0.ofReal_comp
    have hd : HasDerivAt (fun y' : ℝ => inputPhasor ((σ : ℂ) + Complex.I * (y' : ℂ)) k)
        ((-1 : ℂ) ^ k * (-(Complex.I * (Real.log ((k : ℝ) + 1) : ℂ)) *
          ((k : ℂ) + 1) ^ (-((σ : ℂ) + Complex.I * (y : ℂ))))) y :=
      (hasDerivAt_cpow_neg_ordinate k σ y).const_mul ((-1 : ℂ) ^ k)
    exact hc.mul hd
  refine (hsum.congr_of_eventuallyEq hnhds).congr_deriv ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold growthKernel inputPhasor
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  push_cast
  field_simp

end CriticalLinePhasor.TwoEndedGrownState
