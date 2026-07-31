import RequestProject.BesselOrderLadder

/-!
# Channel separation: finitely many Bessel order channels are linearly independent

Route (b)'s separation gap, converted from an unnamed obstruction into compiled theorems
plus ONE named input.  The engine: the order channel `cosKernel n` of `BesselOrderLadder`
vanishes at `z = 0` to order exactly `n` — its `m`-th Taylor-coefficient functional is the
trigonometric moment `∫_0^π cos(nθ)·cos^m θ dθ`, which vanishes for `m < n` and equals
`π/2^n` at `m = n`.  Hence finitely many distinct order channels are linearly independent,
hence rung data is jet-extractable from an aggregate.

* **S0 (orthogonality core)** — `cosMoment`, `cosMoment_eq_zero` (`m < n` kills the
  moment), `cosMoment_diag` (`∫_0^π cos(nθ)·cos^n θ dθ = π/2^n`, nonzero), by the
  product-to-sum recurrence `cosMoment (n+1) (m+1) = (cosMoment (n+2) m + cosMoment n m)/2`.
* **S1 (series form)** — `hasSum_cosKernel` / `cosKernel_eq_tsum`: the order channel IS its
  Taylor series `cosKernel n z = ∑_m ((-i)^m z^m / m!) · cosMoment n m`, by dominated
  interchange of the exponential series with the interval integral (the integrand is
  bounded by `|z|^m/m!` on the compact clock).  Combined with S0 this is the
  vanishing-order statement in Taylor-coefficient form: the `m`-th coefficient functional
  of `cosKernel n` vanishes for `m < n` and is nonzero at `m = n`.
* **The extraction engine** — `coeff_eq_zero_of_tsum_eq_zero`: a power series with
  factorial-decay coefficients that sums to `0` for every `z ∈ (0,1]` has all coefficients
  `0`; elementary strong induction with explicit tail bounds, no analytic-continuation
  machinery.
* **S2 (THE SEPARATOR)** — `channelSeparation`: if a finite `ℂ`-combination
  `∑_{n ∈ s} c n · cosKernel n z` vanishes for every real frequency `z`, then every
  coefficient vanishes.  Via `combo_moment_eq_zero` (aggregate vanishing forces every
  aggregated moment to vanish) and `moment_separation` (the moment system is triangular
  with nonzero diagonal at the minimal order).
* **S3 (ladder band form)** — `ladderSeparation`: through the compiled ladder
  `semicircleTransform_eq_orderLadder`, rung `r` contributes orders `{r, r+2}` with
  leading (order-`r`) coefficient `w r / 2`; aggregate vanishing of
  `∑_{r ∈ t} w r · semicircleTransform r z` forces every rung weight to vanish.  Proven
  for EVERY finite rung set `t` — the same-parity triangular band of the compiled ladder
  is the special case; no parity hypothesis is needed because full separation (S2)
  subsumes triangularity, with the minimal rung still the induction engine.
* **S4 (the named input, typed)** — `AggregateReality`: what certifier (b) must now
  supply — an aggregate identity with rung-resolved coefficients (the `reality` field:
  two rung-resolved readouts of the aggregate agree at every frequency).
  `AggregateReality.perRung` is the compiled conditional: given that input, the per-rung
  channel identities follow from S3.  `AggregateReality.diagonal` inhabits the type
  degenerately (type-level smoke test, no arithmetic content).

S0–S3 and the extraction engine are unconditional: interval-integral identities,
elementary series estimates, and finite triangular algebra.  S4's `reality` field for the
arithmetic aggregate is the ONE named remaining input — not proven in this file.
-/

open Complex intervalIntegral
open CriticalLinePhasor.BesselOrderLadder

namespace CriticalLinePhasor.ChannelSeparation

/-! ## S0: the trigonometric moments of the order channel -/

/-- The `(n, m)` trigonometric moment `∫_0^π cos(nθ)·cos^m θ dθ` — the `m`-th
Taylor-coefficient functional of the order-`n` channel (up to the factor `(-i)^m/m!`). -/
noncomputable def cosMoment (n m : ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi, Real.cos ((n : ℝ) * θ) * Real.cos θ ^ m

/-- The moment integrand is continuous. -/
theorem continuous_cosMomentIntegrand (n m : ℕ) :
    Continuous fun θ : ℝ => Real.cos ((n : ℝ) * θ) * Real.cos θ ^ m :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
    (Real.continuous_cos.pow m)

/-- `∫_0^π cos(kθ) dθ = 0` for `k ≠ 0`: the pure clock harmonic has no DC component on
the half-period. -/
theorem integral_cos_nat_mul {k : ℕ} (hk : k ≠ 0) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.cos ((k : ℝ) * θ)) = 0 := by
  have hknz : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (fun x : ℝ => Real.sin ((k : ℝ) * x) / k) (Real.cos ((k : ℝ) * θ)) θ := by
    intro θ _
    have h1 : HasDerivAt (fun x : ℝ => (k : ℝ) * x) (k : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (k : ℝ)
    have h2 : HasDerivAt (fun x : ℝ => Real.sin ((k : ℝ) * x))
        (Real.cos ((k : ℝ) * θ) * (k : ℝ)) θ :=
      (Real.hasDerivAt_sin ((k : ℝ) * θ)).comp θ h1
    have h3 := h2.div_const (k : ℝ)
    simpa [mul_div_assoc, div_self hknz] using h3
  have hint : IntervalIntegrable (fun θ : ℝ => Real.cos ((k : ℝ) * θ))
      MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [Real.sin_nat_mul_pi]

/-- **The product-to-sum recurrence of the moments**: from
`2·cos((n+1)θ)·cosθ = cos((n+2)θ) + cos(nθ)`. -/
theorem cosMoment_succ_succ (n m : ℕ) :
    cosMoment (n + 1) (m + 1) = (cosMoment (n + 2) m + cosMoment n m) / 2 := by
  have hkey : ∀ θ : ℝ,
      Real.cos (((n + 1 : ℕ) : ℝ) * θ) * Real.cos θ ^ (m + 1)
        = (Real.cos (((n + 2 : ℕ) : ℝ) * θ) * Real.cos θ ^ m
            + Real.cos ((n : ℝ) * θ) * Real.cos θ ^ m) / 2 := by
    intro θ
    have hsum : Real.cos (((n : ℝ) + 1) * θ + θ) + Real.cos (((n : ℝ) + 1) * θ - θ)
        = 2 * Real.cos (((n : ℝ) + 1) * θ) * Real.cos θ := by
      rw [Real.cos_add, Real.cos_sub]; ring
    have e1 : ((n + 1 : ℕ) : ℝ) * θ = ((n : ℝ) + 1) * θ := by push_cast; ring
    have e2 : ((n + 2 : ℕ) : ℝ) * θ = ((n : ℝ) + 1) * θ + θ := by push_cast; ring
    have e3 : (n : ℝ) * θ = ((n : ℝ) + 1) * θ - θ := by ring
    rw [e1, e2, e3, pow_succ]
    linear_combination (-(Real.cos θ ^ m) / 2) * hsum
  have hint1 : IntervalIntegrable (fun θ : ℝ => Real.cos (((n + 2 : ℕ) : ℝ) * θ) *
      Real.cos θ ^ m) MeasureTheory.volume 0 Real.pi :=
    (continuous_cosMomentIntegrand (n + 2) m).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ : ℝ => Real.cos ((n : ℝ) * θ) * Real.cos θ ^ m)
      MeasureTheory.volume 0 Real.pi :=
    (continuous_cosMomentIntegrand n m).intervalIntegrable _ _
  unfold cosMoment
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
      (Real.cos (((n + 2 : ℕ) : ℝ) * θ) * Real.cos θ ^ m
        + Real.cos ((n : ℝ) * θ) * Real.cos θ ^ m) / 2) (fun θ _ => hkey θ),
    intervalIntegral.integral_div, intervalIntegral.integral_add hint1 hint2]

/-- **Sub-diagonal vanishing**: `∫_0^π cos(nθ)·cos^m θ dθ = 0` for `m < n` — the
order-`n` channel vanishes at `z = 0` to order at least `n`. -/
theorem cosMoment_eq_zero : ∀ {m n : ℕ}, m < n → cosMoment n m = 0 := by
  intro m
  induction m with
  | zero =>
    intro n hn
    have h1 : cosMoment n 0 = ∫ θ in (0 : ℝ)..Real.pi, Real.cos ((n : ℝ) * θ) := by
      unfold cosMoment
      simp only [pow_zero, mul_one]
    rw [h1]
    exact integral_cos_nat_mul (by omega)
  | succ m ih =>
    intro n hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [cosMoment_succ_succ, ih (show m < n' + 2 by omega), ih (show m < n' by omega)]
    norm_num

/-- **The nonzero diagonal**: `∫_0^π cos(nθ)·cos^n θ dθ = π/2^n` — the order-`n` channel
vanishes at `z = 0` to order exactly `n`. -/
theorem cosMoment_diag (n : ℕ) : cosMoment n n = Real.pi / 2 ^ n := by
  induction n with
  | zero =>
    have h1 : cosMoment 0 0 = ∫ θ in (0 : ℝ)..Real.pi, (1 : ℝ) := by
      unfold cosMoment
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp
    rw [h1]
    simp
  | succ n ih =>
    rw [cosMoment_succ_succ, cosMoment_eq_zero (show n < n + 2 by omega), ih, pow_succ]
    ring

/-- The uniform moment bound `|cosMoment n m| ≤ π` — the domination input of S1. -/
theorem abs_cosMoment_le (n m : ℕ) : |cosMoment n m| ≤ Real.pi := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
    (f := fun θ : ℝ => Real.cos ((n : ℝ) * θ) * Real.cos θ ^ m) (a := 0) (b := Real.pi) ?_
  · unfold cosMoment
    simpa [Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le] using h
  · intro θ _
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_one₀ (Real.abs_cos_le_one _) (pow_nonneg (abs_nonneg _) m)
      (pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _))

/-! ## S1: the order channel is its Taylor series -/

/-- The `m`-th term of the order-channel series, before integration: the `m`-th
exponential-series term of the integrand of `cosKernel n z`. -/
noncomputable def orderSeriesTerm (n : ℕ) (z : ℝ) (m : ℕ) (θ : ℝ) : ℂ :=
  ((-I) ^ m * (z : ℂ) ^ m / (m.factorial : ℂ)) *
    ((Real.cos ((n : ℝ) * θ) * Real.cos θ ^ m : ℝ) : ℂ)

/-- The series term is continuous in the clock variable. -/
theorem continuous_orderSeriesTerm (n : ℕ) (z : ℝ) (m : ℕ) :
    Continuous (orderSeriesTerm n z m) :=
  continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_cosMomentIntegrand n m))

/-- Pointwise on the clock, the exponential series of the order-channel integrand: the
`orderSeriesTerm`s sum to `cos(nθ)·e^{-iz·cosθ}`. -/
theorem hasSum_cosKernelIntegrand (n : ℕ) (z θ : ℝ) :
    HasSum (fun m : ℕ => orderSeriesTerm n z m θ) (cosKernelIntegrand n z θ) := by
  have hexp : HasSum
      (fun m : ℕ => (-I * (z : ℂ) * ((Real.cos θ : ℝ) : ℂ)) ^ m / (m.factorial : ℂ))
      (Complex.exp (-I * (z : ℂ) * ((Real.cos θ : ℝ) : ℂ))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have h2 := hexp.mul_left ((Real.cos ((n : ℝ) * θ) : ℝ) : ℂ)
  have hfun : (fun m : ℕ => ((Real.cos ((n : ℝ) * θ) : ℝ) : ℂ) *
      ((-I * (z : ℂ) * ((Real.cos θ : ℝ) : ℂ)) ^ m / (m.factorial : ℂ)))
      = fun m : ℕ => orderSeriesTerm n z m θ := by
    funext m
    unfold orderSeriesTerm
    rw [mul_pow, mul_pow]
    push_cast
    ring
  rw [hfun] at h2
  exact h2

/-- The norm of the series coefficient. -/
theorem norm_orderCoeff (z : ℝ) (m : ℕ) :
    ‖(-I) ^ m * (z : ℂ) ^ m / (m.factorial : ℂ)‖ = |z| ^ m / (m.factorial : ℝ) := by
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]

/-- The series term is dominated by `|z|^m/m!` on the whole clock. -/
theorem norm_orderSeriesTerm_le (n : ℕ) (z : ℝ) (m : ℕ) (θ : ℝ) :
    ‖orderSeriesTerm n z m θ‖ ≤ |z| ^ m / (m.factorial : ℝ) := by
  unfold orderSeriesTerm
  rw [norm_mul, norm_orderCoeff]
  have h2 : ‖((Real.cos ((n : ℝ) * θ) * Real.cos θ ^ m : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_one₀ (Real.abs_cos_le_one _) (pow_nonneg (abs_nonneg _) m)
      (pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _))
  have hnn : (0 : ℝ) ≤ |z| ^ m / (m.factorial : ℝ) := by positivity
  calc |z| ^ m / (m.factorial : ℝ) * ‖((Real.cos ((n : ℝ) * θ) * Real.cos θ ^ m : ℝ) : ℂ)‖
      ≤ |z| ^ m / (m.factorial : ℝ) * 1 := mul_le_mul_of_nonneg_left h2 hnn
    _ = |z| ^ m / (m.factorial : ℝ) := mul_one _

/-- **S1, the series form of the order channel**:
`cosKernel n z = ∑_m ((-i)^m z^m / m!) · cosMoment n m`, as a `HasSum`.  Dominated
interchange of the exponential series with the interval integral; with S0
(`cosMoment_eq_zero`, `cosMoment_diag`) this exhibits `z = 0` as a zero of order
exactly `n`: the `m`-th Taylor-coefficient functional vanishes for `m < n` and equals
`(-i)^n π/(2^n n!) ≠ 0` at `m = n`. -/
theorem hasSum_cosKernel (n : ℕ) (z : ℝ) :
    HasSum (fun m : ℕ => ((-I) ^ m * (z : ℂ) ^ m / (m.factorial : ℂ)) *
        ((cosMoment n m : ℝ) : ℂ))
      (cosKernel n z) := by
  have hFint : ∀ m : ℕ, MeasureTheory.Integrable (orderSeriesTerm n z m)
      (MeasureTheory.volume.restrict (Set.Ioc 0 Real.pi)) := fun m =>
    (continuous_orderSeriesTerm n z m).integrableOn_Ioc
  have hFnormint : ∀ m : ℕ,
      (∫ θ, ‖orderSeriesTerm n z m θ‖
          ∂(MeasureTheory.volume.restrict (Set.Ioc 0 Real.pi)))
        ≤ Real.pi * (|z| ^ m / (m.factorial : ℝ)) := by
    intro m
    have hconstint : MeasureTheory.Integrable (fun _ : ℝ => |z| ^ m / (m.factorial : ℝ))
        (MeasureTheory.volume.restrict (Set.Ioc 0 Real.pi)) :=
      continuous_const.integrableOn_Ioc
    have hle := MeasureTheory.integral_mono (hFint m).norm hconstint
      (fun θ => norm_orderSeriesTerm_le n z m θ)
    have hconst : (∫ _ : ℝ, (|z| ^ m / (m.factorial : ℝ))
        ∂(MeasureTheory.volume.restrict (Set.Ioc 0 Real.pi)))
        = Real.pi * (|z| ^ m / (m.factorial : ℝ)) := by
      simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def,
        Real.volume_Ioc, ENNReal.toReal_ofReal Real.pi_pos.le]
    rw [hconst] at hle
    exact hle
  have hsummable : Summable (fun m : ℕ => ∫ θ, ‖orderSeriesTerm n z m θ‖
      ∂(MeasureTheory.volume.restrict (Set.Ioc 0 Real.pi))) :=
    Summable.of_nonneg_of_le
      (fun m => MeasureTheory.integral_nonneg fun θ => norm_nonneg _)
      hFnormint ((Real.summable_pow_div_factorial |z|).mul_left Real.pi)
  have hHS := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hsummable
  have hterm : ∀ m : ℕ,
      (∫ θ, orderSeriesTerm n z m θ
          ∂(MeasureTheory.volume.restrict (Set.Ioc 0 Real.pi)))
        = ((-I) ^ m * (z : ℂ) ^ m / (m.factorial : ℂ)) * ((cosMoment n m : ℝ) : ℂ) := by
    intro m
    rw [← intervalIntegral.integral_of_le Real.pi_pos.le]
    unfold orderSeriesTerm
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [intervalIntegral.integral_ofReal]
    unfold cosMoment
    rfl
  have htotal : (∫ θ, (∑' m : ℕ, orderSeriesTerm n z m θ)
      ∂(MeasureTheory.volume.restrict (Set.Ioc 0 Real.pi))) = cosKernel n z := by
    have hfun2 : (fun θ : ℝ => ∑' m : ℕ, orderSeriesTerm n z m θ) = cosKernelIntegrand n z :=
      funext fun θ => (hasSum_cosKernelIntegrand n z θ).tsum_eq
    rw [hfun2, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    rfl
  rw [htotal] at hHS
  simpa only [hterm] using hHS

/-- S1 in `tsum` form: the order channel equals its Taylor series at every frequency. -/
theorem cosKernel_eq_tsum (n : ℕ) (z : ℝ) :
    cosKernel n z = ∑' m : ℕ,
      ((-I) ^ m * (z : ℂ) ^ m / (m.factorial : ℂ)) * ((cosMoment n m : ℝ) : ℂ) :=
  (hasSum_cosKernel n z).tsum_eq.symm

/-- Summability of the order-channel series. -/
theorem summable_cosKernel_series (n : ℕ) (z : ℝ) :
    Summable fun m : ℕ =>
      ((-I) ^ m * (z : ℂ) ^ m / (m.factorial : ℂ)) * ((cosMoment n m : ℝ) : ℂ) :=
  (hasSum_cosKernel n z).summable

/-! ## The extraction engine -/

/-- **The Taylor-coefficient extraction engine**: a power series with factorial-decay
coefficients (`‖a m‖ ≤ C/m!`) whose sum vanishes at every `z ∈ (0, 1]` has all
coefficients zero.  Elementary strong induction: strip the known-zero head, divide by
`z^k`, and squeeze the tail bound `‖a k‖ ≤ C·E·z` as `z → 0⁺` (with `E = ∑ 1/m!`).
No analytic-continuation or formal-power-series machinery. -/
theorem coeff_eq_zero_of_tsum_eq_zero (a : ℕ → ℂ) (C : ℝ)
    (hb : ∀ m : ℕ, ‖a m‖ ≤ C / (m.factorial : ℝ))
    (h : ∀ z : ℝ, 0 < z → z ≤ 1 → (∑' m : ℕ, a m * (z : ℂ) ^ m) = 0) :
    ∀ m, a m = 0 := by
  have hEsum : Summable (fun m : ℕ => (1 : ℝ) / (m.factorial : ℝ)) := by
    simpa using Real.summable_pow_div_factorial 1
  set E : ℝ := ∑' m : ℕ, (1 : ℝ) / (m.factorial : ℝ) with hEdef
  intro m
  induction m using Nat.strong_induction_on with
  | _ k ih =>
    have key : ∀ z : ℝ, 0 < z → z ≤ 1 → ‖a k‖ ≤ C * E * z := by
      intro z hz hz1
      have hzc : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
      have hnormpow : ∀ i : ℕ, ‖(z : ℂ) ^ i‖ = z ^ i := by
        intro i
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz]
      have hfaclem : ∀ i j : ℕ, C / ((i + j).factorial : ℝ) ≤ C / (i.factorial : ℝ) := by
        intro i j
        have hC0 : 0 ≤ C := by
          have h0 := (norm_nonneg (a 0)).trans (hb 0)
          simpa using h0
        gcongr
        exact Nat.le_add_right i j
      have hshift : ∀ j : ℕ, Summable (fun i : ℕ => a (i + j) * (z : ℂ) ^ i) := by
        intro j
        apply Summable.of_norm_bounded ((Real.summable_pow_div_factorial z).mul_left C)
        intro i
        rw [norm_mul, hnormpow]
        calc ‖a (i + j)‖ * z ^ i
            ≤ C / (i.factorial : ℝ) * z ^ i :=
              mul_le_mul_of_nonneg_right ((hb (i + j)).trans (hfaclem i j))
                (pow_nonneg hz.le i)
          _ = C * (z ^ i / (i.factorial : ℝ)) := by ring
      have hfin : (∑ i ∈ Finset.range k, a i * (z : ℂ) ^ i) = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [ih i (Finset.mem_range.mp hi), zero_mul]
      have htail : (∑' i : ℕ, a (i + k) * (z : ℂ) ^ (i + k)) = 0 := by
        have h2 := (by simpa using hshift 0 :
          Summable fun i : ℕ => a i * (z : ℂ) ^ i).sum_add_tsum_nat_add k
        rw [hfin, zero_add, h z hz hz1] at h2
        exact h2
      have hg : (∑' i : ℕ, a (i + k) * (z : ℂ) ^ i) = 0 := by
        have hfac : ∀ i : ℕ, a (i + k) * (z : ℂ) ^ (i + k)
            = (z : ℂ) ^ k * (a (i + k) * (z : ℂ) ^ i) := by
          intro i; rw [pow_add]; ring
        rw [tsum_congr hfac, tsum_mul_left] at htail
        rcases mul_eq_zero.mp htail with h' | h'
        · exact absurd h' (pow_ne_zero k hzc)
        · exact h'
      have hsplit : a k = -∑' i : ℕ, a (i + 1 + k) * (z : ℂ) ^ (i + 1) := by
        have h3 := (hshift k).tsum_eq_zero_add
        rw [hg] at h3
        simp only [zero_add, pow_zero, mul_one] at h3
        linear_combination -h3
      have hptb : ∀ i : ℕ, ‖a (i + 1 + k) * (z : ℂ) ^ (i + 1)‖
          ≤ C * z * ((1 : ℝ) / (i.factorial : ℝ)) := by
        intro i
        rw [norm_mul, hnormpow]
        have h1 : ‖a (i + 1 + k)‖ ≤ C / (i.factorial : ℝ) :=
          (hb (i + 1 + k)).trans (by
            have := hfaclem i (1 + k)
            rwa [← Nat.add_assoc] at this)
        have h2 : z ^ (i + 1) ≤ z := by
          calc z ^ (i + 1) ≤ z ^ 1 := pow_le_pow_of_le_one hz.le hz1 (by omega)
            _ = z := pow_one z
        have hC0 : 0 ≤ C := by
          have h0 := (norm_nonneg (a 0)).trans (hb 0)
          simpa using h0
        calc ‖a (i + 1 + k)‖ * z ^ (i + 1)
            ≤ C / (i.factorial : ℝ) * z :=
              mul_le_mul h1 h2 (pow_nonneg hz.le _) (by positivity)
          _ = C * z * ((1 : ℝ) / (i.factorial : ℝ)) := by ring
      have hmaj : Summable (fun i : ℕ => C * z * ((1 : ℝ) / (i.factorial : ℝ))) :=
        hEsum.mul_left _
      have hnormsummand : Summable
          (fun i : ℕ => ‖a (i + 1 + k) * (z : ℂ) ^ (i + 1)‖) :=
        Summable.of_nonneg_of_le (fun i => norm_nonneg _) hptb hmaj
      rw [hsplit, norm_neg]
      calc ‖∑' i : ℕ, a (i + 1 + k) * (z : ℂ) ^ (i + 1)‖
          ≤ ∑' i : ℕ, ‖a (i + 1 + k) * (z : ℂ) ^ (i + 1)‖ :=
            norm_tsum_le_tsum_norm hnormsummand
        _ ≤ ∑' i : ℕ, C * z * ((1 : ℝ) / (i.factorial : ℝ)) :=
            Summable.tsum_le_tsum hptb hnormsummand hmaj
        _ = C * z * E := by rw [tsum_mul_left]
        _ = C * E * z := by ring
    have hfinal : ∀ ε : ℝ, 0 < ε → ‖a k‖ ≤ ε := by
      intro ε hε
      by_cases hpos : 0 < C * E
      case neg =>
        have hle : C * E ≤ 0 := not_lt.mp hpos
        have h1 := key 1 one_pos le_rfl
        have h2 := norm_nonneg (a k)
        nlinarith
      case pos =>
        have hz : (0 : ℝ) < min 1 (ε / (C * E)) := lt_min one_pos (div_pos hε hpos)
        have h1 := key _ hz (min_le_left _ _)
        have h2 : C * E * min 1 (ε / (C * E)) ≤ C * E * (ε / (C * E)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hpos.le
        have h3 : C * E * (ε / (C * E)) = ε := by
          rw [mul_comm (C * E), div_mul_cancel₀ ε hpos.ne']
        linarith
    have hle0 : ‖a k‖ ≤ 0 :=
      le_of_forall_pos_le_add fun ε hε => by simpa using hfinal ε hε
    exact norm_le_zero_iff.mp hle0

/-! ## S2: the separator -/

/-- **Aggregate vanishing forces every aggregated moment to vanish**: if a finite
`ℂ`-combination of order channels (indexed through an order map `ord`) vanishes at every
real frequency, then every Taylor-moment combination vanishes.  S1 + the extraction
engine; only frequencies `z ∈ (0, 1]` are consumed. -/
theorem combo_moment_eq_zero {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ord : ι → ℕ)
    (h : ∀ z : ℝ, (∑ i ∈ s, c i * cosKernel (ord i) z) = 0) (m : ℕ) :
    (∑ i ∈ s, c i * ((cosMoment (ord i) m : ℝ) : ℂ)) = 0 := by
  have hz : ∀ z : ℝ, (∑' k : ℕ,
      (((-I) ^ k / (k.factorial : ℂ)) *
        ∑ i ∈ s, c i * ((cosMoment (ord i) k : ℝ) : ℂ)) * (z : ℂ) ^ k) = 0 := by
    intro z
    have h1 : ∀ k : ℕ,
        (((-I) ^ k / (k.factorial : ℂ)) *
            ∑ i ∈ s, c i * ((cosMoment (ord i) k : ℝ) : ℂ)) * (z : ℂ) ^ k
          = ∑ i ∈ s, c i * (((-I) ^ k * (z : ℂ) ^ k / (k.factorial : ℂ)) *
              ((cosMoment (ord i) k : ℝ) : ℂ)) := by
      intro k
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [tsum_congr h1, Summable.tsum_finsetSum
      (fun i _ => (summable_cosKernel_series (ord i) z).mul_left (c i))]
    have h2 : ∀ i ∈ s, (∑' k : ℕ, c i * (((-I) ^ k * (z : ℂ) ^ k / (k.factorial : ℂ)) *
        ((cosMoment (ord i) k : ℝ) : ℂ))) = c i * cosKernel (ord i) z := by
      intro i _
      rw [tsum_mul_left, ← cosKernel_eq_tsum]
    rw [Finset.sum_congr rfl h2]
    exact h z
  have hCbound : ∀ k : ℕ,
      ‖((-I) ^ k / (k.factorial : ℂ)) *
          ∑ i ∈ s, c i * ((cosMoment (ord i) k : ℝ) : ℂ)‖
        ≤ (Real.pi * ∑ i ∈ s, ‖c i‖) / (k.factorial : ℝ) := by
    intro k
    have h3 : ‖∑ i ∈ s, c i * ((cosMoment (ord i) k : ℝ) : ℂ)‖
        ≤ Real.pi * ∑ i ∈ s, ‖c i‖ := by
      calc ‖∑ i ∈ s, c i * ((cosMoment (ord i) k : ℝ) : ℂ)‖
          ≤ ∑ i ∈ s, ‖c i * ((cosMoment (ord i) k : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ s, ‖c i‖ * Real.pi := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (abs_cosMoment_le _ _) (norm_nonneg _)
        _ = Real.pi * ∑ i ∈ s, ‖c i‖ := by rw [← Finset.sum_mul]; ring
    have h4 : ‖((-I) ^ k / (k.factorial : ℂ))‖ = 1 / (k.factorial : ℝ) := by
      rw [norm_div, norm_pow, norm_neg, Complex.norm_I, one_pow, Complex.norm_natCast]
    rw [norm_mul, h4]
    calc 1 / (k.factorial : ℝ) * ‖∑ i ∈ s, c i * ((cosMoment (ord i) k : ℝ) : ℂ)‖
        = ‖∑ i ∈ s, c i * ((cosMoment (ord i) k : ℝ) : ℂ)‖ / (k.factorial : ℝ) := by
          ring
      _ ≤ (Real.pi * ∑ i ∈ s, ‖c i‖) / (k.factorial : ℝ) := by
          gcongr
  have hext := coeff_eq_zero_of_tsum_eq_zero _ _ hCbound (fun z hz1 _ => hz z) m
  rcases mul_eq_zero.mp hext with h' | h'
  · exact absurd h' (div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
      (Nat.cast_ne_zero.mpr m.factorial_ne_zero))
  · exact h'

/-- **The triangular moment system separates**: if every moment combination
`∑_{n ∈ s} c n · cosMoment n m` vanishes, every coefficient vanishes — at the minimal
order `n₀` of `s` the system is triangular (`cosMoment n n₀ = 0` for `n > n₀`) with
nonzero diagonal (`cosMoment n₀ n₀ = π/2^{n₀}`); strong induction on the finite set. -/
theorem moment_separation (c : ℕ → ℂ) (s : Finset ℕ) :
    (∀ m : ℕ, (∑ n ∈ s, c n * ((cosMoment n m : ℝ) : ℂ)) = 0) → ∀ n ∈ s, c n = 0 := by
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro h n hn
    have hne : s.Nonempty := ⟨n, hn⟩
    have hmin : s.min' hne ∈ s := s.min'_mem hne
    have hzero : c (s.min' hne) = 0 := by
      have hkey := h (s.min' hne)
      rw [Finset.sum_eq_single_of_mem (s.min' hne) hmin (fun b hb hbne => ?_)] at hkey
      · rcases mul_eq_zero.mp hkey with h' | h'
        · exact h'
        · exfalso
          rw [cosMoment_diag] at h'
          exact (by positivity : (Real.pi / 2 ^ s.min' hne : ℝ) ≠ 0) (by exact_mod_cast h')
      · have hlt : s.min' hne < b := lt_of_le_of_ne (s.min'_le b hb) (Ne.symm hbne)
        rw [cosMoment_eq_zero hlt]
        simp
    by_cases heq : n = s.min' hne
    · rw [heq]; exact hzero
    · refine ih (s.erase (s.min' hne)) (Finset.erase_ssubset hmin) ?_ n
        (Finset.mem_erase.mpr ⟨heq, hn⟩)
      intro m
      have hm := h m
      rw [← Finset.add_sum_erase s _ hmin, hzero, zero_mul, zero_add] at hm
      exact hm

/-- **S2, THE SEPARATOR**: finitely many distinct order channels are linearly
independent as functions of the real frequency — if `∑_{n ∈ s} c n · cosKernel n z = 0`
for every `z : ℝ`, then every `c n` with `n ∈ s` vanishes.  (Only frequencies
`z ∈ (0, 1]` are consumed by the proof.)  Rung data is therefore jet-extractable from
any aggregate of order channels. -/
theorem channelSeparation (s : Finset ℕ) (c : ℕ → ℂ)
    (h : ∀ z : ℝ, (∑ n ∈ s, c n * cosKernel n z) = 0) :
    ∀ n ∈ s, c n = 0 :=
  moment_separation c s fun m => combo_moment_eq_zero s c id h m

/-! ## S3: the separation theorem for the compiled ladder -/

/-- The ladder aggregate's moments vanish: through the compiled
`semicircleTransform_eq_orderLadder`, an aggregate `∑_{r ∈ t} w r · semicircleTransform r`
that vanishes at every frequency has all its band moments
`∑_{r ∈ t} w r · (cosMoment r m − cosMoment (r+2) m)` equal to zero. -/
theorem ladder_moment_eq_zero (t : Finset ℕ) (w : ℕ → ℂ)
    (h : ∀ z : ℝ, (∑ r ∈ t, w r * semicircleTransform r z) = 0) (m : ℕ) :
    (∑ r ∈ t, w r * (((cosMoment r m : ℝ) : ℂ) - ((cosMoment (r + 2) m : ℝ) : ℂ))) = 0 := by
  classical
  set ord : ℕ × Bool → ℕ := fun p => p.1 + cond p.2 2 0 with hord
  set cc : ℕ × Bool → ℂ := fun p => cond p.2 (-w p.1) (w p.1) / 2 with hcc
  have hagg : ∀ z : ℝ,
      (∑ p ∈ t ×ˢ (Finset.univ : Finset Bool), cc p * cosKernel (ord p) z) = 0 := by
    intro z
    rw [Finset.sum_product]
    have h1 : ∀ r ∈ t, (∑ b : Bool, cc (r, b) * cosKernel (ord (r, b)) z)
        = w r * semicircleTransform r z := by
      intro r _
      rw [Fintype.sum_bool]
      simp only [hord, hcc, cond_true, cond_false, add_zero]
      rw [semicircleTransform_eq_orderLadder]
      ring
    rw [Finset.sum_congr rfl h1]
    exact h z
  have hm := combo_moment_eq_zero (t ×ˢ (Finset.univ : Finset Bool)) cc ord hagg m
  rw [Finset.sum_product] at hm
  have h2 : ∀ r ∈ t, (∑ b : Bool, cc (r, b) * ((cosMoment (ord (r, b)) m : ℝ) : ℂ))
      = (1 / 2 : ℂ) * (w r * (((cosMoment r m : ℝ) : ℂ)
          - ((cosMoment (r + 2) m : ℝ) : ℂ))) := by
    intro r _
    rw [Fintype.sum_bool]
    simp only [hord, hcc, cond_true, cond_false, add_zero]
    ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum] at hm
  rcases mul_eq_zero.mp hm with h' | h'
  · norm_num at h'
  · exact h'

/-- The band-moment system separates the rungs: triangularity at the minimal rung `r₀`
(`cosMoment r r₀ = 0` for `r > r₀` and `cosMoment (r+2) r₀ = 0` for every `r ∈ t`) with
nonzero diagonal `cosMoment r₀ r₀ = π/2^{r₀}`; strong induction on the finite rung set.
No parity hypothesis on `t` is needed. -/
theorem ladder_moment_separation (w : ℕ → ℂ) (t : Finset ℕ) :
    (∀ m : ℕ, (∑ r ∈ t, w r * (((cosMoment r m : ℝ) : ℂ)
        - ((cosMoment (r + 2) m : ℝ) : ℂ))) = 0) →
    ∀ r ∈ t, w r = 0 := by
  induction t using Finset.strongInduction with
  | _ t ih =>
    intro h r hr
    have hne : t.Nonempty := ⟨r, hr⟩
    have hmin : t.min' hne ∈ t := t.min'_mem hne
    have hzero : w (t.min' hne) = 0 := by
      have hkey := h (t.min' hne)
      rw [Finset.sum_eq_single_of_mem (t.min' hne) hmin (fun b hb hbne => ?_)] at hkey
      · rw [cosMoment_diag,
          cosMoment_eq_zero (show t.min' hne < t.min' hne + 2 by omega)] at hkey
        rcases mul_eq_zero.mp hkey with h' | h'
        · exact h'
        · exfalso
          rw [Complex.ofReal_zero, sub_zero] at h'
          exact (by positivity : (Real.pi / 2 ^ t.min' hne : ℝ) ≠ 0) (by exact_mod_cast h')
      · have hlt : t.min' hne < b := lt_of_le_of_ne (t.min'_le b hb) (Ne.symm hbne)
        rw [cosMoment_eq_zero hlt, cosMoment_eq_zero (show t.min' hne < b + 2 by omega)]
        simp
    by_cases heq : r = t.min' hne
    · rw [heq]; exact hzero
    · refine ih (t.erase (t.min' hne)) (Finset.erase_ssubset hmin) ?_ r
        (Finset.mem_erase.mpr ⟨heq, hr⟩)
      intro m
      have hm := h m
      rw [← Finset.add_sum_erase t _ hmin, hzero, zero_mul, zero_add] at hm
      exact hm

/-- **S3, the separation theorem for the compiled ladder**: rung `r` enters the compiled
dual side only through orders `{r, r+2}` (`semicircleTransform_eq_orderLadder`), with
leading order-`r` coefficient `w r / 2`; if the rung aggregate
`∑_{r ∈ t} w r · semicircleTransform r z` vanishes at every frequency, every rung weight
vanishes.  Proven for EVERY finite rung set — the same-parity triangular band of the
compiled ladder is the special case; full separation (S2) subsumes triangularity, and the
minimal rung is still the induction engine. -/
theorem ladderSeparation (t : Finset ℕ) (w : ℕ → ℂ)
    (h : ∀ z : ℝ, (∑ r ∈ t, w r * semicircleTransform r z) = 0) :
    ∀ r ∈ t, w r = 0 :=
  ladder_moment_separation w t (ladder_moment_eq_zero t w h)

/-! ## S4: the named input, typed -/

/-- **The certifier-(b) target, typed — aggregate reality with rung-resolved
coefficients.**  What certifier (b) must now supply for the arithmetic aggregate: two
rung-resolved coefficient families whose ladder aggregates agree at every real frequency
(the `reality` field — e.g. the aggregate and its reality/registration-side readout).
Given an inhabitant, `perRung` extracts the per-rung channel identities through S3.
Inhabiting `reality` for the arithmetic aggregate is not proven in this file. -/
structure AggregateReality (t : Finset ℕ) where
  /-- The rung-resolved coefficients of the aggregate readout. -/
  coeff : ℕ → ℂ
  /-- The rung-resolved coefficients of the dual (reality-side) readout. -/
  dual : ℕ → ℂ
  /-- THE NAMED INPUT: the two rung-resolved readouts of the aggregate agree at every
  real frequency.  Not proven in this file for arithmetic aggregates. -/
  reality : ∀ z : ℝ, (∑ r ∈ t, coeff r * semicircleTransform r z)
      = ∑ r ∈ t, dual r * semicircleTransform r z

/-- **The compiled conditional (S4 ⟹ per-rung identities)**: given the named input
`AggregateReality`, the per-rung channel identities follow — the two coefficient families
agree rung by rung.  One application of the separation theorem `ladderSeparation` to the
difference family. -/
theorem AggregateReality.perRung {t : Finset ℕ} (A : AggregateReality t) :
    ∀ r ∈ t, A.coeff r = A.dual r := by
  intro r hr
  have h : ∀ z : ℝ, (∑ r ∈ t, (A.coeff r - A.dual r) * semicircleTransform r z) = 0 := by
    intro z
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib, A.reality z, sub_self]
  exact sub_eq_zero.mp (ladderSeparation t (fun r => A.coeff r - A.dual r) h r hr)

/-- Non-vacuity of the named-input type, DEGENERATE: any coefficient family paired with
itself.  Type-level smoke test only; it carries no arithmetic content. -/
def AggregateReality.diagonal (t : Finset ℕ) (c : ℕ → ℂ) : AggregateReality t :=
  ⟨c, c, fun _ => rfl⟩

end CriticalLinePhasor.ChannelSeparation

#print axioms CriticalLinePhasor.ChannelSeparation.cosMoment
#print axioms CriticalLinePhasor.ChannelSeparation.continuous_cosMomentIntegrand
#print axioms CriticalLinePhasor.ChannelSeparation.integral_cos_nat_mul
#print axioms CriticalLinePhasor.ChannelSeparation.cosMoment_succ_succ
#print axioms CriticalLinePhasor.ChannelSeparation.cosMoment_eq_zero
#print axioms CriticalLinePhasor.ChannelSeparation.cosMoment_diag
#print axioms CriticalLinePhasor.ChannelSeparation.abs_cosMoment_le
#print axioms CriticalLinePhasor.ChannelSeparation.orderSeriesTerm
#print axioms CriticalLinePhasor.ChannelSeparation.continuous_orderSeriesTerm
#print axioms CriticalLinePhasor.ChannelSeparation.hasSum_cosKernelIntegrand
#print axioms CriticalLinePhasor.ChannelSeparation.norm_orderCoeff
#print axioms CriticalLinePhasor.ChannelSeparation.norm_orderSeriesTerm_le
#print axioms CriticalLinePhasor.ChannelSeparation.hasSum_cosKernel
#print axioms CriticalLinePhasor.ChannelSeparation.cosKernel_eq_tsum
#print axioms CriticalLinePhasor.ChannelSeparation.summable_cosKernel_series
#print axioms CriticalLinePhasor.ChannelSeparation.coeff_eq_zero_of_tsum_eq_zero
#print axioms CriticalLinePhasor.ChannelSeparation.combo_moment_eq_zero
#print axioms CriticalLinePhasor.ChannelSeparation.moment_separation
#print axioms CriticalLinePhasor.ChannelSeparation.channelSeparation
#print axioms CriticalLinePhasor.ChannelSeparation.ladder_moment_eq_zero
#print axioms CriticalLinePhasor.ChannelSeparation.ladder_moment_separation
#print axioms CriticalLinePhasor.ChannelSeparation.ladderSeparation
#print axioms CriticalLinePhasor.ChannelSeparation.AggregateReality.perRung
#print axioms CriticalLinePhasor.ChannelSeparation.AggregateReality.diagonal
