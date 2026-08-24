import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Data.Rat.BigOperators
import RequestProject.DVPEulerMaclaurin

/-!
# E10a: the arctan enclosure with exact geometric remainder

`arctan x = Σ_{k<N} (−1)^k x^{2k+1}/(2k+1) ± x^{2N+1}/(2N+1)` for `x ≥ 0`,
from the EXACT identity `1/(1+t²) = Σ_{k<N}(−t²)^k + (−t²)^N/(1+t²)` —
no alternating-series lemma needed.  Feeds every `Im log`/`Arg` certificate
(the θ(1) base evaluation reduces to finitely many arctans).
-/

open Finset intervalIntegral

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The exact geometric remainder for the arctan integrand. -/
private lemma one_div_one_add_sq_eq (t : ℝ) (N : ℕ) :
    1 / (1 + t ^ 2)
      = (∑ k ∈ range N, (-1 : ℝ) ^ k * t ^ (2 * k))
        + (-1) ^ N * t ^ (2 * N) / (1 + t ^ 2) := by
  have hne : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  have hgeom : (∑ k ∈ range N, (-1 : ℝ) ^ k * t ^ (2 * k)) * (1 + t ^ 2)
      = 1 - (-1) ^ N * t ^ (2 * N) := by
    induction N with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, add_mul, ih]
      have h1 : (-1 : ℝ) ^ n * t ^ (2 * n) * (1 + t ^ 2)
          = (-1) ^ n * t ^ (2 * n) + (-1) ^ n * t ^ (2 * n + 2) := by
        ring
      have h2 : (2 : ℕ) * (n + 1) = 2 * n + 2 := by ring
      rw [h2]
      have h3 : (-1 : ℝ) ^ (n + 1) = -(-1) ^ n := by
        rw [pow_succ]
        ring
      rw [h3]
      ring
  field_simp
  linarith [hgeom]

/-- **E10a: the arctan enclosure.**  For `x ≥ 0` and every order `N`:
`|arctan x − Σ_{k<N}(−1)^k x^{2k+1}/(2k+1)| ≤ x^{2N+1}/(2N+1)`. -/
theorem arctan_enclosure {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    |Real.arctan x - ∑ k ∈ range N, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1)|
      ≤ x ^ (2 * N + 1) / (2 * N + 1) := by
  -- arctan as the integral
  have harctan : Real.arctan x = ∫ t in (0:ℝ)..x, 1 / (1 + t ^ 2) := by
    rw [integral_one_div_one_add_sq, Real.arctan_zero, sub_zero]
  -- integrate the geometric identity
  have hpoly : ∀ k : ℕ, ∫ t in (0:ℝ)..x, (-1 : ℝ) ^ k * t ^ (2 * k)
      = (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1) := by
    intro k
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have h0 : (0:ℝ) ^ (2 * k + 1) = 0 := by
      apply zero_pow
      omega
    rw [h0, sub_zero]
    push_cast
    ring
  have hintsum : IntervalIntegrable
      (fun t : ℝ => ∑ k ∈ range N, (-1 : ℝ) ^ k * t ^ (2 * k))
      MeasureTheory.volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    continuity
  have hintrem : IntervalIntegrable
      (fun t : ℝ => (-1 : ℝ) ^ N * t ^ (2 * N) / (1 + t ^ 2))
      MeasureTheory.volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    have hne : ∀ t : ℝ, (1 : ℝ) + t ^ 2 ≠ 0 := fun t => by positivity
    exact (continuous_const.mul (continuous_pow _)).div
      (continuous_const.add (continuous_pow 2)) hne
  have hsplit : Real.arctan x
      = (∑ k ∈ range N, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1))
        + ∫ t in (0:ℝ)..x, (-1 : ℝ) ^ N * t ^ (2 * N) / (1 + t ^ 2) := by
    rw [harctan]
    have hcongr : ∀ t ∈ Set.uIcc (0:ℝ) x,
        1 / (1 + t ^ 2)
          = (∑ k ∈ range N, (-1 : ℝ) ^ k * t ^ (2 * k))
            + (-1) ^ N * t ^ (2 * N) / (1 + t ^ 2) := fun t _ =>
      one_div_one_add_sq_eq t N
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_add hintsum hintrem,
      intervalIntegral.integral_finset_sum]
    · congr 1
      exact Finset.sum_congr rfl fun k _ => hpoly k
    · intro k _
      apply ContinuousOn.intervalIntegrable
      apply Continuous.continuousOn
      continuity
  rw [hsplit]
  have hkey : ∀ t ∈ Set.uIcc (0:ℝ) x,
      ‖(-1 : ℝ) ^ N * t ^ (2 * N) / (1 + t ^ 2)‖ ≤ |t| ^ (2 * N) := by
    intro t _
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_pow, abs_neg,
      abs_one, one_pow, one_mul]
    have h1 : (0:ℝ) < |1 + t ^ 2| := by
      rw [abs_of_pos (by positivity)]
      positivity
    rw [div_le_iff₀ h1]
    have h2 : (1:ℝ) ≤ |1 + t ^ 2| := by
      rw [abs_of_pos (by positivity)]
      nlinarith [sq_nonneg t]
    calc |t| ^ (2 * N) = |t| ^ (2 * N) * 1 := (mul_one _).symm
      _ ≤ |t| ^ (2 * N) * |1 + t ^ 2| := by
          apply mul_le_mul_of_nonneg_left h2 (by positivity)
  have habs : |∫ t in (0:ℝ)..x, (-1 : ℝ) ^ N * t ^ (2 * N) / (1 + t ^ 2)|
      ≤ x ^ (2 * N + 1) / (2 * N + 1) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
      (f := fun t : ℝ => (-1 : ℝ) ^ N * t ^ (2 * N) / (1 + t ^ 2))
      (g := fun t : ℝ => t ^ (2 * N)) hx ?_ ?_
    · rw [Real.norm_eq_abs] at hb
      have hval : ∫ t in (0:ℝ)..x, t ^ (2 * N)
          = x ^ (2 * N + 1) / (2 * N + 1) := by
        rw [integral_pow]
        have h0 : (0:ℝ) ^ (2 * N + 1) = 0 := by
          apply zero_pow
          omega
        rw [h0, sub_zero]
        push_cast
        ring
      rwa [hval] at hb
    · apply Filter.Eventually.of_forall
      intro t ht
      have ht' : t ∈ Set.uIcc (0:ℝ) x := by
        rw [Set.uIcc_of_le hx]
        exact Set.Ioc_subset_Icc_self ht
      have h1 := hkey t ht'
      have ht0 : 0 ≤ t := by
        rw [Set.uIcc_of_le hx] at ht'
        exact ht'.1
      rwa [abs_of_nonneg ht0] at h1
    · apply ContinuousOn.intervalIntegrable
      apply Continuous.continuousOn
      continuity
  calc |(∑ k ∈ range N, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1))
        + (∫ t in (0:ℝ)..x, (-1 : ℝ) ^ N * t ^ (2 * N) / (1 + t ^ 2))
        - ∑ k ∈ range N, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1)|
      = |∫ t in (0:ℝ)..x, (-1 : ℝ) ^ N * t ^ (2 * N) / (1 + t ^ 2)| := by
        congr 1
        ring
    _ ≤ x ^ (2 * N + 1) / (2 * N + 1) := habs

/-- **E10b: the vertical-segment resolvent integral.**  For `a > 0`:
`∫₀¹ a/(a² + t²/4) dt = 2·arctan(1/(2a))` — the per-term integral of the
digamma series along the θ(1) segment. -/
theorem integral_lorentz_eq_arctan {a : ℝ} (ha : 0 < a) :
    ∫ t in (0:ℝ)..1, a / (a ^ 2 + t ^ 2 / 4)
      = 2 * Real.arctan (1 / (2 * a)) := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x : ℝ => 2 * Real.arctan (x / (2 * a)))
        (a / (a ^ 2 + t ^ 2 / 4)) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => x / (2 * a)) (1 / (2 * a)) t :=
      (hasDerivAt_id t).div_const _
    have h2 := (Real.hasDerivAt_arctan (t / (2 * a))).comp t h1
    have h3 := h2.const_mul (2 : ℝ)
    have hval : (2 : ℝ) * (1 / (1 + (t / (2 * a)) ^ 2) * (1 / (2 * a)))
        = a / (a ^ 2 + t ^ 2 / 4) := by
      have h4a : (0:ℝ) < 4 * a ^ 2 := by positivity
      field_simp
      ring
    rw [hval] at h3
    exact h3
  have hint : IntervalIntegrable (fun t : ℝ => a / (a ^ 2 + t ^ 2 / 4))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    apply continuous_const.div
    · continuity
    · intro t
      positivity
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc]
  norm_num

/-- **E10b′: the general vertical-segment resolvent integral.**
`∫₀ᵀ a/(a² + t²/4) dt = 2·arctan(T/(2a))` for `a > 0` — the θ(T)-anchor
generalization of the unit-segment case. -/
theorem integral_lorentz_eq_arctan_T {a T : ℝ} (ha : 0 < a) :
    ∫ t in (0:ℝ)..T, a / (a ^ 2 + t ^ 2 / 4)
      = 2 * Real.arctan (T / (2 * a)) := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun x : ℝ => 2 * Real.arctan (x / (2 * a)))
        (a / (a ^ 2 + t ^ 2 / 4)) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => x / (2 * a)) (1 / (2 * a)) t :=
      (hasDerivAt_id t).div_const _
    have h2 := (Real.hasDerivAt_arctan (t / (2 * a))).comp t h1
    have h3 := h2.const_mul (2 : ℝ)
    have hval : (2 : ℝ) * (1 / (1 + (t / (2 * a)) ^ 2) * (1 / (2 * a)))
        = a / (a ^ 2 + t ^ 2 / 4) := by
      have h4a : (0:ℝ) < 4 * a ^ 2 := by positivity
      field_simp
      ring
    rw [hval] at h3
    exact h3
  have hint : IntervalIntegrable (fun t : ℝ => a / (a ^ 2 + t ^ 2 / 4))
      MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    apply continuous_const.div
    · continuity
    · intro t
      positivity
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc]
  norm_num

/-- **E10c: `arctan 2`, certified** via the complement identity
`arctan 2 = π/2 − arctan ½` (kernel Taylor at ½, order 6; the true value
is `1.10714871…`). -/
theorem arctan_two_enclosure :
    |Real.arctan 2 - (Real.pi / 2 - ((4636/10000 : ℚ) : ℝ))| ≤ 2/10000 := by
  have hcomp : Real.arctan 2 = Real.pi / 2 - Real.arctan (1/2) := by
    have h := Real.arctan_inv_of_pos (by norm_num : (0:ℝ) < 2)
    have h2 : (2:ℝ)⁻¹ = 1/2 := by norm_num
    rw [h2] at h
    linarith
  rw [hcomp]
  have henc := arctan_enclosure (x := (1/2 : ℝ)) (by norm_num) 6
  have hsum : ∑ k ∈ Finset.range 6,
      (-1 : ℝ) ^ k * (1/2) ^ (2 * k + 1) / (2 * k + 1)
      = 3290137/7096320 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at henc
  have htail : ((1:ℝ)/2) ^ (2 * 6 + 1) / (2 * (6:ℕ) + 1) ≤ 1/100000 := by
    norm_num
  have hval : |Real.arctan (1/2) - 3290137/7096320| ≤ 1/100000 :=
    le_trans henc htail
  have hclose : |(3290137/7096320 : ℝ) - ((4636/10000 : ℚ) : ℝ)|
      ≤ 4/100000 := by
    push_cast
    rw [abs_le]
    constructor <;> norm_num
  calc |Real.pi / 2 - Real.arctan (1/2)
        - (Real.pi / 2 - ((4636/10000 : ℚ) : ℝ))|
      = |((4636/10000 : ℚ) : ℝ) - Real.arctan (1/2)| := by
        rw [show Real.pi / 2 - Real.arctan (1/2)
            - (Real.pi / 2 - ((4636/10000 : ℚ) : ℝ))
            = ((4636/10000 : ℚ) : ℝ) - Real.arctan (1/2) from by ring]
    _ ≤ |((4636/10000 : ℚ) : ℝ) - (3290137/7096320 : ℝ)|
        + |(3290137/7096320 : ℝ) - Real.arctan (1/2)| :=
        abs_sub_le _ _ _
    _ ≤ 4/100000 + 1/100000 := by
        refine add_le_add ?_ ?_
        · rw [abs_sub_comm]
          exact hclose
        · rw [abs_sub_comm]
          exact hval
    _ ≤ 2/10000 := by norm_num

/-- **E10d: the θ(1) series-integral exchange.**  The digamma series
integrates termwise along the unit segment into pure arctans:
`∫₀¹ Σ'ₙ (1/(n+1) − a_n/(a_n²+t²/4)) dt
   = Σ'ₙ (1/(n+1) − 2·arctan(1/(2a_n)))`, `a_n = n + 5/4`.
Nonnegative summands under a `9/(16(n+1)²)` majorant. -/
theorem theta_one_series_integral :
    ∫ t in (0:ℝ)..1, (∑' n : ℕ,
        (1/((n:ℝ)+1) - ((n:ℝ)+5/4)/(((n:ℝ)+5/4)^2 + t^2/4)))
      = ∑' n : ℕ,
        (1/((n:ℝ)+1) - 2 * Real.arctan (1/(2*((n:ℝ)+5/4)))) := by
  set g : ℕ → ℝ → ℝ := fun n t =>
    1/((n:ℝ)+1) - ((n:ℝ)+5/4)/(((n:ℝ)+5/4)^2 + t^2/4) with hg
  have hcont : ∀ n, Continuous (g n) := by
    intro n
    rw [hg]
    dsimp only
    apply continuous_const.sub
    apply continuous_const.div
    · continuity
    · intro t
      positivity
  -- the uniform majorant
  have hbound : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Ioc (0:ℝ) 1 →
      ‖g n t‖ ≤ (9/16) * (1/((n:ℝ)+1)^2) := by
    intro n t ht
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have ht2 : t^2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have ht0 : 0 ≤ t^2 := sq_nonneg t
    set a : ℝ := (n:ℝ) + 5/4 with ha
    have ha1 : (1:ℝ) ≤ a := by rw [ha]; linarith
    have hden : (0:ℝ) < a^2 + t^2/4 := by positivity
    have hdenq : (0:ℝ) < a^2 + 1/4 := by positivity
    have hnonneg : 0 ≤ g n t := by
      rw [hg]
      dsimp only
      rw [sub_nonneg, div_le_div_iff₀ hden (by positivity : (0:ℝ) < (n:ℝ)+1)]
      rw [← ha]
      nlinarith
    have hupper : g n t ≤ (9/16) * (1/((n:ℝ)+1)^2) := by
      have hstep : g n t ≤ 1/((n:ℝ)+1) - a/(a^2 + 1/4) := by
        rw [hg]
        dsimp only
        rw [← ha]
        have : a/(a^2 + 1/4) ≤ a/(a^2 + t^2/4) := by
          apply div_le_div_of_nonneg_left (by linarith) hden
          nlinarith
        linarith
      have halg : 1/((n:ℝ)+1) - a/(a^2 + 1/4)
          ≤ (9/16) * (1/((n:ℝ)+1)^2) := by
        rw [div_sub_div _ _ (by positivity : ((n:ℝ)+1) ≠ 0) hdenq.ne',
          div_le_iff₀ (by positivity), one_mul]
        have hexp : a^2 + 1/4 - ((n:ℝ)+1)*a = a/4 + 1/4 := by
          rw [ha]
          ring
        rw [hexp]
        have hgoal : (a/4 + 1/4) * (16 * ((n:ℝ)+1)^2)
            ≤ 9 * (((n:ℝ)+1) * (a^2 + 1/4)) := by
          rw [ha]
          nlinarith [sq_nonneg ((n:ℝ)+1), hn0]
        calc a/4 + 1/4
            = ((a/4 + 1/4) * (16 * ((n:ℝ)+1)^2)) / (16 * ((n:ℝ)+1)^2) := by
              field_simp
          _ ≤ (9 * (((n:ℝ)+1) * (a^2 + 1/4))) / (16 * ((n:ℝ)+1)^2) := by
              apply div_le_div_of_nonneg_right hgoal (by positivity)
          _ = 9/16 * (1/((n:ℝ)+1)^2) * (((n:ℝ)+1) * (a^2 + 1/4)) := by
              field_simp
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hupper
  -- integrability and integral-norm summability
  have hint : ∀ n : ℕ, MeasureTheory.IntegrableOn (g n)
      (Set.Ioc (0:ℝ) 1) MeasureTheory.volume := fun n =>
    (hcont n).integrableOn_Ioc
  have hnorm_int : ∀ n : ℕ,
      (∫ t in Set.Ioc (0:ℝ) 1, ‖g n t‖)
        ≤ (9/16) * (1/((n:ℝ)+1)^2) := by
    intro n
    calc (∫ t in Set.Ioc (0:ℝ) 1, ‖g n t‖)
        ≤ ∫ _ in Set.Ioc (0:ℝ) 1, (9/16) * (1/((n:ℝ)+1)^2) := by
          apply MeasureTheory.setIntegral_mono_on
            (hint n).norm
            (MeasureTheory.integrableOn_const (by simp))
            measurableSet_Ioc
          exact hbound n
      _ = (9/16) * (1/((n:ℝ)+1)^2) := by
          rw [MeasureTheory.setIntegral_const]
          simp
  have hmaj : Summable (fun n : ℕ => (9/16) * (1/((n:ℝ)+1)^2)) := by
    apply Summable.mul_left
    have hbase0 : Summable (fun n : ℕ => 1/((n:ℝ))^2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hbase : Summable (fun n : ℕ => 1/(((n+1:ℕ)):ℝ)^2) :=
      hbase0.comp_injective (fun a b h => by omega)
    apply hbase.congr
    intro n
    push_cast
    ring
  have hF_sum : Summable (fun n : ℕ => ∫ t in Set.Ioc (0:ℝ) 1, ‖g n t‖) := by
    apply Summable.of_nonneg_of_le
      (fun n => MeasureTheory.integral_nonneg (fun t => norm_nonneg _))
      hnorm_int hmaj
  -- the exchange
  have hexch := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1))
    (F := g) (fun n => hint n) hF_sum
  -- back to interval integrals and per-term FTC
  have hio : ∫ t in (0:ℝ)..1, (∑' n : ℕ, g n t)
      = ∫ t in Set.Ioc (0:ℝ) 1, (∑' n : ℕ, g n t) :=
    intervalIntegral.integral_of_le (by norm_num)
  have hterm : ∀ n : ℕ, (∫ t in Set.Ioc (0:ℝ) 1, g n t)
      = 1/((n:ℝ)+1) - 2 * Real.arctan (1/(2*((n:ℝ)+5/4))) := by
    intro n
    have hio' : (∫ t in Set.Ioc (0:ℝ) 1, g n t)
        = ∫ t in (0:ℝ)..1, g n t :=
      (intervalIntegral.integral_of_le (by norm_num)).symm
    rw [hio']
    have ha : (0:ℝ) < (n:ℝ) + 5/4 := by positivity
    have hlor := integral_lorentz_eq_arctan ha
    have hintc : IntervalIntegrable
        (fun t : ℝ => ((n:ℝ)+5/4)/(((n:ℝ)+5/4)^2 + t^2/4))
        MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      apply Continuous.continuousOn
      apply continuous_const.div
      · continuity
      · intro t
        positivity
    rw [hg]
    dsimp only
    rw [intervalIntegral.integral_sub intervalIntegrable_const hintc,
      intervalIntegral.integral_const, hlor]
    have h1 : ((1:ℝ) - 0) • (1/((n:ℝ)+1)) = 1/((n:ℝ)+1) := by
      simp
    rw [h1]
  rw [hio, ← hexch]
  exact tsum_congr hterm

/-- The θ(1) series summand. -/
noncomputable def sTerm (n : ℕ) : ℝ :=
  1/((n:ℝ)+1) - 2 * Real.arctan (1/(2*((n:ℝ)+5/4)))

/-- Per-term two-sided control from the order-1 arctan enclosure:
`|sTerm n − (1/4)/((n+1)(n+5/4))| ≤ (2/3)·(1/(2n+5/2))³`. -/
theorem sTerm_control (n : ℕ) :
    |sTerm n - (1/4)/(((n:ℝ)+1)*((n:ℝ)+5/4))|
      ≤ (2/3) * (1/(2*((n:ℝ)+5/4)))^3 := by
  set x : ℝ := 1/(2*((n:ℝ)+5/4)) with hx
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hx0 : 0 ≤ x := by
    rw [hx]
    positivity
  have henc := arctan_enclosure hx0 1
  have hP1 : ∑ k ∈ Finset.range 1,
      (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1) = x := by
    norm_num
  rw [hP1] at henc
  have hlin : 1/((n:ℝ)+1) - 2 * x = (1/4)/(((n:ℝ)+1)*((n:ℝ)+5/4)) := by
    rw [hx]
    field_simp
    ring
  have hkey : sTerm n - (1/4)/(((n:ℝ)+1)*((n:ℝ)+5/4))
      = 2 * (x - Real.arctan x) := by
    rw [sTerm, ← hlin, ← hx]
    ring
  rw [hkey, abs_mul, abs_two]
  have h1 : |x - Real.arctan x| = |Real.arctan x - x| := abs_sub_comm _ _
  rw [h1]
  have h2 : x ^ (2 * 1 + 1) / (2 * (1:ℕ) + 1) = x^3/3 := by
    norm_num
  rw [h2] at henc
  calc 2 * |Real.arctan x - x| ≤ 2 * (x^3/3) := by
        exact mul_le_mul_of_nonneg_left henc (by norm_num)
    _ = (2/3) * x^3 := by ring

/-- The summand is absolutely dominated by `(1/3)/(n+1)²`. -/
theorem sTerm_abs_le (n : ℕ) : |sTerm n| ≤ (1/3) * (1/((n:ℝ)+1)^2) := by
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hc := sTerm_control n
  have h1 : (1/4)/(((n:ℝ)+1)*((n:ℝ)+5/4)) ≤ (1/4) * (1/((n:ℝ)+1)^2) := by
    rw [div_le_iff₀ (by positivity)]
    rw [show (1/4 : ℝ) * (1/((n:ℝ)+1)^2) * (((n:ℝ)+1)*((n:ℝ)+5/4))
      = (1/4) * (((n:ℝ)+5/4)/((n:ℝ)+1)) from by field_simp]
    have : (1:ℝ) ≤ ((n:ℝ)+5/4)/((n:ℝ)+1) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith
  have h2 : (2/3) * (1/(2*((n:ℝ)+5/4)))^3 ≤ (1/12) * (1/((n:ℝ)+1)^2) := by
    have ha : (1:ℝ)/(2*((n:ℝ)+5/4)) ≤ 1/(2*((n:ℝ)+1)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      linarith
    have hb : (1/(2*((n:ℝ)+5/4)))^3 ≤ (1/(2*((n:ℝ)+1)))^3 := by
      apply pow_le_pow_left₀ (by positivity) ha
    have hc' : (1/(2*((n:ℝ)+1)))^3 ≤ (1/8) * (1/((n:ℝ)+1)^2) := by
      rw [show ((1:ℝ)/(2*((n:ℝ)+1)))^3 = (1/8) * (1/((n:ℝ)+1)^3) from by
        field_simp
        ring]
      have : (1:ℝ)/((n:ℝ)+1)^3 ≤ 1/((n:ℝ)+1)^2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith
      linarith
    calc (2/3 : ℝ) * (1/(2*((n:ℝ)+5/4)))^3
        ≤ (2/3) * ((1/8) * (1/((n:ℝ)+1)^2)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact le_trans hb hc'
      _ = (1/12) * (1/((n:ℝ)+1)^2) := by ring
  have htri : |sTerm n| ≤ (1/4)/(((n:ℝ)+1)*((n:ℝ)+5/4))
      + (2/3) * (1/(2*((n:ℝ)+5/4)))^3 := by
    have := abs_sub_abs_le_abs_sub (sTerm n)
      ((1/4)/(((n:ℝ)+1)*((n:ℝ)+5/4)))
    have habs : |(1/4)/(((n:ℝ)+1)*((n:ℝ)+5/4))|
        = (1/4)/(((n:ℝ)+1)*((n:ℝ)+5/4)) := abs_of_pos (by positivity)
    linarith [hc, this, habs.le, habs.ge]
  calc |sTerm n| ≤ (1/4)/(((n:ℝ)+1)*((n:ℝ)+5/4))
        + (2/3) * (1/(2*((n:ℝ)+5/4)))^3 := htri
    _ ≤ (1/4) * (1/((n:ℝ)+1)^2) + (1/12) * (1/((n:ℝ)+1)^2) :=
        add_le_add h1 h2
    _ = (1/3) * (1/((n:ℝ)+1)^2) := by ring

/-- The θ(1) series is summable. -/
theorem sTerm_summable : Summable sTerm := by
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => (1/3) * (1/((n:ℝ)+1)^2))
  · apply Summable.mul_left
    have hbase0 : Summable (fun n : ℕ => 1/((n:ℝ))^2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hbase : Summable (fun n : ℕ => 1/(((n+1:ℕ)):ℝ)^2) :=
      hbase0.comp_injective (fun a b h => by omega)
    apply hbase.congr
    intro n
    push_cast
    ring
  · intro n
    rw [Real.norm_eq_abs]
    exact sTerm_abs_le n

/-- **E10d′: the T-parametrized series-integral exchange.**
`∫₀ᵀ Σ'ₙ gₙ(t) dt = Σ'ₙ (T/(n+1) − 2·arctan(T/(2aₙ)))`, majorant
`T(1+T²)/4·(n+1)⁻²`. -/
theorem theta_T_series_integral {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0:ℝ)..T, (∑' n : ℕ,
        (1/((n:ℝ)+1) - ((n:ℝ)+5/4)/(((n:ℝ)+5/4)^2 + t^2/4)))
      = ∑' n : ℕ,
        (T/((n:ℝ)+1) - 2 * Real.arctan (T/(2*((n:ℝ)+5/4)))) := by
  set g : ℕ → ℝ → ℝ := fun n t =>
    1/((n:ℝ)+1) - ((n:ℝ)+5/4)/(((n:ℝ)+5/4)^2 + t^2/4) with hg
  have hcont : ∀ n, Continuous (g n) := by
    intro n
    rw [hg]
    dsimp only
    apply continuous_const.sub
    apply continuous_const.div
    · continuity
    · intro t
      positivity
  have hbound : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Ioc (0:ℝ) T →
      ‖g n t‖ ≤ ((1+T^2)/4) * (1/((n:ℝ)+1)^2) := by
    intro n t ht
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have ht2 : t^2 ≤ T^2 := by nlinarith [ht.1, ht.2]
    set a : ℝ := (n:ℝ) + 5/4 with ha
    have ha1 : (1:ℝ) ≤ a := by rw [ha]; linarith
    have hden : (0:ℝ) < a^2 + t^2/4 := by positivity
    have hnonneg : 0 ≤ g n t := by
      rw [hg]
      dsimp only
      rw [sub_nonneg, div_le_div_iff₀ hden (by positivity : (0:ℝ) < (n:ℝ)+1)]
      rw [← ha]
      nlinarith
    have hupper : g n t ≤ ((1+T^2)/4) * (1/((n:ℝ)+1)^2) := by
      have hfrac : g n t = (a/4 + t^2/4)/(((n:ℝ)+1)*(a^2 + t^2/4)) := by
        rw [hg]
        dsimp only
        rw [← ha]
        rw [div_sub_div _ _ (by positivity : ((n:ℝ)+1) ≠ 0) hden.ne']
        congr 1
        rw [ha]
        ring
      rw [hfrac]
      have hnum : a/4 + t^2/4 ≤ (1+T^2)/4 * a := by
        nlinarith
      have hden2 : ((n:ℝ)+1)^2 * a ≤ ((n:ℝ)+1)*(a^2 + t^2/4) := by
        have hna : ((n:ℝ)+1) ≤ a := by rw [ha]; linarith
        have hprod : (0:ℝ) ≤ (((n:ℝ)+1) * a) * (a - ((n:ℝ)+1)) :=
          mul_nonneg (mul_nonneg (by linarith) (by linarith))
            (sub_nonneg.mpr hna)
        nlinarith [sq_nonneg t, hprod]
      rw [div_le_iff₀ (by positivity)]
      have hgoal : (a/4 + t^2/4) * (((n:ℝ)+1)^2 * a)
          ≤ ((1+T^2)/4 * (1/((n:ℝ)+1)^2) * (((n:ℝ)+1)*(a^2 + t^2/4)))
            * (((n:ℝ)+1)^2 * a) := by
        have hx : ((1+T^2)/4 * (1/((n:ℝ)+1)^2) * (((n:ℝ)+1)*(a^2 + t^2/4)))
            * (((n:ℝ)+1)^2 * a)
            = ((1+T^2)/4 * a) * (((n:ℝ)+1)*(a^2 + t^2/4)) := by
          field_simp
        rw [hx]
        apply mul_le_mul hnum hden2 (by positivity) (by positivity)
      have hpos : (0:ℝ) < ((n:ℝ)+1)^2 * a := by positivity
      exact le_of_mul_le_mul_right hgoal hpos
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hupper
  have hint : ∀ n : ℕ, MeasureTheory.IntegrableOn (g n)
      (Set.Ioc (0:ℝ) T) MeasureTheory.volume := fun n =>
    (hcont n).integrableOn_Ioc
  have hnorm_int : ∀ n : ℕ,
      (∫ t in Set.Ioc (0:ℝ) T, ‖g n t‖)
        ≤ (T * ((1+T^2)/4)) * (1/((n:ℝ)+1)^2) := by
    intro n
    calc (∫ t in Set.Ioc (0:ℝ) T, ‖g n t‖)
        ≤ ∫ _ in Set.Ioc (0:ℝ) T, ((1+T^2)/4) * (1/((n:ℝ)+1)^2) := by
          apply MeasureTheory.setIntegral_mono_on
            (hint n).norm
            (MeasureTheory.integrableOn_const (by simp))
            measurableSet_Ioc
          exact hbound n
      _ = (T * ((1+T^2)/4)) * (1/((n:ℝ)+1)^2) := by
          rw [MeasureTheory.setIntegral_const]
          simp [Real.volume_Ioc, hT]
          ring
  have hmaj : Summable
      (fun n : ℕ => (T * ((1+T^2)/4)) * (1/((n:ℝ)+1)^2)) := by
    apply Summable.mul_left
    have hbase0 : Summable (fun n : ℕ => 1/((n:ℝ))^2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hbase : Summable (fun n : ℕ => 1/(((n+1:ℕ)):ℝ)^2) :=
      hbase0.comp_injective (fun a b h => by omega)
    apply hbase.congr
    intro n
    push_cast
    ring
  have hF_sum : Summable
      (fun n : ℕ => ∫ t in Set.Ioc (0:ℝ) T, ‖g n t‖) := by
    apply Summable.of_nonneg_of_le
      (fun n => MeasureTheory.integral_nonneg (fun t => norm_nonneg _))
      hnorm_int hmaj
  have hexch := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) T))
    (F := g) (fun n => hint n) hF_sum
  have hio : ∫ t in (0:ℝ)..T, (∑' n : ℕ, g n t)
      = ∫ t in Set.Ioc (0:ℝ) T, (∑' n : ℕ, g n t) :=
    intervalIntegral.integral_of_le hT
  have hterm : ∀ n : ℕ, (∫ t in Set.Ioc (0:ℝ) T, g n t)
      = T/((n:ℝ)+1) - 2 * Real.arctan (T/(2*((n:ℝ)+5/4))) := by
    intro n
    have hio' : (∫ t in Set.Ioc (0:ℝ) T, g n t)
        = ∫ t in (0:ℝ)..T, g n t :=
      (intervalIntegral.integral_of_le hT).symm
    rw [hio']
    have ha : (0:ℝ) < (n:ℝ) + 5/4 := by positivity
    have hlor := integral_lorentz_eq_arctan_T (T := T) ha
    have hintc : IntervalIntegrable
        (fun t : ℝ => ((n:ℝ)+5/4)/(((n:ℝ)+5/4)^2 + t^2/4))
        MeasureTheory.volume 0 T := by
      apply ContinuousOn.intervalIntegrable
      apply Continuous.continuousOn
      apply continuous_const.div
      · continuity
      · intro t
        positivity
    rw [hg]
    dsimp only
    rw [intervalIntegral.integral_sub intervalIntegrable_const hintc,
      intervalIntegral.integral_const, hlor]
    have h1 : (T - 0) • (1/((n:ℝ)+1)) = T/((n:ℝ)+1) := by
      simp
      ring
    rw [h1]
  rw [hio, ← hexch]
  exact tsum_congr hterm

/-- **The S-window**: the θ(1) series is its 10-term head to within
`34/1000` (tail via the `(1/3)/(n+1)²` majorant against the compiled
`p = 2` tail bound). -/
theorem S_window :
    |(∑' n : ℕ, sTerm n) - ∑ n ∈ Finset.range 10, sTerm n| ≤ 34/1000 := by
  have hsplit := sTerm_summable.sum_add_tsum_nat_add 10
  have htail_sum : Summable (fun i : ℕ => sTerm (i + 10)) :=
    (summable_nat_add_iff 10).mpr sTerm_summable
  have hkey : (∑' n : ℕ, sTerm n) - ∑ n ∈ Finset.range 10, sTerm n
      = ∑' i : ℕ, sTerm (i + 10) := by
    rw [← hsplit]
    ring
  rw [hkey]
  -- the tail majorant
  have hmaj : Summable (fun i : ℕ => (1/3) * (1/((i:ℝ)+11)^2)) := by
    apply Summable.mul_left
    have hbase0 : Summable (fun n : ℕ => 1/((n:ℝ))^2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hbase : Summable (fun n : ℕ => 1/(((n+11:ℕ)):ℝ)^2) :=
      hbase0.comp_injective (fun a b h => by omega)
    apply hbase.congr
    intro n
    push_cast
    ring
  have habs1 : |∑' i : ℕ, sTerm (i + 10)|
      ≤ ∑' i : ℕ, (1/3) * (1/((i:ℝ)+11)^2) := by
    have hn : Summable (fun i : ℕ => ‖sTerm (i + 10)‖) := by
      simp only [Real.norm_eq_abs]
      exact htail_sum.abs
    have hb := norm_tsum_le_tsum_norm hn
    simp only [Real.norm_eq_abs] at hb
    refine le_trans hb ?_
    apply Summable.tsum_le_tsum _ htail_sum.abs hmaj
    intro i
    have := sTerm_abs_le (i + 10)
    have hcast : (((i + 10 : ℕ)):ℝ) + 1 = (i:ℝ) + 11 := by
      push_cast
      ring
    rwa [hcast] at this
  -- evaluate the majorant sum
  have hval : ∑' i : ℕ, (1/3) * (1/((i:ℝ)+11)^2) ≤ (1/3) * (12/121) := by
    rw [tsum_mul_left]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hrpow := tsum_shift_rpow_le (N := 11) (by norm_num)
      (p := (2:ℝ)) (by norm_num)
    have hconv : ∀ k : ℕ, (((11 + k : ℕ)):ℝ) ^ (-(2:ℝ))
        = 1/((k:ℝ)+11)^2 := by
      intro k
      have hpos : (0:ℝ) < ((11 + k : ℕ):ℝ) := by positivity
      rw [show (-(2:ℝ)) = ((-2 : ℤ) : ℝ) by norm_num,
        Real.rpow_intCast]
      have hcast : (((11 + k : ℕ)):ℝ) = (k:ℝ) + 11 := by
        push_cast
        ring
      rw [hcast]
      have h2 : ((k:ℝ) + 11) ^ (-2 : ℤ) = (((k:ℝ)+11)^2)⁻¹ := by
        rw [zpow_neg]
        norm_num
      rw [h2, one_div]
    rw [funext hconv] at hrpow
    have hrhs : (((11:ℕ)):ℝ) ^ (-(2:ℝ)) + (((11:ℕ)):ℝ) ^ (1 - (2:ℝ)) / ((2:ℝ) - 1)
        = 12/121 := by
      have h1 : (((11:ℕ)):ℝ) = 11 := by norm_num
      rw [h1, show (-(2:ℝ)) = ((-2 : ℤ) : ℝ) by norm_num,
        show ((1:ℝ) - 2) = ((-1 : ℤ) : ℝ) by norm_num,
        Real.rpow_intCast, Real.rpow_intCast]
      norm_num
    rw [hrhs] at hrpow
    exact hrpow
  calc |∑' i : ℕ, sTerm (i + 10)|
      ≤ ∑' i : ℕ, (1/3) * (1/((i:ℝ)+11)^2) := habs1
    _ ≤ (1/3) * (12/121) := hval
    _ ≤ 34/1000 := by norm_num

/-- **The T-parametrized per-term control, order 2**: the θ(T)-series
summand equals its exact DC `(T/4)/((n+1)aₙ)` plus the exact cube mode
`T³/(12aₙ³)` to within `T⁵/(80aₙ⁵)`, `aₙ = n + 5/4`. -/
theorem sTermT_control {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    |(T/((n:ℝ)+1) - 2 * Real.arctan (T/(2*((n:ℝ)+5/4))))
      - (T/4)/(((n:ℝ)+1)*((n:ℝ)+5/4)) - T^3/(12*((n:ℝ)+5/4)^3)|
      ≤ T^5/(80*((n:ℝ)+5/4)^5) := by
  set a : ℝ := (n:ℝ) + 5/4 with ha
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have ha0 : (0:ℝ) < a := by rw [ha]; linarith
  set x : ℝ := T/(2*a) with hx
  have hx0 : 0 ≤ x := by
    rw [hx]
    positivity
  have henc := arctan_enclosure hx0 2
  have hP2 : ∑ k ∈ Finset.range 2,
      (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1) = x - x^3/3 := by
    norm_num [Finset.sum_range_succ]
    ring
  rw [hP2] at henc
  have h5 : x ^ (2 * 2 + 1) / (2 * (2:ℕ) + 1) = x^5/5 := by
    norm_num
  rw [h5] at henc
  have hkey : (T/((n:ℝ)+1) - 2 * Real.arctan x)
      - (T/4)/(((n:ℝ)+1)*a) - T^3/(12*a^3)
      = -2 * (Real.arctan x - (x - x^3/3)) := by
    have h2x : 2 * x = T/a := by
      rw [hx]
      field_simp
    have hdc : T/((n:ℝ)+1) - T/a = (T/4)/(((n:ℝ)+1)*a) := by
      rw [ha]
      field_simp
      ring
    have hcube : (2/3) * x^3 = T^3/(12*a^3) := by
      rw [hx]
      field_simp
      ring
    have hexpand : T/((n:ℝ)+1) - 2 * Real.arctan x
        = (T/((n:ℝ)+1) - T/a) + (2/3) * x^3
          - 2 * (Real.arctan x - (x - x^3/3)) := by
      have : T/a = 2*x := h2x.symm
      rw [this]
      ring
    rw [hexpand, hdc, hcube]
    ring
  rw [hkey, abs_mul]
  have habs2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [habs2]
  have hbound : 2 * |Real.arctan x - (x - x^3/3)| ≤ 2 * (x^5/5) :=
    mul_le_mul_of_nonneg_left henc (by norm_num)
  have hval : 2 * (x^5/5) = T^5/(80*a^5) := by
    rw [hx]
    field_simp
    ring
  rw [hval] at hbound
  exact hbound

/-- **E10a′: the arctan enclosure for ALL real arguments** (odd
extension of `arctan_enclosure`). -/
theorem arctan_enclosure_all (x : ℝ) (N : ℕ) :
    |Real.arctan x - ∑ k ∈ Finset.range N,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1)|
      ≤ |x| ^ (2 * N + 1) / (2 * N + 1) := by
  rcases le_or_gt 0 x with hx | hx
  · have h := arctan_enclosure hx N
    rwa [abs_of_nonneg hx]
  · set y : ℝ := -x with hy
    have hy0 : 0 ≤ y := by rw [hy]; linarith
    have h := arctan_enclosure hy0 N
    have harctan : Real.arctan x = -Real.arctan y := by
      rw [hy]
      simp [Real.arctan_neg]
    have hP : ∑ k ∈ Finset.range N,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1)
        = -∑ k ∈ Finset.range N,
          (-1 : ℝ) ^ k * y ^ (2 * k + 1) / (2 * k + 1) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [hy]
      have hodd : (-x) ^ (2 * k + 1) = -x ^ (2 * k + 1) := by
        rw [Odd.neg_pow ⟨k, by ring⟩]
      rw [hodd]
      ring
    have habs : |x| = y := by
      rw [hy, abs_of_neg hx]
    rw [harctan, hP, habs]
    calc |-Real.arctan y - -∑ k ∈ Finset.range N,
          (-1 : ℝ) ^ k * y ^ (2 * k + 1) / (2 * k + 1)|
        = |Real.arctan y - ∑ k ∈ Finset.range N,
          (-1 : ℝ) ^ k * y ^ (2 * k + 1) / (2 * k + 1)| := by
          rw [← abs_neg]
          congr 1
          ring
      _ ≤ y ^ (2 * N + 1) / (2 * N + 1) := h

/-- **The half-anchor identity**: for `0 ≤ x ≤ 1`,
`arctan x = arctan ½ + arctan ((x − ½)/(1 + x/2))` — every head argument
lands at a shifted argument of size at most ⅓. -/
theorem arctan_anchor_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.arctan x
      = Real.arctan (1/2) + Real.arctan ((x - 1/2)/(1 + x/2)) := by
  set z : ℝ := (x - 1/2)/(1 + x/2) with hz
  have hden : (0:ℝ) < 1 + x/2 := by linarith
  have hzval : z ≤ 1/3 := by
    rw [hz, div_le_iff₀ hden]
    linarith
  have hzval' : -1/2 ≤ z := by
    rw [hz, le_div_iff₀ hden]
    nlinarith
  have hprod : (1/2 : ℝ) * z < 1 := by nlinarith
  have hadd := Real.arctan_add (x := (1/2:ℝ)) (y := z) hprod
  have hne : (1:ℝ) - (1/2) * z ≠ 0 := by
    intro h
    nlinarith [hzval]
  have hkey : (1/2 : ℝ) + z = x * (1 - (1/2) * z) := by
    rw [hz]
    field_simp
    ring
  have hval : ((1/2 : ℝ) + z) / (1 - (1/2) * z) = x := by
    rw [hkey, mul_div_assoc, div_self hne, mul_one]
  rw [hval] at hadd
  linarith [hadd]

/-- **The anchored arctan evaluator** on `[0, 1]`: kernel Taylor at the
shifted argument plus the certified `arctan ½`. -/
theorem arctan_half_range {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (N : ℕ) :
    |Real.arctan x - ((3290137/7096320 : ℝ)
        + ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k
          * ((x - 1/2)/(1 + x/2)) ^ (2 * k + 1) / (2 * k + 1))|
      ≤ 1/100000 + |(x - 1/2)/(1 + x/2)| ^ (2 * N + 1) / (2 * N + 1) := by
  rw [arctan_anchor_half hx0 hx1]
  -- the arctan ½ certificate (the 361 block)
  have hhalf : |Real.arctan (1/2) - 3290137/7096320| ≤ 1/100000 := by
    have henc := arctan_enclosure (x := (1/2 : ℝ)) (by norm_num) 6
    have hsum : ∑ k ∈ Finset.range 6,
        (-1 : ℝ) ^ k * (1/2) ^ (2 * k + 1) / (2 * k + 1)
        = 3290137/7096320 := by
      norm_num [Finset.sum_range_succ]
    rw [hsum] at henc
    refine le_trans henc ?_
    norm_num
  have hz := arctan_enclosure_all ((x - 1/2)/(1 + x/2)) N
  calc |Real.arctan (1/2) + Real.arctan ((x - 1/2)/(1 + x/2))
        - ((3290137/7096320 : ℝ)
          + ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k
            * ((x - 1/2)/(1 + x/2)) ^ (2 * k + 1) / (2 * k + 1))|
      = |(Real.arctan (1/2) - 3290137/7096320)
          + (Real.arctan ((x - 1/2)/(1 + x/2))
            - ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k
              * ((x - 1/2)/(1 + x/2)) ^ (2 * k + 1) / (2 * k + 1))| := by
        congr 1
        ring
    _ ≤ |Real.arctan (1/2) - 3290137/7096320|
        + |Real.arctan ((x - 1/2)/(1 + x/2))
          - ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k
            * ((x - 1/2)/(1 + x/2)) ^ (2 * k + 1) / (2 * k + 1)| :=
        abs_add_le _ _
    _ ≤ 1/100000
        + |(x - 1/2)/(1 + x/2)| ^ (2 * N + 1) / (2 * N + 1) :=
        add_le_add hhalf hz

/-- rpow at a negative natural exponent, for positive base. -/
private lemma rpow_neg_ofNat {x : ℝ} (hx : 0 < x) (m : ℕ) :
    x ^ (-(m:ℝ)) = (x^m)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.rpow_natCast]

/-- The θ(T)-series summand, named. -/
noncomputable def sTermT (T : ℝ) (n : ℕ) : ℝ :=
  T/((n:ℝ)+1) - 2 * Real.arctan (T/(2*((n:ℝ)+5/4)))

set_option maxHeartbeats 6400000 in
/-- **The θ(30) tail bracket**: `Σ'ₖ sTermT 30 (k+40) ∈ [0.8139, 0.9110]`
— DC and cube modes bracketed by 372, quintic bounded above. -/
theorem theta30_tail_bracket :
    (8139/10000 : ℝ) ≤ (∑' k : ℕ, sTermT 30 (k+40))
      ∧ (∑' k : ℕ, sTermT 30 (k+40)) ≤ 9110/10000 := by
  -- per-term control at m = k + 40
  have hctrl : ∀ k : ℕ,
      |sTermT 30 (k+40) - (30/4)/((((k+40:ℕ)):ℝ)+1)/(((k+40:ℕ):ℝ)+5/4)
        - 30^3/(12*((((k+40:ℕ)):ℝ)+5/4)^3)|
      ≤ 30^5/(80*((((k+40:ℕ)):ℝ)+5/4)^5) := by
    intro k
    have h := sTermT_control (T := (30:ℝ)) (by norm_num) (k+40)
    rw [sTermT]
    have hshape : (30/4 : ℝ)/(((k+40:ℕ):ℝ)+1)/(((k+40:ℕ):ℝ)+5/4)
        = (30/4 : ℝ)/((((k+40:ℕ):ℝ)+1)*(((k+40:ℕ):ℝ)+5/4)) := by
      rw [div_div]
    rw [hshape]
    exact h
  -- the three mode families and their summabilities
  have hbase : Summable (fun n : ℕ => 1/((n:ℝ))^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsum_gen : ∀ (q : ℕ), 2 ≤ q → Summable
      (fun k : ℕ => ((((k+40:ℕ)):ℝ)+5/4) ^ (-(q:ℝ))) := by
    intro q hq
    have hmaj : Summable (fun k : ℕ => 1/(((k+1:ℕ)):ℝ)^2) :=
      hbase.comp_injective (fun a b h => by omega)
    apply Summable.of_nonneg_of_le
      (fun k => Real.rpow_nonneg (by positivity) _) _ hmaj
    intro k
    rw [rpow_neg_ofNat (by positivity) q, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    calc ((((k+1:ℕ)):ℝ))^2 ≤ ((((k+40:ℕ)):ℝ)+5/4)^2 := by
          apply pow_le_pow_left₀ (by positivity)
          push_cast
          linarith
      _ ≤ ((((k+40:ℕ)):ℝ)+5/4)^q := by
          apply pow_le_pow_right₀ _ hq
          push_cast
          linarith [Nat.cast_nonneg (α := ℝ) k]
  -- bracket instances from 372 (converted to pow form)
  have hconv : ∀ (q : ℕ) (k : ℕ),
      (((40:ℕ):ℝ) + (k:ℝ) + 5/4) ^ (-(q:ℝ))
        = ((((k+40:ℕ)):ℝ)+5/4) ^ (-(q:ℝ)) := by
    intro q k
    congr 1
    push_cast
    ring
  have hH2 := tsum_rpow_tail_bracket (c := (5/4:ℝ)) (N := 40)
    (p := ((2:ℕ):ℝ)) (by norm_num) (by norm_num)
  have hH3 := tsum_rpow_tail_bracket (c := (5/4:ℝ)) (N := 40)
    (p := ((3:ℕ):ℝ)) (by norm_num) (by norm_num)
  have hH5 := tsum_rpow_tail_bracket (c := (5/4:ℝ)) (N := 40)
    (p := ((5:ℕ):ℝ)) (by norm_num) (by norm_num)
  simp only [funext (hconv 2), funext (hconv 3), funext (hconv 5)] at hH2 hH3 hH5
  have hH2c1 := tsum_rpow_tail_bracket (c := (1:ℝ)) (N := 40)
    (p := ((2:ℕ):ℝ)) (by norm_num) (by norm_num)
  have hconv1 : ∀ k : ℕ, ((((40:ℕ)):ℝ) + (k:ℝ) + 1) ^ (-(((2:ℕ)):ℝ))
      = (((((k+40:ℕ)):ℝ)+1)) ^ (-(((2:ℕ)):ℝ)) := by
    intro k
    congr 1
    push_cast
    ring
  simp only [funext hconv1] at hH2c1
  -- rational endpoint values
  have hep2l : (((40:ℕ):ℝ) + 5/4) ^ (1 - ((2:ℕ):ℝ)) / (((2:ℕ):ℝ) - 1)
      = 4/165 := by
    rw [show ((1:ℝ) - ((2:ℕ):ℝ)) = -((1:ℕ):ℝ) by norm_num,
      rpow_neg_ofNat (by norm_num) 1]
    norm_num
  have hep3l : (((40:ℕ):ℝ) + 5/4) ^ (1 - ((3:ℕ):ℝ)) / (((3:ℕ):ℝ) - 1)
      = 8/27225 := by
    rw [show ((1:ℝ) - ((3:ℕ):ℝ)) = -((2:ℕ):ℝ) by norm_num,
      rpow_neg_ofNat (by norm_num) 2]
    norm_num
  have hep3u : (((40:ℕ):ℝ) + 5/4 - 1) ^ (1 - ((3:ℕ):ℝ)) / (((3:ℕ):ℝ) - 1)
      = 8/25921 := by
    rw [show ((1:ℝ) - ((3:ℕ):ℝ)) = -((2:ℕ):ℝ) by norm_num,
      rpow_neg_ofNat (by norm_num) 2]
    norm_num
  have hep5u : (((40:ℕ):ℝ) + 5/4 - 1) ^ (1 - ((5:ℕ):ℝ)) / (((5:ℕ):ℝ) - 1)
      = 64/671898241 := by
    rw [show ((1:ℝ) - ((5:ℕ):ℝ)) = -((4:ℕ):ℝ) by norm_num,
      rpow_neg_ofNat (by norm_num) 4]
    norm_num
  have hep2c1u : (((40:ℕ):ℝ) + 1 - 1) ^ (1 - ((2:ℕ):ℝ)) / (((2:ℕ):ℝ) - 1)
      = 1/40 := by
    rw [show ((1:ℝ) - ((2:ℕ):ℝ)) = -((1:ℕ):ℝ) by norm_num,
      rpow_neg_ofNat (by norm_num) 1]
    norm_num
  rw [hep2l] at hH2
  rw [hep3l, hep3u] at hH3
  rw [hep5u] at hH5
  rw [hep2c1u] at hH2c1
  -- summabilities
  have hsum2 := hsum_gen 2 (le_refl 2)
  have hsum3 := hsum_gen 3 (by norm_num)
  have hsum5 := hsum_gen 5 (by norm_num)
  have hsum2c1 : Summable
      (fun k : ℕ => (((((k+40:ℕ)):ℝ)+1)) ^ (-(((2:ℕ)):ℝ))) := by
    have hmaj : Summable (fun k : ℕ => 1/(((k+1:ℕ)):ℝ)^2) :=
      hbase.comp_injective (fun a b h => by omega)
    apply Summable.of_nonneg_of_le
      (fun k => Real.rpow_nonneg (by positivity) _) _ hmaj
    intro k
    rw [rpow_neg_ofNat (by positivity) 2, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    linarith
  -- the per-term L and U with their families
  set f2 : ℕ → ℝ := fun k => ((((k+40:ℕ)):ℝ)+5/4) ^ (-(((2:ℕ)):ℝ)) with hf2
  set f3 : ℕ → ℝ := fun k => ((((k+40:ℕ)):ℝ)+5/4) ^ (-(((3:ℕ)):ℝ)) with hf3
  set f5 : ℕ → ℝ := fun k => ((((k+40:ℕ)):ℝ)+5/4) ^ (-(((5:ℕ)):ℝ)) with hf5
  set g2 : ℕ → ℝ := fun k => (((((k+40:ℕ)):ℝ)+1)) ^ (-(((2:ℕ)):ℝ)) with hg2
  have hDC_low : ∀ k : ℕ, (30/4 : ℝ) * f2 k
      ≤ (30/4)/((((k+40:ℕ)):ℝ)+1)/(((k+40:ℕ):ℝ)+5/4) := by
    intro k
    rw [hf2]
    dsimp only
    rw [rpow_neg_ofNat (by positivity) 2, ← div_eq_mul_inv]
    simp only [div_div]
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    have hle : ((((k+40:ℕ)):ℝ)+1) ≤ ((((k+40:ℕ)):ℝ)+5/4) := by linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) (k+40)]
  have hDC_up : ∀ k : ℕ,
      (30/4)/((((k+40:ℕ)):ℝ)+1)/(((k+40:ℕ):ℝ)+5/4)
      ≤ (30/4 : ℝ) * g2 k := by
    intro k
    rw [hg2]
    dsimp only
    rw [rpow_neg_ofNat (by positivity) 2, ← div_eq_mul_inv]
    simp only [div_div]
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    have hle : ((((k+40:ℕ)):ℝ)+1) ≤ ((((k+40:ℕ)):ℝ)+5/4) := by linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) (k+40)]
  have hC_eq : ∀ k : ℕ, (30:ℝ)^3/(12*((((k+40:ℕ)):ℝ)+5/4)^3)
      = 2250 * f3 k := by
    intro k
    rw [hf3]
    dsimp only
    rw [rpow_neg_ofNat (by positivity) 3]
    field_simp
    ring
  have hQ_eq : ∀ k : ℕ, (30:ℝ)^5/(80*((((k+40:ℕ)):ℝ)+5/4)^5)
      = 303750 * f5 k := by
    intro k
    rw [hf5]
    dsimp only
    rw [rpow_neg_ofNat (by positivity) 5]
    field_simp
    ring
  -- per-term bracketing of the summand
  have hterm_low : ∀ k : ℕ,
      (30/4 : ℝ) * f2 k + 2250 * f3 k - 303750 * f5 k
        ≤ sTermT 30 (k+40) := by
    intro k
    have hc := (abs_le.mp (hctrl k)).1
    have h1 := hDC_low k
    rw [hC_eq k, hQ_eq k] at hc
    linarith
  have hterm_up : ∀ k : ℕ, sTermT 30 (k+40)
      ≤ (30/4 : ℝ) * g2 k + 2250 * f3 k + 303750 * f5 k := by
    intro k
    have hc := (abs_le.mp (hctrl k)).2
    have h1 := hDC_up k
    rw [hC_eq k, hQ_eq k] at hc
    linarith
  -- summabilities of L, U, and the summand
  have hLsum : Summable (fun k : ℕ =>
      (30/4 : ℝ) * f2 k + 2250 * f3 k - 303750 * f5 k) :=
    ((hsum2.mul_left _).add (hsum3.mul_left _)).sub (hsum5.mul_left _)
  have hUsum : Summable (fun k : ℕ =>
      (30/4 : ℝ) * g2 k + 2250 * f3 k + 303750 * f5 k) :=
    ((hsum2c1.mul_left _).add (hsum3.mul_left _)).add (hsum5.mul_left _)
  have hSsum : Summable (fun k : ℕ => sTermT 30 (k+40)) := by
    apply Summable.of_norm_bounded hUsum
    intro k
    rw [Real.norm_eq_abs]
    have hc := hctrl k
    have h1 := hDC_up k
    have h2 := hDC_low k
    rw [hC_eq k, hQ_eq k] at hc
    have habs := abs_le.mp hc
    have hf5pos : 0 ≤ 303750 * f5 k := by
      apply mul_nonneg (by norm_num)
      rw [hf5]
      exact Real.rpow_nonneg (by positivity) _
    have hf2pos : 0 ≤ (30/4 : ℝ) * f2 k := by
      apply mul_nonneg (by norm_num)
      rw [hf2]
      exact Real.rpow_nonneg (by positivity) _
    have hf3pos : 0 ≤ 2250 * f3 k := by
      apply mul_nonneg (by norm_num)
      rw [hf3]
      exact Real.rpow_nonneg (by positivity) _
    rw [abs_le]
    constructor
    · linarith [habs.1]
    · linarith [habs.2]
  -- the tsum comparisons
  have hsplit_L : ∑' k : ℕ,
      ((30/4 : ℝ) * f2 k + 2250 * f3 k - 303750 * f5 k)
      = (30/4) * (∑' k, f2 k) + 2250 * (∑' k, f3 k)
        - 303750 * (∑' k, f5 k) := by
    rw [Summable.tsum_sub ((hsum2.mul_left _).add (hsum3.mul_left _))
        (hsum5.mul_left _),
      Summable.tsum_add (hsum2.mul_left _) (hsum3.mul_left _),
      tsum_mul_left, tsum_mul_left, tsum_mul_left]
  have hsplit_U : ∑' k : ℕ,
      ((30/4 : ℝ) * g2 k + 2250 * f3 k + 303750 * f5 k)
      = (30/4) * (∑' k, g2 k) + 2250 * (∑' k, f3 k)
        + 303750 * (∑' k, f5 k) := by
    rw [Summable.tsum_add ((hsum2c1.mul_left _).add (hsum3.mul_left _))
        (hsum5.mul_left _),
      Summable.tsum_add (hsum2c1.mul_left _) (hsum3.mul_left _),
      tsum_mul_left, tsum_mul_left, tsum_mul_left]
  have hf5nonneg : (0:ℝ) ≤ ∑' k, f5 k := by
    apply tsum_nonneg
    intro k
    rw [hf5]
    exact Real.rpow_nonneg (by positivity) _
  constructor
  · calc (8139/10000 : ℝ)
        ≤ (30/4) * (4/165) + 2250 * (8/27225)
          - 303750 * (64/671898241) := by norm_num
      _ ≤ (30/4) * (∑' k, f2 k) + 2250 * (∑' k, f3 k)
          - 303750 * (∑' k, f5 k) := by
          have h2 := hH2.1
          have h3 := hH3.1
          have h5 := hH5.2
          nlinarith
      _ = ∑' k : ℕ,
          ((30/4 : ℝ) * f2 k + 2250 * f3 k - 303750 * f5 k) :=
          hsplit_L.symm
      _ ≤ ∑' k : ℕ, sTermT 30 (k+40) :=
          Summable.tsum_le_tsum hterm_low hLsum hSsum
  · calc ∑' k : ℕ, sTermT 30 (k+40)
        ≤ ∑' k : ℕ,
          ((30/4 : ℝ) * g2 k + 2250 * f3 k + 303750 * f5 k) :=
          Summable.tsum_le_tsum hterm_up hSsum hUsum
      _ = (30/4) * (∑' k, g2 k) + 2250 * (∑' k, f3 k)
          + 303750 * (∑' k, f5 k) := hsplit_U
      _ ≤ (30/4) * (1/40) + 2250 * (8/25921)
          + 303750 * (64/671898241) := by
          have h2 := hH2c1.2
          have h3 := hH3.2
          have h5 := hH5.2
          nlinarith
      _ ≤ 9110/10000 := by norm_num

set_option maxHeartbeats 3200000 in
/-- **The head numeric**: `|Σ_{n<10} sTerm n − 3773/10000| ≤ 15/10000` —
ten kernel arctan brackets (orders 4/3/2), harmonic head `7381/2520`. -/
theorem head_window :
    |(∑ n ∈ Finset.range 10, sTerm n) - 3773/10000| ≤ 15/10000 := by
  obtain ⟨hl0, hu0⟩ := abs_le.mp
    (arctan_enclosure (show (0:ℝ) ≤ 2/5 by norm_num) 4)
  obtain ⟨hl1, hu1⟩ := abs_le.mp
    (arctan_enclosure (show (0:ℝ) ≤ 2/9 by norm_num) 3)
  obtain ⟨hl2, hu2⟩ := abs_le.mp
    (arctan_enclosure (show (0:ℝ) ≤ 2/13 by norm_num) 2)
  obtain ⟨hl3, hu3⟩ := abs_le.mp
    (arctan_enclosure (show (0:ℝ) ≤ 2/17 by norm_num) 2)
  obtain ⟨hl4, hu4⟩ := abs_le.mp
    (arctan_enclosure (show (0:ℝ) ≤ 2/21 by norm_num) 2)
  obtain ⟨hl5, hu5⟩ := abs_le.mp
    (arctan_enclosure (show (0:ℝ) ≤ 2/25 by norm_num) 2)
  obtain ⟨hl6, hu6⟩ := abs_le.mp
    (arctan_enclosure (show (0:ℝ) ≤ 2/29 by norm_num) 2)
  obtain ⟨hl7, hu7⟩ := abs_le.mp
    (arctan_enclosure (show (0:ℝ) ≤ 2/33 by norm_num) 2)
  obtain ⟨hl8, hu8⟩ := abs_le.mp
    (arctan_enclosure (show (0:ℝ) ≤ 2/37 by norm_num) 2)
  obtain ⟨hl9, hu9⟩ := abs_le.mp
    (arctan_enclosure (show (0:ℝ) ≤ 2/41 by norm_num) 2)
  norm_num [Finset.sum_range_succ] at hl0 hu0 hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4
  norm_num [Finset.sum_range_succ] at hl5 hu5 hl6 hu6 hl7 hu7 hl8 hu8 hl9 hu9
  have hexp : (∑ n ∈ Finset.range 10, sTerm n)
      = (7381/2520 : ℝ)
        - 2 * (Real.arctan (2/5) + Real.arctan (2/9) + Real.arctan (2/13)
          + Real.arctan (2/17) + Real.arctan (2/21) + Real.arctan (2/25)
          + Real.arctan (2/29) + Real.arctan (2/33) + Real.arctan (2/37)
          + Real.arctan (2/41)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, sTerm]
    norm_num
    ring
  rw [hexp, abs_le]
  constructor <;> nlinarith [hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3,
    hl4, hu4, hl5, hu5, hl6, hu6, hl7, hu7, hl8, hu8, hl9, hu9]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.arctan_enclosure
#print axioms CriticalLinePhasor.DVP.integral_lorentz_eq_arctan
#print axioms CriticalLinePhasor.DVP.arctan_two_enclosure
#print axioms CriticalLinePhasor.DVP.theta_one_series_integral
#print axioms CriticalLinePhasor.DVP.sTerm_control
#print axioms CriticalLinePhasor.DVP.sTerm_abs_le
#print axioms CriticalLinePhasor.DVP.sTerm_summable
#print axioms CriticalLinePhasor.DVP.S_window
#print axioms CriticalLinePhasor.DVP.head_window
#print axioms CriticalLinePhasor.DVP.sTermT_control
#print axioms CriticalLinePhasor.DVP.theta_T_series_integral
#print axioms CriticalLinePhasor.DVP.integral_lorentz_eq_arctan_T
#print axioms CriticalLinePhasor.DVP.theta30_tail_bracket
#print axioms CriticalLinePhasor.DVP.arctan_enclosure_all
#print axioms CriticalLinePhasor.DVP.arctan_anchor_half
#print axioms CriticalLinePhasor.DVP.arctan_half_range
end AxiomAudit
