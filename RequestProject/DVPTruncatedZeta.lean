import Mathlib

/-!
# DVP campaign, brick B1 (start): the truncated zeta representation

Target (ledger 299): for `Re s > 1` and `N ≥ 1`,

`ζ(s) = Σ_{n≤N} n^{−s} + N^{1−s}/(s−1) − s·∫_N^∞ {x}·x^{−s−1} dx`,

whose right side then continues to `Re s > 0`, `s ≠ 1`, giving the vertical
growth bounds B2/B3 with `N = ⌊t⌋`.

This file: the per-interval closed form (L1) and the finite telescoped
identity (L2) — the elementary core, no limits yet. -/

open Complex intervalIntegral

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The fractional-part integrand on one lattice interval, in closed form:
`∫_n^{n+1} (x−n)·x^{−s−1} dx = [x^{1−s}/(1−s)]ₙ^{n+1} + (n/s)·[x^{−s}]ₙ^{n+1}`. -/
theorem interval_fract_cpow {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : s ≠ 0)
    (hs1 : s ≠ 1) :
    ∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) - (n : ℂ)) * (x : ℂ) ^ (-s - 1)
      = ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) - (((n : ℝ) : ℝ) : ℂ) ^ (1 - s)) / (1 - s)
        + ((n : ℂ) / s) *
          ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) : ℝ) : ℂ) ^ (-s)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h0 : (0 : ℝ) ∉ Set.uIcc (n : ℝ) ((n : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    exact absurd h.1 (by linarith)
  -- split the integrand: (x − n)·x^{−s−1} = x^{−s} − n·x^{−s−1}
  have hsplit : ∀ x : ℝ, x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1) →
      ((x : ℂ) - (n : ℂ)) * (x : ℂ) ^ (-s - 1)
        = (x : ℂ) ^ (-s) - (n : ℂ) * (x : ℂ) ^ (-s - 1) := by
    intro x hx
    have hxpos : (0 : ℝ) < x := by
      rw [Set.uIcc_of_le (by linarith)] at hx
      linarith [hx.1]
    have hxne : (x : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hxpos
    have hpow : (x : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) := by
      have h2 := Complex.cpow_add 1 (-s - 1) hxne
      rw [Complex.cpow_one] at h2
      rw [← h2]
      congr 1
      ring
    linear_combination hpow
  rw [integral_congr hsplit]
  have hint1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s))
      MeasureTheory.volume (n : ℝ) ((n : ℝ) + 1) :=
    (intervalIntegral.intervalIntegrable_cpow (Or.inr h0))
  have hint2 : IntervalIntegrable (fun x : ℝ => (n : ℂ) * (x : ℂ) ^ (-s - 1))
      MeasureTheory.volume (n : ℝ) ((n : ℝ) + 1) :=
    (intervalIntegral.intervalIntegrable_cpow (Or.inr h0)).const_mul _
  rw [intervalIntegral.integral_sub hint1 hint2]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_cpow (Or.inr ⟨by
      intro h
      exact hs1 (by linear_combination -h), h0⟩)]
  rw [integral_cpow (Or.inr ⟨by
      intro h
      exact hs (by linear_combination -h - 1 + (1:ℂ)*0), h0⟩)]
  have he1 : (-s) + 1 = 1 - s := by ring
  have he2 : (-s - 1) + 1 = -s := by ring
  rw [he1, he2]
  field_simp
  ring

/-- Successor rule for the power: `k·k^{−s} = k^{1−s}` for `k ≥ 1`. -/
theorem natCast_mul_cpow_neg {k : ℕ} (hk : 1 ≤ k) (s : ℂ) :
    (((k : ℝ) : ℂ)) * (((k : ℝ) : ℂ)) ^ (-s) = (((k : ℝ) : ℂ)) ^ (1 - s) := by
  have hne : (((k : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact_mod_cast ne_of_gt this
  have h := Complex.cpow_add 1 (-s) hne
  rw [Complex.cpow_one] at h
  rw [← h]
  congr 1

/-- On one lattice interval the fractional part integrand agrees a.e. with the
affine one. -/
theorem fract_interval_congr (M : ℕ) (s : ℂ) :
    ∫ x : ℝ in (M : ℝ)..((M : ℝ) + 1), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
      = ∫ x : ℝ in (M : ℝ)..((M : ℝ) + 1), ((x : ℂ) - (M : ℂ)) * (x : ℂ) ^ (-s - 1) := by
  apply intervalIntegral.integral_congr_ae
  have hnull : ∀ᵐ x : ℝ, x ≠ (M : ℝ) + 1 := by
    rw [MeasureTheory.ae_iff]
    have : {x : ℝ | ¬x ≠ (M : ℝ) + 1} = {(M : ℝ) + 1} := by
      ext x
      simp [not_not]
    rw [this]
    exact MeasureTheory.measure_singleton _
  filter_upwards [hnull] with x hxne hx
  rw [Set.uIoc_of_le (by linarith)] at hx
  have hlt : x < (M : ℝ) + 1 := lt_of_le_of_ne hx.2 hxne
  have hfloor : ⌊x⌋ = (M : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast
      linarith [hx.1]
    · push_cast
      linarith
  have hfract : Int.fract x = x - (M : ℝ) := by
    rw [Int.fract, hfloor]
    push_cast
    ring
  rw [hfract]
  push_cast
  rfl

/-- **The telescoped identity (L2, lattice form)**: for `1 ≤ N ≤ M`,
`s · Σ_{N≤n<M} ∫_n^{n+1} {x}·x^{−s−1} dx
   = (M^{1−s} − N^{1−s})/(1−s) − Σ_{N<n≤M} n^{−s}`.
The tail of ζ in truncated form, with the integral kept as its lattice sum —
no measure-theoretic splitting enters. -/
theorem telescoped_fract_sum {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M)
    {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    s * ∑ n ∈ Finset.Ico N M,
        ∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
      = ((((M : ℝ)) : ℂ) ^ (1 - s) - (((N : ℝ)) : ℂ) ^ (1 - s)) / (1 - s)
        - ∑ n ∈ Finset.Ioc N M, (((n : ℝ)) : ℂ) ^ (-s) := by
  induction M with
  | zero => omega
  | succ M ih =>
    rcases Nat.lt_or_ge N (M + 1) with hlt | hge
    · have hNM' : N ≤ M := by omega
      have hM1 : 1 ≤ M := le_trans hN hNM'
      have hstep := ih hNM'
      rw [Finset.sum_Ico_succ_top hNM', Finset.sum_Ioc_succ_top hNM']
      rw [mul_add, hstep]
      -- the new interval's exact value
      rw [fract_interval_congr M s, interval_fract_cpow hM1 hs hs1]
      -- cpow successor identities
      have hA := natCast_mul_cpow_neg hM1 s
      have hB : ((((M : ℝ) + 1) : ℂ)) * ((((M : ℝ) + 1) : ℂ)) ^ (-s)
          = ((((M : ℝ) + 1) : ℂ)) ^ (1 - s) := by
        have h := natCast_mul_cpow_neg (k := M + 1) (by omega) s
        push_cast at h ⊢
        exact h
      have hs1' : (1 : ℂ) - s ≠ 0 := fun h => hs1 (by linear_combination -h)
      push_cast at hA hB ⊢
      field_simp
      linear_combination (s - 1) * hA + (1 - s) * hB
    · have hEq : N = M + 1 := by omega
      subst hEq
      simp

open Filter Topology

/-- Each lattice integral is bounded by `n^{−σ−1}` (for `σ ≥ 0`). -/
theorem interval_fract_norm_le {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hσ : 0 ≤ s.re) :
    ‖∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ ((n : ℝ)) ^ (-s.re - 1) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hbound : ∀ x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1),
      ‖((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ ≤ ((n : ℝ)) ^ (-s.re - 1) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0 : ℝ) < x := by linarith [hx.1]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    have h1 : |Int.fract x| ≤ 1 := by
      rw [abs_of_nonneg (Int.fract_nonneg x)]
      exact le_of_lt (Int.fract_lt_one x)
    have h2 : x ^ ((-s - 1).re) ≤ ((n : ℝ)) ^ (-s.re - 1) := by
      have hre : (-s - 1).re = -s.re - 1 := by simp
      rw [hre]
      exact Real.rpow_le_rpow_of_nonpos hnpos hx.1 (by linarith)
    calc |Int.fract x| * x ^ ((-s - 1).re)
        ≤ 1 * ((n : ℝ)) ^ (-s.re - 1) :=
          mul_le_mul h1 h2 (Real.rpow_nonneg (le_of_lt hxpos) _) (by norm_num)
      _ = ((n : ℝ)) ^ (-s.re - 1) := one_mul _
  calc ‖∫ x : ℝ in (n : ℝ)..((n : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ ((n : ℝ)) ^ (-s.re - 1) * |((n : ℝ) + 1) - (n : ℝ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
          hbound x (Set.uIoc_subset_uIcc hx)
    _ = ((n : ℝ)) ^ (-s.re - 1) := by
        simp

/-- Summability of the shifted powers for `σ > 1`. -/
theorem summable_shift_cpow {N : ℕ} {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ => (((N + 1 + k : ℕ) : ℝ) : ℂ) ^ (-s)) := by
  have hbase : Summable (fun n : ℕ => ((n : ℂ)) ^ (-s)) := by
    have h := (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
    apply h.congr
    intro n
    rw [Complex.cpow_neg, one_div]
  have hshift : Summable (fun k : ℕ => (((N + 1 + k : ℕ) : ℂ)) ^ (-s)) :=
    hbase.comp_injective (fun a b hab => by omega)
  apply hshift.congr
  intro k
  norm_num

/-- Summability of the lattice integrals for `σ > 0`. -/
theorem summable_shift_integral {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hσ : 0 < s.re) :
    Summable (fun k : ℕ => ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
      ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
  have hmaj : Summable (fun k : ℕ => (((N + k : ℕ) : ℝ)) ^ (-s.re - 1)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s.re - 1)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  apply Summable.of_norm_bounded hmaj
  intro k
  exact interval_fract_norm_le (by omega) (le_of_lt hσ)

/-- **B1 for `σ > 1` (the truncated tail representation)**:
`Σ_{n>N} n^{−s} = N^{1−s}/(s−1) − s·Σ_k ∫_{N+k}^{N+k+1} {x}·x^{−s−1} dx`. -/
theorem truncated_zeta_tail {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 1 < s.re) :
    ∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ) : ℂ) ^ (-s)
      = (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs1' : (1 : ℂ) - s ≠ 0 := fun h => hs1 (by linear_combination -h)
  have hsumP := summable_shift_cpow (N := N) hs
  have hsumI := summable_shift_integral hN (by linarith : (0:ℝ) < s.re)
  -- the three limits
  have hlimI : Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m,
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) atTop
      (𝓝 (∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) :=
    hsumI.hasSum.tendsto_sum_nat
  have hlimP : Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m,
      (((N + 1 + k : ℕ) : ℝ) : ℂ) ^ (-s)) atTop
      (𝓝 (∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ) : ℂ) ^ (-s))) :=
    hsumP.hasSum.tendsto_sum_nat
  have hlimM : Tendsto (fun m : ℕ => (((N + m : ℕ) : ℝ) : ℂ) ^ (1 - s)) atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hrw : (fun m : ℕ => ‖(((N + m : ℕ) : ℝ) : ℂ) ^ (1 - s)‖)
        = fun m : ℕ => (((N + m : ℕ) : ℝ)) ^ (-(s.re - 1)) := by
      funext m
      have hpos : (0:ℝ) < ((N + m : ℕ) : ℝ) := by
        have : 1 ≤ N + m := by omega
        exact_mod_cast this
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      congr 1
      simp [Complex.sub_re]
    rw [hrw]
    have hy : (0:ℝ) < s.re - 1 := by linarith
    have hcomp : Tendsto (fun m : ℕ => (((N + m : ℕ) : ℝ))) atTop atTop := by
      apply tendsto_natCast_atTop_atTop.comp
      simpa [Nat.add_comm] using tendsto_add_atTop_nat N
    exact (tendsto_rpow_neg_atTop hy).comp hcomp
  -- the telescoped identity along m, reindexed to `range m`
  have hident : ∀ m : ℕ,
      s * ∑ k ∈ Finset.range m,
          ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
        = ((((N + m : ℕ) : ℝ) : ℂ) ^ (1 - s) - (((N : ℝ)) : ℂ) ^ (1 - s)) / (1 - s)
          - ∑ k ∈ Finset.range m, (((N + 1 + k : ℕ) : ℝ) : ℂ) ^ (-s) := by
    intro m
    have h := telescoped_fract_sum hN (Nat.le_add_right N m) hs0 hs1
    rw [Finset.sum_Ico_eq_sum_range] at h
    simp only [Nat.add_sub_cancel_left] at h
    have hIoc : ∑ n ∈ Finset.Ioc N (N + m), (((n : ℝ)) : ℂ) ^ (-s)
        = ∑ k ∈ Finset.range m, (((N + 1 + k : ℕ) : ℝ) : ℂ) ^ (-s) := by
      refine Finset.sum_nbij' (fun n => n - (N + 1)) (fun k => N + 1 + k)
        (fun n hn => ?_) (fun k hk => ?_) (fun n hn => ?_) (fun k hk => ?_)
        (fun n hn => ?_)
      · rw [Finset.mem_Ioc] at hn
        rw [Finset.mem_range]
        omega
      · rw [Finset.mem_range] at hk
        rw [Finset.mem_Ioc]
        omega
      · rw [Finset.mem_Ioc] at hn
        omega
      · rw [Finset.mem_range] at hk
        omega
      · rw [Finset.mem_Ioc] at hn
        have hval : N + 1 + (n - (N + 1)) = n := by omega
        rw [hval]
    rw [hIoc] at h
    exact h
  -- pass to the limit on both sides
  have hlhs : Tendsto (fun m : ℕ => s * ∑ k ∈ Finset.range m,
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) atTop
      (𝓝 (s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) :=
    hlimI.const_mul s
  have hrhs : Tendsto (fun m : ℕ =>
      ((((N + m : ℕ) : ℝ) : ℂ) ^ (1 - s) - (((N : ℝ)) : ℂ) ^ (1 - s)) / (1 - s)
        - ∑ k ∈ Finset.range m, (((N + 1 + k : ℕ) : ℝ) : ℂ) ^ (-s)) atTop
      (𝓝 (((0 : ℂ) - (((N : ℝ)) : ℂ) ^ (1 - s)) / (1 - s)
        - ∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ) : ℂ) ^ (-s))) := by
    apply Tendsto.sub
    · exact (hlimM.sub_const _).div_const _
    · exact hlimP
  have hkey := tendsto_nhds_unique ((funext hident :
    (fun m : ℕ => s * ∑ k ∈ Finset.range m,
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) = _) ▸ hlhs) hrhs
  have hgoal : ∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ) : ℂ) ^ (-s)
      = (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
    have hs1'' : s - 1 ≠ 0 := fun h => hs1 (by linear_combination h)
    field_simp at hkey ⊢
    linear_combination -hkey
  exact hgoal

/-- **B1, the truncated zeta representation for `σ > 1`**:
`ζ(s) = Σ_{n≤N} n^{−s} + N^{1−s}/(s−1) − s·Σ_k ∫_{N+k}^{N+k+1} {x}·x^{−s−1}dx`.
Head, boundary, and lattice-integral tail — every vertical growth bound of the
zero-free-region campaign reads this identity at `N = ⌊t⌋`. -/
theorem truncated_zeta {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s
      = (∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
  have hζ := zeta_eq_tsum_one_div_nat_cpow hs
  have hsumm : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
  have hsplit := hsumm.sum_add_tsum_nat_add (N + 1)
  have htail_congr : (∑' i : ℕ, 1 / ((i + (N + 1) : ℕ) : ℂ) ^ s)
      = ∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ) : ℂ) ^ (-s) := by
    apply tsum_congr
    intro k
    rw [Complex.cpow_neg, one_div]
    congr 2
    push_cast
    ring
  have hhead_congr : (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s)
      = ∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.cpow_neg, one_div]
    congr 2
  have htail := truncated_zeta_tail hN hs
  -- assemble: ζ = head + tail, and the tail has its closed form
  have hζsplit : riemannZeta s
      = (∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + ∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ) : ℂ) ^ (-s) := by
    rw [hζ, ← hsplit, hhead_congr, htail_congr]
  rw [hζsplit, htail]
  ring

/-- **Cutoff independence of the truncated representation** on `σ > 0`: the
right side of `truncated_zeta` takes the same value at `N+1` as at `N` — the
algebraic half of its analytic continuation, with no analyticity input.  The
mechanism is the compiled telescoped identity at a single interval. -/
theorem truncated_rep_succ {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hσ : 0 < s.re)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (∑ n ∈ Finset.range (N + 2), (((n : ℝ)) : ℂ) ^ (-s))
      + (((N + 1 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)
      - s * ∑' k : ℕ, ∫ x : ℝ in ((N + 1 + k : ℕ) : ℝ)..(((N + 1 + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
    = (∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
      + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
      - s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
  have hs1' : (1 : ℂ) - s ≠ 0 := fun h => hs1 (by linear_combination -h)
  have hs1'' : s - 1 ≠ 0 := fun h => hs1 (by linear_combination h)
  -- tsum shift: T_N = ∫_N + T_{N+1}
  have hsumI := summable_shift_integral hN hσ
  have hshift := hsumI.tsum_eq_zero_add
  have hreindex : (∑' k : ℕ, ∫ x : ℝ in ((N + (k + 1) : ℕ) : ℝ)..(((N + (k + 1) : ℕ) : ℝ) + 1),
      ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      = ∑' k : ℕ, ∫ x : ℝ in ((N + 1 + k : ℕ) : ℝ)..(((N + 1 + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
    apply tsum_congr
    intro k
    have : N + (k + 1) = N + 1 + k := by omega
    rw [this]
  rw [hreindex] at hshift
  -- the single-interval telescoped identity
  have hL2 := telescoped_fract_sum hN (Nat.le_add_right N 1) hs0 hs1
  have hIco : Finset.Ico N (N + 1) = {N} := by
    rw [Nat.Ico_succ_singleton]
  have hIoc : Finset.Ioc N (N + 1) = {N + 1} := by
    rw [Nat.Ioc_succ_singleton]
  rw [hIco, hIoc, Finset.sum_singleton, Finset.sum_singleton] at hL2
  -- head extension
  have hhead : (∑ n ∈ Finset.range (N + 2), (((n : ℝ)) : ℂ) ^ (-s))
      = (∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N + 1 : ℕ) : ℝ) : ℂ) ^ (-s) := by
    rw [Finset.sum_range_succ]
  rw [hhead, hshift]
  field_simp at hL2 ⊢
  linear_combination -hL2

/-- **The tail in elementary closed form**: the lattice-integral tail equals
the sum of explicit cpow expressions — so the truncated representation's
analytic continuation needs no parametric-integral machinery, only locally
uniform sums of elementary functions. -/
theorem tail_closed_form {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) :
    (∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      = ∑' k : ℕ,
          ((((((N + k : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s)
              - ((((N + k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - s)) / (1 - s)
            + (((N + k : ℕ) : ℂ) / s) *
              (((((N + k : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
                - ((((N + k : ℕ) : ℝ) : ℝ) : ℂ) ^ (-s))) := by
  refine tsum_congr fun k => ?_
  rw [fract_interval_congr (N + k) s, interval_fract_cpow (by omega) hs0 hs1]

/-- **Analyticity of the lattice tail** on every right half-plane
`{σ₀ < Re s} \ {1}` (`σ₀ > 0`): each term is congruent to its elementary
closed form, and the compiled integral bound gives the uniform Weierstrass
majorant `(N+k)^{−σ₀−1}`. -/
theorem tail_differentiableOn {N : ℕ} (hN : 1 ≤ N) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    DifferentiableOn ℂ
      (fun s : ℂ => ∑' k : ℕ,
        ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      {s : ℂ | σ₀ < s.re ∧ s ≠ 1} := by
  have hU : IsOpen {s : ℂ | σ₀ < s.re ∧ s ≠ 1} := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const Complex.continuous_re
    · exact isOpen_compl_singleton
  have hsummu : Summable (fun k : ℕ => (((N + k : ℕ) : ℝ)) ^ (-σ₀ - 1)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-σ₀ - 1)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  apply differentiableOn_tsum_of_summable_norm hsummu
  · -- each term differentiable, via the closed form
    intro k
    have hbase1 : ((((N + k : ℕ) : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
      have : (0:ℝ) < ((N + k : ℕ) : ℝ) + 1 := by positivity
      exact_mod_cast ne_of_gt this
    have hbase0 : ((((N + k : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
      have : (0:ℝ) < ((N + k : ℕ) : ℝ) := by
        have : 1 ≤ N + k := by omega
        exact_mod_cast this
      exact_mod_cast ne_of_gt this
    have hclosed : DifferentiableOn ℂ
        (fun s : ℂ =>
          ((((((N + k : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s)
              - ((((N + k : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - s)) / (1 - s)
            + (((N + k : ℕ) : ℂ) / s) *
              (((((N + k : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
                - ((((N + k : ℕ) : ℝ) : ℝ) : ℂ) ^ (-s))))
        {s : ℂ | σ₀ < s.re ∧ s ≠ 1} := by
      have hd1 : Differentiable ℂ (fun s : ℂ => (1 : ℂ) - s) :=
        (differentiable_const _).sub differentiable_id
      have hdneg : Differentiable ℂ (fun s : ℂ => -s) := differentiable_id.neg
      apply DifferentiableOn.add
      · apply DifferentiableOn.div
        · exact ((hd1.const_cpow (Or.inl hbase1)).sub
            (hd1.const_cpow (Or.inl hbase0))).differentiableOn
        · exact hd1.differentiableOn
        · intro s hs
          exact fun h => hs.2 (by linear_combination -h)
      · apply DifferentiableOn.mul
        · apply DifferentiableOn.div
          · exact (differentiable_const _).differentiableOn
          · exact differentiable_id.differentiableOn
          · intro s hs
            intro h
            rw [h] at hs
            simp at hs
            linarith [hs, hσ₀]
        · exact ((hdneg.const_cpow (Or.inl hbase1)).sub
            (hdneg.const_cpow (Or.inl hbase0))).differentiableOn
    apply hclosed.congr
    intro s hs
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      simp at hs
      linarith [hs, hσ₀]
    rw [fract_interval_congr (N + k) s, interval_fract_cpow (by omega) hs0 hs.2]
  · exact hU
  · -- the uniform majorant
    intro k s hs
    have hσ : 0 ≤ s.re := by linarith [hs.1, hσ₀]
    calc ‖∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
        ≤ (((N + k : ℕ) : ℝ)) ^ (-s.re - 1) :=
          interval_fract_norm_le (by omega) hσ
      _ ≤ (((N + k : ℕ) : ℝ)) ^ (-σ₀ - 1) := by
          apply Real.rpow_le_rpow_of_exponent_le
          · have : 1 ≤ N + k := by omega
            exact_mod_cast this
          · linarith [hs.1]

/-- The truncated representation: head, boundary, and lattice tail. -/
noncomputable def truncatedRep (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
    + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
    - s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

/-- `truncated_zeta`, repackaged: ζ agrees with the truncated representation
on the half-plane `σ > 1`. -/
theorem zeta_eqOn_truncatedRep {N : ℕ} (hN : 1 ≤ N) :
    Set.EqOn riemannZeta (truncatedRep N) {s : ℂ | 1 < s.re} := by
  intro s hs
  exact truncated_zeta hN hs

/-- **The truncated representation is analytic** on `{σ₀ < Re s} \ {1}` for
every `σ₀ > 0`. -/
theorem truncatedRep_differentiableOn {N : ℕ} (hN : 1 ≤ N) {σ₀ : ℝ}
    (hσ₀ : 0 < σ₀) :
    DifferentiableOn ℂ (truncatedRep N) {s : ℂ | σ₀ < s.re ∧ s ≠ 1} := by
  have hU : IsOpen {s : ℂ | σ₀ < s.re ∧ s ≠ 1} := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const Complex.continuous_re
    · exact isOpen_compl_singleton
  unfold truncatedRep
  apply DifferentiableOn.sub
  · apply DifferentiableOn.add
    · -- the head: termwise; the `n = 0` term is the zero function on the set
      apply DifferentiableOn.fun_sum
      intro n _
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        have hzero : Set.EqOn (fun s : ℂ => (((0 : ℕ) : ℝ) : ℂ) ^ (-s))
            (fun _ : ℂ => (0 : ℂ)) {s : ℂ | σ₀ < s.re ∧ s ≠ 1} := by
          intro s hs
          have hsne : -s ≠ 0 := by
            intro h
            have : s = 0 := by linear_combination -h
            rw [this] at hs
            simp at hs
            linarith [hs, hσ₀]
          simp [Complex.zero_cpow hsne]
        exact (differentiableOn_const 0).congr hzero
      · have hbase : (((n : ℝ)) : ℂ) ≠ 0 := by
          have : (0:ℝ) < (n : ℝ) := by exact_mod_cast hpos
          exact_mod_cast ne_of_gt this
        exact ((differentiable_id.neg).const_cpow (Or.inl hbase)).differentiableOn
    · -- the boundary term
      have hbase : (((N : ℝ)) : ℂ) ≠ 0 := by
        have : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
        exact_mod_cast ne_of_gt this
      apply DifferentiableOn.div
      · exact (((differentiable_const _).sub
          differentiable_id).const_cpow (Or.inl hbase)).differentiableOn
      · exact (differentiable_id.sub (differentiable_const _)).differentiableOn
      · intro s hs
        intro h
        exact hs.2 (by linear_combination h)
  · -- s times the analytic tail
    exact differentiable_id.differentiableOn.mul (tail_differentiableOn hN hσ₀)

/-- **The continuation**: ζ agrees with the truncated representation on all of
`{σ₀ < Re s} \ {1}` — by the identity theorem chained across four convex
pieces (σ > 1; upper; lower; the middle band), each anchored in the previous
one.  No punctured-region connectivity machinery is needed. -/
theorem zeta_eqOn_truncatedRep_ext {N : ℕ} (hN : 1 ≤ N) {σ₀ : ℝ}
    (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    Set.EqOn riemannZeta (truncatedRep N) {s : ℂ | σ₀ < s.re ∧ s ≠ 1} := by
  have hUopen : IsOpen {s : ℂ | σ₀ < s.re ∧ s ≠ 1} := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const Complex.continuous_re
    · exact isOpen_compl_singleton
  have hζdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | σ₀ < s.re ∧ s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs.2).differentiableWithinAt
  have hRdiff := truncatedRep_differentiableOn hN h0
  have key : ∀ V : Set ℂ, IsOpen V → Convex ℝ V →
      V ⊆ {s : ℂ | σ₀ < s.re ∧ s ≠ 1} →
      ∀ z₀ ∈ V, riemannZeta =ᶠ[𝓝 z₀] truncatedRep N →
      Set.EqOn riemannZeta (truncatedRep N) V := by
    intro V hVo hVc hVU z₀ hz₀ hev
    exact ((hζdiff.mono hVU).analyticOnNhd hVo).eqOn_of_preconnected_of_eventuallyEq
      ((hRdiff.mono hVU).analyticOnNhd hVo) hVc.isPreconnected hz₀ hev
  have mkev : ∀ (W : Set ℂ), IsOpen W →
      Set.EqOn riemannZeta (truncatedRep N) W →
      ∀ z₀ ∈ W, riemannZeta =ᶠ[𝓝 z₀] truncatedRep N := by
    intro W hWo hWeq z₀ hz₀
    exact Filter.eventuallyEq_of_mem (hWo.mem_nhds hz₀) hWeq
  have hU₁open : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hEq₁ := zeta_eqOn_truncatedRep (N := N) hN
  -- upper piece
  have hUpopen : IsOpen {s : ℂ | σ₀ < s.re ∧ 0 < s.im} := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const Complex.continuous_re
    · exact isOpen_lt continuous_const Complex.continuous_im
  have hEqp : Set.EqOn riemannZeta (truncatedRep N)
      {s : ℂ | σ₀ < s.re ∧ 0 < s.im} := by
    apply key _ hUpopen
      ((convex_halfSpace_re_gt σ₀).inter (convex_halfSpace_im_gt 0))
      (fun s hs => ⟨hs.1, fun h => by
        rw [h] at hs
        simp at hs⟩)
      (2 + Complex.I)
      ⟨by simp; linarith, by simp⟩
    exact mkev _ hU₁open hEq₁ _ (by simp)
  -- lower piece
  have hUmopen : IsOpen {s : ℂ | σ₀ < s.re ∧ s.im < 0} := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const Complex.continuous_re
    · exact isOpen_lt Complex.continuous_im continuous_const
  have hEqm : Set.EqOn riemannZeta (truncatedRep N)
      {s : ℂ | σ₀ < s.re ∧ s.im < 0} := by
    apply key _ hUmopen
      ((convex_halfSpace_re_gt σ₀).inter (convex_halfSpace_im_lt 0))
      (fun s hs => ⟨hs.1, fun h => by
        rw [h] at hs
        simp at hs⟩)
      (2 - Complex.I)
      ⟨by simp; linarith, by simp⟩
    exact mkev _ hU₁open hEq₁ _ (by simp)
  -- middle piece
  have hU₀open : IsOpen {s : ℂ | σ₀ < s.re ∧ s.re < 1} := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const Complex.continuous_re
    · exact isOpen_lt Complex.continuous_re continuous_const
  have hEq₀ : Set.EqOn riemannZeta (truncatedRep N)
      {s : ℂ | σ₀ < s.re ∧ s.re < 1} := by
    apply key _ hU₀open
      ((convex_halfSpace_re_gt σ₀).inter (convex_halfSpace_re_lt 1))
      (fun s hs => ⟨hs.1, fun h => by
        rw [h] at hs
        simp at hs⟩)
      ((((σ₀ + 1) / 2 : ℝ) : ℂ) + Complex.I)
      ⟨by simp; linarith, by simp; linarith⟩
    exact mkev _ hUpopen hEqp _ (by simp; linarith)
  -- assemble
  intro s hs
  rcases lt_trichotomy s.im 0 with him | him | him
  · exact hEqm ⟨hs.1, him⟩
  · rcases lt_or_ge s.re 1 with hre | hre
    · exact hEq₀ ⟨hs.1, hre⟩
    · rcases eq_or_lt_of_le hre with heq | hlt
      · exact absurd (Complex.ext heq.symm him) hs.2
      · exact hEq₁ hlt
  · exact hEqp ⟨hs.1, him⟩

/-- **B1, extended: the truncated representation of ζ on `Re s > 0`**. -/
theorem truncated_zeta_pos_re {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = truncatedRep N s := by
  have h0 : 0 < min (s.re / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  have h1 : min (s.re / 2) (1 / 2) < 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  exact zeta_eqOn_truncatedRep_ext hN h0 h1
    ⟨lt_of_le_of_lt (min_le_left _ _) (by linarith), hs1⟩

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.interval_fract_cpow
#print axioms CriticalLinePhasor.DVP.natCast_mul_cpow_neg
#print axioms CriticalLinePhasor.DVP.fract_interval_congr
#print axioms CriticalLinePhasor.DVP.telescoped_fract_sum
#print axioms CriticalLinePhasor.DVP.interval_fract_norm_le
#print axioms CriticalLinePhasor.DVP.summable_shift_cpow
#print axioms CriticalLinePhasor.DVP.summable_shift_integral
#print axioms CriticalLinePhasor.DVP.truncated_zeta_tail
#print axioms CriticalLinePhasor.DVP.truncated_zeta
#print axioms CriticalLinePhasor.DVP.truncated_rep_succ
#print axioms CriticalLinePhasor.DVP.tail_closed_form
#print axioms CriticalLinePhasor.DVP.tail_differentiableOn
#print axioms CriticalLinePhasor.DVP.truncatedRep_differentiableOn
#print axioms CriticalLinePhasor.DVP.zeta_eqOn_truncatedRep_ext
#print axioms CriticalLinePhasor.DVP.truncated_zeta_pos_re
end AxiomAudit
