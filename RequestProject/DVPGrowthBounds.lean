import RequestProject.DVPTruncatedZeta

/-!
# DVP campaign, brick B2: vertical growth bounds

From the compiled truncated representation (`truncated_zeta_pos_re`), bound
the three blocks at `N = ⌊|t|⌋` on the region `σ ≥ 1 − 1/log|t|`, `|t| ≥ e²`:
head `≤ e(1 + log N)`, boundary `≤ e/|t|·|t| = O(1)`, tail `= O(1)` — giving
`|ζ(σ+it)| ≤ C log|t|`.  This file: the head bound.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

/-- Each head term of index `n ≥ 1` is at most `e/n` on the region
`1 − 1/log T ≤ σ`, `n ≤ T`, `T ≥ e` . -/
theorem head_term_bound {n : ℕ} (hn : 1 ≤ n) {s : ℂ} {T : ℝ}
    (hT : Real.exp 1 ≤ T) (hnT : (n : ℝ) ≤ T)
    (hσ : 1 - 1 / Real.log T ≤ s.re) :
    ‖(((n : ℝ)) : ℂ) ^ (-s)‖ ≤ Real.exp 1 / (n : ℝ) := by
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have h1T : (1:ℝ) ≤ T := by
    have h := Real.add_one_le_exp (1:ℝ)
    linarith
  have hlogT : (1:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 1) hT
    rwa [Real.log_exp] at this
  have hlogTpos : (0:ℝ) < Real.log T := by linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
  have hre : (-s).re = -s.re := by simp
  rw [hre]
  -- n^{−σ} = n^{−1}·n^{1−σ} and n^{1−σ} ≤ e
  have hsplit : (n:ℝ) ^ (-s.re) = ((n:ℝ) ^ (-(1:ℝ))) * ((n:ℝ) ^ (1 - s.re)) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  rw [hsplit]
  have hfac : (n:ℝ) ^ (1 - s.re) ≤ Real.exp 1 := by
    rcases le_or_gt s.re 1 with hcase | hcase
    · calc (n:ℝ) ^ (1 - s.re) ≤ T ^ (1 - s.re) := by
            apply Real.rpow_le_rpow (le_of_lt hnpos) hnT (by linarith)
        _ ≤ T ^ (1 / Real.log T) := by
            apply Real.rpow_le_rpow_of_exponent_le h1T
            have h2 : 1 - s.re ≤ 1 / Real.log T := by linarith
            exact h2
        _ = Real.exp 1 := by
            rw [Real.rpow_def_of_pos hTpos]
            congr 1
            field_simp
    · calc (n:ℝ) ^ (1 - s.re) ≤ (n:ℝ) ^ (0:ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le
            · exact_mod_cast hn
            · linarith
        _ = 1 := Real.rpow_zero _
        _ ≤ Real.exp 1 := by
            have := Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)
            linarith
  calc ((n:ℝ) ^ (-(1:ℝ))) * ((n:ℝ) ^ (1 - s.re))
      ≤ ((n:ℝ) ^ (-(1:ℝ))) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left hfac (Real.rpow_nonneg (le_of_lt hnpos) _)
    _ = Real.exp 1 / (n:ℝ) := by
        rw [Real.rpow_neg_one]
        ring

/-- **The head bound**: on the region the head sum is at most `e·(1+log N)`. -/
theorem head_sum_bound {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs0 : s ≠ 0) {T : ℝ}
    (hT : Real.exp 1 ≤ T) (hNT : (N : ℝ) ≤ T)
    (hσ : 1 - 1 / Real.log T ≤ s.re) :
    ‖∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s)‖
      ≤ Real.exp 1 * (1 + Real.log N) := by
  have hsne : -s ≠ 0 := neg_ne_zero.mpr hs0
  calc ‖∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s)‖
      ≤ ∑ n ∈ Finset.range (N + 1), ‖(((n : ℝ)) : ℂ) ^ (-s)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1),
          (if n = 0 then 0 else Real.exp 1 / (n : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          simp [Complex.zero_cpow hsne]
        · rw [if_neg (by omega)]
          exact head_term_bound hpos hT
            (le_trans (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn)) hNT)
            hσ
    _ = Real.exp 1 * ∑ n ∈ Finset.range (N + 1),
          (if n = 0 then 0 else 1 / (n : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        split_ifs with h
        · ring
        · ring
    _ ≤ Real.exp 1 * (1 + Real.log N) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos 1))
        have hharm : ∑ n ∈ Finset.range (N + 1),
            (if n = 0 then 0 else 1 / (n : ℝ)) = ((harmonic N : ℚ) : ℝ) := by
          rw [harmonic_eq_sum_Icc]
          push_cast
          rw [show Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) by
            ext n
            simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
            omega]
          rw [Finset.sum_insert (by simp)]
          rw [if_pos rfl, zero_add]
          apply Finset.sum_congr rfl
          intro n hn
          rw [if_neg (by rw [Finset.mem_Icc] at hn; omega), one_div]
        rw [hharm]
        exact_mod_cast harmonic_le_one_add_log N

/-- The region mechanism, factored: `x^{1−σ} ≤ e` for `1 ≤ x ≤ T`,
`σ ≥ 1 − 1/log T`. -/
theorem base_rpow_one_sub_re_le {x : ℝ} (hx : 1 ≤ x) {σ : ℝ} {T : ℝ}
    (hT : Real.exp 1 ≤ T) (hxT : x ≤ T) (hσ : 1 - 1 / Real.log T ≤ σ) :
    x ^ (1 - σ) ≤ Real.exp 1 := by
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have h1T : (1:ℝ) ≤ T := by
    have h := Real.add_one_le_exp (1:ℝ)
    linarith
  have hlogT : (1:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 1) hT
    rwa [Real.log_exp] at this
  rcases le_or_gt σ 1 with hcase | hcase
  · calc x ^ (1 - σ) ≤ T ^ (1 - σ) :=
        Real.rpow_le_rpow (by linarith) hxT (by linarith)
      _ ≤ T ^ (1 / Real.log T) := by
          apply Real.rpow_le_rpow_of_exponent_le h1T
          linarith
      _ = Real.exp 1 := by
          rw [Real.rpow_def_of_pos hTpos]
          congr 1
          field_simp
  · calc x ^ (1 - σ) ≤ x ^ (0:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    _ = 1 := Real.rpow_zero _
    _ ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp (1:ℝ)
        linarith

/-- **The boundary bound**: `‖N^{1−s}/(s−1)‖ ≤ e/2` on the region with
`|Im s| ≥ 2`. -/
theorem boundary_bound {N : ℕ} (hN : 1 ≤ N) {s : ℂ} {T : ℝ}
    (hT : Real.exp 1 ≤ T) (hNT : (N : ℝ) ≤ T)
    (hσ : 1 - 1 / Real.log T ≤ s.re) (him : 2 ≤ |s.im|) :
    ‖(((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ Real.exp 1 / 2 := by
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
  have hre : (1 - s).re = 1 - s.re := by simp
  rw [hre]
  have hnum : ((N:ℝ)) ^ (1 - s.re) ≤ Real.exp 1 :=
    base_rpow_one_sub_re_le (by exact_mod_cast hN) hT hNT hσ
  have hden : (2:ℝ) ≤ ‖s - 1‖ := by
    calc (2:ℝ) ≤ |s.im| := him
      _ = |(s - 1).im| := by simp
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hdenpos : (0:ℝ) < ‖s - 1‖ := by linarith
  gcongr <;> first
    | exact hnum
    | exact hden
    | positivity
    | linarith

/-- One-interval integral comparison: `(a+1)^{−p} ≤ ∫_a^{a+1} x^{−p}` for
`a ≥ 1`. -/
theorem rpow_le_interval_integral {a : ℝ} (ha : 1 ≤ a) {p : ℝ} (hp : 0 < p) :
    (a + 1) ^ (-p) ≤ ∫ x : ℝ in a..(a + 1), x ^ (-p) := by
  have h0 : (0:ℝ) ∉ Set.uIcc a (a + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (-p))
      MeasureTheory.volume a (a + 1) :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr h0)
  have hconst : IntervalIntegrable (fun _ : ℝ => (a + 1) ^ (-p))
      MeasureTheory.volume a (a + 1) := intervalIntegrable_const
  have hmono : ∀ x ∈ Set.uIcc a (a + 1), (a + 1) ^ (-p) ≤ x ^ (-p) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxpos : (0:ℝ) < x := by linarith [hx.1]
    exact Real.rpow_le_rpow_of_nonpos hxpos hx.2 (by linarith)
  calc (a + 1) ^ (-p)
      = ∫ _ : ℝ in a..(a + 1), (a + 1) ^ (-p) := by
        rw [intervalIntegral.integral_const]
        simp
    _ ≤ ∫ x : ℝ in a..(a + 1), x ^ (-p) := by
        apply intervalIntegral.integral_mono_on (by linarith) hconst hint
        intro x hx
        exact hmono x (Set.mem_uIcc_of_le hx.1 hx.2)

/-- The telescoped partial-sum comparison:
`Σ_{k<m} (N+1+k)^{−p} ≤ N^{1−p}/(p−1)`. -/
theorem rpow_tail_partial {N : ℕ} (hN : 1 ≤ N) {p : ℝ} (hp : 1 < p) (m : ℕ) :
    ∑ k ∈ Finset.range m, (((N + 1 + k : ℕ) : ℝ)) ^ (-p)
      ≤ ((N : ℝ)) ^ (1 - p) / (p - 1) := by
  have hkey : ∀ j : ℕ, 1 ≤ j →
      ∫ x : ℝ in (j : ℝ)..((j : ℝ) + 1), x ^ (-p)
        = ((j : ℝ) ^ (1 - p) - ((j : ℝ) + 1) ^ (1 - p)) / (p - 1) := by
    intro j hj
    have hjpos : (0:ℝ) < (j : ℝ) := by exact_mod_cast hj
    have h0 : (0:ℝ) ∉ Set.uIcc (j : ℝ) ((j : ℝ) + 1) := by
      rw [Set.uIcc_of_le (by linarith)]
      intro h
      linarith [h.1]
    rw [integral_rpow (Or.inr ⟨by intro h; linarith, h0⟩)]
    have he : -p + 1 = 1 - p := by ring
    rw [he]
    have hpne : p - 1 ≠ 0 := by intro h; linarith
    have h1pne : (1:ℝ) - p ≠ 0 := by intro h; linarith
    field_simp
    ring
  -- partial sums of the integrals telescope
  have htel : ∀ m : ℕ,
      ∑ k ∈ Finset.range m, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        x ^ (-p)
      = (((N : ℝ)) ^ (1 - p) - (((N + m : ℕ) : ℝ)) ^ (1 - p)) / (p - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, hkey (N + m) (by omega)]
      push_cast
      ring
  calc ∑ k ∈ Finset.range m, (((N + 1 + k : ℕ) : ℝ)) ^ (-p)
      ≤ ∑ k ∈ Finset.range m,
          ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1), x ^ (-p) := by
        apply Finset.sum_le_sum
        intro k _
        have h := rpow_le_interval_integral
          (a := ((N + k : ℕ) : ℝ)) (by exact_mod_cast (by omega : 1 ≤ N + k))
          (by linarith : (0:ℝ) < p)
        calc (((N + 1 + k : ℕ) : ℝ)) ^ (-p)
            = (((N + k : ℕ) : ℝ) + 1) ^ (-p) := by
              congr 1
              push_cast
              ring
          _ ≤ _ := h
    _ = (((N : ℝ)) ^ (1 - p) - (((N + m : ℕ) : ℝ)) ^ (1 - p)) / (p - 1) := htel m
    _ ≤ ((N : ℝ)) ^ (1 - p) / (p - 1) := by
        have hB : (0:ℝ) ≤ (((N + m : ℕ) : ℝ)) ^ (1 - p) :=
          Real.rpow_nonneg (by positivity) _
        have hp1 : (0:ℝ) < p - 1 := by linarith
        gcongr
        linarith

/-- The tail tsum comparison: `Σ_{k} (N+1+k)^{−p} ≤ N^{1−p}/(p−1)`. -/
theorem rpow_tail_tsum_le {N : ℕ} (hN : 1 ≤ N) {p : ℝ} (hp : 1 < p) :
    ∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ)) ^ (-p)
      ≤ ((N : ℝ)) ^ (1 - p) / (p - 1) :=
  Real.tsum_le_of_sum_range_le
    (fun _ => Real.rpow_nonneg (by positivity) _)
    (fun m => rpow_tail_partial hN hp m)

/-- **The tail block bound**: on the region, the whole tail term of the
truncated representation is at most `12e` — an absolute constant. -/
theorem tail_block_bound {N : ℕ} (hN : 1 ≤ N) {s : ℂ} {T : ℝ}
    (hT : Real.exp 1 ≤ T) (hNT : (N : ℝ) ≤ T) (hTN : T ≤ 2 * N)
    (hσl : (1:ℝ)/2 ≤ s.re) (hσ : 1 - 1 / Real.log T ≤ s.re) (hσu : s.re ≤ 2)
    (him : |s.im| ≤ T) :
    ‖s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ 12 * Real.exp 1 := by
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hT2 : (2:ℝ) ≤ T := by
    have h := Real.add_one_le_exp (1:ℝ)
    linarith
  have hσpos : (0:ℝ) < s.re := by linarith
  -- ‖s‖ ≤ 2T
  have hs_norm : ‖s‖ ≤ 2 * T := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 2 + T := by
          apply add_le_add
          · rw [abs_of_pos hσpos]
            exact hσu
          · exact him
      _ ≤ 2 * T := by linarith
  -- the norm sum
  have hsumI := summable_shift_integral hN hσpos
  have hmajsum : Summable (fun k : ℕ => (((N + k : ℕ) : ℝ)) ^ (-s.re - 1)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s.re - 1)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  have htail_sum : (∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 1))
      ≤ 3 * ((N:ℝ)) ^ (-s.re) := by
    have hshift := hmajsum.tsum_eq_zero_add
    have hreindex : (∑' k : ℕ, (((N + (k + 1) : ℕ) : ℝ)) ^ (-s.re - 1))
        = ∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ)) ^ (-s.re - 1) := by
      refine tsum_congr fun k => ?_
      congr 2
      omega
    rw [hshift, hreindex]
    have h1 : (((N + 0 : ℕ) : ℝ)) ^ (-s.re - 1) ≤ ((N:ℝ)) ^ (-s.re) := by
      simp only [Nat.add_zero]
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
      linarith
    have h2 : (∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ)) ^ (-s.re - 1))
        ≤ 2 * ((N:ℝ)) ^ (-s.re) := by
      have hp : (1:ℝ) < s.re + 1 := by linarith
      have h := rpow_tail_tsum_le hN hp
      have hexp : -(s.re + 1) = -s.re - 1 := by ring
      have hexp2 : (1:ℝ) - (s.re + 1) = -s.re := by ring
      rw [hexp, hexp2] at h
      calc (∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ)) ^ (-s.re - 1))
          ≤ ((N:ℝ)) ^ (-s.re) / (s.re + 1 - 1) := h
        _ = ((N:ℝ)) ^ (-s.re) / s.re := by ring_nf
        _ ≤ ((N:ℝ)) ^ (-s.re) / (1/2) := by
            apply div_le_div_of_nonneg_left (Real.rpow_nonneg (le_of_lt hNpos) _)
              (by norm_num) hσl
        _ = 2 * ((N:ℝ)) ^ (-s.re) := by ring
    linarith
  -- assemble
  have hnorm_tsum : ‖∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
      ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ 3 * ((N:ℝ)) ^ (-s.re) := by
    calc ‖∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
        ≤ ∑' k : ℕ, ‖∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ :=
          norm_tsum_le_tsum_norm hsumI.norm
      _ ≤ ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 1) :=
          hsumI.norm.tsum_le_tsum
            (fun k => interval_fract_norm_le (by omega) (le_of_lt hσpos)) hmajsum
      _ ≤ 3 * ((N:ℝ)) ^ (-s.re) := htail_sum
  have hNσ : ((N:ℝ)) ^ (-s.re) ≤ Real.exp 1 / (N:ℝ) := by
    have hsplit : ((N:ℝ)) ^ (-s.re) = ((N:ℝ) ^ (-(1:ℝ))) * ((N:ℝ) ^ (1 - s.re)) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    rw [hsplit, Real.rpow_neg_one]
    have hfac := base_rpow_one_sub_re_le (x := (N:ℝ)) (by exact_mod_cast hN) hT hNT hσ
    calc ((N:ℝ))⁻¹ * ((N:ℝ) ^ (1 - s.re))
        ≤ ((N:ℝ))⁻¹ * Real.exp 1 :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = Real.exp 1 / (N:ℝ) := by ring
  calc ‖s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      = ‖s‖ * ‖∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ := norm_mul _ _
    _ ≤ (2 * T) * (3 * ((N:ℝ)) ^ (-s.re)) := by
        apply mul_le_mul hs_norm hnorm_tsum (norm_nonneg _) (by linarith)
    _ ≤ (2 * (2 * N)) * (3 * (Real.exp 1 / (N:ℝ))) := by
        apply mul_le_mul (by linarith) (by linarith [hNσ]) ?_ (by positivity)
        have := Real.rpow_nonneg (le_of_lt hNpos) (-s.re)
        linarith
    _ = 12 * Real.exp 1 := by
        field_simp
        ring

/-- **B2, assembled: the vertical log-growth bound.**  On the region
`σ ≥ 1 − 1/log|t|`, `σ ≤ 2`, `|t| ≥ e²`:  `‖ζ(s)‖ ≤ 15e·log|t|`. -/
theorem zeta_log_growth {s : ℂ}
    (him : Real.exp 2 ≤ |s.im|)
    (hσ : 1 - 1 / Real.log |s.im| ≤ s.re) (hσu : s.re ≤ 2) :
    ‖riemannZeta s‖ ≤ 15 * Real.exp 1 * Real.log |s.im| := by
  set T : ℝ := |s.im| with hTdef
  have hTe : Real.exp 1 ≤ T := by
    calc Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ T := him
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hTe
  have hlogT2 : (2:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 2) him
    rwa [Real.log_exp] at this
  have hσhalf : (1:ℝ)/2 ≤ s.re := by
    have h1 : 1 / Real.log T ≤ 1/2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have himne : s.im ≠ 0 := by
    intro h
    rw [hTdef, h] at him
    simp at him
    linarith [Real.exp_pos 2, him]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at himne
    simp at himne
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at himne
    simp at himne
  -- the cutoff
  set N : ℕ := ⌊T⌋₊ with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    apply Nat.le_floor
    norm_num
    linarith [Real.add_one_le_exp (1:ℝ)]
  have hNT : (N : ℝ) ≤ T := Nat.floor_le (le_of_lt hTpos)
  have hTN : T ≤ 2 * N := by
    have h := Nat.lt_floor_add_one T
    have hN1' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    rw [← hNdef] at h
    linarith
  -- the representation and the three bounds
  rw [truncated_zeta_pos_re hN1 (by linarith) hs1]
  unfold truncatedRep
  have hhead := head_sum_bound hN1 hs0 hTe hNT hσ
  have hbdry := boundary_bound hN1 hTe hNT hσ
    (by rw [← hTdef]; linarith [Real.add_one_le_exp (1:ℝ)])
  have htail := tail_block_bound hN1 hTe hNT hTN hσhalf hσ hσu (le_refl T)
  have hlogN : Real.log N ≤ Real.log T := by
    apply Real.log_le_log (by exact_mod_cast hN1)
    exact hNT
  calc ‖(∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ ‖(∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
          + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)‖
        + ‖s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ := norm_sub_le _ _
    _ ≤ (‖∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s)‖
          + ‖(((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)‖)
        + ‖s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ (Real.exp 1 * (1 + Real.log N) + Real.exp 1 / 2) + 12 * Real.exp 1 := by
        apply add_le_add (add_le_add hhead hbdry) htail
    _ ≤ 15 * Real.exp 1 * Real.log T := by
        have hexppos := Real.exp_pos 1
        nlinarith [hlogN, hlogT2, hexppos,
          mul_le_mul_of_nonneg_left hlogN (le_of_lt hexppos)]

/-- **B3: the derivative log²-growth bound.**  Cauchy's estimate on a disk of
radius `1/(4 log|t|)` inside the B2 region:
`‖ζ′(σ+it)‖ ≤ 120e·log²|t|` for `σ ≥ 1 − 1/(4 log|t|)`, `σ ≤ 3/2`,
`|t| ≥ e² + 1`. -/
theorem zeta_deriv_log_sq_growth {s : ℂ}
    (him : Real.exp 2 + 1 ≤ |s.im|)
    (hσ : 1 - 1 / (4 * Real.log |s.im|) ≤ s.re) (hσu : s.re ≤ 3/2) :
    ‖deriv riemannZeta s‖ ≤ 120 * Real.exp 1 * (Real.log |s.im|)^2 := by
  set T : ℝ := |s.im| with hTdef
  have hTe2 : Real.exp 2 + 1 ≤ T := him
  have hTe2' : Real.exp 2 ≤ T := by linarith [Real.exp_pos 2]
  have hT2 : (2:ℝ) ≤ T := by
    have h := Real.add_one_le_exp (2:ℝ)
    linarith
  have hTpos : (0:ℝ) < T := by linarith
  set L : ℝ := Real.log T with hLdef
  have hL2 : (2:ℝ) ≤ L := by
    rw [hLdef]
    have := Real.log_le_log (Real.exp_pos 2) hTe2'
    rwa [Real.log_exp] at this
  have hLpos : (0:ℝ) < L := by linarith
  set r : ℝ := 1 / (4 * L) with hrdef
  have hrpos : (0:ℝ) < r := by rw [hrdef]; positivity
  have hr8 : r ≤ 1/8 := by
    rw [hrdef]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  -- every point of the closed disk is in the B2 region
  have hdisk : ∀ z ∈ Metric.closedBall s r,
      Real.exp 2 ≤ |z.im| ∧ 1 - 1 / Real.log |z.im| ≤ z.re ∧ z.re ≤ 2 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have him_diff : |z.im - s.im| ≤ r := by
      calc |z.im - s.im| = |(z - s).im| := by simp
        _ ≤ ‖z - s‖ := Complex.abs_im_le_norm _
        _ ≤ r := hz
    have hre_diff : |z.re - s.re| ≤ r := by
      calc |z.re - s.re| = |(z - s).re| := by simp
        _ ≤ ‖z - s‖ := Complex.abs_re_le_norm _
        _ ≤ r := hz
    have hzim_lb : T - r ≤ |z.im| := by
      have h := abs_sub_abs_le_abs_sub s.im z.im
      rw [abs_sub_comm] at h
      rw [← hTdef] at h
      linarith [abs_le.mp him_diff, h]
    have hzim_ub : |z.im| ≤ T + r := by
      have := abs_sub_abs_le_abs_sub z.im s.im
      have h2 := abs_le.mp him_diff
      have h3 := abs_abs_sub_abs_le_abs_sub z.im s.im
      rw [← hTdef] at h3
      linarith [abs_le.mp h3]
    have hzim_e2 : Real.exp 2 ≤ |z.im| := by linarith
    have hzim_pos : (0:ℝ) < |z.im| := by
      linarith [Real.exp_pos 2]
    -- log|z.im| ≤ 2L
    have hlog_ub : Real.log |z.im| ≤ 2 * L := by
      have h1 : |z.im| ≤ T ^ 2 := by
        have : T + r ≤ T^2 := by nlinarith
        linarith
      calc Real.log |z.im| ≤ Real.log (T ^ 2) :=
          Real.log_le_log hzim_pos h1
        _ = 2 * L := by
            rw [hLdef, Real.log_pow]
            push_cast
            ring
    have hlog_lb : (2:ℝ) ≤ Real.log |z.im| := by
      have := Real.log_le_log (Real.exp_pos 2) hzim_e2
      rwa [Real.log_exp] at this
    refine ⟨hzim_e2, ?_, ?_⟩
    · -- z.re ≥ 1 − 1/log|z.im|
      have h1 : 1 - 1/(2*L) ≤ z.re := by
        have hab := abs_le.mp hre_diff
        have h3 : 1 - r - r ≤ z.re := by linarith [hab.1, hσ]
        have h4 : r + r = 1/(2*L) := by
          rw [hrdef]
          field_simp
          ring
        linarith [h3, h4]
      have h2 : 1/(2*L) ≤ 1/Real.log |z.im| := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      linarith
    · -- z.re ≤ 2
      have := abs_le.mp hre_diff
      linarith [this.2, hr8]
  -- ζ is differentiable on the closed disk (no point equals 1)
  have hdiff : DifferentiableOn ℂ riemannZeta (Metric.closedBall s r) := by
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      obtain ⟨hz_e2, _, _⟩ := hdisk z hz
      rw [h] at hz_e2
      simp at hz_e2
      linarith [Real.exp_pos 2, hz_e2]
    exact (differentiableAt_riemannZeta hz1).differentiableWithinAt
  have hdcc : DiffContOnCl ℂ riemannZeta (Metric.ball s r) :=
    (hdiff.mono Metric.closure_ball_subset_closedBall).diffContOnCl
  -- the sphere bound
  have hC : ∀ z ∈ Metric.sphere s r, ‖riemannZeta z‖ ≤ 30 * Real.exp 1 * L := by
    intro z hz
    have hzball : z ∈ Metric.closedBall s r :=
      Metric.sphere_subset_closedBall hz
    obtain ⟨hz_e2, hz_re, hz_re2⟩ := hdisk z hzball
    have hzim_pos : (0:ℝ) < |z.im| := by linarith [Real.exp_pos 2]
    have hlog_ub : Real.log |z.im| ≤ 2 * L := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hzball
      have him_diff : |z.im - s.im| ≤ r := by
        calc |z.im - s.im| = |(z - s).im| := by simp
          _ ≤ ‖z - s‖ := Complex.abs_im_le_norm _
          _ ≤ r := hzball
      have h3 := abs_abs_sub_abs_le_abs_sub z.im s.im
      rw [← hTdef] at h3
      have h1 : |z.im| ≤ T ^ 2 := by
        have h4 := abs_le.mp h3
        have : T + r ≤ T^2 := by nlinarith
        linarith [h4.2]
      calc Real.log |z.im| ≤ Real.log (T ^ 2) :=
          Real.log_le_log hzim_pos h1
        _ = 2 * L := by
            rw [hLdef, Real.log_pow]
            push_cast
            ring
    calc ‖riemannZeta z‖ ≤ 15 * Real.exp 1 * Real.log |z.im| :=
        zeta_log_growth hz_e2 hz_re hz_re2
      _ ≤ 15 * Real.exp 1 * (2 * L) := by
          apply mul_le_mul_of_nonneg_left hlog_ub (by positivity)
      _ = 30 * Real.exp 1 * L := by ring
  -- Cauchy
  have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hdcc hC
  calc ‖deriv riemannZeta s‖ ≤ (30 * Real.exp 1 * L) / r := hcauchy
    _ = 120 * Real.exp 1 * L^2 := by
        rw [hrdef]
        field_simp
        ring

/-- One-interval value of the `x^{−3/4}` integral. -/
theorem interval_rpow_34_value {k : ℕ} (hk : 1 ≤ k) :
    ∫ x : ℝ in ((k:ℕ) : ℝ)..(((k:ℕ) : ℝ) + 1), x ^ (-(3:ℝ)/4)
      = 4 * ((((k:ℕ) : ℝ) + 1) ^ ((1:ℝ)/4) - (((k:ℕ) : ℝ)) ^ ((1:ℝ)/4)) := by
  have hkpos : (0:ℝ) < ((k:ℕ) : ℝ) := by exact_mod_cast hk
  have h0 : (0:ℝ) ∉ Set.uIcc ((k:ℕ) : ℝ) (((k:ℕ) : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
  norm_num
  ring

/-- Telescoped sum of the `x^{−3/4}` interval integrals. -/
theorem sum_Ico_integral_rpow_telescope {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Ico 1 N,
      ∫ x : ℝ in ((k:ℕ) : ℝ)..(((k:ℕ) : ℝ) + 1), x ^ (-(3:ℝ)/4)
    = 4 * (((N : ℝ)) ^ ((1:ℝ)/4) - 1) := by
  induction N with
  | zero => omega
  | succ M ih =>
    rcases Nat.lt_or_ge M 1 with hlt | hge
    · have hM0 : M = 0 := by omega
      subst hM0
      simp
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ M), ih hge,
        interval_rpow_34_value hge]
      push_cast
      ring

/-- **Polynomial head bound**: `Σ_{n≤N} n^{−σ} ≤ 1 + 4·N^{1/4}` for
`σ ≥ 3/4`, `N ≥ 1`. -/
theorem head_polynomial_bound {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs0 : s ≠ 0)
    (hσ : (3:ℝ)/4 ≤ s.re) :
    ‖∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s)‖
      ≤ 1 + 4 * ((N : ℝ)) ^ ((1:ℝ)/4) := by
  have hsne : -s ≠ 0 := neg_ne_zero.mpr hs0
  calc ‖∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s)‖
      ≤ ∑ n ∈ Finset.range (N + 1), ‖(((n : ℝ)) : ℂ) ^ (-s)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1),
          (if n = 0 then 0 else ((n : ℝ)) ^ (-(3:ℝ)/4)) := by
        apply Finset.sum_le_sum
        intro n _
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          simp [Complex.zero_cpow hsne]
        · rw [if_neg (by omega)]
          have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hpos
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
          have hre : (-s).re = -s.re := by simp
          rw [hre]
          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos)
          linarith
    _ ≤ 1 + 4 * ((N : ℝ)) ^ ((1:ℝ)/4) := by
        -- peel n = 0 and n = 1; compare the rest with the integral
        have hsplit : ∑ n ∈ Finset.range (N + 1),
            (if n = 0 then 0 else ((n : ℝ)) ^ (-(3:ℝ)/4))
            = ∑ n ∈ Finset.range N,
              (((n + 1 : ℕ) : ℝ)) ^ (-(3:ℝ)/4) := by
          rw [Finset.sum_range_succ']
          simp
        rw [hsplit]
        -- term k (value (k+1)^{-3/4}): for k ≥ 1 bounded by ∫_k^{k+1} x^{-3/4}
        have hterm : ∀ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ)) ^ (-(3:ℝ)/4)
            ≤ (if k = 0 then 1 else
              ∫ x : ℝ in ((k:ℕ) : ℝ)..(((k:ℕ) : ℝ) + 1), x ^ (-(3:ℝ)/4)) := by
          intro k _
          rcases Nat.eq_zero_or_pos k with h0 | hpos
          · subst h0
            simp only [if_pos rfl]
            push_cast
            simp
          · rw [if_neg (by omega)]
            have h := rpow_le_interval_integral
              (a := ((k:ℕ) : ℝ)) (by exact_mod_cast hpos)
              (p := (3:ℝ)/4) (by norm_num)
            have hexp : -((3:ℝ)/4) = (-3:ℝ)/4 := by norm_num
            rw [hexp] at h
            calc (((k + 1 : ℕ) : ℝ)) ^ (-(3:ℝ)/4)
                = (((k:ℕ) : ℝ) + 1) ^ ((-3:ℝ)/4) := by
                  push_cast
                  norm_num
              _ ≤ _ := h
        calc ∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ)) ^ (-(3:ℝ)/4)
            ≤ ∑ k ∈ Finset.range N, (if k = 0 then 1 else
                ∫ x : ℝ in ((k:ℕ) : ℝ)..(((k:ℕ) : ℝ) + 1), x ^ (-(3:ℝ)/4)) :=
              Finset.sum_le_sum hterm
          _ ≤ 1 + 4 * ((N : ℝ)) ^ ((1:ℝ)/4) := by
              rcases Nat.eq_zero_or_pos N with h0 | hNpos
              · omega
              -- split off k = 0 and telescope the integrals
              have hsplit2 : ∑ k ∈ Finset.range N, (if k = 0 then 1 else
                  ∫ x : ℝ in ((k:ℕ) : ℝ)..(((k:ℕ) : ℝ) + 1), x ^ (-(3:ℝ)/4))
                  = 1 + ∑ k ∈ Finset.Ico 1 N,
                    ∫ x : ℝ in ((k:ℕ) : ℝ)..(((k:ℕ) : ℝ) + 1), x ^ (-(3:ℝ)/4) := by
                rw [Finset.range_eq_Ico,
                  show Finset.Ico 0 N = insert 0 (Finset.Ico 1 N) by
                    ext k
                    simp only [Finset.mem_Ico, Finset.mem_insert]
                    omega,
                  Finset.sum_insert (by simp)]
                rw [if_pos rfl]
                congr 1
                apply Finset.sum_congr rfl
                intro k hk
                rw [Finset.mem_Ico] at hk
                rw [if_neg (by omega)]
              rw [hsplit2]
              have htel := sum_Ico_integral_rpow_telescope hNpos
              have hN14 : (0:ℝ) ≤ ((N : ℝ)) ^ ((1:ℝ)/4) :=
                Real.rpow_nonneg (by positivity) _
              rw [htel]
              linarith

/-- Polynomial boundary bound: `‖N^{1−s}/(s−1)‖ ≤ N^{1/4}/2` for `σ ≥ 3/4`,
`|Im s| ≥ 2`. -/
theorem boundary_polynomial_bound {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hσ : (3:ℝ)/4 ≤ s.re) (him : 2 ≤ |s.im|) :
    ‖(((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ ((N : ℝ)) ^ ((1:ℝ)/4) / 2 := by
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
  have hre : (1 - s).re = 1 - s.re := by simp
  rw [hre]
  have hnum : ((N:ℝ)) ^ (1 - s.re) ≤ ((N:ℝ)) ^ ((1:ℝ)/4) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    linarith
  have hden : (2:ℝ) ≤ ‖s - 1‖ := by
    calc (2:ℝ) ≤ |s.im| := him
      _ = |(s - 1).im| := by simp
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hdenpos : (0:ℝ) < ‖s - 1‖ := by linarith
  gcongr <;> first
    | exact hnum
    | exact hden
    | positivity
    | linarith

/-- Polynomial tail bound: the tail block is at most `8·T^{1/4}` on the
region `σ ∈ [3/4, 2]`. -/
theorem tail_polynomial_bound {N : ℕ} (hN : 1 ≤ N) {s : ℂ} {T : ℝ}
    (hT : (2:ℝ) ≤ T) (hNT : (N : ℝ) ≤ T) (hTN : T ≤ 2 * N)
    (hσl : (3:ℝ)/4 ≤ s.re) (hσu : s.re ≤ 2) (him : |s.im| ≤ T) :
    ‖s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ 10 * T ^ ((1:ℝ)/4) := by
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hσpos : (0:ℝ) < s.re := by linarith
  have hs_norm : ‖s‖ ≤ 2 * T := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 2 + T := by
          apply add_le_add
          · rw [abs_of_pos hσpos]
            exact hσu
          · exact him
      _ ≤ 2 * T := by linarith
  have hsumI := summable_shift_integral hN hσpos
  have hmajsum : Summable (fun k : ℕ => (((N + k : ℕ) : ℝ)) ^ (-s.re - 1)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s.re - 1)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  have htail_sum : (∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 1))
      ≤ (7:ℝ)/3 * ((N:ℝ)) ^ (-(3:ℝ)/4) := by
    have hshift := hmajsum.tsum_eq_zero_add
    have hreindex : (∑' k : ℕ, (((N + (k + 1) : ℕ) : ℝ)) ^ (-s.re - 1))
        = ∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ)) ^ (-s.re - 1) := by
      refine tsum_congr fun k => ?_
      congr 2
      omega
    rw [hshift, hreindex]
    have hmono34 : ((N:ℝ)) ^ (-s.re) ≤ ((N:ℝ)) ^ (-(3:ℝ)/4) := by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
      linarith
    have h1 : (((N + 0 : ℕ) : ℝ)) ^ (-s.re - 1) ≤ ((N:ℝ)) ^ (-(3:ℝ)/4) := by
      simp only [Nat.add_zero]
      calc ((N:ℝ)) ^ (-s.re - 1) ≤ ((N:ℝ)) ^ (-s.re) := by
            apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
            linarith
        _ ≤ ((N:ℝ)) ^ (-(3:ℝ)/4) := hmono34
    have h2 : (∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ)) ^ (-s.re - 1))
        ≤ (4:ℝ)/3 * ((N:ℝ)) ^ (-(3:ℝ)/4) := by
      have hp : (1:ℝ) < s.re + 1 := by linarith
      have h := rpow_tail_tsum_le hN hp
      have hexp : -(s.re + 1) = -s.re - 1 := by ring
      have hexp2 : (1:ℝ) - (s.re + 1) = -s.re := by ring
      rw [hexp, hexp2] at h
      calc (∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ)) ^ (-s.re - 1))
          ≤ ((N:ℝ)) ^ (-s.re) / (s.re + 1 - 1) := h
        _ = ((N:ℝ)) ^ (-s.re) / s.re := by ring_nf
        _ ≤ ((N:ℝ)) ^ (-s.re) / ((3:ℝ)/4) := by
            apply div_le_div_of_nonneg_left
              (Real.rpow_nonneg (le_of_lt hNpos) _) (by norm_num) hσl
        _ = (4:ℝ)/3 * ((N:ℝ)) ^ (-s.re) := by ring
        _ ≤ (4:ℝ)/3 * ((N:ℝ)) ^ (-(3:ℝ)/4) := by
            apply mul_le_mul_of_nonneg_left hmono34 (by norm_num)
    linarith
  have hnorm_tsum : ‖∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
      ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ (7:ℝ)/3 * ((N:ℝ)) ^ (-(3:ℝ)/4) := by
    calc ‖∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
        ≤ ∑' k : ℕ, ‖∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ :=
          norm_tsum_le_tsum_norm hsumI.norm
      _ ≤ ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 1) :=
          hsumI.norm.tsum_le_tsum
            (fun k => interval_fract_norm_le (by omega) (le_of_lt hσpos)) hmajsum
      _ ≤ (7:ℝ)/3 * ((N:ℝ)) ^ (-(3:ℝ)/4) := htail_sum
  -- N^{-3/4} ≤ 2^{3/4}·T^{-3/4} ≤ 2·T^{-3/4}
  have hNT34 : ((N:ℝ)) ^ (-(3:ℝ)/4) ≤ 2 * T ^ (-(3:ℝ)/4) := by
    have hTpos : (0:ℝ) < T := by linarith
    have h1 : T / 2 ≤ (N:ℝ) := by linarith
    have h2 : ((N:ℝ)) ^ (-(3:ℝ)/4) ≤ (T / 2) ^ (-(3:ℝ)/4) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
    have h3 : (T / 2) ^ (-(3:ℝ)/4) = 2 ^ ((3:ℝ)/4) * T ^ (-(3:ℝ)/4) := by
      rw [div_eq_mul_inv, Real.mul_rpow (le_of_lt hTpos) (by norm_num),
        Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
      norm_num [mul_comm]
    have h4 : (2:ℝ) ^ ((3:ℝ)/4) ≤ 2 := by
      calc (2:ℝ) ^ ((3:ℝ)/4) ≤ 2 ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := by norm_num
    have hT34 : (0:ℝ) ≤ T ^ (-(3:ℝ)/4) := Real.rpow_nonneg (le_of_lt hTpos) _
    calc ((N:ℝ)) ^ (-(3:ℝ)/4) ≤ (T / 2) ^ (-(3:ℝ)/4) := h2
      _ = 2 ^ ((3:ℝ)/4) * T ^ (-(3:ℝ)/4) := h3
      _ ≤ 2 * T ^ (-(3:ℝ)/4) := by nlinarith
  have hTpos : (0:ℝ) < T := by linarith
  calc ‖s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      = ‖s‖ * ‖∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ := norm_mul _ _
    _ ≤ (2 * T) * ((7:ℝ)/3 * (2 * T ^ (-(3:ℝ)/4))) := by
        apply mul_le_mul hs_norm ?_ (norm_nonneg _) (by positivity)
        calc ‖∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
              ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
            ≤ (7:ℝ)/3 * ((N:ℝ)) ^ (-(3:ℝ)/4) := hnorm_tsum
          _ ≤ (7:ℝ)/3 * (2 * T ^ (-(3:ℝ)/4)) := by
              apply mul_le_mul_of_nonneg_left hNT34 (by norm_num)
    _ ≤ 10 * T ^ ((1:ℝ)/4) := by
        have hsplit : T * T ^ (-(3:ℝ)/4) = T ^ ((1:ℝ)/4) := by
          nth_rewrite 1 [show (T : ℝ) = T ^ (1:ℝ) from (Real.rpow_one T).symm]
          rw [← Real.rpow_add hTpos]
          norm_num
        calc (2 * T) * ((7:ℝ)/3 * (2 * T ^ (-(3:ℝ)/4)))
            = (28:ℝ)/3 * (T * T ^ (-(3:ℝ)/4)) := by ring
          _ = (28:ℝ)/3 * T ^ ((1:ℝ)/4) := by rw [hsplit]
          _ ≤ 10 * T ^ ((1:ℝ)/4) := by
              apply mul_le_mul_of_nonneg_right (by norm_num)
                (Real.rpow_nonneg (le_of_lt hTpos) _)

/-- **B2′, assembled: the polynomial growth bound** —
`‖ζ(σ+it)‖ ≤ 16·|t|^{1/4}` on `σ ∈ [3/4, 2]`, `|t| ≥ 2`.  The growth input
for the movable-center Jensen count. -/
theorem zeta_polynomial_growth {s : ℂ}
    (him : 2 ≤ |s.im|) (hσl : (3:ℝ)/4 ≤ s.re) (hσu : s.re ≤ 2) :
    ‖riemannZeta s‖ ≤ 16 * |s.im| ^ ((1:ℝ)/4) := by
  set T : ℝ := |s.im| with hTdef
  have hTpos : (0:ℝ) < T := by linarith
  have himne : s.im ≠ 0 := by
    intro h
    rw [hTdef, h] at him
    simp at him
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at himne
    simp at himne
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at himne
    simp at himne
  set N : ℕ := ⌊T⌋₊ with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    apply Nat.le_floor
    norm_num
    linarith
  have hNT : (N : ℝ) ≤ T := Nat.floor_le (le_of_lt hTpos)
  have hTN : T ≤ 2 * N := by
    have h := Nat.lt_floor_add_one T
    have hN1' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    rw [← hNdef] at h
    linarith
  rw [truncated_zeta_pos_re hN1 (by linarith) hs1]
  unfold truncatedRep
  have hhead := head_polynomial_bound hN1 hs0 hσl
  have hbdry := boundary_polynomial_bound hN1 hσl (by rw [← hTdef]; linarith)
  have htail := tail_polynomial_bound hN1 (by linarith) hNT hTN hσl hσu
    (le_refl T)
  have hN14 : ((N:ℝ)) ^ ((1:ℝ)/4) ≤ T ^ ((1:ℝ)/4) :=
    Real.rpow_le_rpow (by positivity) hNT (by norm_num)
  have hT14 : (1:ℝ) ≤ T ^ ((1:ℝ)/4) := by
    calc (1:ℝ) = 1 ^ ((1:ℝ)/4) := by rw [Real.one_rpow]
      _ ≤ T ^ ((1:ℝ)/4) := Real.rpow_le_rpow (by norm_num) (by linarith)
        (by norm_num)
  calc ‖(∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ ‖(∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
          + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)‖
        + ‖s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ := norm_sub_le _ _
    _ ≤ (‖∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s)‖
          + ‖(((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)‖)
        + ‖s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ ((1 + 4 * ((N : ℝ)) ^ ((1:ℝ)/4)) + ((N : ℝ)) ^ ((1:ℝ)/4) / 2)
        + 10 * T ^ ((1:ℝ)/4) := by
        apply add_le_add (add_le_add hhead hbdry) htail
    _ ≤ 16 * T ^ ((1:ℝ)/4) := by
        have h1 : ((N:ℝ)) ^ ((1:ℝ)/4) / 2 ≤ T ^ ((1:ℝ)/4) := by
          linarith [hN14, Real.rpow_nonneg (le_of_lt hTpos) ((1:ℝ)/4)]
        linarith [hN14, hT14]

/-! ### B2″: the exponent-3/4 growth bound on `σ ≥ 1/4`
The same three blocks at the wider strip — the growth input for the
unit-window (RvM) zero count. -/

/-- One-interval value of the `x^{−1/4}` integral. -/
theorem interval_rpow_14_value {k : ℕ} (hk : 1 ≤ k) :
    ∫ x : ℝ in ((k:ℕ) : ℝ)..(((k:ℕ) : ℝ) + 1), x ^ (-(1:ℝ)/4)
      = (4:ℝ)/3 * ((((k:ℕ) : ℝ) + 1) ^ ((3:ℝ)/4)
        - (((k:ℕ) : ℝ)) ^ ((3:ℝ)/4)) := by
  have hkpos : (0:ℝ) < ((k:ℕ) : ℝ) := by exact_mod_cast hk
  have h0 : (0:ℝ) ∉ Set.uIcc ((k:ℕ) : ℝ) (((k:ℕ) : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
  norm_num
  ring

/-- Telescoped sum of the `x^{−1/4}` interval integrals. -/
theorem sum_Ico_integral_rpow_telescope_14 {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Ico 1 N,
      ∫ x : ℝ in ((k:ℕ) : ℝ)..(((k:ℕ) : ℝ) + 1), x ^ (-(1:ℝ)/4)
    = (4:ℝ)/3 * (((N : ℝ)) ^ ((3:ℝ)/4) - 1) := by
  induction N with
  | zero => omega
  | succ M ih =>
    rcases Nat.lt_or_ge M 1 with hlt | hge
    · have hM0 : M = 0 := by omega
      subst hM0
      simp
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ M), ih hge,
        interval_rpow_14_value hge]
      push_cast
      ring

/-- **Quarter-strip head bound**: `Σ_{n≤N} n^{−σ} ≤ 1 + 2·N^{3/4}` for
`σ ≥ 1/4`, `N ≥ 1`. -/
theorem head_polynomial_bound_quarter {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs0 : s ≠ 0) (hσ : (1:ℝ)/4 ≤ s.re) :
    ‖∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s)‖
      ≤ 1 + 2 * ((N : ℝ)) ^ ((3:ℝ)/4) := by
  have hsne : -s ≠ 0 := neg_ne_zero.mpr hs0
  calc ‖∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s)‖
      ≤ ∑ n ∈ Finset.range (N + 1), ‖(((n : ℝ)) : ℂ) ^ (-s)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1),
          (if n = 0 then 0 else ((n : ℝ)) ^ (-(1:ℝ)/4)) := by
        apply Finset.sum_le_sum
        intro n _
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          simp [Complex.zero_cpow hsne]
        · rw [if_neg (by omega)]
          have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hpos
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
          have hre : (-s).re = -s.re := by simp
          rw [hre]
          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos)
          linarith
    _ ≤ 1 + 2 * ((N : ℝ)) ^ ((3:ℝ)/4) := by
        have hsplit : ∑ n ∈ Finset.range (N + 1),
            (if n = 0 then 0 else ((n : ℝ)) ^ (-(1:ℝ)/4))
            = ∑ n ∈ Finset.range N,
              (((n + 1 : ℕ) : ℝ)) ^ (-(1:ℝ)/4) := by
          rw [Finset.sum_range_succ']
          simp
        rw [hsplit]
        have hterm : ∀ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ)) ^ (-(1:ℝ)/4)
            ≤ (if k = 0 then 1 else
              ∫ x : ℝ in ((k:ℕ) : ℝ)..(((k:ℕ) : ℝ) + 1), x ^ (-(1:ℝ)/4)) := by
          intro k _
          rcases Nat.eq_zero_or_pos k with h0 | hpos
          · subst h0
            simp only [if_pos rfl]
            push_cast
            simp
          · rw [if_neg (by omega)]
            have h := rpow_le_interval_integral
              (a := ((k:ℕ) : ℝ)) (by exact_mod_cast hpos)
              (p := (1:ℝ)/4) (by norm_num)
            have hexp : -((1:ℝ)/4) = (-1:ℝ)/4 := by norm_num
            rw [hexp] at h
            calc (((k + 1 : ℕ) : ℝ)) ^ (-(1:ℝ)/4)
                = (((k:ℕ) : ℝ) + 1) ^ ((-1:ℝ)/4) := by
                  push_cast
                  norm_num
              _ ≤ _ := h
        calc ∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ)) ^ (-(1:ℝ)/4)
            ≤ ∑ k ∈ Finset.range N, (if k = 0 then 1 else
                ∫ x : ℝ in ((k:ℕ) : ℝ)..(((k:ℕ) : ℝ) + 1), x ^ (-(1:ℝ)/4)) :=
              Finset.sum_le_sum hterm
          _ ≤ 1 + 2 * ((N : ℝ)) ^ ((3:ℝ)/4) := by
              rcases Nat.eq_zero_or_pos N with h0 | hNpos
              · omega
              have hsplit2 : ∑ k ∈ Finset.range N, (if k = 0 then 1 else
                  ∫ x : ℝ in ((k:ℕ) : ℝ)..(((k:ℕ) : ℝ) + 1), x ^ (-(1:ℝ)/4))
                  = 1 + ∑ k ∈ Finset.Ico 1 N,
                    ∫ x : ℝ in ((k:ℕ) : ℝ)..(((k:ℕ) : ℝ) + 1),
                      x ^ (-(1:ℝ)/4) := by
                rw [Finset.range_eq_Ico,
                  show Finset.Ico 0 N = insert 0 (Finset.Ico 1 N) by
                    ext k
                    simp only [Finset.mem_Ico, Finset.mem_insert]
                    omega,
                  Finset.sum_insert (by simp)]
                rw [if_pos rfl]
                congr 1
                apply Finset.sum_congr rfl
                intro k hk
                rw [Finset.mem_Ico] at hk
                rw [if_neg (by omega)]
              rw [hsplit2]
              have htel := sum_Ico_integral_rpow_telescope_14 hNpos
              have hN34 : (0:ℝ) ≤ ((N : ℝ)) ^ ((3:ℝ)/4) :=
                Real.rpow_nonneg (by positivity) _
              rw [htel]
              linarith

/-- Quarter-strip boundary bound: `‖N^{1−s}/(s−1)‖ ≤ N^{3/4}/2` for
`σ ≥ 1/4`, `|Im s| ≥ 2`. -/
theorem boundary_polynomial_bound_quarter {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hσ : (1:ℝ)/4 ≤ s.re) (him : 2 ≤ |s.im|) :
    ‖(((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ ((N : ℝ)) ^ ((3:ℝ)/4) / 2 := by
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
  have hre : (1 - s).re = 1 - s.re := by simp
  rw [hre]
  have hnum : ((N:ℝ)) ^ (1 - s.re) ≤ ((N:ℝ)) ^ ((3:ℝ)/4) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    linarith
  have hden : (2:ℝ) ≤ ‖s - 1‖ := by
    calc (2:ℝ) ≤ |s.im| := him
      _ = |(s - 1).im| := by simp
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hdenpos : (0:ℝ) < ‖s - 1‖ := by linarith
  gcongr <;> first
    | exact hnum
    | exact hden
    | positivity
    | linarith

/-- Quarter-strip tail bound: the tail block is at most `20·T^{3/4}` on
`σ ∈ [1/4, 2]`. -/
theorem tail_polynomial_bound_quarter {N : ℕ} (hN : 1 ≤ N) {s : ℂ} {T : ℝ}
    (hT : (2:ℝ) ≤ T) (hNT : (N : ℝ) ≤ T) (hTN : T ≤ 2 * N)
    (hσl : (1:ℝ)/4 ≤ s.re) (hσu : s.re ≤ 2) (him : |s.im| ≤ T) :
    ‖s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ 20 * T ^ ((3:ℝ)/4) := by
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hσpos : (0:ℝ) < s.re := by linarith
  have hs_norm : ‖s‖ ≤ 2 * T := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 2 + T := by
          apply add_le_add
          · rw [abs_of_pos hσpos]
            exact hσu
          · exact him
      _ ≤ 2 * T := by linarith
  have hsumI := summable_shift_integral hN hσpos
  have hmajsum : Summable (fun k : ℕ => (((N + k : ℕ) : ℝ)) ^ (-s.re - 1)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s.re - 1)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  have htail_sum : (∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 1))
      ≤ 5 * ((N:ℝ)) ^ (-(1:ℝ)/4) := by
    have hshift := hmajsum.tsum_eq_zero_add
    have hreindex : (∑' k : ℕ, (((N + (k + 1) : ℕ) : ℝ)) ^ (-s.re - 1))
        = ∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ)) ^ (-s.re - 1) := by
      refine tsum_congr fun k => ?_
      congr 2
      omega
    rw [hshift, hreindex]
    have hmono14 : ((N:ℝ)) ^ (-s.re) ≤ ((N:ℝ)) ^ (-(1:ℝ)/4) := by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
      linarith
    have h1 : (((N + 0 : ℕ) : ℝ)) ^ (-s.re - 1) ≤ ((N:ℝ)) ^ (-(1:ℝ)/4) := by
      simp only [Nat.add_zero]
      calc ((N:ℝ)) ^ (-s.re - 1) ≤ ((N:ℝ)) ^ (-s.re) := by
            apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
            linarith
        _ ≤ ((N:ℝ)) ^ (-(1:ℝ)/4) := hmono14
    have h2 : (∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ)) ^ (-s.re - 1))
        ≤ 4 * ((N:ℝ)) ^ (-(1:ℝ)/4) := by
      have hp : (1:ℝ) < s.re + 1 := by linarith
      have h := rpow_tail_tsum_le hN hp
      have hexp : -(s.re + 1) = -s.re - 1 := by ring
      have hexp2 : (1:ℝ) - (s.re + 1) = -s.re := by ring
      rw [hexp, hexp2] at h
      calc (∑' k : ℕ, (((N + 1 + k : ℕ) : ℝ)) ^ (-s.re - 1))
          ≤ ((N:ℝ)) ^ (-s.re) / (s.re + 1 - 1) := h
        _ = ((N:ℝ)) ^ (-s.re) / s.re := by ring_nf
        _ ≤ ((N:ℝ)) ^ (-s.re) / ((1:ℝ)/4) := by
            apply div_le_div_of_nonneg_left
              (Real.rpow_nonneg (le_of_lt hNpos) _) (by norm_num) hσl
        _ = 4 * ((N:ℝ)) ^ (-s.re) := by ring
        _ ≤ 4 * ((N:ℝ)) ^ (-(1:ℝ)/4) := by
            apply mul_le_mul_of_nonneg_left hmono14 (by norm_num)
    linarith
  have hnorm_tsum : ‖∑' k : ℕ,
      ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
      ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ 5 * ((N:ℝ)) ^ (-(1:ℝ)/4) := by
    calc ‖∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
        ≤ ∑' k : ℕ, ‖∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ :=
          norm_tsum_le_tsum_norm hsumI.norm
      _ ≤ ∑' k : ℕ, (((N + k : ℕ) : ℝ)) ^ (-s.re - 1) :=
          hsumI.norm.tsum_le_tsum
            (fun k => interval_fract_norm_le (by omega) (le_of_lt hσpos))
            hmajsum
      _ ≤ 5 * ((N:ℝ)) ^ (-(1:ℝ)/4) := htail_sum
  have hNT14 : ((N:ℝ)) ^ (-(1:ℝ)/4) ≤ 2 * T ^ (-(1:ℝ)/4) := by
    have hTpos : (0:ℝ) < T := by linarith
    have h1 : T / 2 ≤ (N:ℝ) := by linarith
    have h2 : ((N:ℝ)) ^ (-(1:ℝ)/4) ≤ (T / 2) ^ (-(1:ℝ)/4) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
    have h3 : (T / 2) ^ (-(1:ℝ)/4) = 2 ^ ((1:ℝ)/4) * T ^ (-(1:ℝ)/4) := by
      rw [div_eq_mul_inv, Real.mul_rpow (le_of_lt hTpos) (by norm_num),
        Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
      norm_num [mul_comm]
    have h4 : (2:ℝ) ^ ((1:ℝ)/4) ≤ 2 := by
      calc (2:ℝ) ^ ((1:ℝ)/4) ≤ 2 ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := by norm_num
    have hT14 : (0:ℝ) ≤ T ^ (-(1:ℝ)/4) := Real.rpow_nonneg (le_of_lt hTpos) _
    calc ((N:ℝ)) ^ (-(1:ℝ)/4) ≤ (T / 2) ^ (-(1:ℝ)/4) := h2
      _ = 2 ^ ((1:ℝ)/4) * T ^ (-(1:ℝ)/4) := h3
      _ ≤ 2 * T ^ (-(1:ℝ)/4) := by nlinarith
  have hTpos : (0:ℝ) < T := by linarith
  calc ‖s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      = ‖s‖ * ‖∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ := norm_mul _ _
    _ ≤ (2 * T) * (5 * (2 * T ^ (-(1:ℝ)/4))) := by
        apply mul_le_mul hs_norm ?_ (norm_nonneg _) (by positivity)
        calc ‖∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
              ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
            ≤ 5 * ((N:ℝ)) ^ (-(1:ℝ)/4) := hnorm_tsum
          _ ≤ 5 * (2 * T ^ (-(1:ℝ)/4)) := by
              apply mul_le_mul_of_nonneg_left hNT14 (by norm_num)
    _ ≤ 20 * T ^ ((3:ℝ)/4) := by
        have hsplit : T * T ^ (-(1:ℝ)/4) = T ^ ((3:ℝ)/4) := by
          nth_rewrite 1 [show (T : ℝ) = T ^ (1:ℝ) from (Real.rpow_one T).symm]
          rw [← Real.rpow_add hTpos]
          norm_num
        calc (2 * T) * (5 * (2 * T ^ (-(1:ℝ)/4)))
            = 20 * (T * T ^ (-(1:ℝ)/4)) := by ring
          _ = 20 * T ^ ((3:ℝ)/4) := by rw [hsplit]
          _ ≤ 20 * T ^ ((3:ℝ)/4) := le_refl _

/-- **B2″, assembled**: `‖ζ(σ+it)‖ ≤ 24·|t|^{3/4}` on `σ ∈ [1/4, 2]`,
`|t| ≥ 2`.  The growth input for the unit-window zero count. -/
theorem zeta_polynomial_growth_quarter {s : ℂ}
    (him : 2 ≤ |s.im|) (hσl : (1:ℝ)/4 ≤ s.re) (hσu : s.re ≤ 2) :
    ‖riemannZeta s‖ ≤ 24 * |s.im| ^ ((3:ℝ)/4) := by
  set T : ℝ := |s.im| with hTdef
  have hTpos : (0:ℝ) < T := by linarith
  have himne : s.im ≠ 0 := by
    intro h
    rw [hTdef, h] at him
    simp at him
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at himne
    simp at himne
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at himne
    simp at himne
  set N : ℕ := ⌊T⌋₊ with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    apply Nat.le_floor
    norm_num
    linarith
  have hNT : (N : ℝ) ≤ T := Nat.floor_le (le_of_lt hTpos)
  have hTN : T ≤ 2 * N := by
    have h := Nat.lt_floor_add_one T
    have hN1' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    rw [← hNdef] at h
    linarith
  rw [truncated_zeta_pos_re hN1 (by linarith) hs1]
  unfold truncatedRep
  have hhead := head_polynomial_bound_quarter hN1 hs0 hσl
  have hbdry := boundary_polynomial_bound_quarter hN1 hσl
    (by rw [← hTdef]; linarith)
  have htail := tail_polynomial_bound_quarter hN1 (by linarith) hNT hTN
    hσl hσu (le_refl T)
  have hN34 : ((N:ℝ)) ^ ((3:ℝ)/4) ≤ T ^ ((3:ℝ)/4) :=
    Real.rpow_le_rpow (by positivity) hNT (by norm_num)
  have hT34 : (1:ℝ) ≤ T ^ ((3:ℝ)/4) := by
    calc (1:ℝ) = 1 ^ ((3:ℝ)/4) := by rw [Real.one_rpow]
      _ ≤ T ^ ((3:ℝ)/4) := Real.rpow_le_rpow (by norm_num) (by linarith)
        (by norm_num)
  calc ‖(∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)
        - s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ ‖(∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
          + (((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)‖
        + ‖s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ := norm_sub_le _ _
    _ ≤ (‖∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s)‖
          + ‖(((N : ℝ)) : ℂ) ^ (1 - s) / (s - 1)‖)
        + ‖s * ∑' k : ℕ, ∫ x : ℝ in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ ((1 + 2 * ((N : ℝ)) ^ ((3:ℝ)/4)) + ((N : ℝ)) ^ ((3:ℝ)/4) / 2)
        + 20 * T ^ ((3:ℝ)/4) := by
        apply add_le_add (add_le_add hhead hbdry) htail
    _ ≤ 24 * T ^ ((3:ℝ)/4) := by
        have h1 : ((N:ℝ)) ^ ((3:ℝ)/4) / 2 ≤ T ^ ((3:ℝ)/4) := by
          linarith [hN34, Real.rpow_nonneg (le_of_lt hTpos) ((3:ℝ)/4)]
        linarith [hN34, hT34]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.head_term_bound
#print axioms CriticalLinePhasor.DVP.head_sum_bound
#print axioms CriticalLinePhasor.DVP.base_rpow_one_sub_re_le
#print axioms CriticalLinePhasor.DVP.boundary_bound
#print axioms CriticalLinePhasor.DVP.rpow_le_interval_integral
#print axioms CriticalLinePhasor.DVP.rpow_tail_partial
#print axioms CriticalLinePhasor.DVP.rpow_tail_tsum_le
#print axioms CriticalLinePhasor.DVP.tail_block_bound
#print axioms CriticalLinePhasor.DVP.zeta_log_growth
#print axioms CriticalLinePhasor.DVP.zeta_deriv_log_sq_growth
#print axioms CriticalLinePhasor.DVP.head_polynomial_bound
#print axioms CriticalLinePhasor.DVP.boundary_polynomial_bound
#print axioms CriticalLinePhasor.DVP.tail_polynomial_bound
#print axioms CriticalLinePhasor.DVP.zeta_polynomial_growth
#print axioms CriticalLinePhasor.DVP.zeta_polynomial_growth_quarter
end AxiomAudit
