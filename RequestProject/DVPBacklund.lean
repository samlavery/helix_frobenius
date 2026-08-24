import RequestProject.DVPWeightedCount
import RequestProject.ZetaContourArgument

/-!
# Backlund campaign, brick B1: tube confinement

The reusable core of Backlund's `S(T) = O(log T)` argument: a continuous
logarithm whose exponential stays in the open right half-plane has imaginary
part confined to an open interval of length `π` — so the argument variation
along any such stretch is `< π`.  Applied piecewise between the sign changes
of `Re ζ` on the horizontal segment, with the sign-change count bounded by a
Jensen count, this gives the classical bound.
-/

open Complex Set

noncomputable section

namespace CriticalLinePhasor.DVP

/-- A length-π closed interval contains a zero of the cosine. -/
theorem exists_cos_zero_of_length_ge_pi {c d : ℝ} (hcd : c ≤ d)
    (hlen : Real.pi ≤ d - c) :
    ∃ z ∈ Set.Icc c d, Real.cos z = 0 := by
  set k : ℤ := ⌈(c - Real.pi/2) / Real.pi⌉ with hk
  refine ⟨Real.pi/2 + k * Real.pi, ⟨?_, ?_⟩, ?_⟩
  · have h1 : (c - Real.pi/2) / Real.pi ≤ (k:ℝ) := Int.le_ceil _
    have hπ : (0:ℝ) < Real.pi := Real.pi_pos
    rw [div_le_iff₀ hπ] at h1
    linarith
  · have h2 : (k:ℝ) < (c - Real.pi/2) / Real.pi + 1 := Int.ceil_lt_add_one _
    have hπ : (0:ℝ) < Real.pi := Real.pi_pos
    have h3 : (k:ℝ) * Real.pi < c - Real.pi/2 + Real.pi := by
      have hm := mul_lt_mul_of_pos_right h2 hπ
      rw [add_mul, one_mul, div_mul_cancel₀ _ hπ.ne'] at hm
      linarith
    linarith
  · rw [add_comm, Real.cos_add_pi_div_two, Real.sin_int_mul_pi]
    ring

/-- **B1: tube confinement.**  A continuous function `L` on `[a,b]` whose
exponential has positive real part throughout has `Im L` varying by less
than `π`. -/
theorem im_confined_of_exp_re_pos {a b : ℝ} (hab : a ≤ b) {L : ℝ → ℂ}
    (hL : ContinuousOn L (Set.Icc a b))
    (hpos : ∀ u ∈ Set.Icc a b, 0 < (Complex.exp (L u)).re) :
    |(L b).im - (L a).im| < Real.pi := by
  have hcos : ∀ u ∈ Set.Icc a b, 0 < Real.cos ((L u).im) := by
    intro u hu
    have h := hpos u hu
    rw [Complex.exp_re] at h
    have hexp : (0:ℝ) < Real.exp ((L u).re) := Real.exp_pos _
    nlinarith
  -- the image of Im ∘ L is preconnected, hence order-connected
  set S : Set ℝ := (fun u => (L u).im) '' Set.Icc a b with hS
  have hSconn : IsPreconnected S := by
    apply IsPreconnected.image isPreconnected_Icc
    exact Complex.continuous_im.comp_continuousOn hL
  have hSa : (L a).im ∈ S :=
    ⟨a, ⟨le_refl a, hab⟩, rfl⟩
  have hSb : (L b).im ∈ S :=
    ⟨b, ⟨hab, le_refl b⟩, rfl⟩
  have hScos : ∀ y ∈ S, 0 < Real.cos y := by
    rintro y ⟨u, hu, rfl⟩
    exact hcos u hu
  by_contra hcon
  push_neg at hcon
  -- the interval between the endpoint values sits inside S
  set c : ℝ := min ((L a).im) ((L b).im) with hc
  set d : ℝ := max ((L a).im) ((L b).im) with hd
  have hcd : c ≤ d := min_le_max
  have hlen : Real.pi ≤ d - c := by
    rw [hd, hc, max_sub_min_eq_abs]
    exact hcon
  have hsub : Set.Icc c d ⊆ S := by
    have hord : S.OrdConnected := hSconn.ordConnected
    apply hord.out
    · rw [hc]
      rcases min_cases ((L a).im) ((L b).im) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; exact hSa
      · rw [h]; exact hSb
    · rw [hd]
      rcases max_cases ((L a).im) ((L b).im) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; exact hSa
      · rw [h]; exact hSb
  obtain ⟨z, hz, hzcos⟩ := exists_cos_zero_of_length_ge_pi hcd hlen
  have := hScos z (hsub hz)
  rw [hzcos] at this
  exact lt_irrefl 0 this

/-- The center floor for the symmetrization: `Re ζ(2+iT) ≥ 1/4`. -/
theorem re_zeta_two_add_it_ge {T : ℝ} :
    (1:ℝ)/4 ≤ (riemannZeta ((2:ℂ) + T * Complex.I)).re := by
  set s : ℂ := (2:ℂ) + T * Complex.I with hs
  have hsre : s.re = 2 := by
    rw [hs]
    simp
  have hs1 : (1:ℝ) < s.re := by
    rw [hsre]
    norm_num
  have hsum : Summable (fun n : ℕ => 1 / ((n:ℂ)) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs1
  have hre_eq : (riemannZeta s).re = ∑' n : ℕ, (1 / ((n:ℂ)) ^ s).re := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs1, Complex.re_tsum hsum]
  have hre_sum : Summable (fun n : ℕ => (1 / ((n:ℂ)) ^ s).re) :=
    ⟨_, hsum.hasSum.mapL Complex.reCLM⟩
  -- peel n = 0 and n = 1
  have h0 : (1 / ((0:ℕ):ℂ) ^ s).re = 0 := by
    rw [Nat.cast_zero, zero_cpow (by
      intro h
      rw [h] at hsre
      simp at hsre)]
    simp
  have h1 : (1 / ((1:ℕ):ℂ) ^ s).re = 1 := by
    rw [Nat.cast_one, one_cpow]
    simp
  rw [hre_eq, hre_sum.tsum_eq_zero_add]
  rw [((summable_nat_add_iff 1).mpr hre_sum).tsum_eq_zero_add]
  simp only [Nat.cast_ofNat, zero_add]
  rw [h0, h1]
  -- the n ≥ 2 block is bounded by 3/4 in absolute value
  have habs : |∑' n : ℕ, (1 / (((n+1+1:ℕ)):ℂ) ^ s).re| ≤ 3/4 := by
    have hterm : ∀ n : ℕ, |(1 / (((n+1+1:ℕ)):ℂ) ^ s).re|
        ≤ (((n+2:ℕ)):ℝ) ^ (-(2:ℝ)) := by
      intro n
      have hpos : 0 < n+1+1 := by omega
      calc |(1 / (((n+1+1:ℕ)):ℂ) ^ s).re|
          ≤ ‖1 / (((n+1+1:ℕ)):ℂ) ^ s‖ := Complex.abs_re_le_norm _
        _ = (((n+1+1:ℕ)):ℝ) ^ (-s.re) := by
            rw [norm_div, norm_one,
              Complex.norm_natCast_cpow_of_pos hpos, one_div,
              Real.rpow_neg (Nat.cast_nonneg _)]
        _ = (((n+2:ℕ)):ℝ) ^ (-(2:ℝ)) := by
            rw [hsre]
    have hmaj : Summable (fun n : ℕ => (((n+2:ℕ)):ℝ) ^ (-(2:ℝ))) := by
      have hbase : Summable (fun n : ℕ => ((n:ℝ)) ^ (-(2:ℝ))) := by
        rw [Real.summable_nat_rpow]
        norm_num
      apply Summable.congr ((summable_nat_add_iff 2).mpr hbase)
      intro n
      norm_num
    have hmaj_sum : (∑' n : ℕ, (((n+2:ℕ)):ℝ) ^ (-(2:ℝ))) ≤ 3/4 := by
      rw [hmaj.tsum_eq_zero_add]
      have hz : (((0+2:ℕ)):ℝ) ^ (-(2:ℝ)) = 1/4 := by
        rw [show (((0+2:ℕ)):ℝ) = 2 by norm_num,
          Real.rpow_neg (by norm_num),
          show ((2:ℝ)) ^ ((2:ℝ)) = 4 by
            rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
            norm_num]
        norm_num
      rw [hz]
      have hshift : (∑' n : ℕ, (((n+1+2:ℕ)):ℝ) ^ (-(2:ℝ))) ≤ 1/2 := by
        have hcongr : ∀ n : ℕ, (((n+1+2:ℕ)):ℝ) ^ (-(2:ℝ))
            = (((2+1+n:ℕ)):ℝ) ^ (-(2:ℝ)) := by
          intro n
          congr 2
          omega
        rw [tsum_congr hcongr]
        have := rpow_tail_tsum_le (N := 2) (by norm_num) (p := 2)
          (by norm_num)
        calc (∑' k : ℕ, (((2+1+k:ℕ)):ℝ) ^ (-(2:ℝ)))
            ≤ ((2:ℕ):ℝ) ^ ((1:ℝ) - 2) / (2 - 1) := this
          _ ≤ 1/2 := by
              rw [show ((1:ℝ) - 2) = -1 by norm_num, Real.rpow_neg_one]
              norm_num
      linarith
    have hns : Summable (fun n : ℕ =>
        |(1 / (((n+1+1:ℕ)):ℂ) ^ s).re|) :=
      Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm hmaj
    calc |∑' n : ℕ, (1 / (((n+1+1:ℕ)):ℂ) ^ s).re|
        ≤ ∑' n : ℕ, |(1 / (((n+1+1:ℕ)):ℂ) ^ s).re| := by
          calc |∑' n : ℕ, (1 / (((n+1+1:ℕ)):ℂ) ^ s).re|
              = ‖∑' n : ℕ, (1 / (((n+1+1:ℕ)):ℂ) ^ s).re‖ :=
                (Real.norm_eq_abs _).symm
            _ ≤ ∑' n : ℕ, ‖(1 / (((n+1+1:ℕ)):ℂ) ^ s).re‖ := by
                apply norm_tsum_le_tsum_norm
                have heq : (fun n : ℕ => ‖(1 / (((n+1+1:ℕ)):ℂ) ^ s).re‖)
                    = fun n => |(1 / (((n+1+1:ℕ)):ℂ) ^ s).re| := by
                  funext n
                  exact Real.norm_eq_abs _
                rw [heq]
                exact hns
            _ = ∑' n : ℕ, |(1 / (((n+1+1:ℕ)):ℂ) ^ s).re| := by
                apply tsum_congr
                intro n
                exact Real.norm_eq_abs _
      _ ≤ ∑' n : ℕ, (((n+2:ℕ)):ℝ) ^ (-(2:ℝ)) := by
          apply Summable.tsum_le_tsum _ _ hmaj
          · exact hterm
          · apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
              hterm hmaj
      _ ≤ 3/4 := hmaj_sum
  have := abs_le.mp habs
  linarith [this.1]

/-- The reusable band bound: `‖ζ(w)‖ ≤ 48·T^{3/4}` for `w` in the strip
`Re ∈ [¼, 15/4]` at height `|Im w| ∈ [T−7/4, T+7/4]`, `T ≥ 50`. -/
theorem zeta_band_bound_at_height {w : ℂ} {T : ℝ} (hT50 : (50:ℝ) ≤ T)
    (hrel : (1:ℝ)/4 ≤ w.re) (hreu : w.re ≤ 15/4)
    (himl : T - 7/4 ≤ |w.im|) (himu : |w.im| ≤ T + 7/4) :
    ‖riemannZeta w‖ ≤ 48 * T ^ ((3:ℝ)/4) := by
  have hTpos : (0:ℝ) < T := by linarith
  have hT34ge1 : (1:ℝ) ≤ T ^ ((3:ℝ)/4) := by
    calc (1:ℝ) = 1 ^ ((3:ℝ)/4) := (Real.one_rpow _).symm
      _ ≤ T ^ ((3:ℝ)/4) := Real.rpow_le_rpow (by norm_num) (by linarith)
        (by norm_num)
  rcases le_or_gt w.re 2 with hre2 | hre2
  · have hzim2 : (2:ℝ) ≤ |w.im| := by linarith
    have hgrowth := zeta_polynomial_growth_quarter hzim2 hrel hre2
    have hzimT : |w.im| ≤ 2 * T := by linarith
    calc ‖riemannZeta w‖ ≤ 24 * |w.im| ^ ((3:ℝ)/4) := hgrowth
      _ ≤ 24 * (2 * T) ^ ((3:ℝ)/4) := by
          apply mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg _) hzimT (by norm_num))
            (by norm_num)
      _ = 24 * ((2:ℝ) ^ ((3:ℝ)/4) * T ^ ((3:ℝ)/4)) := by
          rw [Real.mul_rpow (by norm_num) hTpos.le]
      _ ≤ 24 * (2 * T ^ ((3:ℝ)/4)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _
            (Real.rpow_nonneg hTpos.le _)
          calc (2:ℝ) ^ ((3:ℝ)/4) ≤ 2 ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
      _ = 48 * T ^ ((3:ℝ)/4) := by ring
  · have h1 : ‖riemannZeta w‖ ≤ 1 + 1/(w.re - 1) :=
      zeta_norm_le_of_one_lt (by linarith)
    have h2 : 1/(w.re - 1) ≤ 1 := by
      apply div_le_one_of_le₀ (by linarith) (by linarith)
    calc ‖riemannZeta w‖ ≤ 1 + 1/(w.re - 1) := h1
      _ ≤ 2 := by linarith
      _ ≤ 48 * T ^ ((3:ℝ)/4) := by nlinarith

set_option maxHeartbeats 3200000 in
/-- **B2b: the sign-change count.**  For `T ≥ e⁶` there is a finite
`Z ⊂ ℝ` with at most `20·log T` elements containing every zero of
`σ ↦ ζ(σ+iT) + ζ(σ−iT)` (= `2·Re ζ(σ+iT)` for real σ) on `[½, 2]`. -/
theorem F_symm_zeros_count {T : ℝ} (hT : Real.exp 6 ≤ T) :
    ∃ Z : Finset ℝ,
      (∀ σ : ℝ, σ ∈ Set.Icc (1/2 : ℝ) 2 →
        riemannZeta (((σ:ℝ):ℂ) + T * Complex.I)
          + riemannZeta (((σ:ℝ):ℂ) - T * Complex.I) = 0 → σ ∈ Z) ∧
      (Z.card : ℝ) ≤ 20 * Real.log T := by
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 6) hT
  have hL6 : (6:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 6) hT
    rwa [Real.log_exp] at this
  have hT400 : (400:ℝ) ≤ T := by
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h6 : Real.exp 6 = (Real.exp 1 * Real.exp 1)
        * (Real.exp 1 * Real.exp 1) * (Real.exp 1 * Real.exp 1) := by
      rw [show (6:ℝ) = 1+1+(1+1)+(1+1) by norm_num]
      simp only [Real.exp_add]
    nlinarith [he2, Real.exp_pos 1]
  set L : ℝ := Real.log T with hLdef
  have hLpos : (0:ℝ) < L := by linarith
  set F : ℂ → ℂ := fun z =>
    riemannZeta (z + T * Complex.I) + riemannZeta (z - T * Complex.I)
    with hFdef
  -- analyticity on the ball
  have hanal : AnalyticOnNhd ℂ F (Metric.closedBall (2:ℂ) (7/4)) := by
    have hopen : IsOpen {z : ℂ | z + T * Complex.I ≠ 1
        ∧ z - T * Complex.I ≠ 1} := by
      apply IsOpen.inter
      · exact isOpen_ne.preimage (by continuity)
      · exact isOpen_ne.preimage (by continuity)
    apply AnalyticOnNhd.mono (DifferentiableOn.analyticOnNhd
      (f := F) (s := {z : ℂ | z + T * Complex.I ≠ 1
        ∧ z - T * Complex.I ≠ 1}) ?_ hopen)
    · intro z hz
      simp only [Metric.mem_closedBall] at hz
      have him : |(z - 2).im| ≤ 7/4 := by
        rw [dist_eq_norm] at hz
        exact le_trans (Complex.abs_im_le_norm _) hz
      rw [show (z - 2 : ℂ).im = z.im by simp] at him
      rw [abs_le] at him
      constructor
      · intro h
        have := congrArg Complex.im h
        simp at this
        linarith
      · intro h
        have := congrArg Complex.im h
        simp at this
        linarith
    · intro z hz
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.add
      · exact (differentiableAt_riemannZeta hz.1).comp z
          (differentiableAt_id.add_const _)
      · exact (differentiableAt_riemannZeta hz.2).comp z
          (differentiableAt_id.sub_const _)
  -- the M bound
  have hM : ∀ z ∈ Metric.closedBall (2:ℂ) (7/4),
      ‖F z‖ ≤ 96 * T ^ ((3:ℝ)/4) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre : |(z - 2).re| ≤ 7/4 := le_trans (Complex.abs_re_le_norm _) hz
    have him : |(z - 2).im| ≤ 7/4 := le_trans (Complex.abs_im_le_norm _) hz
    rw [show (z - 2 : ℂ).re = z.re - 2 by simp] at hre
    rw [show (z - 2 : ℂ).im = z.im by simp] at him
    rw [abs_le] at hre him
    have hb1 : ‖riemannZeta (z + T * Complex.I)‖ ≤ 48 * T ^ ((3:ℝ)/4) := by
      apply zeta_band_bound_at_height (by linarith)
      · simp
        linarith [hre.1]
      · simp
        linarith [hre.2]
      · rw [show (z + T * Complex.I).im = z.im + T by simp]
        rw [abs_of_pos (by linarith [him.1])]
        linarith [him.1]
      · rw [show (z + T * Complex.I).im = z.im + T by simp]
        rw [abs_of_pos (by linarith [him.1])]
        linarith [him.2]
    have hb2 : ‖riemannZeta (z - T * Complex.I)‖ ≤ 48 * T ^ ((3:ℝ)/4) := by
      apply zeta_band_bound_at_height (by linarith)
      · simp
        linarith [hre.1]
      · simp
        linarith [hre.2]
      · rw [show (z - T * Complex.I).im = z.im - T by simp]
        rw [abs_of_neg (by linarith [him.2])]
        linarith [him.2]
      · rw [show (z - T * Complex.I).im = z.im - T by simp]
        rw [abs_of_neg (by linarith [him.2])]
        linarith [him.1]
    calc ‖F z‖ ≤ ‖riemannZeta (z + T * Complex.I)‖
        + ‖riemannZeta (z - T * Complex.I)‖ := norm_add_le _ _
      _ ≤ 96 * T ^ ((3:ℝ)/4) := by linarith
  -- the center floor
  have hF2re : (1:ℝ)/2 ≤ (F 2).re := by
    rw [hFdef]
    dsimp only
    rw [Complex.add_re]
    have hconj : riemannZeta ((2:ℂ) - T * Complex.I)
        = (starRingEnd ℂ) (riemannZeta ((2:ℂ) + T * Complex.I)) := by
      rw [← riemannZeta_conj]
      congr 1
      apply Complex.ext <;> simp
    rw [hconj, Complex.conj_re]
    have := re_zeta_two_add_it_ge (T := T)
    linarith
  have hF2norm : (1:ℝ)/2 ≤ ‖F 2‖ :=
    le_trans hF2re (Complex.re_le_norm _)
  have hF2ne : F 2 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hF2norm
    linarith
  have hM1 : (1:ℝ) ≤ 96 * T ^ ((3:ℝ)/4) := by
    have : (1:ℝ) ≤ T ^ ((3:ℝ)/4) := by
      calc (1:ℝ) = 1 ^ ((3:ℝ)/4) := (Real.one_rpow _).symm
        _ ≤ T ^ ((3:ℝ)/4) := Real.rpow_le_rpow (by norm_num) (by linarith)
          (by norm_num)
    nlinarith
  -- Jensen
  have hjensen := AnalyticOnNhd.sum_divisor_le
    (c := (2:ℂ)) (r := 8/5) (R := 7/4) (M := 96 * T ^ ((3:ℝ)/4))
    (f := F) (by norm_num) (by norm_num) hM1
    (by
      rw [show |(7/4 : ℝ)| = 7/4 by norm_num]
      exact hanal)
    hF2ne
    (by
      rw [show |(7/4 : ℝ)| = 7/4 by norm_num]
      intro z hz
      exact hM z (Metric.sphere_subset_closedBall hz))
  rw [show |(8/5 : ℝ)| = 8/5 by norm_num] at hjensen
  -- numerator/denominator
  have hquot : Real.log (96 * T ^ ((3:ℝ)/4) / ‖F 2‖)
      / Real.log ((7/4 : ℝ) / (8/5 : ℝ)) ≤ 20 * L := by
    have hnum : Real.log (96 * T ^ ((3:ℝ)/4) / ‖F 2‖) ≤ 1.7 * L := by
      have hq : 96 * T ^ ((3:ℝ)/4) / ‖F 2‖ ≤ 192 * T ^ ((3:ℝ)/4) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖F 2‖)]
        nlinarith [Real.rpow_nonneg hTpos.le ((3:ℝ)/4)]
      have hstep := Real.log_le_log (by positivity) hq
      have hsplit : Real.log (192 * T ^ ((3:ℝ)/4))
          = Real.log 192 + (3/4) * L := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hTpos]
      have hlog192 : Real.log 192 ≤ 5.56 := by
        have h192 : (192:ℝ) = 2^(6:ℕ) * 3 := by norm_num
        rw [h192, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
        have hlog3 : Real.log 3 ≤ 1.4 := by
          calc Real.log 3 ≤ Real.log 4 :=
              Real.log_le_log (by norm_num) (by norm_num)
            _ = Real.log (2^(2:ℕ)) := by norm_num
            _ = 2 * Real.log 2 := by
                rw [Real.log_pow]
                push_cast
                ring
            _ ≤ 1.4 := by nlinarith [Real.log_two_lt_d9]
        push_cast
        nlinarith [Real.log_two_lt_d9]
      rw [hsplit] at hstep
      have h556 : (5.56:ℝ) ≤ 0.95 * L := by nlinarith
      linarith
    have hden : (3:ℝ)/35 ≤ Real.log ((7/4 : ℝ) / (8/5 : ℝ)) := by
      have hval : ((7/4 : ℝ) / (8/5 : ℝ)) = 35/32 := by norm_num
      rw [hval]
      have h1 : Real.log (32/35 : ℝ) ≤ 32/35 - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num)
      have h2 : Real.log (35/32 : ℝ) = -Real.log (32/35 : ℝ) := by
        rw [← Real.log_inv]
        norm_num
      rw [h2]
      linarith
    have hdenpos : (0:ℝ) < Real.log ((7/4 : ℝ) / (8/5 : ℝ)) := by linarith
    rw [div_le_iff₀ hdenpos]
    calc Real.log (96 * T ^ ((3:ℝ)/4) / ‖F 2‖) ≤ 1.7 * L := hnum
      _ ≤ 20 * L * (3/35) := by nlinarith
      _ ≤ 20 * L * Real.log ((7/4 : ℝ) / (8/5 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hden (by positivity)
  -- the divisor support and the real-zero collection
  have hsupp : (MeromorphicOn.divisor F
      (Metric.closedBall (2:ℂ) (8/5))).support.Finite :=
    (MeromorphicOn.divisor F _).finiteSupport
      (isCompact_closedBall (2:ℂ) (8/5))
  set Z : Finset ℝ :=
    (hsupp.toFinset.filter (fun z => z.im = 0)).image Complex.re with hZdef
  refine ⟨Z, ?_, ?_⟩
  · -- completeness: every real zero of F on [½,2] is collected
    intro σ hσ hFσ
    have hσball : ((σ:ℝ):ℂ) ∈ Metric.closedBall (2:ℂ) (8/5) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [show ((σ:ℝ):ℂ) - 2 = (((σ - 2 : ℝ)):ℂ) by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor
      · linarith [hσ.1]
      · linarith [hσ.2]
    have hanal85 : AnalyticOnNhd ℂ F (Metric.closedBall (2:ℂ) (8/5)) :=
      hanal.mono (Metric.closedBall_subset_closedBall (by norm_num))
    have hFσ' : F ((σ:ℝ):ℂ) = 0 := hFσ
    have hordne : analyticOrderAt F ((σ:ℝ):ℂ) ≠ 0 := by
      rw [analyticOrderAt_ne_zero]
      exact ⟨hanal85 _ hσball, hFσ'⟩
    have hordtop : analyticOrderAt F ((σ:ℝ):ℂ) ≠ ⊤ :=
      analyticOrderAt_ne_top_of_ne_zero
        (convex_closedBall (2:ℂ) (8/5)).isPreconnected hanal85
        (Metric.mem_closedBall_self (by norm_num)) hF2ne hσball
    have hdiv_ne : MeromorphicOn.divisor F
        (Metric.closedBall (2:ℂ) (8/5)) ((σ:ℝ):ℂ) ≠ 0 := by
      obtain ⟨m, hm⟩ : ∃ m : ℕ, (m:ℕ∞) = analyticOrderAt F ((σ:ℝ):ℂ) :=
        ENat.ne_top_iff_exists.mp hordtop
      have hm_ne : m ≠ 0 := fun h => hordne (by rw [← hm, h]; rfl)
      rw [MeromorphicOn.divisor_apply hanal85.meromorphicOn hσball,
        (hanal85 _ hσball).meromorphicOrderAt_eq, ← hm]
      simp
      exact_mod_cast hm_ne
    have hmem : ((σ:ℝ):ℂ) ∈ hsupp.toFinset := by
      rw [Set.Finite.mem_toFinset, Function.mem_support]
      exact hdiv_ne
    rw [hZdef]
    exact Finset.mem_image.mpr ⟨((σ:ℝ):ℂ),
      Finset.mem_filter.mpr ⟨hmem, by simp⟩, by simp⟩
  · -- the count: card ≤ divisor total ≤ Jensen
    have hanal85 : AnalyticOnNhd ℂ F (Metric.closedBall (2:ℂ) (8/5)) :=
      hanal.mono (Metric.closedBall_subset_closedBall (by norm_num))
    have hone : ∀ z ∈ hsupp.toFinset.filter (fun z => z.im = 0),
        1 ≤ MeromorphicOn.divisor F (Metric.closedBall (2:ℂ) (8/5)) z := by
      intro z hz
      rw [Finset.mem_filter, Set.Finite.mem_toFinset,
        Function.mem_support] at hz
      obtain ⟨hne, _⟩ := hz
      have hnn : (0:ℤ) ≤ (MeromorphicOn.divisor F
          (Metric.closedBall (2:ℂ) (8/5))) z :=
        MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanal85 z
      omega
    have hfinsum : (∑ᶠ u, MeromorphicOn.divisor F
        (Metric.closedBall (2:ℂ) (8/5)) u)
        = ∑ u ∈ hsupp.toFinset, MeromorphicOn.divisor F
            (Metric.closedBall (2:ℂ) (8/5)) u :=
      finsum_eq_sum _ hsupp
    have hcard : ((hsupp.toFinset.filter (fun z => z.im = 0)).card : ℤ)
        ≤ ∑ᶠ u, MeromorphicOn.divisor F
            (Metric.closedBall (2:ℂ) (8/5)) u := by
      rw [hfinsum]
      calc ((hsupp.toFinset.filter (fun z => z.im = 0)).card : ℤ)
          = ∑ _z ∈ hsupp.toFinset.filter (fun z => z.im = 0), (1:ℤ) := by
            rw [Finset.sum_const]
            simp
        _ ≤ ∑ z ∈ hsupp.toFinset.filter (fun z => z.im = 0),
              MeromorphicOn.divisor F
                (Metric.closedBall (2:ℂ) (8/5)) z :=
            Finset.sum_le_sum hone
        _ ≤ ∑ z ∈ hsupp.toFinset, MeromorphicOn.divisor F
              (Metric.closedBall (2:ℂ) (8/5)) z := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _)
            intro z _ _
            exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanal85 z
    have hZcard : (Z.card : ℝ)
        ≤ ((hsupp.toFinset.filter (fun z => z.im = 0)).card : ℝ) := by
      rw [hZdef]
      exact_mod_cast Finset.card_image_le
    calc (Z.card : ℝ)
        ≤ ((hsupp.toFinset.filter (fun z => z.im = 0)).card : ℝ) := hZcard
      _ ≤ ((∑ᶠ u, MeromorphicOn.divisor F
            (Metric.closedBall (2:ℂ) (8/5)) u : ℤ) : ℝ) := by
          exact_mod_cast hcard
      _ ≤ Real.log (96 * T ^ ((3:ℝ)/4) / ‖F 2‖)
          / Real.log ((7/4 : ℝ) / (8/5 : ℝ)) := hjensen
      _ ≤ 20 * L := hquot

set_option maxHeartbeats 1600000 in
/-- **B3: the variation bound by crossing count.**  If every `σ` where
`Re(exp(L σ)) = 0` lies in the finite set `Z`, then the argument varies by
at most `(|Z|+1)·π`: a larger swing would, by the intermediate value
theorem, force `|Z|+1` distinct crossings of the cosine lattice
`π/2 + πℤ`, each a member of `Z`. -/
theorem lift_variation_le_of_zeros_card {a b : ℝ} (hab : a ≤ b)
    {L : ℝ → ℂ} (hL : ContinuousOn L (Set.Icc a b))
    {Z : Finset ℝ}
    (hZ : ∀ σ ∈ Set.Icc a b, (Complex.exp (L σ)).re = 0 → σ ∈ Z) :
    |(L b).im - (L a).im| ≤ (Z.card + 1) * Real.pi := by
  by_contra hcon
  push_neg at hcon
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  set c : ℝ := min ((L a).im) ((L b).im) with hc
  set d : ℝ := max ((L a).im) ((L b).im) with hd
  have hlen : (Z.card + 1) * Real.pi < d - c := by
    rw [hd, hc, max_sub_min_eq_abs]
    exact hcon
  set j₀ : ℤ := ⌈(c - Real.pi/2) / Real.pi⌉ with hj₀
  set p : Fin (Z.card + 1) → ℝ :=
    fun j => Real.pi/2 + ((j₀ : ℝ) + (j : ℕ)) * Real.pi with hp
  have hp_mem : ∀ j : Fin (Z.card + 1), p j ∈ Set.Icc c d := by
    intro j
    have h1 : (c - Real.pi/2) / Real.pi ≤ (j₀:ℝ) := Int.le_ceil _
    rw [div_le_iff₀ hπ] at h1
    have h2 : (j₀:ℝ) < (c - Real.pi/2) / Real.pi + 1 := Int.ceil_lt_add_one _
    have h2' : (j₀:ℝ) * Real.pi < c - Real.pi/2 + Real.pi := by
      have hm := mul_lt_mul_of_pos_right h2 hπ
      rw [add_mul, one_mul, div_mul_cancel₀ _ hπ.ne'] at hm
      linarith
    have hj_le : ((j:ℕ):ℝ) ≤ (Z.card : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.mp j.isLt
    constructor
    · rw [hp]
      dsimp only
      nlinarith [Nat.cast_nonneg' (α := ℝ) (j:ℕ)]
    · rw [hp]
      dsimp only
      nlinarith
  have hIm_cont : ContinuousOn (fun σ => (L σ).im) (Set.Icc a b) :=
    Complex.continuous_im.comp_continuousOn hL
  have hattain : ∀ j : Fin (Z.card + 1),
      ∃ σ ∈ Set.Icc a b, (L σ).im = p j := by
    intro j
    rcases le_total ((L a).im) ((L b).im) with hle | hle
    · have hsub := intermediate_value_Icc hab hIm_cont
      have hpj : p j ∈ Set.Icc ((L a).im) ((L b).im) := by
        constructor
        · calc (L a).im = c := by rw [hc, min_eq_left hle]
            _ ≤ p j := (hp_mem j).1
        · calc p j ≤ d := (hp_mem j).2
            _ = (L b).im := by rw [hd, max_eq_right hle]
      obtain ⟨σ, hσ, hval⟩ := hsub hpj
      exact ⟨σ, hσ, hval⟩
    · have hsub := intermediate_value_Icc' hab hIm_cont
      have hpj : p j ∈ Set.Icc ((L b).im) ((L a).im) := by
        constructor
        · calc (L b).im = c := by rw [hc, min_eq_right hle]
            _ ≤ p j := (hp_mem j).1
        · calc p j ≤ d := (hp_mem j).2
            _ = (L a).im := by rw [hd, max_eq_left hle]
      obtain ⟨σ, hσ, hval⟩ := hsub hpj
      exact ⟨σ, hσ, hval⟩
  choose σsel hσsel_mem hσsel_val using hattain
  have hσZ : ∀ j, σsel j ∈ Z := by
    intro j
    apply hZ (σsel j) (hσsel_mem j)
    rw [Complex.exp_re, hσsel_val j, hp]
    dsimp only
    have hcos : Real.cos (Real.pi/2 + ((j₀:ℝ) + (j:ℕ)) * Real.pi) = 0 := by
      rw [show ((j₀:ℝ) + ((j:ℕ):ℝ)) = (((j₀ + (j:ℕ)):ℤ):ℝ) by push_cast; ring]
      rw [add_comm, Real.cos_add_pi_div_two, Real.sin_int_mul_pi]
      ring
    rw [hcos, mul_zero]
  have hinj : Function.Injective σsel := by
    intro i j h
    have : p i = p j := by
      rw [← hσsel_val i, ← hσsel_val j, h]
    rw [hp] at this
    dsimp only at this
    have hpi : ((i:ℕ):ℝ) = ((j:ℕ):ℝ) := by
      have := mul_right_cancel₀ hπ.ne'
        (show (((j₀:ℝ) + (i:ℕ))) * Real.pi = (((j₀:ℝ) + (j:ℕ))) * Real.pi by
          linarith)
      linarith
    exact Fin.ext (by exact_mod_cast hpi)
  -- card contradiction
  have hcard : Z.card + 1 ≤ Z.card := by
    have hle := Finset.card_le_card_of_injOn (s := Finset.univ)
      (t := Z) σsel (fun j _ => hσZ j)
      (hinj.injOn)
    simpa using hle
  omega

/-- **B4: the vertical segment is a single tube.**  Any continuous logarithm
of `ζ` along `σ = 2` from height `0` to `T` has argument variation `< π` —
the values never leave `Re > 0` (`Re ζ(2+it) ≥ ¼`). -/
theorem vertical_lift_confined {T : ℝ} (hT : 0 ≤ T) {L : ℝ → ℂ}
    (hL : ContinuousOn L (Set.Icc 0 T))
    (hexp : ∀ t ∈ Set.Icc (0:ℝ) T,
      Complex.exp (L t) = riemannZeta ((2:ℂ) + t * Complex.I)) :
    |(L T).im - (L 0).im| < Real.pi := by
  apply im_confined_of_exp_re_pos hT hL
  intro t ht
  rw [hexp t ht]
  have := re_zeta_two_add_it_ge (T := t)
  linarith

/-! ## The S-contour assembly -/

open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

/-- The ζ-contour lift extended to the real parameter line. -/
noncomputable def zetaLiftReal {T : ℝ} (hT : GoodHeight T) : C(ℝ, ℂ) :=
  ContinuousMap.IccExtendCM (contourLogLift hT)

theorem zetaLiftReal_of_mem {T : ℝ} (hT : GoodHeight T) {u : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    zetaLiftReal hT u = contourLogLift hT ⟨u, hu⟩ :=
  ContinuousMap.IccExtendCM_of_mem hu

set_option maxHeartbeats 1600000 in
/-- The lift along the vertical edge exponentiates to `ζ(2+iy)`. -/
theorem exp_zetaLiftReal_vertical {T : ℝ} (hT : GoodHeight T) {y : ℝ}
    (hy : y ∈ Set.Icc (0:ℝ) T) :
    Complex.exp (zetaLiftReal hT (y / (2*T)))
      = riemannZeta (2 + (y:ℂ) * Complex.I) := by
  have hT0 : 0 < T := hT.1
  have hTne : (T:ℝ) ≠ 0 := hT0.ne'
  have hu0 : 0 ≤ y/(2*T) := div_nonneg hy.1 (by linarith)
  have huhalf : y/(2*T) ≤ 1/2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith [hy.2]
  have hu : y/(2*T) ∈ Set.Icc (0:ℝ) 1 := ⟨hu0, huhalf.trans (by norm_num)⟩
  rw [zetaLiftReal_of_mem hT hu, exp_contourLogLift]
  rw [standardContour, Path.trans_apply]
  split_ifs with hbranch
  · change riemannZeta (AffineMap.lineMap (2 : ℂ) (upperRight T) _) = _
    rw [AffineMap.lineMap_apply_module]
    congr 1
    apply Complex.ext
    · simp [upperRight, Complex.mul_re, Complex.mul_im, Complex.div_re,
        Complex.div_im, Complex.normSq_apply]
      ring
    · simp [upperRight, Complex.mul_re, Complex.mul_im, Complex.div_re,
        Complex.div_im, Complex.normSq_apply]
      field_simp
  · exact (hbranch (by simpa using huhalf)).elim

set_option maxHeartbeats 1600000 in
/-- The lift along the top edge exponentiates to `ζ(x+iT)`. -/
theorem exp_zetaLiftReal_top {T : ℝ} (hT : GoodHeight T) {x : ℝ}
    (hx : x ∈ Set.Icc (1/2:ℝ) 2) :
    Complex.exp (zetaLiftReal hT ((7/2 - x) / 3))
      = riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I) := by
  have hu0 : 0 ≤ (7/2 - x)/3 := by linarith [hx.2]
  have huhalf : 1/2 ≤ (7/2 - x)/3 := by linarith [hx.2]
  have hu1 : (7/2 - x)/3 ≤ 1 := by linarith [hx.1]
  rw [zetaLiftReal_of_mem hT ⟨hu0, hu1⟩, exp_contourLogLift]
  rw [standardContour, Path.trans_apply]
  split_ifs with hbranch
  · have hle : (7/2 - x)/3 ≤ 1/2 := by simpa using hbranch
    have hxeq : x = 2 := by linarith
    subst hxeq
    change riemannZeta (AffineMap.lineMap (2 : ℂ) (upperRight T) _) = _
    rw [AffineMap.lineMap_apply_module]
    congr 1
    apply Complex.ext <;> simp [upperRight] <;> ring
  · change riemannZeta (AffineMap.lineMap (upperRight T) (line T) _) = _
    rw [AffineMap.lineMap_apply_module]
    congr 1
    apply Complex.ext <;>
      simp [upperRight, CriticalLinePhasor.CarrierScale.line,
        CriticalLinePhasor.CarrierScale.lineC] <;> ring

set_option maxHeartbeats 3200000 in
/-- **THE S-CONTOUR BOUND**: `|S(T)| ≤ 20·log T + 3` at every good height
`T ≥ e⁶`.  The vertical edge contributes `< π` (tube), the top edge at most
`(Q+1)·π` with `Q ≤ 20·log T` sign changes (crossing count + Jensen). -/
theorem abs_classicalSContour_le {T : ℝ} (hT6 : Real.exp 6 ≤ T)
    (hT : GoodHeight T) :
    |classicalSContour hT| ≤ 20 * Real.log T + 3 := by
  have hT0 : 0 < T := hT.1
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  -- the initial imaginary part vanishes
  have h0im : (contourLogLift hT 0).im = 0 := by
    rw [contourLogLift_zero]
    rw [initialLog]
    simp
  -- vertical edge
  set Lv : ℝ → ℂ := fun y => zetaLiftReal hT (y / (2*T)) with hLv
  have hLv_cont : ContinuousOn Lv (Set.Icc 0 T) := by
    apply Continuous.continuousOn
    exact (zetaLiftReal hT).continuous.comp (by continuity)
  have hvert := vertical_lift_confined hT0.le hLv_cont
    (fun t ht => exp_zetaLiftReal_vertical hT ht)
  -- top edge
  set Lh : ℝ → ℂ := fun x => zetaLiftReal hT ((7/2 - x) / 3) with hLh
  have hLh_cont : ContinuousOn Lh (Set.Icc (1/2:ℝ) 2) := by
    apply Continuous.continuousOn
    exact (zetaLiftReal hT).continuous.comp (by continuity)
  obtain ⟨Z, hZmem, hZcard⟩ := F_symm_zeros_count hT6
  have htop := lift_variation_le_of_zeros_card
    (by norm_num : (1/2:ℝ) ≤ 2) hLh_cont
    (Z := Z)
    (by
      intro σ hσ hre0
      apply hZmem σ hσ
      have hexp := exp_zetaLiftReal_top hT hσ
      rw [hLh] at hre0
      dsimp only at hre0
      rw [hexp] at hre0
      -- F(σ) = ζ(σ+iT) + ζ(σ−iT) = 2·Re ζ(σ+iT) = 0
      have hconj : riemannZeta (((σ:ℝ):ℂ) - T * Complex.I)
          = (starRingEnd ℂ) (riemannZeta (((σ:ℝ):ℂ) + T * Complex.I)) := by
        rw [← riemannZeta_conj]
        congr 1
        apply Complex.ext <;> simp
      rw [hconj]
      apply Complex.ext
      · rw [Complex.add_re, Complex.conj_re]
        simp only [Complex.zero_re]
        linarith [hre0]
      · rw [Complex.add_im, Complex.conj_im]
        simp
    )
  -- endpoint identifications
  have hLv0 : Lv 0 = contourLogLift hT 0 := by
    rw [hLv]
    dsimp only
    rw [show (0:ℝ)/(2*T) = 0 by ring]
    rw [zetaLiftReal_of_mem hT (by norm_num : (0:ℝ) ∈ Set.Icc (0:ℝ) 1)]
    congr 1
  have hLvT : Lv T = zetaLiftReal hT (1/2) := by
    rw [hLv]
    dsimp only
    congr 1
    field_simp
  have hLh2 : Lh 2 = zetaLiftReal hT (1/2) := by
    rw [hLh]
    dsimp only
    congr 1
    norm_num
  have hLhhalf : Lh (1/2) = contourLogLift hT 1 := by
    rw [hLh]
    dsimp only
    rw [show ((7:ℝ)/2 - 1/2)/3 = 1 by norm_num]
    rw [zetaLiftReal_of_mem hT (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]
    congr 1
  -- combine
  have hchain : |(contourLogLift hT 1).im|
      ≤ ((Z.card : ℝ) + 1) * Real.pi + Real.pi := by
    have h1 : |(Lh 2).im - (Lh (1/2)).im| ≤ ((Z.card : ℝ) + 1) * Real.pi :=
      htop
    have h2 : |(Lv T).im - (Lv 0).im| < Real.pi := hvert
    rw [hLh2, hLhhalf] at h1
    rw [hLvT, hLv0] at h2
    rw [h0im] at h2
    have h3 : |(contourLogLift hT 1).im|
        ≤ |(zetaLiftReal hT (1/2)).im - (contourLogLift hT 1).im|
          + |(zetaLiftReal hT (1/2)).im - (contourLogLift hT 0).im|
          + |(contourLogLift hT 0).im| := by
      calc |(contourLogLift hT 1).im|
          = |((contourLogLift hT 1).im - (zetaLiftReal hT (1/2)).im)
            + ((zetaLiftReal hT (1/2)).im - (contourLogLift hT 0).im)
            + (contourLogLift hT 0).im| := by ring_nf
        _ ≤ |((contourLogLift hT 1).im - (zetaLiftReal hT (1/2)).im)
            + ((zetaLiftReal hT (1/2)).im - (contourLogLift hT 0).im)|
            + |(contourLogLift hT 0).im| := abs_add_le _ _
        _ ≤ |(contourLogLift hT 1).im - (zetaLiftReal hT (1/2)).im|
            + |(zetaLiftReal hT (1/2)).im - (contourLogLift hT 0).im|
            + |(contourLogLift hT 0).im| := by
              linarith [abs_add_le ((contourLogLift hT 1).im
                - (zetaLiftReal hT (1/2)).im)
                ((zetaLiftReal hT (1/2)).im - (contourLogLift hT 0).im)]
        _ = |(zetaLiftReal hT (1/2)).im - (contourLogLift hT 1).im|
            + |(zetaLiftReal hT (1/2)).im - (contourLogLift hT 0).im|
            + |(contourLogLift hT 0).im| := by
              rw [abs_sub_comm ((contourLogLift hT 1).im) _]
    rw [h0im] at h3
    simp only [abs_zero, add_zero] at h3
    linarith
  -- divide by π
  rw [classicalSContour, abs_div, abs_of_pos hπ]
  rw [div_le_iff₀ hπ]
  have hL6 : (6:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 6) hT6
    rwa [Real.log_exp] at this
  calc |(contourLogLift hT 1).im|
      ≤ ((Z.card : ℝ) + 1) * Real.pi + Real.pi := hchain
    _ ≤ (20 * Real.log T + 1) * Real.pi + Real.pi := by
        nlinarith [hZcard]
    _ = (20 * Real.log T + 2) * Real.pi := by ring
    _ ≤ (20 * Real.log T + 3) * Real.pi := by nlinarith

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.im_confined_of_exp_re_pos
#print axioms CriticalLinePhasor.DVP.re_zeta_two_add_it_ge
#print axioms CriticalLinePhasor.DVP.zeta_band_bound_at_height
#print axioms CriticalLinePhasor.DVP.F_symm_zeros_count
#print axioms CriticalLinePhasor.DVP.lift_variation_le_of_zeros_card
#print axioms CriticalLinePhasor.DVP.vertical_lift_confined
#print axioms CriticalLinePhasor.DVP.abs_classicalSContour_le
end AxiomAudit
