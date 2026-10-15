import RequestProject.DVPWeightedCount

/-!
# The exponent-one zero-free region with a sharper constant (ledger 1353)

`zero_free_region_exponent_one` (R5, ledger 313) gives `Re ρ ≤ 1 − (1/50000)/log|Im ρ|` for `|Im ρ| ≥ e³²`. Its
constant is assembled from the anchor `σ = 1 + 1/(10000 L)`, the real-axis rung `1/(σ−1) + 3`, and the
partial-fraction remainder `300·L`, itself `8·log(M/m)/r + N·4/(3r)` with `r = 1/8`, `log(M/m) ≤ 3L` and
`N ≤ 8L`. Two of these bounds are loose in the regime `L = log T ≥ 32` where the theorem lives:

* `log(M/m) = log 32 + L/4 + log(L+1)` was bounded using `log(L+1) ≤ L`; for `L ≥ 32`,
  `log(L+1) ≤ log 32 + (L+1)/32 − 1`, so `log(M/m) ≤ L/2` (`logMm_le_half`);
* the local count `N` is Jensen's `log(M/m)/log 2`, hence `N ≤ 0.73·L` (`zeta_local_zero_count_sharp`);
* so the remainder is `≤ 32L + 7.8L ≤ 40L` (`zeta_partial_fraction_sharp`);
* with the anchor re-optimised to `σ = 1 + 1/(400 L)`, the 3-4-1 budget is `4/(σ−β) ≤ 1402 L`, and
  `c₀ = 4/1402 − 1/400 > 1/3000` (`zero_free_region_exponent_one_sharp`).

Every ingredient is a compiled lemma of `DVPWeightedCount` (`landau_lemma`, `zeta_polynomial_growth`,
`zeta_center_floor`, `three_four_one`, `zeta_logDeriv_rung_sharp`, `AnalyticOnNhd.sum_divisor_le`); only the
arithmetic is sharper. This is an improvement of the repository's unconditional constant (from `1/50000` to
`1/3000`), not of the literature's (`1/5.558691`, Mossinghoff–Trudgian–Yang 2022). No `sorry`, no `axiom`.
-/

open Real Complex MeasureTheory Filter Topology Set

noncomputable section

namespace CriticalLinePhasor.DVP

/-! ## The sharper `log(M/m)` bound at `L ≥ 32` -/

/-- `log(32·T^{1/4}·(L+1)) ≤ L/2` for `L = log T ≥ 32`. -/
theorem logMm_le_half {T : ℝ} (hT : Real.exp 32 ≤ T) :
    Real.log (32 * T ^ ((1:ℝ)/4) * (Real.log T + 1)) ≤ Real.log T / 2 := by
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 32) hT
  have hL32 : (32:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 32) hT
    rwa [Real.log_exp] at this
  set L : ℝ := Real.log T with hLdef
  have hsplit : Real.log (32 * T ^ ((1:ℝ)/4) * (L + 1))
      = Real.log 32 + (1/4) * L + Real.log (L + 1) := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow hTpos]
  have hlog32 : Real.log 32 ≤ 3.5 := by
    have h32 : (32:ℝ) = 2 ^ (5:ℕ) := by norm_num
    rw [h32, Real.log_pow]
    push_cast
    nlinarith [Real.log_two_lt_d9]
  have hlogL1 : Real.log (L + 1) ≤ 3.5 + ((L + 1) / 32 - 1) := by
    have hpos : (0:ℝ) < (L + 1) / 32 := by positivity
    have h1 : Real.log (L + 1) = Real.log 32 + Real.log ((L + 1) / 32) := by
      rw [← Real.log_mul (by norm_num) hpos.ne']
      congr 1
      field_simp
    have h2 : Real.log ((L + 1) / 32) ≤ (L + 1) / 32 - 1 := Real.log_le_sub_one_of_pos hpos
    linarith
  rw [hsplit]
  linarith

/-! ## The local zero count at `L ≥ 32` -/

set_option maxHeartbeats 1600000 in
/-- The movable-center local zero count at `L ≥ 32`: at most `0.73·log T` zeros of `ζ` (with multiplicity)
in `B(1 + 1/log T + iT, 1/8)`. The compiled `zeta_local_zero_count` with the sharper numerator. -/
theorem zeta_local_zero_count_sharp {T : ℝ} (hT : Real.exp 32 ≤ T) :
    (↑(∑ᶠ u, MeromorphicOn.divisor riemannZeta
        (Metric.closedBall (((1 + 1 / Real.log T : ℝ) : ℂ) + T * Complex.I)
          (1/8)) u) : ℝ)
      ≤ 0.73 * Real.log T := by
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 32) hT
  have hL32 : (32:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 32) hT
    rwa [Real.log_exp] at this
  have hT7 : (7:ℝ) ≤ T := by
    have h2 : Real.exp 2 ≤ T := le_trans (Real.exp_le_exp.mpr (by norm_num)) hT
    have h2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  set L : ℝ := Real.log T with hLdef
  have hLpos : (0:ℝ) < L := by linarith
  set c : ℂ := ((1 + 1 / L : ℝ) : ℂ) + T * Complex.I with hcdef
  have hcre : c.re = 1 + 1 / L := by
    rw [hcdef]; simp
  have hcim : c.im = T := by
    rw [hcdef]; simp
  have hinvL : (0:ℝ) < 1 / L := by positivity
  have hinvL2 : 1 / L ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le
    · norm_num
    · linarith
  have hT14ge1 : (1:ℝ) ≤ T ^ ((1:ℝ)/4) := by
    calc (1:ℝ) = 1 ^ ((1:ℝ)/4) := (Real.one_rpow _).symm
      _ ≤ T ^ ((1:ℝ)/4) := Real.rpow_le_rpow (by norm_num) (by linarith)
        (by norm_num)
  -- Analyticity on the closed ball (the pole at 1 is at distance ≥ T)
  have hanal : AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall c |(1/4 : ℝ)|) := by
    apply AnalyticOnNhd.mono
      (DifferentiableOn.analyticOnNhd
        (f := riemannZeta) (s := {z : ℂ | z ≠ 1})
        (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
        isOpen_ne)
    intro z hz
    simp only [Metric.mem_closedBall] at hz
    intro h1
    rw [h1, dist_eq_norm] at hz
    have him : |((1:ℂ) - c).im| ≤ ‖(1:ℂ) - c‖ := Complex.abs_im_le_norm _
    have : ((1:ℂ) - c).im = -T := by
      simp [Complex.sub_im, hcim]
    rw [this, abs_neg, abs_of_pos hTpos] at him
    have : |(1/4 : ℝ)| = 1/4 := by norm_num
    rw [this] at hz
    linarith
  -- Center nonvanishing
  have hcre1 : (1:ℝ) < c.re := by
    rw [hcre]; linarith
  have hζc : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hcre1
  -- Sphere bound from B2′
  have hbound : ∀ z ∈ Metric.sphere c |(1/4 : ℝ)|,
      ‖riemannZeta z‖ ≤ 32 * T ^ ((1:ℝ)/4) := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have habs14 : |(1/4 : ℝ)| = 1/4 := by norm_num
    rw [habs14] at hz
    have hre : |(z - c).re| ≤ 1/4 := hz ▸ Complex.abs_re_le_norm _
    have him : |(z - c).im| ≤ 1/4 := hz ▸ Complex.abs_im_le_norm _
    rw [Complex.sub_re, hcre] at hre
    rw [Complex.sub_im, hcim] at him
    rw [abs_le] at hre him
    have hzim2 : (2:ℝ) ≤ |z.im| := by
      rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
      linarith
    have hzrel : (3:ℝ)/4 ≤ z.re := by linarith
    have hzreu : z.re ≤ 2 := by linarith
    have hgrowth := zeta_polynomial_growth hzim2 hzrel hzreu
    have hzimT : |z.im| ≤ 2 * T := by
      rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
      linarith
    calc ‖riemannZeta z‖ ≤ 16 * |z.im| ^ ((1:ℝ)/4) := hgrowth
      _ ≤ 16 * (2 * T) ^ ((1:ℝ)/4) := by
          apply mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg _) hzimT (by norm_num))
            (by norm_num)
      _ = 16 * ((2:ℝ) ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/4)) := by
          rw [Real.mul_rpow (by norm_num) hTpos.le]
      _ ≤ 16 * (2 * T ^ ((1:ℝ)/4)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _
            (Real.rpow_nonneg hTpos.le _)
          calc (2:ℝ) ^ ((1:ℝ)/4) ≤ 2 ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
      _ = 32 * T ^ ((1:ℝ)/4) := by ring
  have hM1 : (1:ℝ) ≤ 32 * T ^ ((1:ℝ)/4) := by nlinarith
  -- Jensen's inequality, movable center
  have hjensen := AnalyticOnNhd.sum_divisor_le
    (c := c) (r := 1/8) (R := 1/4) (M := 32 * T ^ ((1:ℝ)/4))
    (f := riemannZeta) (by norm_num) (by norm_num) hM1 hanal hζc hbound
  have habs18 : |(1/8 : ℝ)| = 1/8 := by norm_num
  rw [habs18] at hjensen
  refine le_trans hjensen ?_
  -- The right-hand side: log(M/‖ζ(c)‖)/log 2 ≤ 0.73·L
  have hfloor : 1 / (L + 1) ≤ ‖riemannZeta c‖ := by
    have h := zeta_center_floor hcre1
    have : (c.re - 1) / c.re = 1 / (L + 1) := by
      rw [hcre]
      field_simp
      ring
    rwa [this] at h
  have hζcpos : (0:ℝ) < ‖riemannZeta c‖ :=
    lt_of_lt_of_le (by positivity) hfloor
  have hquot : 32 * T ^ ((1:ℝ)/4) / ‖riemannZeta c‖
      ≤ 32 * T ^ ((1:ℝ)/4) * (L + 1) := by
    rw [div_le_iff₀ hζcpos]
    calc 32 * T ^ ((1:ℝ)/4)
        = 32 * T ^ ((1:ℝ)/4) * (L + 1) * (1 / (L + 1)) := by
          field_simp
      _ ≤ 32 * T ^ ((1:ℝ)/4) * (L + 1) * ‖riemannZeta c‖ := by
          apply mul_le_mul_of_nonneg_left hfloor
          positivity
  have hRr : Real.log ((1/4 : ℝ) / (1/8 : ℝ)) = Real.log 2 := by
    norm_num
  rw [hRr]
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ hlog2pos]
  -- Numerator: log(M/‖ζc‖) ≤ log(32·T^{1/4}·(L+1)) ≤ L/2
  have hnum : Real.log (32 * T ^ ((1:ℝ)/4) / ‖riemannZeta c‖) ≤ L / 2 := by
    have hstep1 : Real.log (32 * T ^ ((1:ℝ)/4) / ‖riemannZeta c‖)
        ≤ Real.log (32 * T ^ ((1:ℝ)/4) * (L + 1)) := by
      apply Real.log_le_log (by positivity) hquot
    exact hstep1.trans (logMm_le_half hT)
  calc Real.log (32 * T ^ ((1:ℝ)/4) / ‖riemannZeta c‖)
      ≤ L / 2 := hnum
    _ ≤ 0.73 * L * Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]

/-! ## The partial-fraction inequality at `L ≥ 32` -/

set_option maxHeartbeats 3200000 in
/-- The partial-fraction inequality for `ζ` at the movable center, `L ≥ 32`: for every `s` within `1/32` of
`c = 1 + 1/log T + iT` where `ζ(s) ≠ 0`, `‖ζ'/ζ(s) − Σ_ρ m_ρ/(s−ρ)‖ ≤ 40·log T`, the sum over the divisor of
`B(c, 1/8)`, with certificates that the `ρ` are genuine zeros and that every zero of the ball is seated. -/
theorem zeta_partial_fraction_sharp {T : ℝ} (hT : Real.exp 32 ≤ T) :
    ∃ (S : Finset ℂ) (n : ℂ → ℕ),
      (∀ u ∈ S, u ∈ Metric.closedBall
        (((1 + 1 / Real.log T : ℝ) : ℂ) + T * Complex.I) (1/8)) ∧
      (∀ u ∈ S, 1 ≤ n u → riemannZeta u = 0) ∧
      (∀ u ∈ Metric.closedBall
        (((1 + 1 / Real.log T : ℝ) : ℂ) + T * Complex.I) (1/8),
        riemannZeta u = 0 → u ∈ S ∧ 1 ≤ n u) ∧
      ∀ s ∈ Metric.closedBall
          (((1 + 1 / Real.log T : ℝ) : ℂ) + T * Complex.I) (1/32),
        riemannZeta s ≠ 0 →
        ‖logDeriv riemannZeta s - ∑ u ∈ S, (n u : ℂ) / (s - u)‖
          ≤ 40 * Real.log T := by
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 32) hT
  have hL32 : (32:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 32) hT
    rwa [Real.log_exp] at this
  have hT7 : (7:ℝ) ≤ T := by
    have h2 : Real.exp 2 ≤ T := le_trans (Real.exp_le_exp.mpr (by norm_num)) hT
    have h2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_one_gt_d9]
  set L : ℝ := Real.log T with hLdef
  have hLpos : (0:ℝ) < L := by linarith
  set c : ℂ := ((1 + 1 / L : ℝ) : ℂ) + T * Complex.I with hcdef
  have hcre : c.re = 1 + 1 / L := by
    rw [hcdef]
    simp
  have hcim : c.im = T := by
    rw [hcdef]
    simp
  have hinvL : (0:ℝ) < 1 / L := by positivity
  have hinvL2 : 1 / L ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le
    · norm_num
    · linarith
  have hT14ge1 : (1:ℝ) ≤ T ^ ((1:ℝ)/4) := by
    calc (1:ℝ) = 1 ^ ((1:ℝ)/4) := (Real.one_rpow _).symm
      _ ≤ T ^ ((1:ℝ)/4) := Real.rpow_le_rpow (by norm_num) (by linarith)
        (by norm_num)
  -- analyticity on the 1/8-ball
  have hanal : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c (1/8)) := by
    apply AnalyticOnNhd.mono
      (DifferentiableOn.analyticOnNhd
        (f := riemannZeta) (s := {z : ℂ | z ≠ 1})
        (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
        isOpen_ne)
    intro z hz
    simp only [Metric.mem_closedBall] at hz
    intro h1
    rw [h1, dist_eq_norm] at hz
    have him : |((1:ℂ) - c).im| ≤ ‖(1:ℂ) - c‖ := Complex.abs_im_le_norm _
    have : ((1:ℂ) - c).im = -T := by
      simp [Complex.sub_im, hcim]
    rw [this, abs_neg, abs_of_pos hTpos] at him
    linarith
  -- the M-bound on the 1/8-ball
  have hM : ∀ z ∈ Metric.closedBall c (1/8),
      ‖riemannZeta z‖ ≤ 32 * T ^ ((1:ℝ)/4) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre : |(z - c).re| ≤ 1/8 := le_trans (Complex.abs_re_le_norm _) hz
    have him : |(z - c).im| ≤ 1/8 := le_trans (Complex.abs_im_le_norm _) hz
    rw [Complex.sub_re, hcre] at hre
    rw [Complex.sub_im, hcim] at him
    rw [abs_le] at hre him
    have hzim2 : (2:ℝ) ≤ |z.im| := by
      rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
      linarith
    have hgrowth := zeta_polynomial_growth hzim2 (by linarith) (by linarith)
    have hzimT : |z.im| ≤ 2 * T := by
      rw [abs_of_pos (by linarith : (0:ℝ) < z.im)]
      linarith
    calc ‖riemannZeta z‖ ≤ 16 * |z.im| ^ ((1:ℝ)/4) := hgrowth
      _ ≤ 16 * (2 * T) ^ ((1:ℝ)/4) := by
          apply mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg _) hzimT (by norm_num))
            (by norm_num)
      _ = 16 * ((2:ℝ) ^ ((1:ℝ)/4) * T ^ ((1:ℝ)/4)) := by
          rw [Real.mul_rpow (by norm_num) hTpos.le]
      _ ≤ 16 * (2 * T ^ ((1:ℝ)/4)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _
            (Real.rpow_nonneg hTpos.le _)
          calc (2:ℝ) ^ ((1:ℝ)/4) ≤ 2 ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
      _ = 32 * T ^ ((1:ℝ)/4) := by ring
  -- the center floor
  have hcre1 : (1:ℝ) < c.re := by
    rw [hcre]
    linarith
  have hfloor : 1 / (L + 1) ≤ ‖riemannZeta c‖ := by
    have h := zeta_center_floor hcre1
    have heq : (c.re - 1) / c.re = 1 / (L + 1) := by
      rw [hcre]
      field_simp
      ring
    rwa [heq] at h
  have hmpos : (0:ℝ) < 1 / (L + 1) := by positivity
  -- log(M/m) bounds
  have hMm : 32 * T ^ ((1:ℝ)/4) / (1 / (L + 1))
      = 32 * T ^ ((1:ℝ)/4) * (L + 1) := by
    field_simp
  have hlogpos : 0 < Real.log (32 * T ^ ((1:ℝ)/4) / (1 / (L + 1))) := by
    rw [hMm]
    apply Real.log_pos
    nlinarith
  have hlogHalf : Real.log (32 * T ^ ((1:ℝ)/4) / (1 / (L + 1))) ≤ L / 2 := by
    rw [hMm]
    exact logMm_le_half hT
  -- Landau's lemma at (c, 1/8)
  obtain ⟨S, n, hS_mem, hn_eq, hd_zero, hbound⟩ :=
    landau_lemma (c := c) (r := 1/8) (by norm_num) hmpos hanal hM hfloor
      hlogpos
  refine ⟨S, n, hS_mem, ?_, ?_, ?_⟩
  · -- zero certificates
    intro u hu hnu
    by_contra hζu
    have hord : analyticOrderAt riemannZeta u = 0 :=
      (hanal u (hS_mem u hu)).analyticOrderAt_eq_zero.mpr hζu
    have hdiv := hn_eq u hu
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanal (hS_mem u hu),
      hord] at hdiv
    simp at hdiv
    omega
  · -- completeness: every zero in the ball is seated in S with n ≥ 1
    intro u hu hζu
    have hζc : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hcre1
    have hordne : analyticOrderAt riemannZeta u ≠ 0 := by
      rw [analyticOrderAt_ne_zero]
      exact ⟨hanal u hu, hζu⟩
    have hordtop : analyticOrderAt riemannZeta u ≠ ⊤ :=
      analyticOrderAt_ne_top_of_ne_zero
        (convex_closedBall c (1/8)).isPreconnected hanal
        (Metric.mem_closedBall_self (by norm_num)) hζc hu
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℕ∞) = analyticOrderAt riemannZeta u :=
      ENat.ne_top_iff_exists.mp hordtop
    have hm_ne : m ≠ 0 := fun h => hordne (by rw [← hm, h]; rfl)
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm_ne
    have hdivge : 1 ≤ MeromorphicOn.divisor riemannZeta
        (Metric.closedBall c (1/8)) u := by
      rw [MeromorphicOn.divisor_apply hanal.meromorphicOn hu,
        (hanal u hu).meromorphicOrderAt_eq, ← hm]
      simp
      exact hm1
    have huS : u ∈ S := by
      by_contra huS
      have := hd_zero u huS
      omega
    refine ⟨huS, ?_⟩
    have := hn_eq u huS
    omega
  · intro s hs hζs
    have hs32 : s ∈ Metric.closedBall c ((1/8)/4) := by
      have := Metric.mem_closedBall.mp hs
      rw [Metric.mem_closedBall]
      linarith
    have hb := hbound s hs32 hζs
    -- N ≤ 0.73·L via the sharp local count
    have hNle : (∑ u ∈ S, (n u : ℝ)) ≤ 0.73 * L := by
      have hsupp : Function.support
          (fun u => MeromorphicOn.divisor riemannZeta
            (Metric.closedBall c (1/8)) u) ⊆ (S : Set ℂ) := by
        intro u hu
        by_contra huS
        exact hu (hd_zero u huS)
      have hfin : (∑ᶠ u, MeromorphicOn.divisor riemannZeta
          (Metric.closedBall c (1/8)) u)
          = ∑ u ∈ S, MeromorphicOn.divisor riemannZeta
              (Metric.closedBall c (1/8)) u :=
        finsum_eq_sum_of_support_subset _ hsupp
      have hcast : (∑ u ∈ S, (n u : ℝ))
          = ((∑ᶠ u, MeromorphicOn.divisor riemannZeta
              (Metric.closedBall c (1/8)) u : ℤ) : ℝ) := by
        rw [hfin]
        push_cast
        apply Finset.sum_congr rfl
        intro u hu
        exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) (hn_eq u hu)
      rw [hcast]
      exact zeta_local_zero_count_sharp hT
    -- assemble the constants
    calc ‖logDeriv riemannZeta s - ∑ u ∈ S, (n u : ℂ) / (s - u)‖
        ≤ 8 * Real.log (32 * T ^ ((1:ℝ)/4) / (1 / (L + 1))) / (1/8)
          + (∑ u ∈ S, (n u : ℝ)) * (4 / (3 * (1/8))) := hb
      _ ≤ 8 * (L / 2) / (1/8) + (0.73 * L) * (4 / (3 * (1/8))) := by
          apply add_le_add
          · apply div_le_div_of_nonneg_right _ (by norm_num)
            apply mul_le_mul_of_nonneg_left hlogHalf (by norm_num)
          · apply mul_le_mul_of_nonneg_right hNle (by norm_num)
      _ ≤ 40 * L := by linarith

/-! ## The exponent-one region with `c₀ = 1/3000` -/

set_option maxHeartbeats 3200000 in
/-- The positive-ordinate case of the sharpened exponent-1 region. -/
theorem zero_free_region_exponent_one_sharp_aux {ρ : ℂ}
    (hζρ : riemannZeta ρ = 0) (hT32 : Real.exp 32 ≤ ρ.im) :
    ρ.re ≤ 1 - (1/3000) / Real.log ρ.im := by
  set T : ℝ := ρ.im with hTdef
  set β : ℝ := ρ.re with hβdef
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 32) hT32
  have hL32 : (32:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 32) hT32
    rwa [Real.log_exp] at this
  set L : ℝ := Real.log T with hLdef
  have hLpos : (0:ℝ) < L := by linarith
  -- β < 1
  have hβ1 : β < 1 := by
    by_contra hc
    push_neg at hc
    exact riemannZeta_ne_zero_of_one_le_re (by rw [← hβdef]; exact hc) hζρ
  -- trivial branch: β far from 1
  by_cases hβtriv : β ≤ 1 - 3/32
  · have hc0 : (1/3000 : ℝ) / L ≤ 3/32 := by
      have h1 : (1/3000 : ℝ) / L ≤ (1/3000 : ℝ) / 32 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL32
      calc (1/3000 : ℝ) / L ≤ (1/3000 : ℝ) / 32 := h1
        _ ≤ 3/32 := by norm_num
    linarith
  push_neg at hβtriv
  -- the anchor
  set σ : ℝ := 1 + 1/(400*L) with hσdef
  have hinv : (0:ℝ) < 1/(400*L) := by positivity
  have hσ1 : 1 < σ := by
    rw [hσdef]
    linarith
  have hσ98 : σ ≤ 9/8 := by
    rw [hσdef]
    have : (1:ℝ)/(400*L) ≤ 1/8 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    linarith
  -- (B) the sharp σ-rung
  have hΦ0 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re
      ≤ 400*L + 3 := by
    rw [vonMangoldt_re_eq_neg_logDeriv (by simp; linarith)]
    have h1 := zeta_logDeriv_rung_sharp hσ1 hσ98
    have h2 : -(logDeriv riemannZeta ((σ:ℝ):ℂ)).re
        ≤ ‖logDeriv riemannZeta ((σ:ℝ):ℂ)‖ := by
      have := Complex.abs_re_le_norm (logDeriv riemannZeta ((σ:ℝ):ℂ))
      have := neg_abs_le (logDeriv riemannZeta ((σ:ℝ):ℂ)).re
      linarith
    have h3 : 1/(σ-1) = 400*L := by
      rw [hσdef, show (1 + 1/(400*L) - 1) = 1/(400*L) by ring,
        one_div_one_div]
    linarith
  -- (C) the s₁ bound with the seated zero
  obtain ⟨S, n, hS_mem, hcert, hcomp, hbound⟩ := zeta_partial_fraction_sharp hT32
  set c : ℂ := ((1 + 1 / Real.log T : ℝ) : ℂ) + T * Complex.I with hcdef
  set s₁ : ℂ := ((σ:ℝ):ℂ) + ((T:ℝ):ℂ) * Complex.I with hs₁def
  have hs₁re : s₁.re = σ := by
    rw [hs₁def]
    simp
  have hs₁im : s₁.im = T := by
    rw [hs₁def]
    simp
  have hζs₁ : riemannZeta s₁ ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hs₁re]; exact hσ1)
  have hs₁c : s₁ - c = (((σ - (1 + 1/L) : ℝ)):ℂ) := by
    rw [hs₁def, hcdef, hLdef]
    push_cast
    ring
  have hs₁mem : s₁ ∈ Metric.closedBall c (1/32) := by
    rw [Metric.mem_closedBall, dist_eq_norm, hs₁c, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · rw [hσdef]
      have h1 : (1:ℝ)/L ≤ 1/32 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL32
      have h2 : (0:ℝ) < 1/(400*L) := hinv
      nlinarith
    · rw [hσdef]
      have h2 : (0:ℝ) < 1/L := by positivity
      have h3 : (1:ℝ)/(400*L) ≤ 1/32 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        nlinarith
      nlinarith
  have hb₁ := hbound s₁ hs₁mem hζs₁
  -- the zero is seated
  have hρc : ρ - c = (((β - (1 + 1/L) : ℝ)):ℂ) := by
    rw [hcdef, hLdef]
    apply Complex.ext
    · simp [hβdef]
    · simp [hTdef]
  have hρmem : ρ ∈ Metric.closedBall c (1/8) := by
    rw [Metric.mem_closedBall, dist_eq_norm, hρc, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · have h1 : (1:ℝ)/L ≤ 1/32 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL32
      nlinarith
    · have h2 : (0:ℝ) < 1/L := by positivity
      nlinarith
  obtain ⟨hρS, hnρ⟩ := hcomp ρ hρmem hζρ
  -- terms of the partial-fraction sum are nonneg; the ρ-term dominates
  have hure : ∀ u ∈ S, 1 ≤ n u → u.re < 1 := by
    intro u hu hnu
    by_contra hc
    push_neg at hc
    exact riemannZeta_ne_zero_of_one_le_re hc (hcert u hu hnu)
  have hterm_nonneg : ∀ u ∈ S,
      0 ≤ ((n u : ℂ) / (s₁ - u)).re := by
    intro u hu
    rcases Nat.eq_zero_or_pos (n u) with h0 | hpos
    · rw [h0]
      simp
    · have hlt := hure u hu hpos
      rw [pf_term_re]
      apply mul_nonneg (Nat.cast_nonneg _)
      apply div_nonneg _ (Complex.normSq_nonneg _)
      rw [Complex.sub_re, hs₁re]
      linarith
  have hρ_term : 1/(σ - β) ≤ ((n ρ : ℂ) / (s₁ - ρ)).re := by
    have hs₁ρ : s₁ - ρ = (((σ - β : ℝ)):ℂ) := by
      apply Complex.ext
      · simp [hs₁re, hβdef]
      · simp [hs₁im, hTdef]
    rw [pf_term_re, hs₁ρ]
    rw [Complex.normSq_ofReal, Complex.ofReal_re]
    have hσβ : (0:ℝ) < σ - β := by linarith
    have hval : (σ - β) / ((σ - β) * (σ - β)) = 1/(σ - β) := by
      field_simp
    rw [hval]
    have h1n : (1:ℝ) ≤ (n ρ : ℝ) := by exact_mod_cast hnρ
    nlinarith [one_div_pos.mpr hσβ]
  have hsum_ge : 1/(σ - β) ≤ (∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re := by
    rw [Complex.re_sum]
    calc 1/(σ - β) ≤ ((n ρ : ℂ) / (s₁ - ρ)).re := hρ_term
      _ ≤ ∑ u ∈ S, ((n u : ℂ) / (s₁ - u)).re :=
          Finset.single_le_sum hterm_nonneg hρS
  have hΦ1 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₁).re
      ≤ -(1/(σ - β)) + 40*L := by
    have hbr := vonMangoldt_re_eq_neg_logDeriv
      (s := s₁) (by rw [hs₁re]; exact hσ1)
    rw [hbr]
    have hsplit : -(logDeriv riemannZeta s₁).re
        = -((logDeriv riemannZeta s₁
            - ∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re)
          - (∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re := by
      rw [Complex.sub_re]
      ring
    rw [hsplit]
    have h1 : -((logDeriv riemannZeta s₁
        - ∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re) ≤ 40*L := by
      have habs := Complex.abs_re_le_norm (logDeriv riemannZeta s₁
        - ∑ u ∈ S, (n u : ℂ) / (s₁ - u))
      have hneg := neg_abs_le (logDeriv riemannZeta s₁
        - ∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re
      rw [hLdef]
      linarith
    linarith [hsum_ge]
  -- (D) the 2T bound
  have hexp32T2 : Real.exp 32 ≤ 2*T := by linarith
  obtain ⟨S₂, n₂, hS₂_mem, hcert₂, _, hbound₂⟩ :=
    zeta_partial_fraction_sharp hexp32T2
  set c₂ : ℂ := ((1 + 1 / Real.log (2*T) : ℝ) : ℂ)
      + ((2*T : ℝ) : ℂ) * Complex.I
    with hc₂def
  set s₂ : ℂ := ((σ:ℝ):ℂ) + ((2*T:ℝ):ℂ) * Complex.I with hs₂def
  have hL₂ : L ≤ Real.log (2*T) := by
    rw [hLdef]
    apply Real.log_le_log hTpos
    linarith
  have hL₂pos : (0:ℝ) < Real.log (2*T) := by linarith
  have hs₂re : s₂.re = σ := by
    rw [hs₂def]
    simp
  have hζs₂ : riemannZeta s₂ ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hs₂re]; exact hσ1)
  have hs₂mem : s₂ ∈ Metric.closedBall c₂ (1/32) := by
    have hs₂c : s₂ - c₂ = (((σ - (1 + 1/Real.log (2*T)) : ℝ)):ℂ) := by
      rw [hs₂def, hc₂def]
      push_cast
      ring
    rw [Metric.mem_closedBall, dist_eq_norm, hs₂c, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_le]
    have hinv₂ : (0:ℝ) < 1/Real.log (2*T) := by positivity
    have hinv₂32 : (1:ℝ)/Real.log (2*T) ≤ 1/32 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    constructor
    · rw [hσdef]
      have h2 : (0:ℝ) < 1/(400*L) := hinv
      nlinarith
    · rw [hσdef]
      have h3 : (1:ℝ)/(400*L) ≤ 1/32 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        nlinarith
      nlinarith
  have hb₂ := hbound₂ s₂ hs₂mem hζs₂
  have hure₂ : ∀ u ∈ S₂, 1 ≤ n₂ u → u.re < 1 := by
    intro u hu hnu
    by_contra hc
    push_neg at hc
    exact riemannZeta_ne_zero_of_one_le_re hc (hcert₂ u hu hnu)
  have hterm₂_nonneg : ∀ u ∈ S₂,
      0 ≤ ((n₂ u : ℂ) / (s₂ - u)).re := by
    intro u hu
    rcases Nat.eq_zero_or_pos (n₂ u) with h0 | hpos
    · rw [h0]
      simp
    · have hlt := hure₂ u hu hpos
      rw [pf_term_re]
      apply mul_nonneg (Nat.cast_nonneg _)
      apply div_nonneg _ (Complex.normSq_nonneg _)
      rw [Complex.sub_re, hs₂re]
      linarith
  have hΦ2 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₂).re
      ≤ 41*L := by
    have hbr := vonMangoldt_re_eq_neg_logDeriv
      (s := s₂) (by rw [hs₂re]; exact hσ1)
    rw [hbr]
    have hsplit : -(logDeriv riemannZeta s₂).re
        = -((logDeriv riemannZeta s₂
            - ∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re)
          - (∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re := by
      rw [Complex.sub_re]
      ring
    rw [hsplit]
    have h1 : -((logDeriv riemannZeta s₂
        - ∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re)
        ≤ 40 * Real.log (2*T) := by
      have habs := Complex.abs_re_le_norm (logDeriv riemannZeta s₂
        - ∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u))
      have hneg := neg_abs_le (logDeriv riemannZeta s₂
        - ∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re
      linarith
    have h2 : (0:ℝ) ≤ (∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re := by
      rw [Complex.re_sum]
      exact Finset.sum_nonneg hterm₂_nonneg
    have h3 : Real.log (2*T) = Real.log 2 + L := by
      rw [hLdef, Real.log_mul (by norm_num) hTpos.ne']
    have h4 : Real.log 2 ≤ 0.7 := by
      nlinarith [Real.log_two_lt_d9]
    have h5 : 40 * Real.log (2*T) ≤ 41*L := by
      rw [h3]
      nlinarith
    linarith
  -- (E) the 3-4-1 assembly
  have h341 := three_four_one (σ := σ) (t := T) hσ1
  have hkey : 4/(σ - β) ≤ 1402*L := by
    have hσβ : (0:ℝ) < σ - β := by linarith
    have hc1 : 0 ≤ 3 * (400*L + 3)
        + 4 * (-(1/(σ - β)) + 40*L) + 41*L := by
      calc (0:ℝ) ≤ 3 * (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re
          + 4 * (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₁).re
          + (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₂).re := h341
        _ ≤ 3 * (400*L + 3)
            + 4 * (-(1/(σ - β)) + 40*L) + 41*L := by
            have := hΦ0
            have := hΦ1
            have := hΦ2
            linarith
    have h9L : (9:ℝ) ≤ L := by linarith
    have h4d : 4/(σ - β) = 4*(1/(σ - β)) := by ring
    rw [h4d]
    linarith
  -- extract β
  have hσβ : (0:ℝ) < σ - β := by linarith
  have hx : 4/(1402*L) ≤ σ - β := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 1402*L)]
    rw [div_le_iff₀ hσβ] at hkey
    nlinarith [hkey]
  have hfinal : β ≤ 1 - (1/3000)/L := by
    have hnum : (1:ℝ)/400 + 1/3000 ≤ 4/1402 := by norm_num
    have hkey2 : 1/(400*L) + (1/3000)/L ≤ 4/(1402*L) := by
      have e1 : (1:ℝ)/(400*L) = (1/400)/L := (div_div 1 400 L).symm
      have e2 : (4:ℝ)/(1402*L) = (4/1402)/L := (div_div 4 1402 L).symm
      rw [e1, e2, ← add_div]
      exact div_le_div_of_nonneg_right hnum hLpos.le
    rw [hσdef] at hx
    linarith
  rw [← hLdef, ← hβdef] at *
  exact hfinal

/-- **The exponent-1 zero-free region with the explicit constant `1/3000`.** Every zero `ρ = β + iγ` of `ζ`
with `|γ| ≥ e³²` satisfies `β ≤ 1 − (1/3000)/log|γ|`. -/
theorem zero_free_region_exponent_one_sharp' :
    ∀ ρ : ℂ, riemannZeta ρ = 0 →
      Real.exp 32 ≤ |ρ.im| → ρ.re ≤ 1 - (1/3000) / Real.log |ρ.im| := by
  intro ρ hζρ him
  rcases abs_cases ρ.im with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq] at him ⊢
    exact zero_free_region_exponent_one_sharp_aux hζρ him
  · have hζρ' : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
      rw [riemannZeta_conj, hζρ, map_zero]
    have hconj_im : ((starRingEnd ℂ) ρ).im = -ρ.im := Complex.conj_im ρ
    have him' : Real.exp 32 ≤ ((starRingEnd ℂ) ρ).im := by
      rw [hconj_im]
      rw [heq] at him
      linarith
    have haux := zero_free_region_exponent_one_sharp_aux hζρ' him'
    rw [Complex.conj_re, hconj_im] at haux
    rw [heq]
    exact haux

/-- **The exponent-1 zero-free region with `c₀ = 1/3000`**, in the form of the compiled
`zero_free_region_exponent_one` (constant `1/50000`): the two loose bounds sharpened in the theorem's own regime
and the anchor re-optimised. -/
theorem zero_free_region_exponent_one_sharp :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      Real.exp 32 ≤ |ρ.im| → ρ.re ≤ 1 - c₀ / Real.log |ρ.im| :=
  ⟨1/3000, by norm_num, zero_free_region_exponent_one_sharp'⟩

/-- The sharpened region implies the compiled one: a strictly stronger conclusion, same hypotheses. -/
theorem zero_free_region_exponent_one_sharp_implies_old :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → Real.exp 32 ≤ |ρ.im| →
      ρ.re ≤ 1 - (1/50000) / Real.log |ρ.im| := by
  intro ρ hζρ him
  have hL32 : (32:ℝ) ≤ Real.log |ρ.im| := by
    have := Real.log_le_log (Real.exp_pos 32) him
    rwa [Real.log_exp] at this
  have hLpos : (0:ℝ) < Real.log |ρ.im| := by linarith
  have hsharp := zero_free_region_exponent_one_sharp' ρ hζρ him
  have hmono : (1/50000 : ℝ) / Real.log |ρ.im| ≤ (1/3000) / Real.log |ρ.im| :=
    div_le_div_of_nonneg_right (by norm_num) hLpos.le
  linarith

end CriticalLinePhasor.DVP

end

#print axioms CriticalLinePhasor.DVP.logMm_le_half
#print axioms CriticalLinePhasor.DVP.zeta_local_zero_count_sharp
#print axioms CriticalLinePhasor.DVP.zeta_partial_fraction_sharp
#print axioms CriticalLinePhasor.DVP.zero_free_region_exponent_one_sharp
