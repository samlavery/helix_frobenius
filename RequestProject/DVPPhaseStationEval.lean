import RequestProject.DVPPhaseStation

/-!
# The evaluated-boundary station core

For thin stations (narrow Gram windows), the magnitude bound `√N/M` on
the Euler–Maclaurin boundary term wastes the whole margin.  Here the
boundary is kept EXACT: with `s = ½ + Mi`,

`Re(e^{iψ}·N^{1−s}/(s−1)) = √N·(−cos α/2 − M·sin α)/(¼ + M²)`,
`α := M·log N − ψ`,

so ONE certified cosine/sine pair at `n = N` replaces the magnitude
loss.  `sinMulShift_eval` is the matching sine evaluator.
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The shifted sine evaluator**: `|sin(M·L − ψ) − u| ≤ ε`. -/
theorem sinMulShift_eval {L : ℝ} {lo hi r δ ψ u ε : ℚ} (M k : ℕ)
    (hlo : ((lo : ℚ) : ℝ) ≤ L) (hhi : L ≤ ((hi : ℚ) : ℝ))
    (hr : |r| ≤ 1)
    (ha1 : M * hi - ψ - k * (628318530717958647692/10^20 : ℚ) - 4 * r ≤ δ)
    (ha2 : -δ ≤ M * lo - ψ - k * (628318530717958647694/10^20 : ℚ) - 4 * r)
    (hs2 : |sinTaylor r 5| ≤ 2)
    (hε : δ + 72 * (|r| ^ 10 * (11/36288000) + |r| ^ 10 * (11/36288000))
        + |u - (4 * sinTaylor r 5 * cosTaylor r 5
            * (1 - 2 * (sinTaylor r 5) ^ 2))| ≤ ε) :
    |Real.sin ((M:ℝ) * L - ((ψ : ℚ) : ℝ)) - ((u : ℚ) : ℝ)|
      ≤ ((ε : ℚ) : ℝ) := by
  have hθ := angle_window_shift M k hlo hhi ha1 ha2
  have hsin := sin_enclosure (x := r) hr (n := 5) (by norm_num)
  have hbrs : |((r : ℚ) : ℝ)| ^ (2 * 5)
      * (((2 * 5).succ : ℝ) * (((2 * 5).factorial : ℝ) * ((2 * 5 : ℕ) : ℝ))⁻¹)
      ≤ ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]
    push_cast
    norm_num [Nat.factorial]
  have hŝ := le_trans hsin hbrs
  have hcos := cos_enclosure (x := r) hr (n := 5) (by norm_num)
  have hbrc : |((r : ℚ) : ℝ)| ^ (2 * 5)
      * (((2 * 5).succ : ℝ) * (((2 * 5).factorial : ℝ) * ((2 * 5 : ℕ) : ℝ))⁻¹)
      ≤ ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]
    push_cast
    norm_num [Nat.factorial]
  have hĉ := le_trans hcos hbrc
  have hs2' : |((sinTaylor r 5 : ℚ) : ℝ)| ≤ 2 := by
    rw [← Rat.cast_abs]
    exact_mod_cast hs2
  have hmain := sin_angle_eval (θ := (M:ℝ) * L - ((ψ : ℚ) : ℝ)) (r := r)
    (ŝ := sinTaylor r 5) (ĉ := cosTaylor r 5) (δ := δ)
    (τs := |r| ^ 10 * (11/36288000)) (τc := |r| ^ 10 * (11/36288000))
    ((k : ℕ) : ℤ) hθ hŝ hĉ hs2'
  have hvF : |((u : ℚ) : ℝ)
      - ((4 * sinTaylor r 5 * cosTaylor r 5
          * (1 - 2 * (sinTaylor r 5) ^ 2) : ℚ) : ℝ)|
      = ((|u - (4 * sinTaylor r 5 * cosTaylor r 5
          * (1 - 2 * (sinTaylor r 5) ^ 2))| : ℚ) : ℝ) := by
    rw [← Rat.cast_sub, ← Rat.cast_abs]
  calc |Real.sin ((M:ℝ) * L - ((ψ : ℚ) : ℝ)) - ((u : ℚ) : ℝ)|
      ≤ |Real.sin ((M:ℝ) * L - ((ψ : ℚ) : ℝ))
          - ((4 * sinTaylor r 5 * cosTaylor r 5
            * (1 - 2 * (sinTaylor r 5) ^ 2) : ℚ) : ℝ)|
        + |((4 * sinTaylor r 5 * cosTaylor r 5
            * (1 - 2 * (sinTaylor r 5) ^ 2) : ℚ) : ℝ)
          - ((u : ℚ) : ℝ)| := by
        calc |Real.sin ((M:ℝ) * L - ((ψ : ℚ) : ℝ)) - ((u : ℚ) : ℝ)|
            = |(Real.sin ((M:ℝ) * L - ((ψ : ℚ) : ℝ))
                - ((4 * sinTaylor r 5 * cosTaylor r 5
                  * (1 - 2 * (sinTaylor r 5) ^ 2) : ℚ) : ℝ))
              + (((4 * sinTaylor r 5 * cosTaylor r 5
                  * (1 - 2 * (sinTaylor r 5) ^ 2) : ℚ) : ℝ)
                - ((u : ℚ) : ℝ))| := by ring_nf
          _ ≤ _ := abs_add_le _ _
    _ ≤ (((δ : ℚ) : ℝ)
          + 72 * (((|r| ^ 10 * (11/36288000) : ℚ) : ℝ)
            + ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ)))
        + ((|u - (4 * sinTaylor r 5 * cosTaylor r 5
            * (1 - 2 * (sinTaylor r 5) ^ 2))| : ℚ) : ℝ) := by
        refine add_le_add ?_ ?_
        · first
          | exact hmain
          | (convert hmain using 2)
        · rw [abs_sub_comm, hvF]
    _ ≤ ((ε : ℚ) : ℝ) := by
        rw [show (((δ : ℚ) : ℝ)
              + 72 * (((|r| ^ 10 * (11/36288000) : ℚ) : ℝ)
                + ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ)))
            + ((|u - (4 * sinTaylor r 5 * cosTaylor r 5
                * (1 - 2 * (sinTaylor r 5) ^ 2))| : ℚ) : ℝ)
            = ((δ + 72 * (|r| ^ 10 * (11/36288000) + |r| ^ 10 * (11/36288000))
              + |u - (4 * sinTaylor r 5 * cosTaylor r 5
                * (1 - 2 * (sinTaylor r 5) ^ 2))| : ℚ) : ℝ) by
          push_cast; ring]
        exact_mod_cast hε

/-- **The exact boundary real part** at `s = ½ + Mi`. -/
theorem boundary_re_eval (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N) (ψ : ℝ) :
    (Complex.exp ((ψ : ℝ) * Complex.I)
        * ((((N : ℕ) : ℝ) : ℂ) ^ (1 - (↑(1/2 : ℝ) + ↑((M:ℕ) : ℝ) * Complex.I))
          / ((↑(1/2 : ℝ) + ↑((M:ℕ) : ℝ) * Complex.I) - 1))).re
      = (N:ℝ) ^ ((1/2 : ℝ))
        * (-(Real.cos ((M:ℝ) * Real.log N - ψ)) / 2
          - (M:ℝ) * Real.sin ((M:ℝ) * Real.log N - ψ))
        / ((1/4 : ℝ) + (M:ℝ) ^ 2) := by
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  set α : ℝ := (M:ℝ) * Real.log N with hα
  have hcpow : (((N : ℕ) : ℝ) : ℂ) ^ (1 - (↑(1/2 : ℝ) + ↑((M:ℕ) : ℝ) * Complex.I))
      = (((N:ℝ) ^ ((1/2 : ℝ)) : ℝ) : ℂ)
        * Complex.exp (((-α : ℝ)) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero (by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity)]
    rw [← Complex.ofReal_log hN0.le]
    rw [show ((Real.log (N:ℝ) : ℝ) : ℂ)
          * (1 - (↑(1/2 : ℝ) + ↑((M:ℕ) : ℝ) * Complex.I))
        = ((Real.log (N:ℝ) / 2 : ℝ) : ℂ) + ((-α : ℝ) : ℂ) * Complex.I by
      rw [hα]
      push_cast
      ring]
    rw [Complex.exp_add]
    congr 1
    rw [← Complex.ofReal_exp]
    norm_cast
    rw [Real.rpow_def_of_pos hN0]
    ring_nf
  rw [hcpow]
  have hform : Complex.exp ((ψ : ℝ) * Complex.I)
      * ((((N:ℝ) ^ ((1/2 : ℝ)) : ℝ) : ℂ)
          * Complex.exp (((-α : ℝ)) * Complex.I)
        / ((↑(1/2 : ℝ) + ↑((M:ℕ) : ℝ) * Complex.I) - 1))
      = (((N:ℝ) ^ ((1/2 : ℝ)) : ℝ) : ℂ)
        * (Complex.exp ((((ψ - α : ℝ))) * Complex.I)
          * ((((-(1/2) : ℝ)) : ℂ) + ((M:ℝ) : ℂ) * Complex.I)⁻¹) := by
    rw [div_eq_mul_inv,
      show ((((ψ - α : ℝ))) : ℂ) * Complex.I
        = ((ψ : ℝ) : ℂ) * Complex.I + ((-α : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
      Complex.exp_add,
      show ((↑(1/2 : ℝ) + ↑((M:ℕ) : ℝ) * Complex.I) - 1)
        = (((-(1/2) : ℝ)) : ℂ) + ((M:ℝ) : ℂ) * Complex.I by push_cast; ring]
    ring
  rw [hform]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.inv_re, Complex.inv_im]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.normSq_apply, mul_zero, mul_one, zero_mul,
    sub_zero, zero_add, zero_sub]
  rw [show ψ - α = -(α - ψ) by ring, Real.cos_neg, Real.sin_neg]
  have hD0 : (-(1/2) : ℝ) * -(1/2) + (M:ℝ) * (M:ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **The evaluated-boundary station lower bound.** -/
theorem phase_station_lower_eval (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (ψ : ℝ) :
    (∑ i ∈ Finset.range N,
        (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
          * Real.cos ((M:ℝ) * Real.log ((i+1 : ℕ)) - ψ))
      + (N:ℝ) ^ ((1/2 : ℝ))
        * (-(Real.cos ((M:ℝ) * Real.log N - ψ)) / 2
          - (M:ℝ) * Real.sin ((M:ℝ) * Real.log N - ψ))
        / ((1/4 : ℝ) + (M:ℝ) ^ 2)
      - (N:ℝ) ^ (-(1/2 : ℝ)) / 2
      - ((M:ℝ)+1) * ((M:ℝ)+2) / 8
        * ((N:ℝ) ^ (-(5/2 : ℝ)) + (N:ℝ) ^ (-(3/2 : ℝ)) / (3/2))
    ≤ (Complex.exp ((ψ : ℝ) * Complex.I)
        * riemannZeta (line ((M:ℕ) : ℝ))).re := by
  have hMR : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hsform : line ((M:ℕ) : ℝ) = ↑(1/2 : ℝ) + ↑((M:ℕ) : ℝ) * Complex.I := by
    apply Complex.ext
    · rw [line_re]
      simp
    · rw [lineIm]
      simp
  set s : ℂ := ↑(1/2 : ℝ) + ↑((M:ℕ) : ℝ) * Complex.I with hsdef
  have hsre : s.re = 1/2 := by rw [hsdef]; simp
  have hsim : s.im = (M:ℝ) := by rw [hsdef]; simp
  have hσ0 : 0 < s.re := by rw [hsre]; norm_num
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    rw [hsim] at this
    simp at this
    linarith
  have hEM := zeta_EM_enclosure_numeric (N := N) hN hσ0 hs1
  set EMval : ℂ := (∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
      + (((N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)
      - (((N : ℕ) : ℝ) : ℂ) ^ (-s) / 2 with hEMdef
  have hunit : ‖Complex.exp ((ψ : ℝ) * Complex.I)‖ = 1 := by
    rw [show ((ψ : ℝ)) * Complex.I = Complex.I * ((ψ : ℝ)) by ring]
    exact Complex.norm_exp_I_mul_ofReal ψ
  have hdiff : |(Complex.exp ((ψ : ℝ) * Complex.I) * riemannZeta s).re
      - (Complex.exp ((ψ : ℝ) * Complex.I) * EMval).re|
      ≤ ‖riemannZeta s - EMval‖ := by
    have h1 : (Complex.exp ((ψ : ℝ) * Complex.I) * riemannZeta s).re
        - (Complex.exp ((ψ : ℝ) * Complex.I) * EMval).re
        = (Complex.exp ((ψ : ℝ) * Complex.I)
            * (riemannZeta s - EMval)).re := by
      simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
      ring
    rw [h1]
    calc |(Complex.exp ((ψ : ℝ) * Complex.I)
          * (riemannZeta s - EMval)).re|
        ≤ ‖Complex.exp ((ψ : ℝ) * Complex.I)
            * (riemannZeta s - EMval)‖ := Complex.abs_re_le_norm _
      _ = ‖riemannZeta s - EMval‖ := by rw [norm_mul, hunit, one_mul]
  have herr : ‖s‖ * ‖s + 1‖ * (1/8)
      * ((((N : ℕ) : ℝ)) ^ (-s.re - 2)
        + (((N : ℕ) : ℝ)) ^ (-s.re - 1) / (s.re + 1))
      ≤ ((M:ℝ)+1) * ((M:ℝ)+2) / 8
        * ((N:ℝ) ^ (-(5/2 : ℝ)) + (N:ℝ) ^ (-(3/2 : ℝ)) / (3/2)) := by
    have hns : ‖s‖ ≤ (M:ℝ) + 1 := by
      calc ‖s‖ ≤ ‖(↑(1/2 : ℝ) : ℂ)‖ + ‖↑((M:ℕ) : ℝ) * Complex.I‖ := by
            rw [hsdef]; exact norm_add_le _ _
        _ = 1/2 + (M:ℝ) := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul,
              Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos (by norm_num), abs_of_pos (by positivity)]
        _ ≤ (M:ℝ) + 1 := by linarith
    have hns1 : ‖s + 1‖ ≤ (M:ℝ) + 2 := by
      calc ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ (M:ℝ) + 2 := by rw [norm_one]; linarith
    have hexp1 : (((N : ℕ) : ℝ)) ^ (-s.re - 2) = (N:ℝ) ^ (-(5/2 : ℝ)) := by
      rw [hsre]
      norm_num
    have hexp2 : (((N : ℕ) : ℝ)) ^ (-s.re - 1) = (N:ℝ) ^ (-(3/2 : ℝ)) := by
      rw [hsre]
      norm_num
    have hden : s.re + 1 = 3/2 := by rw [hsre]; norm_num
    rw [hexp1, hexp2, hden]
    have hX : (0:ℝ) ≤ (N:ℝ) ^ (-(5/2 : ℝ)) + (N:ℝ) ^ (-(3/2 : ℝ)) / (3/2) := by
      have h1 := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ)) (-(5/2 : ℝ))
      have h2 := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ)) (-(3/2 : ℝ))
      positivity
    have hprod : ‖s‖ * ‖s + 1‖ ≤ ((M:ℝ)+1) * ((M:ℝ)+2) :=
      mul_le_mul hns hns1 (norm_nonneg _) (by positivity)
    nlinarith [hprod, hX, norm_nonneg s, norm_nonneg (s+1),
      mul_nonneg (norm_nonneg s) (norm_nonneg (s+1))]
  have hhead : (Complex.exp ((ψ : ℝ) * Complex.I)
        * (∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))).re
      = ∑ i ∈ Finset.range N,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((M:ℝ) * Real.log ((i+1 : ℕ)) - ψ) := by
    rw [Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_range_succ']
    have hterm0 : (Complex.exp ((ψ : ℝ) * Complex.I)
        * (((0 : ℕ) : ℝ) : ℂ) ^ (-s)).re = 0 := by
      have h0 : ((((0 : ℕ) : ℝ)) : ℂ) ^ (-s) = 0 := by
        rw [show ((((0 : ℕ) : ℝ)) : ℂ) = 0 by norm_num]
        refine Complex.zero_cpow ?_
        intro h
        have hs0 : s = 0 := neg_eq_zero.mp h
        rw [hs0] at hsim
        simp at hsim
        linarith
      rw [h0, mul_zero]
      simp
    rw [hterm0, add_zero]
    refine Finset.sum_congr rfl ?_
    intro i _
    have := re_phase_term (n := i + 1) (by omega) (1/2) ((M:ℕ) : ℝ) ψ
    rw [this]
  have hbdyre := boundary_re_eval M N hM hN ψ
  have hhalf : ‖(((N : ℕ) : ℝ) : ℂ) ^ (-s) / 2‖
      ≤ (N:ℝ) ^ (-(1/2 : ℝ)) / 2 := by
    rw [norm_div]
    have hb1 : ‖(((N : ℕ) : ℝ) : ℂ) ^ (-s)‖
        = ((N : ℕ) : ℝ) ^ ((-s).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) _
    have hres : (-s).re = -(1/2 : ℝ) := by simp [hsre]
    rw [hb1, hres]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
  have hEMre : (∑ i ∈ Finset.range N,
        (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
          * Real.cos ((M:ℝ) * Real.log ((i+1 : ℕ)) - ψ))
      + (N:ℝ) ^ ((1/2 : ℝ))
        * (-(Real.cos ((M:ℝ) * Real.log N - ψ)) / 2
          - (M:ℝ) * Real.sin ((M:ℝ) * Real.log N - ψ))
        / ((1/4 : ℝ) + (M:ℝ) ^ 2)
      - (N:ℝ) ^ (-(1/2 : ℝ)) / 2
      ≤ (Complex.exp ((ψ : ℝ) * Complex.I) * EMval).re := by
    rw [hEMdef]
    rw [show Complex.exp ((ψ : ℝ) * Complex.I)
        * ((∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
          + (((N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)
          - (((N : ℕ) : ℝ) : ℂ) ^ (-s) / 2)
      = Complex.exp ((ψ : ℝ) * Complex.I)
          * (∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + Complex.exp ((ψ : ℝ) * Complex.I)
          * ((((N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1))
        - Complex.exp ((ψ : ℝ) * Complex.I)
          * ((((N : ℕ) : ℝ) : ℂ) ^ (-s) / 2) by ring]
    simp only [Complex.add_re, Complex.sub_re]
    rw [hhead]
    have hbdy_eq : (Complex.exp ((ψ : ℝ) * Complex.I)
        * ((((N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1))).re
        = (N:ℝ) ^ ((1/2 : ℝ))
          * (-(Real.cos ((M:ℝ) * Real.log N - ψ)) / 2
            - (M:ℝ) * Real.sin ((M:ℝ) * Real.log N - ψ))
          / ((1/4 : ℝ) + (M:ℝ) ^ 2) := by
      rw [← hbdyre, hsdef]
    have hh := Complex.abs_re_le_norm (Complex.exp ((ψ : ℝ) * Complex.I)
      * ((((N : ℕ) : ℝ) : ℂ) ^ (-s) / 2))
    rw [norm_mul, hunit, one_mul] at hh
    have hh' := abs_le.mp hh
    rw [hbdy_eq]
    linarith [hh'.2, hhalf]
  have hζform : riemannZeta (line ((M:ℕ) : ℝ)) = riemannZeta s := by
    rw [hsform]
  rw [hζform]
  have habs := abs_le.mp hdiff
  have hEMb := le_trans hEM herr
  linarith [habs.1, hEMre, hEMb]


/-- **The SECOND-ORDER evaluated-boundary station lower bound.**  Same
closed-form boundary; the error side consumes
`zeta_EM_enclosure_second_numeric`. -/
theorem phase_station_lower_eval_second (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (ψ : ℝ) :
    (∑ i ∈ Finset.range N,
        (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
          * Real.cos ((M:ℝ) * Real.log ((i+1 : ℕ)) - ψ))
      + (N:ℝ) ^ ((1/2 : ℝ))
        * (-(Real.cos ((M:ℝ) * Real.log N - ψ)) / 2
          - (M:ℝ) * Real.sin ((M:ℝ) * Real.log N - ψ))
        / ((1/4 : ℝ) + (M:ℝ) ^ 2)
      - (N:ℝ) ^ (-(1/2 : ℝ)) / 2
      - ((M:ℝ)+1) * (N:ℝ) ^ (-(3/2 : ℝ)) / 12
      - ((M:ℝ)+1) * ((M:ℝ)+2) * ((M:ℝ)+3) / 48
        * ((N:ℝ) ^ (-(7/2 : ℝ)) + (N:ℝ) ^ (-(5/2 : ℝ)) / (5/2))
    ≤ (Complex.exp ((ψ : ℝ) * Complex.I)
        * riemannZeta (line ((M:ℕ) : ℝ))).re := by
  have hMR : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hsform : line ((M:ℕ) : ℝ) = ↑(1/2 : ℝ) + ↑((M:ℕ) : ℝ) * Complex.I := by
    apply Complex.ext
    · rw [line_re]
      simp
    · rw [lineIm]
      simp
  set s : ℂ := ↑(1/2 : ℝ) + ↑((M:ℕ) : ℝ) * Complex.I with hsdef
  have hsre : s.re = 1/2 := by rw [hsdef]; simp
  have hsim : s.im = (M:ℝ) := by rw [hsdef]; simp
  have hσ0 : 0 < s.re := by rw [hsre]; norm_num
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    rw [hsim] at this
    simp at this
    linarith
  have hnsM : ‖s‖ ≤ (M:ℝ) + 1 := by
    calc ‖s‖ ≤ ‖(↑(1/2 : ℝ) : ℂ)‖ + ‖↑((M:ℕ) : ℝ) * Complex.I‖ := by
          rw [hsdef]; exact norm_add_le _ _
      _ = 1/2 + (M:ℝ) := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul,
            Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
          rw [abs_of_pos (by norm_num), abs_of_pos (by positivity)]
      _ ≤ (M:ℝ) + 1 := by linarith
  have hEM := zeta_EM_enclosure_second_numeric (N := N) hN hσ0 hs1
  set EMval : ℂ := (∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
      + (((N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)
      - (((N : ℕ) : ℝ) : ℂ) ^ (-s) / 2
      + s * (((N : ℕ) : ℝ) : ℂ) ^ (-s - 1) / 12 with hEMdef
  have hunit : ‖Complex.exp ((ψ : ℝ) * Complex.I)‖ = 1 := by
    rw [show ((ψ : ℝ)) * Complex.I = Complex.I * ((ψ : ℝ)) by ring]
    exact Complex.norm_exp_I_mul_ofReal ψ
  have hdiff : |(Complex.exp ((ψ : ℝ) * Complex.I) * riemannZeta s).re
      - (Complex.exp ((ψ : ℝ) * Complex.I) * EMval).re|
      ≤ ‖riemannZeta s - EMval‖ := by
    have h1 : (Complex.exp ((ψ : ℝ) * Complex.I) * riemannZeta s).re
        - (Complex.exp ((ψ : ℝ) * Complex.I) * EMval).re
        = (Complex.exp ((ψ : ℝ) * Complex.I)
            * (riemannZeta s - EMval)).re := by
      simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
      ring
    rw [h1]
    calc |(Complex.exp ((ψ : ℝ) * Complex.I)
          * (riemannZeta s - EMval)).re|
        ≤ ‖Complex.exp ((ψ : ℝ) * Complex.I)
            * (riemannZeta s - EMval)‖ := Complex.abs_re_le_norm _
      _ = ‖riemannZeta s - EMval‖ := by rw [norm_mul, hunit, one_mul]
  have herr : ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * (1/48)
      * ((((N : ℕ) : ℝ)) ^ (-s.re - 3)
        + (((N : ℕ) : ℝ)) ^ (-s.re - 2) / (s.re + 2))
      ≤ ((M:ℝ)+1) * ((M:ℝ)+2) * ((M:ℝ)+3) / 48
        * ((N:ℝ) ^ (-(7/2 : ℝ)) + (N:ℝ) ^ (-(5/2 : ℝ)) / (5/2)) := by
    have hns := hnsM
    have hns1 : ‖s + 1‖ ≤ (M:ℝ) + 2 := by
      calc ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ (M:ℝ) + 2 := by rw [norm_one]; linarith
    have hns2 : ‖s + 2‖ ≤ (M:ℝ) + 3 := by
      calc ‖s + 2‖ ≤ ‖s‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
        _ ≤ (M:ℝ) + 3 := by
            rw [show ‖(2:ℂ)‖ = 2 by norm_num]; linarith
    have hexp1 : (((N : ℕ) : ℝ)) ^ (-s.re - 3) = (N:ℝ) ^ (-(7/2 : ℝ)) := by
      rw [hsre]
      norm_num
    have hexp2 : (((N : ℕ) : ℝ)) ^ (-s.re - 2) = (N:ℝ) ^ (-(5/2 : ℝ)) := by
      rw [hsre]
      norm_num
    have hden : s.re + 2 = 5/2 := by rw [hsre]; norm_num
    rw [hexp1, hexp2, hden]
    have hX : (0:ℝ) ≤ (N:ℝ) ^ (-(7/2 : ℝ)) + (N:ℝ) ^ (-(5/2 : ℝ)) / (5/2) := by
      have h1 := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ)) (-(7/2 : ℝ))
      have h2 := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ)) (-(5/2 : ℝ))
      positivity
    have hprod : ‖s‖ * ‖s + 1‖ * ‖s + 2‖ ≤ ((M:ℝ)+1) * ((M:ℝ)+2) * ((M:ℝ)+3) := by
      have h12 : ‖s‖ * ‖s + 1‖ ≤ ((M:ℝ)+1) * ((M:ℝ)+2) :=
        mul_le_mul hns hns1 (norm_nonneg _) (by positivity)
      calc ‖s‖ * ‖s + 1‖ * ‖s + 2‖
          ≤ (((M:ℝ)+1) * ((M:ℝ)+2)) * ((M:ℝ)+3) :=
            mul_le_mul h12 hns2 (norm_nonneg _) (by positivity)
        _ = ((M:ℝ)+1) * ((M:ℝ)+2) * ((M:ℝ)+3) := by ring
    nlinarith [hprod, hX, norm_nonneg s, norm_nonneg (s+1), norm_nonneg (s+2),
      mul_nonneg (mul_nonneg (norm_nonneg s) (norm_nonneg (s+1))) (norm_nonneg (s+2))]
  have hhead : (Complex.exp ((ψ : ℝ) * Complex.I)
        * (∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))).re
      = ∑ i ∈ Finset.range N,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((M:ℝ) * Real.log ((i+1 : ℕ)) - ψ) := by
    rw [Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_range_succ']
    have hterm0 : (Complex.exp ((ψ : ℝ) * Complex.I)
        * (((0 : ℕ) : ℝ) : ℂ) ^ (-s)).re = 0 := by
      have h0 : ((((0 : ℕ) : ℝ)) : ℂ) ^ (-s) = 0 := by
        rw [show ((((0 : ℕ) : ℝ)) : ℂ) = 0 by norm_num]
        refine Complex.zero_cpow ?_
        intro h
        have hs0 : s = 0 := neg_eq_zero.mp h
        rw [hs0] at hsim
        simp at hsim
        linarith
      rw [h0, mul_zero]
      simp
    rw [hterm0, add_zero]
    refine Finset.sum_congr rfl ?_
    intro i _
    have := re_phase_term (n := i + 1) (by omega) (1/2) ((M:ℕ) : ℝ) ψ
    rw [this]
  have hbdyre := boundary_re_eval M N hM hN ψ
  have hhalf : ‖(((N : ℕ) : ℝ) : ℂ) ^ (-s) / 2‖
      ≤ (N:ℝ) ^ (-(1/2 : ℝ)) / 2 := by
    rw [norm_div]
    have hb1 : ‖(((N : ℕ) : ℝ) : ℂ) ^ (-s)‖
        = ((N : ℕ) : ℝ) ^ ((-s).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) _
    have hres : (-s).re = -(1/2 : ℝ) := by simp [hsre]
    rw [hb1, hres]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
  have hEMre : (∑ i ∈ Finset.range N,
        (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
          * Real.cos ((M:ℝ) * Real.log ((i+1 : ℕ)) - ψ))
      + (N:ℝ) ^ ((1/2 : ℝ))
        * (-(Real.cos ((M:ℝ) * Real.log N - ψ)) / 2
          - (M:ℝ) * Real.sin ((M:ℝ) * Real.log N - ψ))
        / ((1/4 : ℝ) + (M:ℝ) ^ 2)
      - (N:ℝ) ^ (-(1/2 : ℝ)) / 2
      - ((M:ℝ)+1) * (N:ℝ) ^ (-(3/2 : ℝ)) / 12
      ≤ (Complex.exp ((ψ : ℝ) * Complex.I) * EMval).re := by
    rw [hEMdef]
    rw [show Complex.exp ((ψ : ℝ) * Complex.I)
        * ((∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
          + (((N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)
          - (((N : ℕ) : ℝ) : ℂ) ^ (-s) / 2
          + s * (((N : ℕ) : ℝ) : ℂ) ^ (-s - 1) / 12)
      = Complex.exp ((ψ : ℝ) * Complex.I)
          * (∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))
        + Complex.exp ((ψ : ℝ) * Complex.I)
          * ((((N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1))
        - Complex.exp ((ψ : ℝ) * Complex.I)
          * ((((N : ℕ) : ℝ) : ℂ) ^ (-s) / 2)
        + Complex.exp ((ψ : ℝ) * Complex.I)
          * (s * (((N : ℕ) : ℝ) : ℂ) ^ (-s - 1) / 12) by ring]
    simp only [Complex.add_re, Complex.sub_re]
    rw [hhead]
    have hbdy_eq : (Complex.exp ((ψ : ℝ) * Complex.I)
        * ((((N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1))).re
        = (N:ℝ) ^ ((1/2 : ℝ))
          * (-(Real.cos ((M:ℝ) * Real.log N - ψ)) / 2
            - (M:ℝ) * Real.sin ((M:ℝ) * Real.log N - ψ))
          / ((1/4 : ℝ) + (M:ℝ) ^ 2) := by
      rw [← hbdyre, hsdef]
    have hh := Complex.abs_re_le_norm (Complex.exp ((ψ : ℝ) * Complex.I)
      * ((((N : ℕ) : ℝ) : ℂ) ^ (-s) / 2))
    have hB2 := Complex.abs_re_le_norm (Complex.exp ((ψ : ℝ) * Complex.I)
      * (s * (((N : ℕ) : ℝ) : ℂ) ^ (-s - 1) / 12))
    rw [norm_mul, hunit, one_mul] at hh hB2
    have hB2n : ‖s * (((N : ℕ) : ℝ) : ℂ) ^ (-s - 1) / 12‖
        ≤ ((M:ℝ)+1) * (N:ℝ) ^ (-(3/2 : ℝ)) / 12 := by
      rw [norm_div, norm_mul, show ‖(12:ℂ)‖ = 12 by norm_num]
      have hcp : ‖(((N : ℕ) : ℝ) : ℂ) ^ (-s - 1)‖ = (N:ℝ) ^ (-(3/2 : ℝ)) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
        congr 1
        rw [show (-s - 1).re = -s.re - 1 by simp, hsre]
        norm_num
      rw [hcp]
      have hNn : (0:ℝ) ≤ (N:ℝ) ^ (-(3/2 : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      have : ‖s‖ * (N:ℝ) ^ (-(3/2 : ℝ)) ≤ ((M:ℝ)+1) * (N:ℝ) ^ (-(3/2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hnsM hNn
      linarith
    have hh' := abs_le.mp hh
    have hB2' := abs_le.mp hB2
    rw [hbdy_eq]
    linarith [hh'.2, hhalf, hB2'.1, hB2n]
  have hζform : riemannZeta (line ((M:ℕ) : ℝ)) = riemannZeta s := by
    rw [hsform]
  rw [hζform]
  have habs := abs_le.mp hdiff
  have hEMb := le_trans hEM herr
  linarith [habs.1, hEMre, hEMb]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.sinMulShift_eval
#print axioms CriticalLinePhasor.DVP.boundary_re_eval
#print axioms CriticalLinePhasor.DVP.phase_station_lower_eval
#print axioms CriticalLinePhasor.DVP.phase_station_lower_eval_second
end AxiomAudit
