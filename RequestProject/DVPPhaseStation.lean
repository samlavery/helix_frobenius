import RequestProject.DVPCosSinEval
import RequestProject.DVPStationSign

/-!
# The phase-folded station core

For a station at integer height `M` with rational proxy phase `ψ`, the
quantity whose sign the ladder needs is `Re(e^{iψ}·ζ(½+Mi))`.  Folding
the phase into the Euler–Maclaurin head turns every term into
`n^{−1/2}·cos(M·log n − ψ)` — ONE cosine certificate per `(M, n)`, no
sines, no separate `Re ζ`/`Im ζ` enclosures, and the boundary/half/error
costs bounded in closed form.  `cosMulShift_eval` is the matching
evaluator with the rational shift in the angle window.
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The shifted angle window. -/
theorem angle_window_shift {L : ℝ} {lo hi r δ ψ : ℚ} (M k : ℕ)
    (hlo : ((lo : ℚ) : ℝ) ≤ L) (hhi : L ≤ ((hi : ℚ) : ℝ))
    (ha1 : M * hi - ψ - k * (628318530717958647692/10^20 : ℚ) - 4 * r ≤ δ)
    (ha2 : -δ ≤ M * lo - ψ - k * (628318530717958647694/10^20 : ℚ) - 4 * r) :
    |((M:ℝ) * L - ((ψ : ℚ) : ℝ)) - ((k : ℤ) : ℝ) * (2 * Real.pi)
        - 4 * ((r : ℚ) : ℝ)|
      ≤ ((δ : ℚ) : ℝ) := by
  have h2π_lo : ((628318530717958647692/10^20 : ℚ) : ℝ) ≤ 2 * Real.pi := by
    have := Real.pi_gt_d20
    push_cast
    linarith
  have h2π_hi : 2 * Real.pi ≤ ((628318530717958647694/10^20 : ℚ) : ℝ) := by
    have := Real.pi_lt_d20
    push_cast
    linarith
  have hcast : ((k : ℤ) : ℝ) = ((k : ℕ) : ℝ) := by push_cast; rfl
  rw [abs_le, hcast]
  constructor
  · have h1 : ((k : ℕ) : ℝ) * (2 * Real.pi)
        ≤ ((k : ℕ) : ℝ) * ((628318530717958647694/10^20 : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left h2π_hi (by positivity)
    have h3 : (((-δ) : ℚ) : ℝ)
        ≤ ((M * lo - ψ - k * (628318530717958647694/10^20) - 4 * r
          : ℚ) : ℝ) := by exact_mod_cast ha2
    have hM0 : (0:ℝ) ≤ (M:ℝ) := by positivity
    push_cast at h3 ⊢
    nlinarith [h1, h3, hlo]
  · have h1 : ((k : ℕ) : ℝ) * ((628318530717958647692/10^20 : ℚ) : ℝ)
        ≤ ((k : ℕ) : ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left h2π_lo (by positivity)
    have h3 : ((M * hi - ψ - k * (628318530717958647692/10^20) - 4 * r
        : ℚ) : ℝ) ≤ ((δ : ℚ) : ℝ) := by exact_mod_cast ha1
    have hM0 : (0:ℝ) ≤ (M:ℝ) := by positivity
    push_cast at h3 ⊢
    nlinarith [h1, h3, hhi]

/-- **The shifted cosine evaluator**: `|cos(M·L − ψ) − v| ≤ ε`. -/
theorem cosMulShift_eval {L : ℝ} {lo hi r δ ψ v ε : ℚ} (M k : ℕ)
    (hlo : ((lo : ℚ) : ℝ) ≤ L) (hhi : L ≤ ((hi : ℚ) : ℝ))
    (hr : |r| ≤ 1)
    (ha1 : M * hi - ψ - k * (628318530717958647692/10^20 : ℚ) - 4 * r ≤ δ)
    (ha2 : -δ ≤ M * lo - ψ - k * (628318530717958647694/10^20 : ℚ) - 4 * r)
    (hs2 : |sinTaylor r 5| ≤ 2)
    (hε : δ + 96 * (|r| ^ 10 * (11/36288000))
        + |v - (2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1)| ≤ ε) :
    |Real.cos ((M:ℝ) * L - ((ψ : ℚ) : ℝ)) - ((v : ℚ) : ℝ)|
      ≤ ((ε : ℚ) : ℝ) := by
  have hθ := angle_window_shift M k hlo hhi ha1 ha2
  have hsin := sin_enclosure (x := r) hr (n := 5) (by norm_num)
  have hbr : |((r : ℚ) : ℝ)| ^ (2 * 5)
      * (((2 * 5).succ : ℝ) * (((2 * 5).factorial : ℝ) * ((2 * 5 : ℕ) : ℝ))⁻¹)
      ≤ ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]
    push_cast
    norm_num [Nat.factorial]
  have hŝ := le_trans hsin hbr
  have hs2' : |((sinTaylor r 5 : ℚ) : ℝ)| ≤ 2 := by
    rw [← Rat.cast_abs]
    exact_mod_cast hs2
  have hmain := cos_angle_eval (θ := (M:ℝ) * L - ((ψ : ℚ) : ℝ)) (r := r)
    (ŝ := sinTaylor r 5) (δ := δ) (τ := |r| ^ 10 * (11/36288000))
    ((k : ℕ) : ℤ) hθ hŝ hs2'
  have hvF : |((v : ℚ) : ℝ)
      - ((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ)|
      = ((|v - (2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1)| : ℚ) : ℝ) := by
    rw [← Rat.cast_sub, ← Rat.cast_abs]
  calc |Real.cos ((M:ℝ) * L - ((ψ : ℚ) : ℝ)) - ((v : ℚ) : ℝ)|
      ≤ |Real.cos ((M:ℝ) * L - ((ψ : ℚ) : ℝ))
          - ((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ)|
        + |((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ)
          - ((v : ℚ) : ℝ)| := by
        calc |Real.cos ((M:ℝ) * L - ((ψ : ℚ) : ℝ)) - ((v : ℚ) : ℝ)|
            = |(Real.cos ((M:ℝ) * L - ((ψ : ℚ) : ℝ))
                - ((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ))
              + (((2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1 : ℚ) : ℝ)
                - ((v : ℚ) : ℝ))| := by ring_nf
          _ ≤ _ := abs_add_le _ _
    _ ≤ (((δ : ℚ) : ℝ) + 96 * ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ))
        + ((|v - (2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1)| : ℚ) : ℝ) := by
        refine add_le_add hmain ?_
        rw [abs_sub_comm, hvF]
    _ ≤ ((ε : ℚ) : ℝ) := by
        rw [show (((δ : ℚ) : ℝ) + 96 * ((|r| ^ 10 * (11/36288000) : ℚ) : ℝ))
            + ((|v - (2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1)| : ℚ) : ℝ)
            = ((δ + 96 * (|r| ^ 10 * (11/36288000))
              + |v - (2 * (1 - 2 * (sinTaylor r 5) ^ 2) ^ 2 - 1)| : ℚ) : ℝ) by
          push_cast; ring]
        exact_mod_cast hε

/-- The phase-rotated term: `Re(e^{iψ}·n^{−s}) = n^{−σ}·cos(t·log n − ψ)`. -/
theorem re_phase_term {n : ℕ} (hn : 1 ≤ n) (σ t ψ : ℝ) :
    (Complex.exp ((ψ : ℝ) * Complex.I)
        * (((n : ℝ) : ℂ) ^ (-(↑σ + ↑t * Complex.I)))).re
      = (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n - ψ) := by
  have hsplit := nat_cpow_neg_split hn σ t
  rw [Complex.mul_re, hsplit.1, hsplit.2,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_sub]
  ring

/-- **The phase-station lower bound.**  All costs in closed form; the
head is the shifted-cosine sum the tables certify. -/
theorem phase_station_lower (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N) (ψ : ℝ) :
    (∑ i ∈ Finset.range N,
        (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
          * Real.cos ((M:ℝ) * Real.log ((i+1 : ℕ)) - ψ))
      - (N:ℝ) ^ ((1/2 : ℝ)) / (M:ℝ) - (N:ℝ) ^ (-(1/2 : ℝ)) / 2
      - ((M:ℝ)+1) * ((M:ℝ)+2) / 8
        * ((N:ℝ) ^ (-(5/2 : ℝ)) + (N:ℝ) ^ (-(3/2 : ℝ)) / (3/2))
    ≤ (Complex.exp ((ψ : ℝ) * Complex.I)
        * riemannZeta (line ((M:ℕ) : ℝ))).re := by
  have hMR : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  -- the point in split form
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
  -- transfer through the unit phase
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
  -- the error majorant in closed form
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
  -- the phase-rotated head
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
  -- boundary and half in closed form
  have hbdy : ‖(((N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖
      ≤ (N:ℝ) ^ ((1/2 : ℝ)) / (M:ℝ) := by
    rw [norm_div]
    have hb1 : ‖(((N : ℕ) : ℝ) : ℂ) ^ (1 - s)‖
        = ((N : ℕ) : ℝ) ^ ((1 - s).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) _
    have hre1s : (1 - s).re = 1/2 := by
      simp [hsre]
      norm_num
    have hden : (M:ℝ) ≤ ‖s - 1‖ := by
      have habsim := Complex.abs_im_le_norm (s - 1)
      have him : (s - 1).im = (M:ℝ) := by simp [hsim]
      rw [him] at habsim
      calc (M:ℝ) = |(M:ℝ)| := (abs_of_pos (by positivity)).symm
        _ ≤ ‖s - 1‖ := habsim
    rw [hb1, hre1s]
    apply div_le_div_of_nonneg_left _ (by positivity) hden
    positivity
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
  -- assemble
  have hEMre : (∑ i ∈ Finset.range N,
        (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
          * Real.cos ((M:ℝ) * Real.log ((i+1 : ℕ)) - ψ))
      - (N:ℝ) ^ ((1/2 : ℝ)) / (M:ℝ) - (N:ℝ) ^ (-(1/2 : ℝ)) / 2
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
    have hb := Complex.abs_re_le_norm (Complex.exp ((ψ : ℝ) * Complex.I)
      * ((((N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)))
    have hh := Complex.abs_re_le_norm (Complex.exp ((ψ : ℝ) * Complex.I)
      * ((((N : ℕ) : ℝ) : ℂ) ^ (-s) / 2))
    rw [norm_mul, hunit, one_mul] at hb hh
    have hb' := abs_le.mp hb
    have hh' := abs_le.mp hh
    linarith [hb'.1, hh'.2, hbdy, hhalf]
  have hζform : riemannZeta (line ((M:ℕ) : ℝ)) = riemannZeta s := by
    rw [hsform]
  rw [hζform]
  have habs := abs_le.mp hdiff
  have hEMb := le_trans hEM herr
  linarith [habs.1, hEMre, hEMb]

/-- **The SECOND-ORDER phase-station lower bound.**  Identical in shape to
`phase_station_lower`, but consuming `zeta_EM_enclosure_second_numeric`: the
`B₂` head term is booked at its (single-`s`) magnitude and the residual
carries two further powers of `N`.  At the campaign's heights this is a
14–25× smaller total cost. -/
theorem phase_station_lower_second (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N) (ψ : ℝ) :
    (∑ i ∈ Finset.range N,
        (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
          * Real.cos ((M:ℝ) * Real.log ((i+1 : ℕ)) - ψ))
      - (N:ℝ) ^ ((1/2 : ℝ)) / (M:ℝ) - (N:ℝ) ^ (-(1/2 : ℝ)) / 2
      - ((M:ℝ)+1) * (N:ℝ) ^ (-(3/2 : ℝ)) / 12
      - ((M:ℝ)+1) * ((M:ℝ)+2) * ((M:ℝ)+3) / 48
        * ((N:ℝ) ^ (-(7/2 : ℝ)) + (N:ℝ) ^ (-(5/2 : ℝ)) / (5/2))
    ≤ (Complex.exp ((ψ : ℝ) * Complex.I)
        * riemannZeta (line ((M:ℕ) : ℝ))).re := by
  have hMR : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  -- the point in split form
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
  -- transfer through the unit phase
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
  -- the error majorant in closed form
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
  -- the phase-rotated head
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
  -- boundary and half in closed form
  have hbdy : ‖(((N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖
      ≤ (N:ℝ) ^ ((1/2 : ℝ)) / (M:ℝ) := by
    rw [norm_div]
    have hb1 : ‖(((N : ℕ) : ℝ) : ℂ) ^ (1 - s)‖
        = ((N : ℕ) : ℝ) ^ ((1 - s).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) _
    have hre1s : (1 - s).re = 1/2 := by
      simp [hsre]
      norm_num
    have hden : (M:ℝ) ≤ ‖s - 1‖ := by
      have habsim := Complex.abs_im_le_norm (s - 1)
      have him : (s - 1).im = (M:ℝ) := by simp [hsim]
      rw [him] at habsim
      calc (M:ℝ) = |(M:ℝ)| := (abs_of_pos (by positivity)).symm
        _ ≤ ‖s - 1‖ := habsim
    rw [hb1, hre1s]
    apply div_le_div_of_nonneg_left _ (by positivity) hden
    positivity
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
  -- assemble
  have hEMre : (∑ i ∈ Finset.range N,
        (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
          * Real.cos ((M:ℝ) * Real.log ((i+1 : ℕ)) - ψ))
      - (N:ℝ) ^ ((1/2 : ℝ)) / (M:ℝ) - (N:ℝ) ^ (-(1/2 : ℝ)) / 2
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
    have hb := Complex.abs_re_le_norm (Complex.exp ((ψ : ℝ) * Complex.I)
      * ((((N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)))
    have hh := Complex.abs_re_le_norm (Complex.exp ((ψ : ℝ) * Complex.I)
      * ((((N : ℕ) : ℝ) : ℂ) ^ (-s) / 2))
    have hB2 := Complex.abs_re_le_norm (Complex.exp ((ψ : ℝ) * Complex.I)
      * (s * (((N : ℕ) : ℝ) : ℂ) ^ (-s - 1) / 12))
    rw [norm_mul, hunit, one_mul] at hb hh hB2
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
    have hb' := abs_le.mp hb
    have hh' := abs_le.mp hh
    have hB2' := abs_le.mp hB2
    linarith [hb'.1, hh'.2, hB2'.1, hB2n, hbdy, hhalf]
  have hζform : riemannZeta (line ((M:ℕ) : ℝ)) = riemannZeta s := by
    rw [hsform]
  rw [hζform]
  have habs := abs_le.mp hdiff
  have hEMb := le_trans hEM herr
  linarith [habs.1, hEMre, hEMb]


end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cosMulShift_eval
#print axioms CriticalLinePhasor.DVP.re_phase_term
#print axioms CriticalLinePhasor.DVP.phase_station_lower
#print axioms CriticalLinePhasor.DVP.phase_station_lower_second
end AxiomAudit
