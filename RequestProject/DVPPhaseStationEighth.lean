import RequestProject.DVPPhaseStationEval

/-!
# The eighth-integer station core (rung-199.5 route-around)

Close zero pairs inside one integer cell need stations at half-integer
heights.  The station at `t = M/8` reuses the ℕ-multiplier evaluators
against HALVED log brackets (`cos(M·(log n / 8) − ψ)` — exact rational
halving, no new transcendental content).
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The EIGHTH-INTEGER phase-station lower bound** (height `M/8`).  All costs in closed form; the
head is the shifted-cosine sum the tables certify. -/
theorem phase_station_lower_eighth (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N) (ψ : ℝ) :
    (∑ i ∈ Finset.range N,
        (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
          * Real.cos ((M:ℝ) * (Real.log ((i+1 : ℕ)) / 8) - ψ))
      - (N:ℝ) ^ ((1/2 : ℝ)) / ((M:ℝ)/8) - (N:ℝ) ^ (-(1/2 : ℝ)) / 2
      - ((M:ℝ)/8+1) * ((M:ℝ)/8+2) / 8
        * ((N:ℝ) ^ (-(5/2 : ℝ)) + (N:ℝ) ^ (-(3/2 : ℝ)) / (3/2))
    ≤ (Complex.exp ((ψ : ℝ) * Complex.I)
        * riemannZeta (line (((M:ℕ) : ℝ)/8))).re := by
  have hMR : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  -- the point in split form
  have hsform : line (((M:ℕ) : ℝ)/8) = ↑(1/2 : ℝ) + ↑(((M:ℕ) : ℝ)/8) * Complex.I := by
    apply Complex.ext
    · rw [line_re]
      simp
    · rw [lineIm]
      simp
  set s : ℂ := ↑(1/2 : ℝ) + ↑(((M:ℕ) : ℝ)/8) * Complex.I with hsdef
  have hsre : s.re = 1/2 := by rw [hsdef]; simp
  have hsim : s.im = (M:ℝ)/8 := by rw [hsdef]; simp
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
      ≤ ((M:ℝ)/8+1) * ((M:ℝ)/8+2) / 8
        * ((N:ℝ) ^ (-(5/2 : ℝ)) + (N:ℝ) ^ (-(3/2 : ℝ)) / (3/2)) := by
    have hns : ‖s‖ ≤ (M:ℝ)/8 + 1 := by
      calc ‖s‖ ≤ ‖(↑(1/2 : ℝ) : ℂ)‖ + ‖↑(((M:ℕ) : ℝ)/8) * Complex.I‖ := by
            rw [hsdef]; exact norm_add_le _ _
        _ = 1/2 + (M:ℝ)/8 := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul,
              Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos (by norm_num), abs_of_pos (by positivity)]
        _ ≤ (M:ℝ)/8 + 1 := by linarith
    have hns1 : ‖s + 1‖ ≤ (M:ℝ)/8 + 2 := by
      calc ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ (M:ℝ)/8 + 2 := by rw [norm_one]; linarith
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
    have hprod : ‖s‖ * ‖s + 1‖ ≤ ((M:ℝ)/8+1) * ((M:ℝ)/8+2) :=
      mul_le_mul hns hns1 (norm_nonneg _) (by positivity)
    nlinarith [hprod, hX, norm_nonneg s, norm_nonneg (s+1),
      mul_nonneg (norm_nonneg s) (norm_nonneg (s+1))]
  -- the phase-rotated head
  have hhead : (Complex.exp ((ψ : ℝ) * Complex.I)
        * (∑ n ∈ Finset.range (N + 1), (((n : ℝ)) : ℂ) ^ (-s))).re
      = ∑ i ∈ Finset.range N,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((M:ℝ) * (Real.log ((i+1 : ℕ)) / 8) - ψ) := by
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
    have h0 := re_phase_term (n := i + 1) (by omega) (1/2) (((M:ℕ) : ℝ)/8) ψ
    rw [show (M:ℝ) * (Real.log ((i+1 : ℕ)) / 8) - ψ
        = ((M:ℕ) : ℝ)/8 * Real.log ((i+1 : ℕ)) - ψ by ring]
    rw [h0]
  -- boundary and half in closed form
  have hbdy : ‖(((N : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖
      ≤ (N:ℝ) ^ ((1/2 : ℝ)) / ((M:ℝ)/8) := by
    rw [norm_div]
    have hb1 : ‖(((N : ℕ) : ℝ) : ℂ) ^ (1 - s)‖
        = ((N : ℕ) : ℝ) ^ ((1 - s).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) _
    have hre1s : (1 - s).re = 1/2 := by
      simp [hsre]
      norm_num
    have hden : (M:ℝ)/8 ≤ ‖s - 1‖ := by
      have habsim := Complex.abs_im_le_norm (s - 1)
      have him : (s - 1).im = (M:ℝ)/8 := by simp [hsim]
      rw [him] at habsim
      calc (M:ℝ)/8 = |(M:ℝ)/8| := (abs_of_pos (by positivity)).symm
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
          * Real.cos ((M:ℝ) * (Real.log ((i+1 : ℕ)) / 8) - ψ))
      - (N:ℝ) ^ ((1/2 : ℝ)) / ((M:ℝ)/8) - (N:ℝ) ^ (-(1/2 : ℝ)) / 2
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
  have hζform : riemannZeta (line (((M:ℕ) : ℝ)/8)) = riemannZeta s := by
    rw [hsform]
  rw [hζform]
  have habs := abs_le.mp hdiff
  have hEMb := le_trans hEM herr
  linarith [habs.1, hEMre, hEMb]


end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.phase_station_lower_eighth
end AxiomAudit
