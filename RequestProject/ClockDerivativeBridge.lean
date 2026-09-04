import Mathlib
import Zeta23.FromPNTPlus.ZetaBounds
import Zeta23.XiPrime.Hardy.ZFunction
import RequestProject.ClockDecomposition

/-!
# The clock-derivative bridge: Hardy's `Z′` as the prime clock reading the growth curve (ledger 574)

Three compiled sources meet here.

* **Zeta23** (`Zeta23.XiPrime.Hardy.ZFunction`): Hardy's `Z(t) = Re(e(t) ζ(½+it))` with the phase
  `e(t) = Γℝ(½+it)/|Γℝ(½+it)|` (the classical `e^{iϑ(t)}`), and the exact derivative
  `Z′(t) = Re(i e(t) W(½+it))`, `W = ζ′ + ϑ′ ζ`, `ϑ′(t) = Re(Γℝ′/Γℝ)(½+it)` (`hasDerivAt_hardyZ`,
  `L2_sline`).
* **PrimeNumberTheoremAnd** (`ZetaBounds`): the exact Euler–Maclaurin form
  `ζ(s) = Σ_{n≤N} n^{-s} − N^{1-s}/(1−s) − N^{-s}/2 + s ∫_N^∞ (⌊x⌋+½−x) x^{-s-1} dx` for `Re s > 0`,
  `s ≠ 1`, every `N ≥ 1` (`Zeta0EqZeta`), its `s`-derivative (`HasDerivAtZeta0`,
  `DerivZeta0EqDerivZeta`), and the tail bound `‖s ∫ …‖ ≤ 2|t| N^{-σ}/σ` (`ZetaBnd_aux1`).
* **Ledger 573** (`ClockDecomposition`): for the completely multiplicative bank `n ↦ n^{-s}`,
  `Σ_{n≤N} log n · n^{-s} = Σ_{d≤N} Λ(d) d^{-s} · bank (N/d)`.

**The bridge** (`hardyZ_deriv_bridge`): for `t ≠ 0` and every front `N ≥ 1`,

  `Z′(t) = Re[ i e(t) ( ϑ′(t) · bank N (½+it) − clock N (½+it) ) ] + Re[ i e(t) ( ϑ′(t) · tail N + tail′ N ) ]`

where `bank N s = Σ_{n≤N} n^{-s}` is the growth curve at the front, `clock N s = Σ_{d≤N} Λ(d) d^{-s}
bank (N/d) s` is the prime-power clock sampling the growth curve at the divisor-scaled fronts, and
`tail`, `tail′` are the exact Euler–Maclaurin tail and its derivative (explicit: `tail_eq`; bounded:
`tail_bound`). The bank's derivative is *minus the clock* (`bankDeriv_eq_neg_clock`): this is the whole
content of 573 at the level of the collision variable.

**The double-zero system** (`double_zero_system`): `Z(t) = Z′(t) = 0` forces the two equations
`Re[e(t)(bank + tail)] = 0` and `Re[i e(t)(ϑ′ bank − clock)] = −Re[i e(t)(ϑ′ tail + tail′)]` in the
same finite prime-clock state, with every analytic remainder named.

This is the long-bank (Euler–Maclaurin) bridge, exact at every front; the tail is small once
`N ≫ t²`. The short-bank (Riemann–Siegel, `N = √(t/2π)`) bridge with Gabcke's remainder is not
compiled anywhere in the workspace and is not attempted here.
-/

namespace CriticalLinePhasor.ClockDerivativeBridge

open Complex Finset ArithmeticFunction Zeta23.XiPrime CriticalLinePhasor.ClockDecomposition

/-- The finite bank (growth curve) at the front `N`. -/
noncomputable def bank (N : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s)

/-- Its `s`-derivative, `−Σ log n · n^{-s}`. -/
noncomputable def bankDeriv (N : ℕ) (s : ℂ) : ℂ := -∑ n ∈ Icc 1 N, (Real.log n : ℂ) * (n : ℂ) ^ (-s)

/-- The prime-power clock sampling the growth curve at the divisor-scaled fronts `N / d`. -/
noncomputable def clock (N : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ Icc 1 N, (Λ d : ℂ) * (d : ℂ) ^ (-s) * bank (N / d) s

/-- The exact Euler–Maclaurin tail `ζ₀ N s − bank N s` (PNT+'s `riemannZeta0`). -/
noncomputable def tail (N : ℕ) (s : ℂ) : ℂ := riemannZeta0 N s - bank N s

/-- Its exact `s`-derivative `ζ₀′ N s − bank′ N s`. -/
noncomputable def tailDeriv (N : ℕ) (s : ℂ) : ℂ := ζ₀' N s - bankDeriv N s

/-- **573 at the collision variable:** the derivative of the bank is minus the clock. -/
theorem bankDeriv_eq_neg_clock (N : ℕ) (s : ℂ) : bankDeriv N s = - clock N s := by
  unfold bankDeriv clock bank
  have h := log_weighted_bank (fun n : ℕ => (n : ℂ) ^ (-s)) (compMult_cpow s) N
  simp only [growth] at h
  rw [h]

theorem sline_re (t : ℝ) : (sline t).re = 1 / 2 := by
  simp [sline]

theorem sline_ne_zero (t : ℝ) : sline t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [sline_re] at this
  norm_num at this

/-- `ζ(½+it)` is the bank plus the tail, at every front. -/
theorem zeta_eq_bank_add_tail {N : ℕ} (hN : 0 < N) (t : ℝ) :
    riemannZeta (sline t) = bank N (sline t) + tail N (sline t) := by
  have h := Zeta0EqZeta hN (s := sline t) (by rw [sline_re]; norm_num) (sline_ne_one t)
  rw [← h, tail]
  ring

/-- `ζ′(½+it)` is the bank derivative plus the tail derivative, at every front. -/
theorem deriv_zeta_eq_bankDeriv_add_tailDeriv {N : ℕ} (hN : 0 < N) (t : ℝ) :
    deriv riemannZeta (sline t) = bankDeriv N (sline t) + tailDeriv N (sline t) := by
  have hre : 0 < (sline t).re := by rw [sline_re]; norm_num
  have h1 := DerivZeta0EqDerivZeta hN hre (sline_ne_one t)
  have h2 := (HasDerivAtZeta0 hN hre (sline_ne_one t)).deriv
  rw [← h1, h2, tailDeriv]
  ring

/-- **The clock-derivative bridge.** -/
theorem hardyZ_deriv_bridge {t : ℝ} (ht : t ≠ 0) {N : ℕ} (hN : 0 < N) :
    deriv hardyZ t
      = (I * ephase t * (((gG t).re : ℂ) * bank N (sline t) - clock N (sline t))).re
        + (I * ephase t * (((gG t).re : ℂ) * tail N (sline t) + tailDeriv N (sline t))).re := by
  rw [(hasDerivAt_hardyZ ht).deriv, ← Complex.add_re, ← mul_add]
  congr 2
  rw [hardyW, L2_sline t ht, zeta_eq_bank_add_tail hN t,
    deriv_zeta_eq_bankDeriv_add_tailDeriv hN t, bankDeriv_eq_neg_clock]
  ring

/-- **The double-zero system.** A real double zero of Hardy's `Z` at height `t ≠ 0` forces, at every
front `N`, the crossing equation on the bank and the tangency equation on the clock, with the
Euler–Maclaurin tails as the only remainders. -/
theorem double_zero_system {t : ℝ} (ht : t ≠ 0) {N : ℕ} (hN : 0 < N)
    (hZ : hardyZ t = 0) (hZ' : deriv hardyZ t = 0) :
    (ephase t * (bank N (sline t) + tail N (sline t))).re = 0 ∧
    (I * ephase t * (((gG t).re : ℂ) * bank N (sline t) - clock N (sline t))).re
      = -(I * ephase t * (((gG t).re : ℂ) * tail N (sline t) + tailDeriv N (sline t))).re := by
  constructor
  · rw [← zeta_eq_bank_add_tail hN t]
    have := hardyZ_eq t
    rw [hZ] at this
    have h2 : (ZC t).re = 0 := by
      have := congrArg Complex.re this
      simpa using this.symm
    simpa [ZC] using h2
  · have := hardyZ_deriv_bridge ht hN
    rw [hZ'] at this
    linarith

/-! ## The tail, explicitly, and its bound -/

/-- The range sum of PNT+ is the `Icc` bank (the `n = 0` term vanishes for `s ≠ 0`). -/
theorem range_sum_eq_bank {N : ℕ} {s : ℂ} (hs : s ≠ 0) :
    ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s = bank N s := by
  rw [Finset.sum_range_succ', bank]
  have h0 : (1 : ℂ) / ((0 : ℕ) : ℂ) ^ s = 0 := by
    simp [Complex.zero_cpow hs]
  rw [h0, add_zero]
  have hI : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext n; simp only [mem_Icc, mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) (fun n _ => ?_)
  rw [Complex.cpow_neg, one_div, add_comm]

/-- The exact tail. -/
theorem tail_eq {N : ℕ} {s : ℂ} (hs : s ≠ 0) :
    tail N s = -(N : ℂ) ^ (1 - s) / (1 - s) - (N : ℂ) ^ (-s) / 2
      + s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) := by
  rw [tail, riemannZeta0, range_sum_eq_bank hs]
  ring

/-- The tail bound on the critical line, from PNT+'s `ZetaBnd_aux1`. -/
theorem tail_bound {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 2 ≤ |t|) :
    ‖tail N (sline t)‖ ≤ (N : ℝ) ^ (1 / 2 : ℝ) / ‖1 - sline t‖ + (N : ℝ) ^ (-(1 / 2 : ℝ)) / 2
      + 4 * |t| * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsl : sline t = ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I := by simp [sline]
  rw [tail_eq (sline_ne_zero t)]
  have hb := ZetaBnd_aux1 N hN (σ := 1 / 2) (t := t) (by norm_num) ht
  rw [← hsl] at hb
  have h1 : ‖-(N : ℂ) ^ (1 - sline t) / (1 - sline t)‖ = (N : ℝ) ^ (1 / 2 : ℝ) / ‖1 - sline t‖ := by
    rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos (by omega)]
    congr 2
    simp [sline]; norm_num
  have h2 : ‖(N : ℂ) ^ (-sline t) / 2‖ = (N : ℝ) ^ (-(1 / 2 : ℝ)) / 2 := by
    have h2' : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega), h2']
    congr 2
    simp [sline]
  have h3 : (2 : ℝ) * |t| * (N : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2) = 4 * |t| * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    ring
  rw [h3] at hb
  calc ‖-(N : ℂ) ^ (1 - sline t) / (1 - sline t) - (N : ℂ) ^ (-sline t) / 2
        + sline t * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (sline t + 1)‖
      ≤ ‖-(N : ℂ) ^ (1 - sline t) / (1 - sline t)‖ + ‖(N : ℂ) ^ (-sline t) / 2‖
        + ‖sline t * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (sline t + 1)‖ := by
          refine le_trans (norm_add_le _ _) ?_
          gcongr
          exact norm_sub_le _ _
    _ ≤ _ := by rw [h1, h2]; gcongr

/-! ## The derivative tail, bounded by Cauchy's estimate -/

/-- The general tail bound off the line: `σ ∈ (0, 2]`, `|t| ≥ 2`, `N ≥ 1`. -/
theorem tail_bound_general {N : ℕ} (hN : 1 ≤ N) {σ t : ℝ} (hσ : σ ∈ Set.Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖tail N ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ (N : ℝ) ^ (1 - σ) / ‖1 - ((σ : ℂ) + (t : ℂ) * I)‖ + (N : ℝ) ^ (-σ) / 2
        + 2 * |t| * (N : ℝ) ^ (-σ) / σ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hs] at this
    linarith [hσ.1]
  rw [tail_eq hs0]
  have hb := ZetaBnd_aux1 N hN hσ ht
  rw [← hs] at hb
  have h1 : ‖-(N : ℂ) ^ (1 - s) / (1 - s)‖ = (N : ℝ) ^ (1 - σ) / ‖1 - s‖ := by
    rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos (by omega)]
    congr 2
    simp [hs]
  have h2 : ‖(N : ℂ) ^ (-s) / 2‖ = (N : ℝ) ^ (-σ) / 2 := by
    have h2' : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega), h2']
    congr 2
    simp [hs]
  calc ‖-(N : ℂ) ^ (1 - s) / (1 - s) - (N : ℂ) ^ (-s) / 2
        + s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ ‖-(N : ℂ) ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖
        + ‖s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := by
          refine le_trans (norm_add_le _ _) ?_
          gcongr
          exact norm_sub_le _ _
    _ ≤ _ := by rw [h1, h2]; gcongr

/-- The bank is differentiable with derivative `bankDeriv`. -/
theorem hasDerivAt_bank (N : ℕ) (w : ℂ) : HasDerivAt (bank N) (bankDeriv N w) w := by
  have hs : HasDerivAt (fun w : ℂ => ∑ n ∈ Icc 1 N, (n : ℂ) ^ (-w))
      (∑ n ∈ Icc 1 N, (n : ℂ) ^ (-w) * Complex.log n * (-1)) w := by
    refine HasDerivAt.fun_sum (fun n hn => ?_)
    have hn0 : (n : ℂ) ≠ 0 := by
      rw [mem_Icc] at hn
      exact_mod_cast (by omega : n ≠ 0)
    exact (hasDerivAt_neg' w).const_cpow (c := (n : ℂ)) (Or.inl hn0)
  refine hs.congr_deriv ?_
  unfold bankDeriv
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Complex.natCast_log]
  ring

/-- The tail is differentiable on `Re > 0`, `≠ 1`, with derivative `tailDeriv`. -/
theorem hasDerivAt_tail {N : ℕ} (hN : 0 < N) {w : ℂ} (hre : 0 < w.re) (hw : w ≠ 1) :
    HasDerivAt (tail N) (tailDeriv N w) w :=
  (HasDerivAtZeta0 hN hre hw).sub (hasDerivAt_bank N w)

/-- Points of the closed disc of radius `1/4` about `½ + it` (`|t| ≥ 3`) have `Re ≥ 1/4`, `|Im| ≥ |t| − 1/4`. -/
theorem disc_facts {t : ℝ} {w : ℂ} (hw : dist w (sline t) ≤ 1 / 4) :
    1 / 4 ≤ w.re ∧ w.re ≤ 3 / 4 ∧ |w.im - t| ≤ 1 / 4 ∧ |t| - 1 / 4 ≤ |w.im| ∧ |w.im| ≤ |t| + 1 / 4 := by
  rw [dist_eq_norm] at hw
  have hre := Complex.abs_re_le_norm (w - sline t)
  have him := Complex.abs_im_le_norm (w - sline t)
  have hre' : (w - sline t).re = w.re - 1 / 2 := by simp [sline]
  have him' : (w - sline t).im = w.im - t := by simp [sline]
  rw [hre'] at hre
  rw [him'] at him
  have hA := abs_le.mp (le_trans hre hw)
  have hB := abs_le.mp (le_trans him hw)
  refine ⟨by linarith, by linarith, le_trans him hw, ?_, ?_⟩
  · have := abs_sub_abs_le_abs_sub t w.im
    rw [abs_sub_comm] at this
    linarith [le_trans him hw]
  · have := abs_sub_abs_le_abs_sub w.im t
    linarith [le_trans him hw]

/-- **The derivative-tail bound** (Cauchy's estimate on the disc of radius `1/4`). -/
theorem tailDeriv_bound {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 3 ≤ |t|) :
    ‖tailDeriv N (sline t)‖
      ≤ 4 * ((N : ℝ) ^ (3 / 4 : ℝ) / (|t| - 1 / 4) + (N : ℝ) ^ (-(1 / 4 : ℝ)) / 2
        + 8 * (|t| + 1 / 4) * (N : ℝ) ^ (-(1 / 4 : ℝ))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set C : ℝ := (N : ℝ) ^ (3 / 4 : ℝ) / (|t| - 1 / 4) + (N : ℝ) ^ (-(1 / 4 : ℝ)) / 2
        + 8 * (|t| + 1 / 4) * (N : ℝ) ^ (-(1 / 4 : ℝ)) with hC
  have hR : (0 : ℝ) < 1 / 4 := by norm_num
  have hderiv : deriv (tail N) (sline t) = tailDeriv N (sline t) :=
    (hasDerivAt_tail (by omega) (by rw [sline_re]; norm_num) (sline_ne_one t)).deriv
  rw [← hderiv]
  have key := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := sline t) (R := 1 / 4)
    (C := C) (f := tail N) hR ?_ ?_
  · calc ‖deriv (tail N) (sline t)‖ ≤ C / (1 / 4) := key
      _ = 4 * C := by ring
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num)]
    intro w hw
    obtain ⟨h1, -, -, h4, -⟩ := disc_facts (Metric.mem_closedBall.mp hw)
    have hre : 0 < w.re := by linarith
    have hne : w ≠ 1 := by
      intro h
      have h0 : w.im = 0 := by simpa using congrArg Complex.im h
      rw [h0, abs_zero] at h4
      linarith
    exact (hasDerivAt_tail (by omega) hre hne).differentiableAt.differentiableWithinAt
  · intro w hw
    have hw' : dist w (sline t) ≤ 1 / 4 := le_of_eq (Metric.mem_sphere.mp hw)
    obtain ⟨h1, h2, -, h4, h5⟩ := disc_facts hw'
    have hσ : w.re ∈ Set.Ioc 0 2 := ⟨by linarith, by linarith⟩
    have htw : 2 ≤ |w.im| := by linarith
    have hb := tail_bound_general hN hσ htw
    rw [Complex.re_add_im w] at hb
    refine le_trans hb ?_
    rw [hC]
    have hpos : 0 < |t| - 1 / 4 := by linarith
    -- ‖1 − w‖ ≥ |Im w| ≥ |t| − 1/4
    have hnorm : |t| - 1 / 4 ≤ ‖1 - w‖ := by
      have := Complex.abs_im_le_norm (1 - w)
      have h' : (1 - w).im = -w.im := by simp
      rw [h', abs_neg] at this
      linarith
    have hA : (N : ℝ) ^ (1 - w.re) / ‖1 - w‖ ≤ (N : ℝ) ^ (3 / 4 : ℝ) / (|t| - 1 / 4) := by
      apply div_le_div₀ (by positivity) ?_ hpos hnorm
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hB : (N : ℝ) ^ (-w.re) / 2 ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) / 2 := by
      gcongr
    have hD : 2 * |w.im| * (N : ℝ) ^ (-w.re) / w.re ≤ 8 * (|t| + 1 / 4) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
      have hpow : (N : ℝ) ^ (-w.re) ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      have hpow0 : 0 ≤ (N : ℝ) ^ (-w.re) := by positivity
      rw [div_le_iff₀ (by linarith)]
      have := mul_le_mul (mul_le_mul (by linarith : 2 * |w.im| ≤ 2 * (|t| + 1 / 4)) hpow hpow0
        (by positivity)) (by linarith : 1 / 4 ≤ w.re) (by norm_num) (by positivity)
      nlinarith [this]
    linarith [hA, hB, hD]

#print axioms hardyZ_deriv_bridge
#print axioms double_zero_system
#print axioms tail_bound
#print axioms tailDeriv_bound

end CriticalLinePhasor.ClockDerivativeBridge
