import RequestProject.PrimeCoefficientSymbol
import RequestProject.ConductionClockToeplitz
import Mathlib.Analysis.Complex.Liouville

/-!
The common arithmetic bound remains the target:
`∃ C : ℝ, ∃ p : ℕ, ∀ k, ∀ᶠ N in atTop,
  ‖explicitCoeffStage N k‖ ≤ C * (1 + (k : ℝ) ^ p)`.
This module first bounds a single prime symbol uniformly in its degree.

Unfolded substep: the finite Pascal polynomial q_k(ell) is the derivative at
beta = 0 of the clock's degree k+1 coefficient, divided by ell*exp(-3*ell/2).
The clock has positive weights and unit-modulus transported atoms for |beta|=1.
Cauchy's derivative estimate therefore bounds q_k with a constant independent of k.

Searches: `rg -n 'primeCoeffSymbol|prime_coeff_symbol|symbol.*bound|bound.*symbol|
clock.*bound|bound.*clock' RequestProject`; `rg -n 'Dk.*deriv|deriv.*Dk|
clock_toeplitzCoeff|clockS_re_logDeriv|toeplitzCoeff_jets_differentiableOn'
RequestProject`; `rg -n 'norm_deriv_le|norm_iteratedDeriv_le|cauchyPowerSeries.*le|
diffContOnCl_ball|choose_mul_geometric' .lake/packages/mathlib/Mathlib`.
Semantic searches: LeanSearch for bounded holomorphic Taylor coefficients;
Loogle for `"norm", "cauchy"`.

Two constructions: (A) use `HasDerivAt` on the clock parameter and Cauchy's estimate;
(B) identify q_k with the Taylor coefficients of
`-(exp(3*ell*z/(1+z))-1)/3`. Construction A is developed below.
-/

open Complex Finset Filter Topology Metric

namespace CriticalLinePhasor.SeatingLedger

theorem cayley_re_lt_half {z : ℂ} (hz : ‖z‖ < 1) : (z / (1 + z)).re < 1 / 2 := by
  have hn : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hne : (1 : ℂ) + z ≠ 0 := by
    intro h
    have : z = -1 := by linear_combination h
    simp [this] at hz
  have hd := Complex.normSq_pos.mpr hne
  rw [Complex.div_re, ← add_div]
  apply (div_lt_iff₀ hd).mpr
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    zero_add, Complex.normSq_apply] at hn hd ⊢
  nlinarith

theorem cayley_exp_norm_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖Complex.exp (3 * (ℓ : ℂ) * z / (1 + z))‖ ≤ Real.exp (3 * ℓ / 2) := by
  have hr := cayley_re_lt_half hz
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  rw [mul_div_assoc]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero, add_zero, sub_zero]
  nlinarith

theorem Dk_hasDerivAt_zero (k : ℕ) : HasDerivAt (Dk k) 2 0 := by
  induction k with
  | zero =>
    have h := ((hasDerivAt_const (0 : ℂ) 1).add (hasDerivAt_id 0)).div
      ((hasDerivAt_const (0 : ℂ) 1).sub (hasDerivAt_id 0)) (by norm_num)
    convert h using 1 <;> first | rfl | norm_num [Dk, hker]
  | succ k ih =>
    have hd := ((Dk_analyticOnNhd k).deriv 0 (by simp)).differentiableAt.hasDerivAt
    have h := (hasDerivAt_id (0 : ℂ)).mul hd
    simpa only [Dk, id_eq, mul_zero, zero_mul, add_zero, one_mul, ih.deriv] using! h

theorem iteratedDeriv_Gclock_hasDerivAt_zero {ℓ : ℝ} (hℓ : 0 < ℓ)
    {s : ℂ} (hs : s.re < 1 / 2) (m : ℕ) :
    HasDerivAt (fun β => iteratedDeriv m (Gclock ℓ β) s)
      ((ℓ : ℂ) ^ (m + 1) * dvar ℓ s) 0 := by
  have hd := (Dk_hasDerivAt_zero m).comp_of_eq 0
    ((hasDerivAt_id 0).mul_const (dvar ℓ s)) (by simp)
  simp only [id_eq] at hd
  have hf := hd.const_mul (((ℓ : ℂ) / 2) * (ℓ : ℂ) ^ m)
  have he : (fun β => ((ℓ : ℂ) / 2) * (ℓ : ℂ) ^ m * Dk m (β * dvar ℓ s))
      =ᶠ[𝓝 0] (fun β => iteratedDeriv m (Gclock ℓ β) s) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with β hβ
    exact (Gclock_iteratedDeriv hℓ (le_of_lt (by simpa using hβ)) m hs).symm
  exact (hf.congr_of_eventuallyEq he.symm).congr_deriv (by simp only [pow_succ]; ring)

theorem clockCoeff_hasDerivAt_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    HasDerivAt
      (fun β => toeplitzCoeff (-3) (jets (Gclock ℓ β) (-1)) (k + 1))
      ((ℓ : ℂ) * dvar ℓ (-1) * primeCoeffSymbol (-3) k ℓ) 0 := by
  have hs : (-1 : ℂ).re < 1 / 2 := by norm_num
  have hterm : ∀ i ∈ range (k + 1), HasDerivAt
      (fun β => (k.choose i : ℂ) * (-3) ^ (k - i) * (-1) ^ i *
        jets (Gclock ℓ β) (-1) (k + 2 - i))
      ((ℓ : ℂ) * dvar ℓ (-1) * ((k.choose i : ℂ) * (-3) ^ (k - i) * (-1) ^ i *
        ((-1) ^ (k + 1 - i) / ((k + 1 - i).factorial : ℂ) *
          (ℓ : ℂ) ^ (k + 1 - i)))) 0 := by
    intro i hi
    have hi' : i ≤ k := by simpa only [mem_range, Nat.lt_succ_iff] using hi
    rw [show k + 2 - i = (k + 1 - i) + 1 by omega]
    simp only [jets]
    have h := ((iteratedDeriv_Gclock_hasDerivAt_zero hℓ hs (k + 1 - i)).const_mul
      ((-1 : ℂ) ^ (k + 1 - i) / ((k + 1 - i).factorial : ℂ))).const_mul
      ((k.choose i : ℂ) * (-3) ^ (k - i) * (-1) ^ i)
    exact h.congr_deriv (by rw [pow_succ]; ring)
  have h := HasDerivAt.fun_sum hterm
  simpa only [toeplitzCoeff, primeCoeffSymbol, Finset.mul_sum] using h

theorem clockCoeff_norm_le_mass {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ}
    (hs : s.re < 1 / 2) (k : ℕ) :
    ‖toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (clockJet θ ℓ s) k‖ ≤
      ∑' n : ℤ, tickWeight θ ℓ s n := by
  have hw : ∀ n, ‖transport s (tick θ ℓ n)‖ = 1 := fun n =>
    transport_line_norm (tick_re θ hℓ n) (sub_tick_ne_zero hℓ hs n)
  rw [clock_toeplitzCoeff hℓ hs, atomCoeff]
  calc
    ‖∑' n : ℤ, (tickWeight θ ℓ s n : ℂ) * transport s (tick θ ℓ n) ^ (k : ℤ)‖
        ≤ ∑' n : ℤ, ‖(tickWeight θ ℓ s n : ℂ) *
          transport s (tick θ ℓ n) ^ (k : ℤ)‖ :=
      norm_tsum_le_tsum_norm (summable_atom (summable_tickWeight θ hℓ s) hw _).norm
    _ = ∑' n : ℤ, tickWeight θ ℓ s n := by
      apply tsum_congr
      intro n
      rw [norm_mul, norm_zpow, hw, one_zpow, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (tickWeight_nonneg θ ℓ s n)]

theorem clockCoeff_circle_norm_le {ℓ : ℝ} (hℓ : 0 < ℓ) {β : ℂ}
    (hβ : ‖β‖ = 1) (k : ℕ) :
    ‖toeplitzCoeff (-3) (jets (Gclock ℓ β) (-1)) (k + 1)‖ ≤
      ℓ / 3 * ((1 + ‖dvar ℓ (-1)‖) / (1 - ‖dvar ℓ (-1)‖)) := by
  have hs : (-1 : ℂ).re < 1 / 2 := by norm_num
  have hβ' : β = Complex.exp (-(I * ((-Complex.arg β : ℝ) : ℂ))) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I β]
    rw [hβ, Complex.ofReal_one, one_mul]
    congr 1
    push_cast
    ring
  have hj := jets_clockS_eq hℓ hs (θ := -Complex.arg β)
  rw [← hβ'] at hj
  have hc := clockCoeff_norm_le_mass (θ := -Complex.arg β) hℓ hs (k + 1)
  rw [clockJet_eq_jets hℓ hs, hj, toeplitzCoeff_neg, norm_neg] at hc
  norm_num only [Complex.neg_re, Complex.one_re, Complex.ofReal_neg,
    Complex.ofReal_ofNat] at hc
  have hm := clockS_re_logDeriv (θ := -Complex.arg β) hℓ hs
  rw [clockS_logDeriv_eq_Gclock hℓ hs, ← hβ', Complex.neg_re] at hm
  norm_num only [Complex.neg_re, Complex.one_re] at hm
  have hr := norm_dvar_lt_one hℓ hs
  have hx : ‖β * dvar ℓ (-1)‖ = ‖dvar ℓ (-1)‖ := by rw [norm_mul, hβ, one_mul]
  have hkerb : ‖hker (β * dvar ℓ (-1))‖ ≤
      (1 + ‖dvar ℓ (-1)‖) / (1 - ‖dvar ℓ (-1)‖) := by
    unfold hker
    rw [norm_div]
    refine div_le_div₀ (by positivity) ?_ (by linarith) ?_
    · simpa only [norm_one, hx] using norm_add_le (1 : ℂ) (β * dvar ℓ (-1))
    · simpa only [norm_one, hx] using norm_sub_norm_le (1 : ℂ) (β * dvar ℓ (-1))
  have hg : ‖Gclock ℓ β (-1)‖ ≤ ℓ / 2 *
      ((1 + ‖dvar ℓ (-1)‖) / (1 - ‖dvar ℓ (-1)‖)) := by
    rw [Gclock, norm_mul, norm_div]
    norm_num only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ, norm_ofNat]
    exact mul_le_mul_of_nonneg_left hkerb (by positivity)
  have hre := Complex.re_le_norm (Gclock ℓ β (-1))
  calc
    _ ≤ ∑' n : ℤ, tickWeight (-Complex.arg β) ℓ (-1) n := hc
    _ ≤ ℓ / 3 * ((1 + ‖dvar ℓ (-1)‖) / (1 - ‖dvar ℓ (-1)‖)) := by
      linarith

set_option maxHeartbeats 800000 in
theorem primeCoeffSymbol_weighted_uniform_bound {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    ℓ * ‖dvar ℓ (-1)‖ * ‖primeCoeffSymbol (-3) k ℓ‖ ≤
      ℓ / 3 * ((1 + ‖dvar ℓ (-1)‖) / (1 - ‖dvar ℓ (-1)‖)) := by
  have hs : (-1 : ℂ).re < 1 / 2 := by norm_num
  have hd := toeplitzCoeff_jets_differentiableOn hℓ hs (k := k + 1) (by omega)
  norm_num only [Complex.neg_re, Complex.one_re, Complex.ofReal_neg,
    Complex.ofReal_ofNat] at hd
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1) (hd.diffContOnCl_ball Set.Subset.rfl)
    (fun β hβ => clockCoeff_circle_norm_le hℓ (by simpa using hβ) k)
  rw [(clockCoeff_hasDerivAt_zero hℓ k).deriv] at h
  simpa only [div_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ] using h

theorem norm_dvar_neg_one (ℓ : ℝ) : ‖dvar ℓ (-1)‖ = Real.exp (-3 * ℓ / 2) := by
  rw [dvar, Complex.norm_exp]
  congr 1
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.one_re, zero_mul, sub_zero]
  ring

/-- One explicit constant controls every degree of a single prime symbol. -/
theorem primeCoeffSymbol_uniform_in_degree {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    ‖primeCoeffSymbol (-3) k ℓ‖ ≤
      (1 + Real.exp (-3 * ℓ / 2)) /
        (3 * Real.exp (-3 * ℓ / 2) * (1 - Real.exp (-3 * ℓ / 2))) := by
  have h := primeCoeffSymbol_weighted_uniform_bound hℓ k
  rw [norm_dvar_neg_one] at h
  have hr := Real.exp_pos (-3 * ℓ / 2)
  have hr1 : Real.exp (-3 * ℓ / 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  calc
    _ ≤ (ℓ / 3 * ((1 + Real.exp (-3 * ℓ / 2)) / (1 - Real.exp (-3 * ℓ / 2)))) /
        (ℓ * Real.exp (-3 * ℓ / 2)) :=
      (le_div_iff₀ (mul_pos hℓ hr)).mpr (by nlinarith [h])
    _ = _ := by field_simp

theorem primeCoeffSymbol_norm_le_exp {ℓ : ℝ} (hℓ : Real.log 2 ≤ ℓ) (k : ℕ) :
    ‖primeCoeffSymbol (-3) k ℓ‖ ≤ Real.exp (3 * ℓ / 2) := by
  have hℓ0 : 0 < ℓ := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hℓ
  have hr := Real.exp_pos (-3 * ℓ / 2)
  have hrhalf : Real.exp (-3 * ℓ / 2) ≤ 1 / 2 := by
    calc
      _ ≤ Real.exp (-ℓ) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / Real.exp ℓ := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / Real.exp (Real.log 2) :=
        one_div_le_one_div_of_le (Real.exp_pos _) (Real.exp_le_exp.mpr hℓ)
      _ = 1 / 2 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hd : 0 < 3 * Real.exp (-3 * ℓ / 2) * (1 - Real.exp (-3 * ℓ / 2)) :=
    mul_pos (mul_pos (by norm_num) hr) (by linarith)
  calc
    _ ≤ (1 + Real.exp (-3 * ℓ / 2)) /
        (3 * Real.exp (-3 * ℓ / 2) * (1 - Real.exp (-3 * ℓ / 2))) :=
      primeCoeffSymbol_uniform_in_degree hℓ0 k
    _ ≤ 1 / Real.exp (-3 * ℓ / 2) := by
      apply (div_le_div_iff₀ hd hr).mpr
      nlinarith
    _ = Real.exp (3 * ℓ / 2) := by
      rw [show -3 * ℓ / 2 = -(3 * ℓ / 2) by ring, Real.exp_neg, one_div, inv_inv]

theorem primeCoeffSymbol_log_norm_le {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    ‖primeCoeffSymbol (-3) k (Real.log n)‖ ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  calc
    _ ≤ Real.exp (3 * Real.log n / 2) := primeCoeffSymbol_norm_le_exp hlog k
    _ = _ := by rw [Real.rpow_def_of_pos hn0]; congr 1; ring

theorem primeCoeffSymbol_weighted_log_norm_le {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    ‖(((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * primeCoeffSymbol (-3) k (Real.log n)‖ ≤
      (n : ℝ) ^ (-1 / 2 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
  calc
    _ ≤ (n : ℝ) ^ (-2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (primeCoeffSymbol_log_norm_le hn k)
        (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; norm_num

#print axioms Dk_hasDerivAt_zero
#print axioms clockCoeff_hasDerivAt_zero
#print axioms primeCoeffSymbol_norm_le_exp
#print axioms primeCoeffSymbol_weighted_log_norm_le
#print axioms cayley_exp_norm_le

end CriticalLinePhasor.SeatingLedger
