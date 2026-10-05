import RequestProject.XiJetsArithmetic

/-!
# Prime-symbol phase clock and its first indefinite degree pair

Unfolded target: take `Re Σ conj(r_j) r_k jetValueP s d M j k`. Subtract the same
functional of the pole/Gamma jets. Collect the absolutely convergent remaining
series in `n`, with factor `Λ(n) n^(-σ) exp(-iγ log n)` and a finite quadratic
polynomial in `log n`. The paired first-order coefficient remains explicit.

Search commands used before construction:
`rg -n 'online_of_prime_jets_nonneg|hermForm_eq_hankel|primeJetsForm|primeSymbol|def pf' RequestProject`
`rg -n -i 'prime_?symbol|prime_?jets_?form|hockey.?stick|hankel|pascal|prime_?jet|herm_?form_?eq' --glob '*.lean' .`
`rg -n -i 'pf_fst|pf_snd|pf.*closed|closed.*pf|partial.?fraction|choose_succ_succ|choose_pos|sum_range_add_choose' RequestProject .lake/packages/mathlib/Mathlib`
`rg -n 'logMul|LSeriesSummable.*log|term_def|term_of_ne_zero|re_tsum|conj_tsum' .lake/packages/mathlib/Mathlib`
Semantic searches: LeanSearch finite/infinite sum interchange; Loogle `Nat.choose, _ + _`.

Protocol: absent prior expectations, compute coefficients and test degree (1,2).
Coefficient strategies: `induction j generalizing k a` (Pascal), and
`rw [Nat.sum_range_add_choose]` (cumulative hockey stick).
Collection strategies: `apply HasSum.add` (linearity), and
`rw [Summable.tsum_finsetSum]` (finite/infinite interchange).
-/

open Complex Finset
open LSeries

noncomputable section

namespace CriticalLinePhasor.ContourArgument.PrimeClock

theorem pf_fst_closed (d : ℂ) (j k a : ℕ) :
    (pf d (j + 1) (k + 1)).1 (a + 1) =
      if a ≤ j then
        ((j + k - a).choose k : ℂ) * d⁻¹ ^ (j + k + 1 - a)
      else 0 := by
  induction j generalizing k a with
  | zero =>
    induction k with
    | zero =>
      by_cases ha : a = 0
      · subst a
        simp [pf_succ, pf_zero_right, pf_zero_left]
      · simp [pf_succ, pf_zero_right, pf_zero_left, ha]
    | succ k ih =>
      rw [pf_succ]
      dsimp only
      rw [ih, pf_zero_left]
      by_cases ha : a = 0
      · subst a
        simp [pow_succ, mul_comm]
      · simp [show ¬ a ≤ 0 by omega]
  | succ j ih =>
    induction k with
    | zero =>
      rw [pf_succ]
      dsimp only
      rw [pf_zero_right, ih]
      by_cases ha : a ≤ j
      · have hne : a + 1 ≠ j + 1 + 1 := by omega
        simp only [hne, ↓reduceIte, ha, zero_add, Nat.choose_zero_right,
          Nat.cast_one, one_mul, show a ≤ j + 1 by omega]
        rw [show j + 1 + 1 - a = (j + 1 - a) + 1 by omega, pow_succ]
        simp [mul_comm]
      · by_cases he : a = j + 1
        · subst a
          simp
        · simp [ha, he, show ¬ a ≤ j + 1 by omega]
    | succ k ihk =>
      rw [pf_succ]
      dsimp only
      rw [ihk, ih]
      by_cases ha : a ≤ j
      · simp only [ha, show a ≤ j + 1 by omega, ↓reduceIte]
        rw [show j + 1 + (k + 1) - a = (j + k + 1 - a) + 1 by omega,
          Nat.choose_succ_succ, Nat.cast_add]
        rw [show j + 1 + k - a = j + k + 1 - a by omega,
          show j + (k + 1) - a = j + k + 1 - a by omega]
        rw [show j + 1 + (k + 1) + 1 - a = (j + k + 2 - a) + 1 by omega,
          show j + 1 + k + 1 - a = j + k + 2 - a by omega,
          show j + (k + 1) + 1 - a = j + k + 2 - a by omega, pow_succ]
        simp only [one_div]
        ring
      · by_cases he : a = j + 1
        · subst a
          simp only [le_refl, ↓reduceIte, ha, Nat.add_sub_cancel_left,
            Nat.choose_self, Nat.cast_one, one_mul, add_zero]
          rw [show j + 1 + k + 1 - (j + 1) = k + 1 by omega,
            show j + 1 + (k + 1) + 1 - (j + 1) = (k + 1) + 1 by omega, pow_succ]
          simp [pow_succ, mul_comm]
        · simp [ha, show ¬ a ≤ j + 1 by omega]

theorem pf_swap (d : ℂ) (n : ℕ) :
    ∀ j k, j + k = n → 0 < j + k → ∀ a, (pf d j k).2 a = (pf d k j).1 a := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro j k hn hpos a
    cases k with
    | zero =>
      cases j with
      | zero => omega
      | succ j => simp [pf_zero_right, pf_zero_left]
    | succ k =>
      cases j with
      | zero => simp [pf_zero_right, pf_zero_left]
      | succ j =>
        rw [pf_succ, pf_succ]
        dsimp only
        rw [ih (j + 1 + k) (by omega) (j + 1) k rfl (by omega),
          ih (j + (k + 1)) (by omega) j (k + 1) rfl (by omega)]
        ring

def closedCoeff (d : ℂ) : ℕ → ℕ → ℕ → ℂ
  | j, 0, a => if a = j then 1 else 0
  | 0, _ + 1, _ => 0
  | _ + 1, _ + 1, 0 => 0
  | j + 1, k + 1, a + 1 =>
      if a ≤ j then ((j + k - a).choose k : ℂ) * d⁻¹ ^ (j + k + 1 - a) else 0

theorem pf_fst_eq_closedCoeff (d : ℂ) (j k a : ℕ) :
    (pf d j k).1 a = closedCoeff d j k a := by
  cases k with
  | zero => simp [pf_zero_right, closedCoeff]
  | succ k =>
    cases j with
    | zero => simp [pf_zero_left, closedCoeff]
    | succ j =>
      cases a with
      | zero => exact (pf_index_zero d _ (j + 1) (k + 1) rfl (by omega)).1
      | succ a => exact pf_fst_closed d j k a

theorem pf_snd_eq_closedCoeff (d : ℂ) (j k a : ℕ) :
    (pf d j k).2 a = if j + k = 0 then 0 else closedCoeff d k j a := by
  by_cases h : j + k = 0
  · have hj : j = 0 := by omega
    have hk : k = 0 := by omega
    subst j k
    simp [pf_zero_right]
  · rw [if_neg h, pf_swap d (j + k) j k rfl (by omega), pf_fst_eq_closedCoeff]

theorem pascal_coeff_pos {d : ℝ} (hd : 0 < d) (j k a : ℕ) (ha : a ≤ j) :
    0 < (((j + k - a).choose k : ℝ) * d⁻¹ ^ (j + k + 1 - a)) := by
  have hc : 0 < (j + k - a).choose k := Nat.choose_pos (by omega)
  positivity

def pairFunctional (d : ℂ) (M j k : ℕ) (z : ℕ → ℂ) : ℂ :=
  (pf d j k).1 1 * (z 0 + (starRingEnd ℂ) (z 0))
    + ∑ i ∈ range (M - 1), (pf d j k).1 (i + 2) * z (i + 1)
    + ∑ i ∈ range (M - 1),
        (pf d j k).2 (i + 2) * (starRingEnd ℂ) (z (i + 1))

def momentForm (R : Polynomial ℂ) (d : ℂ) (z : ℕ → ℂ) : ℝ :=
  (∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
    ((starRingEnd ℂ) (R.coeff j) * R.coeff k) *
      pairFunctional d (2 * R.natDegree + 2) j k z).re

def primeMoment (s : ℂ) : ℕ → ℂ
  | 0 => primeLogDeriv s
  | m + 1 => primeJet s (m + 1) / ((-1) ^ (m + 1) * ((m + 1).factorial : ℂ))

def dcMoment (s : ℂ) : ℕ → ℂ
  | 0 => 1 / s + 1 / (s - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2
      + logDeriv Complex.Gamma (s / 2) / 2
  | m + 1 => s ^ (-1 - (m + 1) : ℤ) + (s - 1) ^ (-1 - (m + 1) : ℤ)
      + iteratedDeriv (m + 1) (fun z : ℂ => logDeriv Complex.Gamma (z / 2) / 2) s
          / ((-1) ^ (m + 1) * ((m + 1).factorial : ℂ))

def primeJetsForm (R : Polynomial ℂ) (s d : ℂ) : ℝ :=
  (∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
    ((starRingEnd ℂ) (R.coeff j) * R.coeff k) *
      jetValueP s d (2 * R.natDegree + 2) j k).re

def dcForm (R : Polynomial ℂ) (s d : ℂ) : ℝ := momentForm R d (dcMoment s)

def logWeight (ℓ : ℝ) (m : ℕ) : ℂ := (ℓ : ℂ) ^ m / (m.factorial : ℂ)

def leftSymbol (d : ℂ) (M j k : ℕ) (ℓ : ℝ) : ℂ :=
  (pf d j k).1 1 +
    ∑ i ∈ range (M - 1), (pf d j k).1 (i + 2) * logWeight ℓ (i + 1)

/-- Both first-order terms use the already paired coefficient `a₁`. -/
def rightSymbol (d : ℂ) (M j k : ℕ) (ℓ : ℝ) : ℂ :=
  (pf d j k).1 1 +
    ∑ i ∈ range (M - 1), (pf d j k).2 (i + 2) * logWeight ℓ (i + 1)

def pairSymbol (C d : ℂ) (M j k : ℕ) (ℓ : ℝ) : ℂ :=
  -(C * leftSymbol d M j k ℓ + (starRingEnd ℂ) (C * rightSymbol d M j k ℓ))

def primeSymbol (R : Polynomial ℂ) (d ℓ : ℝ) : ℂ :=
  ∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
    pairSymbol ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
      (d : ℂ) (2 * R.natDegree + 2) j k ℓ

theorem primeMoment_eq_dc_sub (s : ℂ) (m : ℕ) :
    primeMoment s m = dcMoment s m -
      LSeries (logMul^[m] (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))) s
        / (m.factorial : ℂ) := by
  cases m with
  | zero => simp [primeMoment, dcMoment, primeLogDeriv]
  | succ m =>
    unfold primeMoment dcMoment primeJet
    have hf : ((m + 1).factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hp : (-1 : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast
    field_simp

theorem pairFunctional_primeMoment (s d : ℂ) (M j k : ℕ) :
    pairFunctional d M j k (primeMoment s) = jetValueP s d M j k := by
  unfold pairFunctional jetValueP
  simp only [primeMoment, Complex.add_conj, Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp only [map_div₀, map_mul, map_pow, map_neg, map_one, map_natCast]
  have hp : (-1 : ℂ) ^ (i + 1) * (-1 : ℂ) ^ (i + 1) = 1 := by
    rw [← mul_pow]
    simp
  have hf : ((i + 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hp0 : (-1 : ℂ) ^ (i + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  linear_combination -(starRingEnd ℂ) (primeJet s (i + 1)) * hp

theorem primeJetsForm_eq_momentForm (R : Polynomial ℂ) (s d : ℂ) :
    primeJetsForm R s d = momentForm R d (primeMoment s) := by
  simp only [primeJetsForm, momentForm, pairFunctional_primeMoment]

theorem pairFunctional_sub (d : ℂ) (M j k : ℕ) (z w : ℕ → ℂ) :
    pairFunctional d M j k (fun m => z m - w m) =
      pairFunctional d M j k z - pairFunctional d M j k w := by
  simp only [pairFunctional, map_sub, mul_sub, Finset.sum_sub_distrib]
  ring

theorem momentForm_sub (R : Polynomial ℂ) (d : ℂ) (z w : ℕ → ℂ) :
    momentForm R d (fun m => z m - w m) = momentForm R d z - momentForm R d w := by
  simp only [momentForm, pairFunctional_sub, mul_sub, Finset.sum_sub_distrib, Complex.sub_re]

theorem logWeight_conj (ℓ : ℝ) (m : ℕ) :
    (starRingEnd ℂ) (logWeight ℓ m) = logWeight ℓ m := by
  simp [logWeight]

theorem pairFunctional_phase (d q : ℂ) (M j k : ℕ) (ℓ : ℝ) :
    pairFunctional d M j k (fun m => q * logWeight ℓ m) =
      q * leftSymbol d M j k ℓ + (starRingEnd ℂ) q * rightSymbol d M j k ℓ := by
  simp only [pairFunctional, leftSymbol, rightSymbol, map_mul, logWeight_conj]
  simp only [logWeight, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one,
    mul_add, Finset.mul_sum]
  simp only [mul_left_comm]
  ring

theorem pairSymbol_apply (C d q : ℂ) (M j k : ℕ) (ℓ : ℝ) :
    (q * pairSymbol C d M j k ℓ).re =
      -(C * pairFunctional d M j k (fun m => q * logWeight ℓ m)).re := by
  rw [pairFunctional_phase]
  simp only [pairSymbol, mul_neg, Complex.neg_re]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem primeSymbol_apply (R : Polynomial ℂ) (d ℓ : ℝ) (q : ℂ) :
    (q * primeSymbol R d ℓ).re =
      -momentForm R (d : ℂ) (fun m => q * logWeight ℓ m) := by
  simp only [primeSymbol, Finset.mul_sum, Complex.re_sum, pairSymbol_apply,
    momentForm, Finset.sum_neg_distrib]

/-- Closed form: a finite quadratic polynomial with explicit Pascal coefficients. -/
theorem primeSymbol_closed (R : Polynomial ℂ) (d ℓ : ℝ) :
    primeSymbol R d ℓ =
      ∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
        -(((starRingEnd ℂ) (R.coeff j) * R.coeff k) *
          (closedCoeff (d : ℂ) j k 1 +
            ∑ i ∈ range (2 * R.natDegree + 1),
              closedCoeff (d : ℂ) j k (i + 2) * logWeight ℓ (i + 1)) +
          (starRingEnd ℂ) (((starRingEnd ℂ) (R.coeff j) * R.coeff k) *
            (closedCoeff (d : ℂ) j k 1 +
              ∑ i ∈ range (2 * R.natDegree + 1),
                (if j + k = 0 then 0 else closedCoeff (d : ℂ) k j (i + 2)) *
                  logWeight ℓ (i + 1)))) := by
  simp only [primeSymbol, pairSymbol, leftSymbol, rightSymbol,
    pf_fst_eq_closedCoeff, pf_snd_eq_closedCoeff,
    show 2 * R.natDegree + 2 - 1 = 2 * R.natDegree + 1 by omega]

theorem pairFunctional_hasSum {f : ℕ → ℕ → ℂ} {z : ℕ → ℂ}
    (h : ∀ m, HasSum (fun n => f n m) (z m)) (d : ℂ) (M j k : ℕ) :
    HasSum (fun n => pairFunctional d M j k (f n)) (pairFunctional d M j k z) := by
  exact (((h 0).add (Complex.hasSum_conj'.mpr (h 0))).mul_left _).add
    (hasSum_sum (fun i _ => (h (i + 1)).mul_left _)) |>.add
      (hasSum_sum (fun i _ => (Complex.hasSum_conj'.mpr (h (i + 1))).mul_left _))

theorem momentForm_hasSum {f : ℕ → ℕ → ℂ} {z : ℕ → ℂ}
    (h : ∀ m, HasSum (fun n => f n m) (z m)) (R : Polynomial ℂ) (d : ℂ) :
    HasSum (fun n => momentForm R d (f n)) (momentForm R d z) := by
  apply Complex.hasSum_re
  exact hasSum_sum (fun j _ => hasSum_sum (fun k _ =>
    (pairFunctional_hasSum h d (2 * R.natDegree + 2) j k).mul_left _))

def mangoldt (n : ℕ) : ℂ := ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)

theorem logMul_iterate_term (s : ℂ) (m n : ℕ) :
    LSeries.term (logMul^[m] mangoldt) s n =
      (Real.log n : ℂ) ^ m * LSeries.term mangoldt s n := by
  have hi (f : ℕ → ℂ) (m : ℕ) :
      (logMul^[m] f) n = (Complex.log n) ^ m * f n := by
    induction m generalizing f with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply, ih]
      simp only [logMul, pow_succ]
      ring
  have hl : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  unfold LSeries.term
  split_ifs
  · simp
  · rw [hi, hl]
    ring

theorem primeMoment_hasSum {s : ℂ} (hs : 1 < s.re) (m : ℕ) :
    HasSum (fun n => LSeries.term mangoldt s n * logWeight (Real.log n) m)
      (LSeries (logMul^[m] mangoldt) s / (m.factorial : ℂ)) := by
  have h : LSeriesSummable (logMul^[m] mangoldt) s := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    rw [LSeries.absicssaOfAbsConv_logPowMul]
    exact lt_of_le_of_lt abscissa_vonMangoldt_le_one (by exact_mod_cast hs)
  have he : (fun n => LSeries.term mangoldt s n * logWeight (Real.log n) m) =
      (fun n => LSeries.term (logMul^[m] mangoldt) s n / (m.factorial : ℂ)) := by
    funext n
    rw [logMul_iterate_term]
    simp only [logWeight]
    ring
  rw [he]
  exact h.hasSum.div_const (m.factorial : ℂ)

theorem primeSymbol_hasSum (R : Polynomial ℂ) (d : ℝ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n => (LSeries.term mangoldt s n * primeSymbol R d (Real.log n)).re)
      (-momentForm R (d : ℂ) (fun m =>
        LSeries (logMul^[m] mangoldt) s / (m.factorial : ℂ))) := by
  simpa only [primeSymbol_apply] using
    (momentForm_hasSum (primeMoment_hasSum hs) R (d : ℂ)).neg

theorem primeJetsForm_eq_dc_add_series (R : Polynomial ℂ) (d : ℝ)
    {s : ℂ} (hs : 1 < s.re) :
    primeJetsForm R s (d : ℂ) = dcForm R s (d : ℂ) +
      ∑' n, (LSeries.term mangoldt s n * primeSymbol R d (Real.log n)).re := by
  rw [(primeSymbol_hasSum R d hs).tsum_eq, primeJetsForm_eq_momentForm]
  have hm : primeMoment s = fun m => dcMoment s m -
      LSeries (logMul^[m] mangoldt) s / (m.factorial : ℂ) := by
    funext m
    exact primeMoment_eq_dc_sub s m
  rw [hm, momentForm_sub]
  rfl

def phase (γ ℓ : ℝ) : ℂ := Complex.exp (-I * (γ : ℂ) * (ℓ : ℂ))

theorem term_eq_weight_phase (σ γ : ℝ) (n : ℕ) :
    LSeries.term mangoldt ((σ : ℂ) + (γ : ℂ) * I) n =
      ((ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        phase γ (Real.log n) := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hnC,
      ← Complex.natCast_log]
    rw [Real.rpow_def_of_pos hnR, Complex.ofReal_mul, Complex.ofReal_exp]
    simp only [mangoldt, div_eq_mul_inv, ← Complex.exp_neg, phase]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

theorem primeJetsForm_eq_dc_add_phase (R : Polynomial ℂ) (d σ γ : ℝ) (hσ : 1 < σ) :
    primeJetsForm R ((σ : ℂ) + (γ : ℂ) * I) (d : ℂ) =
      dcForm R ((σ : ℂ) + (γ : ℂ) * I) (d : ℂ) +
        ∑' n, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) *
          (phase γ (Real.log n) * primeSymbol R d (Real.log n)).re := by
  rw [primeJetsForm_eq_dc_add_series R d (by simpa using hσ)]
  congr 1
  apply tsum_congr
  intro n
  rw [term_eq_weight_phase]
  simp [mul_assoc]

theorem phase_prime_power (γ : ℝ) (p k : ℕ) :
    phase γ (Real.log ((p ^ k : ℕ) : ℝ)) = phase γ (Real.log p) ^ k := by
  rw [Nat.cast_pow, Real.log_pow]
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem primeSymbol_minor12 (d ℓ : ℝ) (hd : d ≠ 0) :
    (-2 / d) * (-4 / d ^ 3 - 2 * ℓ / d ^ 2)
      - (-2 / d ^ 2 - ℓ / d) ^ 2 = (4 - (d * ℓ) ^ 2) / d ^ 4 := by
  field_simp
  ring

theorem primeSymbol_minor12_neg {d ℓ : ℝ} (hd : 0 < d) (hℓ : 2 < d * ℓ) :
    (-2 / d) * (-4 / d ^ 3 - 2 * ℓ / d ^ 2)
      - (-2 / d ^ 2 - ℓ / d) ^ 2 < 0 := by
  rw [primeSymbol_minor12 d ℓ hd.ne']
  apply div_neg_of_neg_of_pos
  · nlinarith
  · positivity

theorem primeSymbol_quadratic_complete_square (d ℓ u v : ℝ) (hd : d ≠ 0) :
    -2 / d * u ^ 2 + 2 * (-2 / d ^ 2 - ℓ / d) * u * v
      + (-4 / d ^ 3 - 2 * ℓ / d ^ 2) * v ^ 2 =
    -2 / d * (u + (1 / d + ℓ / 2) * v) ^ 2
      + ((d * ℓ) ^ 2 - 4) / (2 * d ^ 3) * v ^ 2 := by
  field_simp
  ring

theorem pairSymbol_entries12 (d ℓ : ℝ) (hd : d ≠ 0) :
    pairSymbol 1 (d : ℂ) 6 1 1 ℓ = ((-2 / d : ℝ) : ℂ) ∧
    pairSymbol 1 (d : ℂ) 6 1 2 ℓ = ((-2 / d ^ 2 - ℓ / d : ℝ) : ℂ) ∧
    pairSymbol 1 (d : ℂ) 6 2 1 ℓ = ((-2 / d ^ 2 - ℓ / d : ℝ) : ℂ) ∧
    pairSymbol 1 (d : ℂ) 6 2 2 ℓ = ((-4 / d ^ 3 - 2 * ℓ / d ^ 2 : ℝ) : ℂ) := by
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  norm_num [pairSymbol, leftSymbol, rightSymbol, logWeight, pf_succ,
    pf_zero_right, pf_zero_left, Finset.sum_range_succ]
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  constructor <;> field_simp <;> ring

theorem primeSymbol_actual_minor12_neg {d ℓ : ℝ} (hd : 0 < d) (hℓ : 2 < d * ℓ) :
    (pairSymbol 1 (d : ℂ) 6 1 1 ℓ).re * (pairSymbol 1 (d : ℂ) 6 2 2 ℓ).re
      - (pairSymbol 1 (d : ℂ) 6 1 2 ℓ).re * (pairSymbol 1 (d : ℂ) 6 2 1 ℓ).re < 0 := by
  obtain ⟨h11, h12, h21, h22⟩ := pairSymbol_entries12 d ℓ hd.ne'
  rw [h11, h12, h21, h22]
  simpa only [Complex.ofReal_re, pow_two] using primeSymbol_minor12_neg hd hℓ

def quadraticSymbol (u v d ℓ : ℝ) : ℝ :=
  (pairSymbol ((u : ℂ) * u) (d : ℂ) 6 1 1 ℓ +
    pairSymbol ((u : ℂ) * v) (d : ℂ) 6 1 2 ℓ +
    pairSymbol ((v : ℂ) * u) (d : ℂ) 6 2 1 ℓ +
    pairSymbol ((v : ℂ) * v) (d : ℂ) 6 2 2 ℓ).re

theorem pairSymbol_real_mul (c : ℝ) (d : ℂ) (M j k : ℕ) (ℓ : ℝ) :
    pairSymbol (c : ℂ) d M j k ℓ = (c : ℂ) * pairSymbol 1 d M j k ℓ := by
  simp only [pairSymbol, map_mul, Complex.conj_ofReal, one_mul]
  ring

theorem quadraticSymbol_eq (u v d ℓ : ℝ) (hd : d ≠ 0) :
    quadraticSymbol u v d ℓ =
      -2 / d * u ^ 2 + 2 * (-2 / d ^ 2 - ℓ / d) * u * v
        + (-4 / d ^ 3 - 2 * ℓ / d ^ 2) * v ^ 2 := by
  obtain ⟨h11, h12, h21, h22⟩ := pairSymbol_entries12 d ℓ hd
  simp only [quadraticSymbol, ← Complex.ofReal_mul, pairSymbol_real_mul, h11, h12, h21,
    h22, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
  ring

theorem primeSymbol_degree_two (R : Polynomial ℂ) (u v d ℓ : ℝ)
    (hdeg : R.natDegree = 2) (h0 : R.coeff 0 = 0)
    (h1 : R.coeff 1 = (u : ℂ)) (h2 : R.coeff 2 = (v : ℂ)) :
    (primeSymbol R d ℓ).re = quadraticSymbol u v d ℓ := by
  simp [primeSymbol, hdeg, Finset.sum_range_succ, h0, h1, h2,
    quadraticSymbol, pairSymbol]
  ring

theorem quadraticSymbol_indefinite {d ℓ : ℝ} (hd : 0 < d) (hℓ : 2 < d * ℓ) :
    quadraticSymbol 1 0 d ℓ < 0 ∧
      0 < quadraticSymbol (-(1 / d + ℓ / 2)) 1 d ℓ := by
  constructor
  · rw [quadraticSymbol_eq _ _ _ _ hd.ne']
    simp only [one_pow, mul_one, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    exact div_neg_of_neg_of_pos (by norm_num) hd
  · rw [quadraticSymbol_eq _ _ _ _ hd.ne',
      primeSymbol_quadratic_complete_square _ _ _ _ hd.ne']
    simp only [mul_one, neg_add_cancel, zero_pow (by decide : 2 ≠ 0), mul_zero,
      one_pow, zero_add]
    apply div_pos
    · nlinarith
    · positivity

theorem quadraticSymbol_not_scalar_square {d ℓ : ℝ} (hd : 0 < d) (hℓ : 2 < d * ℓ) :
    ¬ ∃ (c : ℝ) (P : ℝ → ℝ → ℂ),
      ∀ u v, quadraticSymbol u v d ℓ = c * Complex.normSq (P u v) := by
  obtain ⟨hneg, hpos⟩ := quadraticSymbol_indefinite hd hℓ
  rintro ⟨c, P, hP⟩
  rcases le_total 0 c with hc | hc
  · have h := mul_nonneg hc (Complex.normSq_nonneg (P 1 0))
    rw [← hP] at h
    linarith
  · have h := mul_nonpos_of_nonpos_of_nonneg hc
      (Complex.normSq_nonneg (P (-(1 / d + ℓ / 2)) 1))
    rw [← hP] at h
    linarith

theorem primeSymbol_minor_at_eight {d : ℝ} (hd : 1 < d) :
    (pairSymbol 1 (d : ℂ) 6 1 1 (Real.log 8)).re *
        (pairSymbol 1 (d : ℂ) 6 2 2 (Real.log 8)).re -
      (pairSymbol 1 (d : ℂ) 6 1 2 (Real.log 8)).re *
        (pairSymbol 1 (d : ℂ) 6 2 1 (Real.log 8)).re < 0 := by
  apply primeSymbol_actual_minor12_neg (by linarith)
  have hlog : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
  have h8 : (2 : ℝ) < Real.log 8 := by
    rw [hlog]
    linarith [Real.log_two_gt_d9]
  nlinarith

#print axioms pf_fst_closed
#print axioms primeJetsForm_eq_dc_add_series
#print axioms primeJetsForm_eq_dc_add_phase
#print axioms primeSymbol_closed
#print axioms phase_prime_power
#print axioms primeSymbol_minor12_neg
#print axioms primeSymbol_actual_minor12_neg
#print axioms quadraticSymbol_indefinite
#print axioms quadraticSymbol_not_scalar_square
#print axioms primeSymbol_minor_at_eight
#print axioms CriticalLinePhasor.ContourArgument.pf_identity
#print axioms CriticalLinePhasor.ContourArgument.xi_jet_arith
#print axioms CriticalLinePhasor.ContourArgument.online_of_prime_jets_nonneg

end CriticalLinePhasor.ContourArgument.PrimeClock
