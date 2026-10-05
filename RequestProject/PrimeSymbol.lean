import Mathlib
import RequestProject.XiJetsArithmetic

/-!
# The prime symbol: the door collected by `n` (ledger 596)

`online_of_prime_jets_nonneg` (595) writes the door's hypothesis as a finite functional of jets. Collecting
the prime side by `n` instead of by derivative order gives the normal form

  `primeJetsForm R s = dcForm R s − Σ'_n ( Λ(n) n^{−s} · 𝒜_R(log n) + conj(Λ(n) n^{−s}) · 𝒜′_R(log n) )`

with `𝒜_R(ℓ) = Σ_{j,k} conj(r_j) r_k · primeSymbol d j k ℓ`, an explicit finite polynomial in `ℓ`
sesquilinear in `R`, and `𝒜′_R = conj 𝒜_R` (`pf` symmetry), so the prime side is
`−2 Σ' Λ(n) n^{−σ₀} Re[e^{−iγ log n} 𝒜_R(log n)]`: a weighted phase clock with an `ℓ`-dependent phase.

Closed form (`pf_fst_closed`, hockey stick): `primeSymbol d j k ℓ = Σ_{i=1}^{j} C(j+k−i−1, k−1) d^{−(j+k−i)}
ℓ^{i−1}/(i−1)!`, whose value at `ℓ = 0` is the Pascal–Hankel matrix `C(j+k−2, k−1)/d^{j+k−1}` (589).
-/

open Complex Finset Filter Topology
open scoped LSeries.notation
open LSeries

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. Symmetry and closed form of `pf` -/

/-- `b(j,k) = a(k,j)`: the two coefficient families are mirror images. -/
theorem pf_swap (d : ℂ) : ∀ n : ℕ, ∀ j k : ℕ, j + k = n → 1 ≤ j + k → (pf d j k).2 = (pf d k j).1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j k hn hjk
    rcases k with _ | k
    · rw [pf_zero_right]
      rcases j with _ | j
      · omega
      · rw [pf_zero_left]
    · rcases j with _ | j
      · rw [pf_zero_left, pf_zero_right]
      · rw [pf_succ, pf_succ]
        funext l
        simp only
        rw [ih (j + 1 + k) (by omega) (j + 1) k rfl (by omega),
          ih (j + (k + 1)) (by omega) j (k + 1) rfl (by omega)]
        ring

/-- The closed-form coefficient `C(j+k−i−1, k−1)/d^{j+k−i}` on `1 ≤ i ≤ j`, `0` otherwise. -/
def pfc (d : ℂ) (j k i : ℕ) : ℂ :=
  if 1 ≤ i ∧ i ≤ j then (Nat.choose (j + k - i - 1) (k - 1) : ℂ) / d ^ (j + k - i) else 0

theorem pfc_of_le {d : ℂ} {j k i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ j) :
    pfc d j k i = (Nat.choose (j + k - i - 1) (k - 1) : ℂ) / d ^ (j + k - i) := by
  unfold pfc
  rw [if_pos ⟨h1, h2⟩]

theorem pfc_of_gt {d : ℂ} {j k i : ℕ} (h : j < i) : pfc d j k i = 0 := by
  unfold pfc
  rw [if_neg (fun h' => by omega)]

theorem pfc_zero {d : ℂ} {j k : ℕ} : pfc d j k 0 = 0 := by
  unfold pfc
  rw [if_neg (fun h' => by omega)]

/-- **Closed form of the reduction coefficients** (hockey stick / Pascal), `j, k ≥ 1`. -/
theorem pf_fst_closed (d : ℂ) (hd : d ≠ 0) :
    ∀ n : ℕ, ∀ j k : ℕ, j + k = n → 1 ≤ j → 1 ≤ k → ∀ i, (pf d j k).1 i = pfc d j k i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j k hn hj hk i
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [pf_succ]
    simp only
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · -- i = 0
      subst hi0
      rw [pfc_zero]
      have h1 : (pf d (j' + 1) k').1 0 = 0 := (pf_index_zero d _ (j' + 1) k' rfl (by omega)).1
      have h2 : (pf d j' (k' + 1)).1 0 = 0 := (pf_index_zero d _ j' (k' + 1) rfl (by omega)).1
      rw [h1, h2]
      simp
    rcases Nat.eq_zero_or_pos k' with hk0 | hk0
    · -- k' = 0 : first summand is the pure power δ_{i, j'+1}
      subst hk0
      rw [pf_zero_right]
      simp only
      rcases Nat.eq_zero_or_pos j' with hj0 | hj0
      · -- j' = 0 : X Y
        subst hj0
        rw [pf_zero_left]
        simp only
        by_cases hi1 : i = 1
        · subst hi1
          rw [pfc_of_le le_rfl le_rfl]
          simp
        · rw [if_neg hi1, pfc_of_gt (by omega)]
          simp
      · -- j' ≥ 1 : IH on (j', 1)
        have hih := ih (j' + (0 + 1)) (by omega) j' (0 + 1) rfl hj0 le_rfl i
        simp only [zero_add] at hih ⊢
        rw [hih]
        by_cases hi : i ≤ j'
        · rw [if_neg (by omega), pfc_of_le hi0 hi, pfc_of_le hi0 (by omega)]
          have e : j' + 1 + 1 - i = (j' + 1 - i) + 1 := by omega
          simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, zero_add, e, pow_succ]
          field_simp
        · by_cases hi' : i = j' + 1
          · subst hi'
            rw [if_pos rfl, pfc_of_gt (by omega), pfc_of_le hi0 le_rfl]
            have e : j' + 1 + 1 - (j' + 1) = 1 := by omega
            simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, e, pow_one, add_zero]
            field_simp
          · rw [if_neg hi', pfc_of_gt (by omega), pfc_of_gt (by omega)]
            simp
    · -- k' ≥ 1
      have hih1 := ih (j' + 1 + k') (by omega) (j' + 1) k' rfl (by omega) hk0 i
      rw [hih1]
      rcases Nat.eq_zero_or_pos j' with hj0 | hj0
      · -- j' = 0
        subst hj0
        rw [pf_zero_left]
        simp only
        by_cases hi1 : i = 1
        · subst hi1
          rw [pfc_of_le le_rfl le_rfl, pfc_of_le le_rfl le_rfl]
          have e1 : 0 + 1 + k' - 1 - 1 = k' - 1 := by omega
          have e2 : 0 + 1 + (k' + 1) - 1 - 1 = k' := by omega
          have e3 : 0 + 1 + k' - 1 = k' := by omega
          have e4 : 0 + 1 + (k' + 1) - 1 = k' + 1 := by omega
          have e5 : k' + 1 - 1 = k' := by omega
          simp only [e1, e2, e3, e4, e5, Nat.choose_self, Nat.cast_one, add_zero, pow_succ]
          field_simp
        · rw [pfc_of_gt (by omega), pfc_of_gt (by omega)]
          simp
      · -- j' ≥ 1 : Pascal
        have hih2 := ih (j' + (k' + 1)) (by omega) j' (k' + 1) rfl hj0 (by omega) i
        rw [hih2]
        by_cases hi : i ≤ j'
        · rw [pfc_of_le hi0 (by omega), pfc_of_le hi0 hi, pfc_of_le hi0 (by omega)]
          -- C(j'+k'+1−i, k') = C(j'+k'−i, k'−1) + C(j'+k'−i, k')
          obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
          obtain ⟨m, hm⟩ : ∃ m, j' + k'' + 1 - i = m := ⟨_, rfl⟩
          -- target (j'+1, k''+2): C(m+1, k''+1)/d^{m+2}; hih1 (j'+1, k''+1): C(m, k'')/d^{m+1};
          -- hih2 (j', k''+2): C(m, k''+1)/d^{m+1}
          have e1 : j' + 1 + (k'' + 1 + 1) - i - 1 = m + 1 := by omega
          have e2 : j' + 1 + (k'' + 1 + 1) - i = m + 2 := by omega
          have e3 : j' + 1 + (k'' + 1) - i - 1 = m := by omega
          have e4 : j' + 1 + (k'' + 1) - i = m + 1 := by omega
          have e5 : j' + (k'' + 1 + 1) - i - 1 = m := by omega
          have e6 : j' + (k'' + 1 + 1) - i = m + 1 := by omega
          have e9 : k'' + 1 + 1 - 1 = k'' + 1 := by omega
          have e10 : k'' + 1 - 1 = k'' := by omega
          have e11 : m + 1 - 1 = m := by omega
          have e12 : m + 2 - 1 = m + 1 := by omega
          simp only [e1, e2, e3, e4, e5, e6, e9, e10, e11, e12]
          rw [Nat.choose_succ_succ' m k'', pow_succ]
          push_cast
          field_simp
          ring
        · by_cases hi' : i = j' + 1
          · subst hi'
            rw [pfc_of_le hi0 le_rfl, pfc_of_le hi0 le_rfl, pfc_of_gt (by omega)]
            obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
            have e1 : j' + 1 + (k'' + 1 + 1) - (j' + 1) - 1 = k'' + 1 := by omega
            have e2 : j' + 1 + (k'' + 1 + 1) - (j' + 1) = k'' + 2 := by omega
            have e3 : j' + 1 + (k'' + 1) - (j' + 1) - 1 = k'' := by omega
            have e4 : j' + 1 + (k'' + 1) - (j' + 1) = k'' + 1 := by omega
            have e5 : k'' + 1 + 1 - 1 = k'' + 1 := by omega
            have e6 : k'' + 1 - 1 = k'' := by omega
            simp only [e1, e2, e3, e4, e5, e6, Nat.choose_self, Nat.cast_one]
            rw [pow_succ]
            field_simp
            ring
          · rw [pfc_of_gt (by omega), pfc_of_gt (by omega), pfc_of_gt (by omega)]
            simp

theorem pf_snd_closed (d : ℂ) (hd : d ≠ 0) {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) (i : ℕ) :
    (pf d j k).2 i = pfc d k j i := by
  rw [pf_swap d (j + k) j k rfl (by omega)]
  exact pf_fst_closed d hd (k + j) k j rfl hk hj i

/-! ## 2. The log-power von Mangoldt series termwise -/

/-- `Λ` as a complex sequence. -/
def Λc (n : ℕ) : ℂ := ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)

theorem logMul_iterate (f : ℕ → ℂ) (m : ℕ) (n : ℕ) :
    (logMul^[m] f) n = (Complex.log n) ^ m * f n := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ, Function.comp_apply, ih]
    simp only [logMul, pow_succ]
    ring

/-- `log n` for `n : ℕ` is the real logarithm. -/
theorem log_natCast_eq (n : ℕ) : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
  rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]

theorem term_logMul_iterate (m : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (logMul^[m] Λc) s n = ((Real.log n : ℝ) : ℂ) ^ m * LSeries.term Λc s n := by
  unfold LSeries.term
  split_ifs with h
  · simp
  · rw [logMul_iterate, log_natCast_eq]
    ring

theorem summable_logpow_term {s : ℂ} (hs : 1 < s.re) (m : ℕ) :
    Summable (fun n : ℕ => ((Real.log n : ℝ) : ℂ) ^ m * LSeries.term Λc s n) := by
  have h : LSeriesSummable (logMul^[m] Λc) s := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    rw [LSeries.absicssaOfAbsConv_logPowMul]
    exact lt_of_le_of_lt abscissa_vonMangoldt_le_one (by exact_mod_cast hs)
  exact h.congr (fun n => term_logMul_iterate m s n)

theorem LSeries_logpow_eq {s : ℂ} (m : ℕ) :
    LSeries (logMul^[m] Λc) s = ∑' n : ℕ, ((Real.log n : ℝ) : ℂ) ^ m * LSeries.term Λc s n := by
  unfold LSeries
  exact tsum_congr (fun n => term_logMul_iterate m s n)

theorem conj_tsum_logpow {s : ℂ} (hs : 1 < s.re) (m : ℕ) :
    (starRingEnd ℂ) (∑' n : ℕ, ((Real.log n : ℝ) : ℂ) ^ m * LSeries.term Λc s n)
      = ∑' n : ℕ, ((Real.log n : ℝ) : ℂ) ^ m * (starRingEnd ℂ) (LSeries.term Λc s n) := by
  rw [← Complex.conjCLE_apply, Complex.conjCLE.map_tsum]
  refine tsum_congr (fun n => ?_)
  rw [Complex.conjCLE_apply, map_mul, map_pow, Complex.conj_ofReal]

/-! ## 3. The symbol and the collection by `n` -/

/-- The prime symbol of the monomial pair `(j, k)`: `a₁ + Σ_i a_{i+2} ℓ^{i+1}/(i+1)!`. -/
def primeSymbol (d : ℂ) (M j k : ℕ) (ℓ : ℝ) : ℂ :=
  (pf d j k).1 1 + ∑ i ∈ range (M - 1), (pf d j k).1 (i + 2) * ((ℓ : ℂ) ^ (i + 1) / ((i + 1).factorial : ℂ))

/-- The mirror symbol (the `b`-side). -/
def primeSymbol' (d : ℂ) (M j k : ℕ) (ℓ : ℝ) : ℂ :=
  (pf d j k).2 1 + ∑ l ∈ range (M - 1), (pf d j k).2 (l + 2) * ((ℓ : ℂ) ^ (l + 1) / ((l + 1).factorial : ℂ))

theorem primeSymbol'_eq_swap (d : ℂ) (M : ℕ) {j k : ℕ} (hjk : 1 ≤ j + k) (ℓ : ℝ) :
    primeSymbol' d M j k ℓ = primeSymbol d M k j ℓ := by
  unfold primeSymbol' primeSymbol
  rw [pf_swap d (j + k) j k rfl hjk]

/-- The pole + Archimedean part of the jets. -/
def poleGammaJet (s : ℂ) (m : ℕ) : ℂ :=
  (-1) ^ m * (m.factorial : ℂ) * (s ^ (-1 - m : ℤ) + (s - 1) ^ (-1 - m : ℤ))
    + iteratedDeriv m (fun z : ℂ => logDeriv Complex.Gamma (z / 2) / 2) s

def poleGammaLogDeriv (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1) - ((Real.log Real.pi : ℝ) : ℂ) / 2 + logDeriv Complex.Gamma (s / 2) / 2

/-- The DC (pole + Γ) value of the monomial pair `(j, k)`. -/
def dcValue (s d : ℂ) (M j k : ℕ) : ℂ :=
  (pf d j k).1 1 * (2 * ((poleGammaLogDeriv s).re : ℂ))
    + ∑ i ∈ range (M - 1), (pf d j k).1 (i + 2)
        * (poleGammaJet s (i + 1) / ((-1) ^ (i + 1) * ((i + 1).factorial : ℂ)))
    + ∑ l ∈ range (M - 1), (pf d j k).2 (l + 2)
        * ((-1) ^ (l + 1) * (starRingEnd ℂ) (poleGammaJet s (l + 1)) / ((l + 1).factorial : ℂ))

theorem primeJet_eq (s : ℂ) (m : ℕ) :
    primeJet s m = poleGammaJet s m - (-1) ^ m * LSeries (logMul^[m] Λc) s := rfl

theorem primeLogDeriv_eq (s : ℂ) : primeLogDeriv s = poleGammaLogDeriv s - LSeries Λc s := rfl

/-- **Collection by `n`.** The prime-chart value of `(j, k)` is its DC value minus the von Mangoldt
sum of `Λ(n) n^{−s} · primeSymbol(log n) + conj(Λ(n) n^{−s}) · primeSymbol′(log n)`. -/
theorem summable_logpow_term_conj {s : ℂ} (hs : 1 < s.re) (m : ℕ) :
    Summable (fun n : ℕ => ((Real.log n : ℝ) : ℂ) ^ m * (starRingEnd ℂ) (LSeries.term Λc s n)) := by
  have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).summable.mpr (summable_logpow_term hs m)
  refine this.congr (fun n => ?_)
  simp only [Function.comp_apply, Complex.conjCLE_apply, map_mul, map_pow, Complex.conj_ofReal]

/-- The collected summand, pointwise, as a finite combination of log-power terms. -/
theorem collect_pointwise (s d : ℂ) (M j k : ℕ) (n : ℕ) :
    LSeries.term Λc s n * primeSymbol d M j k (Real.log n)
        + (starRingEnd ℂ) (LSeries.term Λc s n) * primeSymbol' d M j k (Real.log n)
      = ((pf d j k).1 1 * (((Real.log n : ℝ) : ℂ) ^ 0 * LSeries.term Λc s n)
          + (pf d j k).2 1 * (((Real.log n : ℝ) : ℂ) ^ 0 * (starRingEnd ℂ) (LSeries.term Λc s n)))
        + ∑ i ∈ range (M - 1), ((pf d j k).1 (i + 2) / ((i + 1).factorial : ℂ))
            * (((Real.log n : ℝ) : ℂ) ^ (i + 1) * LSeries.term Λc s n)
        + ∑ l ∈ range (M - 1), ((pf d j k).2 (l + 2) / ((l + 1).factorial : ℂ))
            * (((Real.log n : ℝ) : ℂ) ^ (l + 1) * (starRingEnd ℂ) (LSeries.term Λc s n)) := by
  unfold primeSymbol primeSymbol'
  simp only [pow_zero, one_mul, mul_add, Finset.mul_sum]
  have e1 : ∀ i, LSeries.term Λc s n * ((pf d j k).1 (i + 2) * (((Real.log n : ℝ) : ℂ) ^ (i + 1) / ((i + 1).factorial : ℂ)))
      = ((pf d j k).1 (i + 2) / ((i + 1).factorial : ℂ)) * (((Real.log n : ℝ) : ℂ) ^ (i + 1) * LSeries.term Λc s n) :=
    fun i => by ring
  have e2 : ∀ l, (starRingEnd ℂ) (LSeries.term Λc s n) * ((pf d j k).2 (l + 2) * (((Real.log n : ℝ) : ℂ) ^ (l + 1) / ((l + 1).factorial : ℂ)))
      = ((pf d j k).2 (l + 2) / ((l + 1).factorial : ℂ)) * (((Real.log n : ℝ) : ℂ) ^ (l + 1) * (starRingEnd ℂ) (LSeries.term Λc s n)) :=
    fun l => by ring
  simp only [e1, e2]
  ring

theorem summable_collect {s : ℂ} (hs : 1 < s.re) (d : ℂ) (M j k : ℕ) :
    Summable (fun n : ℕ => LSeries.term Λc s n * primeSymbol d M j k (Real.log n)
        + (starRingEnd ℂ) (LSeries.term Λc s n) * primeSymbol' d M j k (Real.log n)) := by
  have hsum := summable_logpow_term hs
  have hsumc := summable_logpow_term_conj hs
  have s1 := (hsum 0).mul_left ((pf d j k).1 1)
  have s2 := (hsumc 0).mul_left ((pf d j k).2 1)
  have s3 : Summable (fun n : ℕ => ∑ i ∈ range (M - 1), ((pf d j k).1 (i + 2) / ((i + 1).factorial : ℂ))
      * (((Real.log n : ℝ) : ℂ) ^ (i + 1) * LSeries.term Λc s n)) :=
    summable_sum (fun i _ => (hsum (i + 1)).mul_left _)
  have s4 : Summable (fun n : ℕ => ∑ l ∈ range (M - 1), ((pf d j k).2 (l + 2) / ((l + 1).factorial : ℂ))
      * (((Real.log n : ℝ) : ℂ) ^ (l + 1) * (starRingEnd ℂ) (LSeries.term Λc s n))) :=
    summable_sum (fun l _ => (hsumc (l + 1)).mul_left _)
  exact (((s1.add s2).add s3).add s4).congr (fun n => (collect_pointwise s d M j k n).symm)

/-- The tsum of the collected summand is the jet combination. -/
theorem tsum_collect {s : ℂ} (hs : 1 < s.re) (d : ℂ) (M j k : ℕ) :
    ∑' n : ℕ, (LSeries.term Λc s n * primeSymbol d M j k (Real.log n)
        + (starRingEnd ℂ) (LSeries.term Λc s n) * primeSymbol' d M j k (Real.log n))
      = (pf d j k).1 1 * LSeries Λc s
        + (pf d j k).2 1 * (starRingEnd ℂ) (LSeries Λc s)
        + ∑ i ∈ range (M - 1), (pf d j k).1 (i + 2)
            * (LSeries (logMul^[i + 1] Λc) s / ((i + 1).factorial : ℂ))
        + ∑ l ∈ range (M - 1), (pf d j k).2 (l + 2)
            * ((starRingEnd ℂ) (LSeries (logMul^[l + 1] Λc) s) / ((l + 1).factorial : ℂ)) := by
  have hsum := summable_logpow_term hs
  have hsumc := summable_logpow_term_conj hs
  rw [tsum_congr (collect_pointwise s d M j k)]
  have s1 := (hsum 0).mul_left ((pf d j k).1 1)
  have s2 := (hsumc 0).mul_left ((pf d j k).2 1)
  have s3 : Summable (fun n : ℕ => ∑ i ∈ range (M - 1), ((pf d j k).1 (i + 2) / ((i + 1).factorial : ℂ))
      * (((Real.log n : ℝ) : ℂ) ^ (i + 1) * LSeries.term Λc s n)) :=
    summable_sum (fun i _ => (hsum (i + 1)).mul_left _)
  have s4 : Summable (fun n : ℕ => ∑ l ∈ range (M - 1), ((pf d j k).2 (l + 2) / ((l + 1).factorial : ℂ))
      * (((Real.log n : ℝ) : ℂ) ^ (l + 1) * (starRingEnd ℂ) (LSeries.term Λc s n))) :=
    summable_sum (fun l _ => (hsumc (l + 1)).mul_left _)
  rw [((s1.add s2).add s3).tsum_add s4, (s1.add s2).tsum_add s3, s1.tsum_add s2, tsum_mul_left,
    tsum_mul_left, Summable.tsum_finsetSum (fun i _ => (hsum (i + 1)).mul_left _),
    Summable.tsum_finsetSum (fun l _ => (hsumc (l + 1)).mul_left _)]
  simp only [tsum_mul_left]
  simp only [pow_zero, one_mul]
  have h0 : LSeries Λc s = ∑' n : ℕ, LSeries.term Λc s n := rfl
  have hc0 := conj_tsum_logpow hs 0
  simp only [pow_zero, one_mul] at hc0
  rw [h0, hc0]
  simp only [LSeries_logpow_eq (s := s)]
  simp only [conj_tsum_logpow hs]
  have hs1 : ∑ i ∈ range (M - 1), ((pf d j k).1 (i + 2) / ((i + 1).factorial : ℂ))
        * (∑' n : ℕ, ((Real.log n : ℝ) : ℂ) ^ (i + 1) * LSeries.term Λc s n)
      = ∑ i ∈ range (M - 1), (pf d j k).1 (i + 2)
        * ((∑' n : ℕ, ((Real.log n : ℝ) : ℂ) ^ (i + 1) * LSeries.term Λc s n) / ((i + 1).factorial : ℂ)) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  have hs2 : ∑ l ∈ range (M - 1), ((pf d j k).2 (l + 2) / ((l + 1).factorial : ℂ))
        * (∑' n : ℕ, ((Real.log n : ℝ) : ℂ) ^ (l + 1) * (starRingEnd ℂ) (LSeries.term Λc s n))
      = ∑ l ∈ range (M - 1), (pf d j k).2 (l + 2)
        * ((∑' n : ℕ, ((Real.log n : ℝ) : ℂ) ^ (l + 1) * (starRingEnd ℂ) (LSeries.term Λc s n))
            / ((l + 1).factorial : ℂ)) :=
    Finset.sum_congr rfl (fun l _ => by ring)
  rw [hs1, hs2]

/-- **Collection by `n`.** For `j, k ≥ 1`, the prime-chart value of `(j, k)` is its DC value minus the
von Mangoldt sum of `Λ(n) n^{−s} · primeSymbol(log n) + conj(Λ(n) n^{−s}) · primeSymbol′(log n)`. -/
theorem jetValueP_collect {s : ℂ} (hs : 1 < s.re) (d : ℂ) (M : ℕ) {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    jetValueP s d M j k
      = dcValue s d M j k
        - ∑' n : ℕ, (LSeries.term Λc s n * primeSymbol d M j k (Real.log n)
            + (starRingEnd ℂ) (LSeries.term Λc s n) * primeSymbol' d M j k (Real.log n)) := by
  rw [tsum_collect hs d M j k]
  unfold jetValueP dcValue
  simp only [primeJet_eq, primeLogDeriv_eq]
  rw [← pf_first_symm d (j + k) j k rfl hj hk]
  have h2re : (2 : ℂ) * (((poleGammaLogDeriv s - LSeries Λc s).re : ℝ) : ℂ)
      = 2 * (((poleGammaLogDeriv s).re : ℝ) : ℂ) - (LSeries Λc s + (starRingEnd ℂ) (LSeries Λc s)) := by
    rw [Complex.sub_re, Complex.add_conj]
    push_cast
    ring
  rw [h2re]
  have hF : ∀ i : ℕ, ((-1 : ℂ) ^ (i + 1) * ((i + 1).factorial : ℂ)) ≠ 0 := fun i =>
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hF' : ∀ i : ℕ, (((i + 1).factorial : ℂ)) ≠ 0 := fun i => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have e1 : ∀ i : ℕ, (pf d j k).1 (i + 2) * ((poleGammaJet s (i + 1) - (-1) ^ (i + 1) * LSeries (logMul^[i + 1] Λc) s)
        / ((-1) ^ (i + 1) * ((i + 1).factorial : ℂ)))
      = (pf d j k).1 (i + 2) * (poleGammaJet s (i + 1) / ((-1) ^ (i + 1) * ((i + 1).factorial : ℂ)))
        - (pf d j k).1 (i + 2) * (LSeries (logMul^[i + 1] Λc) s / ((i + 1).factorial : ℂ)) := by
    intro i
    have := hF i
    have := hF' i
    field_simp
  have e2 : ∀ l : ℕ, (pf d j k).2 (l + 2) * ((-1) ^ (l + 1)
        * (starRingEnd ℂ) (poleGammaJet s (l + 1) - (-1) ^ (l + 1) * LSeries (logMul^[l + 1] Λc) s)
        / ((l + 1).factorial : ℂ))
      = (pf d j k).2 (l + 2) * ((-1) ^ (l + 1) * (starRingEnd ℂ) (poleGammaJet s (l + 1)) / ((l + 1).factorial : ℂ))
        - (pf d j k).2 (l + 2) * ((starRingEnd ℂ) (LSeries (logMul^[l + 1] Λc) s) / ((l + 1).factorial : ℂ)) := by
    intro l
    have := hF' l
    rw [map_sub, map_mul, map_pow, map_neg, map_one]
    have hsq : ((-1 : ℂ) ^ (l + 1)) * ((-1 : ℂ) ^ (l + 1)) = 1 := by
      rw [← mul_pow]
      simp
    field_simp
    linear_combination (-(pf d j k).2 (l + 2) * (starRingEnd ℂ) (LSeries (logMul^[l + 1] Λc) s)) * hsq
  simp only [e1, e2, Finset.sum_sub_distrib]
  ring

/-! ## 4. The sesquilinear endpoint: `primeJetsForm = dcForm − 2 Σ' Re(Λ(n) n^{−s} 𝒜_R(log n))` -/

/-- `pf` commutes with conjugation of `d`. -/
theorem pf_conj (d : ℂ) : ∀ n : ℕ, ∀ j k : ℕ, j + k = n →
    (∀ i, (pf ((starRingEnd ℂ) d) j k).1 i = (starRingEnd ℂ) ((pf d j k).1 i))
    ∧ (∀ i, (pf ((starRingEnd ℂ) d) j k).2 i = (starRingEnd ℂ) ((pf d j k).2 i)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j k hn
    rcases k with _ | k
    · rw [pf_zero_right, pf_zero_right]
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simp only
        split_ifs <;> simp
      · simp
    · rcases j with _ | j
      · rw [pf_zero_left, pf_zero_left]
        refine ⟨fun i => ?_, fun i => ?_⟩
        · simp
        · simp only
          split_ifs <;> simp
      · rw [pf_succ, pf_succ]
        have h1 := ih (j + 1 + k) (by omega) (j + 1) k rfl
        have h2 := ih (j + (k + 1)) (by omega) j (k + 1) rfl
        refine ⟨fun i => ?_, fun i => ?_⟩
        · simp only
          rw [h1.1 i, h2.1 i, map_mul, map_add, map_div₀, map_one]
        · simp only
          rw [h1.2 i, h2.2 i, map_mul, map_add, map_div₀, map_one]

/-- For real `d` and real `ℓ`, `primeSymbol′ d j k ℓ = conj (primeSymbol d k j ℓ)`... and in fact the
symbol is real: `conj (primeSymbol d M j k ℓ) = primeSymbol d M j k ℓ`. -/
theorem primeSymbol_conj {d : ℂ} (hd : (starRingEnd ℂ) d = d) (M j k : ℕ) (ℓ : ℝ) :
    (starRingEnd ℂ) (primeSymbol d M j k ℓ) = primeSymbol d M j k ℓ := by
  unfold primeSymbol
  have h := (pf_conj d (j + k) j k rfl).1
  rw [hd] at h
  rw [map_add, map_sum]
  congr 1
  · exact (h 1).symm
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, map_div₀, map_pow, Complex.conj_ofReal, Complex.conj_natCast, ← h (i + 2)]

/-- The sesquilinear prime symbol `𝒜_R(ℓ)`. -/
def primeSymbolForm (R : Polynomial ℂ) (d : ℂ) (M : ℕ) (ℓ : ℝ) : ℂ :=
  ∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
    ((starRingEnd ℂ) (R.coeff j) * R.coeff k) * primeSymbol d M j k ℓ

/-- The DC form of `R`. -/
def dcForm (R : Polynomial ℂ) (s d : ℂ) (M : ℕ) : ℂ :=
  ∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
    ((starRingEnd ℂ) (R.coeff j) * R.coeff k) * dcValue s d M j k

/-- The prime-chart form of `R` (the door's functional). -/
def primeJetsForm (R : Polynomial ℂ) (s d : ℂ) (M : ℕ) : ℂ :=
  ∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
    ((starRingEnd ℂ) (R.coeff j) * R.coeff k) * jetValueP s d M j k

/-- The mirror form equals the conjugate of the symbol form (real `d`, `R(0) = 0`). -/
theorem primeSymbolForm'_eq_conj (R : Polynomial ℂ) (hR : R.coeff 0 = 0) {d : ℂ}
    (hd : (starRingEnd ℂ) d = d) (M : ℕ) (ℓ : ℝ) :
    ∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
        ((starRingEnd ℂ) (R.coeff j) * R.coeff k) * primeSymbol' d M j k ℓ
      = (starRingEnd ℂ) (primeSymbolForm R d M ℓ) := by
  unfold primeSymbolForm
  rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, map_mul, Complex.conj_conj, primeSymbol_conj hd]
  by_cases h : j = 0 ∧ k = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp [hR]
  · rw [primeSymbol'_eq_swap d M (by omega) ℓ]
    ring

/-- **The endpoint.** For `R(0) = 0`, `Re s > 1`, real `d`:
`primeJetsForm R s d = dcForm R s d − Σ'_n 2·Re( Λ(n) n^{−s} · 𝒜_R(log n) )`. -/
theorem primeJetsForm_collect (R : Polynomial ℂ) (hR : R.coeff 0 = 0) {s : ℂ} (hs : 1 < s.re)
    {d : ℂ} (hd : (starRingEnd ℂ) d = d) (M : ℕ) :
    primeJetsForm R s d M
      = dcForm R s d M
        - ∑' n : ℕ, (2 : ℂ) * (((LSeries.term Λc s n * primeSymbolForm R d M (Real.log n)).re : ℝ) : ℂ) := by
  -- the collected summand of the form
  have hpt : ∀ n : ℕ, (2 : ℂ) * (((LSeries.term Λc s n * primeSymbolForm R d M (Real.log n)).re : ℝ) : ℂ)
      = ∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
          ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
            * (LSeries.term Λc s n * primeSymbol d M j k (Real.log n)
                + (starRingEnd ℂ) (LSeries.term Λc s n) * primeSymbol' d M j k (Real.log n)) := by
    intro n
    have h2 : (2 : ℂ) * (((LSeries.term Λc s n * primeSymbolForm R d M (Real.log n)).re : ℝ) : ℂ)
        = LSeries.term Λc s n * primeSymbolForm R d M (Real.log n)
          + (starRingEnd ℂ) (LSeries.term Λc s n * primeSymbolForm R d M (Real.log n)) := by
      rw [Complex.add_conj]
      push_cast
      ring
    rw [h2, map_mul, ← primeSymbolForm'_eq_conj R hR hd M (Real.log n)]
    unfold primeSymbolForm
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  have hsumm : ∀ j ∈ range (R.natDegree + 1), ∀ k ∈ range (R.natDegree + 1),
      Summable (fun n : ℕ => ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
        * (LSeries.term Λc s n * primeSymbol d M j k (Real.log n)
            + (starRingEnd ℂ) (LSeries.term Λc s n) * primeSymbol' d M j k (Real.log n))) :=
    fun j _ k _ => (summable_collect hs d M j k).mul_left _
  rw [tsum_congr hpt, Summable.tsum_finsetSum (fun j hj => summable_sum (fun k hk => hsumm j hj k hk))]
  unfold primeJetsForm dcForm
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Summable.tsum_finsetSum (fun k hk => hsumm j hj k hk), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [tsum_mul_left]
  by_cases h : j = 0 ∨ k = 0
  · rcases h with rfl | rfl <;> simp [hR]
  · simp only [not_or] at h
    rw [jetValueP_collect hs d M (by omega) (by omega)]
    ring

/-- **The door on the prime symbol.** If for all `γ`, `1 < σ₀ < 3/2`, `R` with `R(0) = 0`:
`Re[ dcForm R s d − 2 Σ'_n Re(Λ(n) n^{−s} 𝒜_R(log n)) ] ≥ 0` at `s = σ₀ + iγ`, `d = 2σ₀ − 1`,
every nontrivial zero is on the line. -/
theorem online_of_prime_symbol_nonneg
    (H : ∀ γ σ₀ : ℝ, 1 < σ₀ → σ₀ < 3 / 2 → ∀ R : Polynomial ℂ, R.coeff 0 = 0 →
      0 ≤ (dcForm R ((σ₀ : ℂ) + (γ : ℂ) * I) ((2 * σ₀ - 1 : ℝ) : ℂ) (2 * R.natDegree + 2)
        - ∑' n : ℕ, (2 : ℂ) * (((LSeries.term Λc ((σ₀ : ℂ) + (γ : ℂ) * I) n
            * primeSymbolForm R ((2 * σ₀ - 1 : ℝ) : ℂ) (2 * R.natDegree + 2) (Real.log n)).re : ℝ) : ℂ)).re) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  apply online_of_prime_jets_nonneg
  have hre : ∀ γ σ₀ : ℝ, 1 < σ₀ → 1 < ((σ₀ : ℂ) + (γ : ℂ) * I).re := by
    intro γ σ₀ h
    simpa using h
  have key : ∀ (γ σ₀ : ℝ), 1 < σ₀ → ∀ R : Polynomial ℂ, R.coeff 0 = 0 →
      primeJetsForm R ((σ₀ : ℂ) + (γ : ℂ) * I) ((2 * σ₀ - 1 : ℝ) : ℂ) (2 * R.natDegree + 2)
        = dcForm R ((σ₀ : ℂ) + (γ : ℂ) * I) ((2 * σ₀ - 1 : ℝ) : ℂ) (2 * R.natDegree + 2)
          - ∑' n : ℕ, (2 : ℂ) * (((LSeries.term Λc ((σ₀ : ℂ) + (γ : ℂ) * I) n
              * primeSymbolForm R ((2 * σ₀ - 1 : ℝ) : ℂ) (2 * R.natDegree + 2) (Real.log n)).re : ℝ) : ℂ) :=
    fun γ σ₀ h R hR => primeJetsForm_collect R hR (hre γ σ₀ h) (Complex.conj_ofReal _) _
  intro γ σ₀ h1 h2 R hR
  have := H γ σ₀ h1 h2 R hR
  rw [← key γ σ₀ h1 R hR] at this
  exact this

/-! ## 5. Closed form of the symbol -/

/-- `primeSymbol d M j k ℓ = Σ_{i ∈ range j} C(j+k−i−2, k−1) d^{−(j+k−i−1)} ℓ^i/i!` for `1 ≤ j, k`,
`j ≤ M − 1`... stated with the coefficient function `pfc`. -/
theorem primeSymbol_closed {d : ℂ} (hd : d ≠ 0) {M j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) (ℓ : ℝ) :
    primeSymbol d M j k ℓ
      = pfc d j k 1 + ∑ i ∈ range (M - 1), pfc d j k (i + 2) * ((ℓ : ℂ) ^ (i + 1) / ((i + 1).factorial : ℂ)) := by
  unfold primeSymbol
  rw [pf_fst_closed d hd (j + k) j k rfl hj hk 1]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by rw [pf_fst_closed d hd (j + k) j k rfl hj hk (i + 2)])

/-- At `ℓ = 0` the symbol is the Pascal–Hankel entry `C(j+k−2, k−1)/d^{j+k−1}` (589). -/
theorem primeSymbol_zero {d : ℂ} (hd : d ≠ 0) {M j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    primeSymbol d M j k 0 = (Nat.choose (j + k - 2) (k - 1) : ℂ) / d ^ (j + k - 1) := by
  rw [primeSymbol_closed hd hj hk, pfc_of_le le_rfl hj]
  simp only [Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero _), zero_div, mul_zero,
    Finset.sum_const_zero, add_zero]
  congr 2

#print axioms pf_fst_closed
#print axioms primeJetsForm_collect
#print axioms online_of_prime_symbol_nonneg

end CriticalLinePhasor.ContourArgument
