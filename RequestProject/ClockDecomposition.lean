import Mathlib

/-!
# The clock decomposition of the log-weighted bank (ledger 572 → theorem)

Let `a : ℕ → ℂ` be completely multiplicative on positive integers (the amplitudes of a phasor
bank, e.g. `a n = n^{-s}`), and let the *growth curve* be the partial sum
`growth a y = Σ_{1 ≤ m ≤ y} a m` (the bank grown to the front `y`).

Because `log n = Σ_{d ∣ n} Λ(d)` (`ArithmeticFunction.vonMangoldt_sum`) and `a (d·m) = a d · a m`,
the **log-weighted bank** at the front `N` is the **von Mangoldt clock sampling the growth curve at
the divisor-scaled fronts** `N / d`:

  `Σ_{n ≤ N} log n · a n = Σ_{d ≤ N} Λ(d) · a d · growth a (N / d)`.

Equivalently, with the Riesz weight `log(N/n)` — the exact frequency weight of the odd lane at a
crossing (ledgers 568, 571) —

  `Σ_{n ≤ N} (log N − log n) · a n = log N · growth a N − Σ_{d ≤ N} Λ(d) · a d · growth a (N / d)`.

Instantiated at the Riemann–Siegel phasors `c · n^{-s}` this is the identity measured to `6e−16` at
360 zeros in `tmp/att574_clock_decomposition.py`: the tangency functional of a zero is the
prime-power clock reading the bank's own growth history, against `log N` times the endpoint.
The identity is exact for every front and every `s`; it uses only complete multiplicativity, which
is precisely the property the flowed weights `e^{t log²(N/n)}` lack for `t ≠ 0` (the control of
ledger 572).
-/

namespace CriticalLinePhasor.ClockDecomposition

open Finset ArithmeticFunction

/-- Completely multiplicative on positive integers. -/
def CompMult (a : ℕ → ℂ) : Prop := ∀ d m : ℕ, 0 < d → 0 < m → a (d * m) = a d * a m

/-- The growth curve of the bank: partial sums up to the front `y`. -/
def growth (a : ℕ → ℂ) (y : ℕ) : ℂ := ∑ m ∈ Icc 1 y, a m

/-- The multiples of `d` up to `N` are `d·m` with `1 ≤ m ≤ N / d`. -/
theorem sum_multiples (a : ℕ → ℂ) {d : ℕ} (hd : 0 < d) (N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter (fun n => d ∣ n), a n = ∑ m ∈ Icc 1 (N / d), a (d * m) := by
  symm
  refine Finset.sum_nbij' (fun m => d * m) (fun n => n / d) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_Icc] at hm
    rw [mem_filter, mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right d m⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hd.ne' (by omega))
    · have := (Nat.le_div_iff_mul_le hd).mp hm.2
      linarith [this, Nat.mul_comm m d]
  · intro n hn
    rw [mem_filter, mem_Icc] at hn
    rw [mem_Icc]
    obtain ⟨⟨h1, h2⟩, hdvd⟩ := hn
    refine ⟨?_, Nat.div_le_div_right h2⟩
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd
  · intro m _
    exact Nat.mul_div_cancel_left m hd
  · intro n hn
    rw [mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _
    rfl

/-- **The clock decomposition.** For a completely multiplicative bank, the log-weighted bank at the
front `N` is the von Mangoldt clock sampling the growth curve at the divisor-scaled fronts `N / d`. -/
theorem log_weighted_bank (a : ℕ → ℂ) (ha : CompMult a) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (Real.log n : ℂ) * a n
      = ∑ d ∈ Icc 1 N, (Λ d : ℂ) * a d * growth a (N / d) := by
  have h1 : ∀ n ∈ Icc 1 N, (Real.log n : ℂ) * a n = ∑ d ∈ n.divisors, (Λ d : ℂ) * a n := by
    intro n _
    rw [← Finset.sum_mul, ← vonMangoldt_sum]
    push_cast
    rfl
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := Icc 1 N) (s' := fun d => (Icc 1 N).filter (fun n => d ∣ n))]
  · refine Finset.sum_congr rfl (fun d hd => ?_)
    have hd0 : 0 < d := by rw [mem_Icc] at hd; omega
    rw [← Finset.mul_sum, sum_multiples a hd0 N, growth, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm0 : 0 < m := by rw [mem_Icc] at hm; omega
    rw [ha d m hd0 hm0]
    ring
  · intro n d
    rw [mem_Icc, Nat.mem_divisors, mem_filter, mem_Icc, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hdvd, hn0⟩
      refine ⟨⟨⟨h1, h2⟩, hdvd⟩, Nat.pos_of_dvd_of_pos hdvd (by omega), le_trans (Nat.le_of_dvd (by omega) hdvd) h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, hdvd⟩, _, _⟩
      exact ⟨⟨h1, h2⟩, hdvd, by omega⟩

/-- **The Riesz form.** With the frequency weight `log(N/n)` of the odd lane at a crossing: the
tangency functional is `log N` times the endpoint minus the clock-sampled growth history. -/
theorem riesz_weighted_bank (a : ℕ → ℂ) (ha : CompMult a) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((Real.log N : ℂ) - (Real.log n : ℂ)) * a n
      = (Real.log N : ℂ) * growth a N - ∑ d ∈ Icc 1 N, (Λ d : ℂ) * a d * growth a (N / d) := by
  rw [← log_weighted_bank a ha N, growth, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

/-- `n ↦ n^{-s}` is completely multiplicative. -/
theorem compMult_cpow (s : ℂ) : CompMult (fun n : ℕ => (n : ℂ) ^ (-s)) := by
  intro d m _ _
  have h := Complex.mul_cpow_ofReal_nonneg (a := (d : ℝ)) (b := (m : ℝ))
    (Nat.cast_nonneg d) (Nat.cast_nonneg m) (-s)
  simpa using h

/-- **The clock decomposition at the Riemann–Siegel phasors** `p n = c · n^{-s}` (with
`c = e^{iϑ}`, `s = ½ + iγ` this is the bank at height `γ`, front `N`): the Riesz-weighted odd lane
is `log N · P(N) − Σ_{d ≤ N} Λ(d) d^{-s} P(N/d)`, where `P(y) = c Σ_{m ≤ y} m^{-s}` is the growth
curve. Exact for every `c`, `s`, `N`. -/
theorem riesz_weighted_phasor_bank (c s : ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((Real.log N : ℂ) - (Real.log n : ℂ)) * (c * (n : ℂ) ^ (-s))
      = (Real.log N : ℂ) * (c * ∑ m ∈ Icc 1 N, (m : ℂ) ^ (-s))
        - ∑ d ∈ Icc 1 N, (Λ d : ℂ) * (d : ℂ) ^ (-s) * (c * ∑ m ∈ Icc 1 (N / d), (m : ℂ) ^ (-s)) := by
  have h := riesz_weighted_bank _ (compMult_cpow s) N
  simp only [growth] at h
  have hl : ∑ n ∈ Icc 1 N, ((Real.log N : ℂ) - (Real.log n : ℂ)) * (c * (n : ℂ) ^ (-s))
      = c * ∑ n ∈ Icc 1 N, ((Real.log N : ℂ) - (Real.log n : ℂ)) * (n : ℂ) ^ (-s) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hl, h, mul_sub]
  congr 1
  · ring
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)

#print axioms log_weighted_bank
#print axioms riesz_weighted_bank
#print axioms riesz_weighted_phasor_bank

end CriticalLinePhasor.ClockDecomposition
