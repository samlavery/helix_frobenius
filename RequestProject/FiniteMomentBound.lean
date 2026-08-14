import Mathlib

/-!
# Finitely many vanishing moments bound the empirical mass of a set

Full Sato--Tate needs cancellation of *every* nontrivial symmetric-power average.  Cancellation at
finitely many ranks is strictly weaker, but it is not vacuous: it still constrains the empirical
distribution, quantitatively, by the classical majorant device.

If a real function `P` dominates the indicator of `I` pointwise and is a finite combination
`P = ∑_{r ≤ N} c r · U r` of the test functions whose prefix averages are known to vanish for
`r ≥ 1`, then the prefix average of `1_I` is eventually at most `c 0 + ε`.  Nothing here is
asymptotic sleight of hand: the inequality `avg 1_I ≤ avg P` is monotonicity of a finite average,
and the limit of `avg P` is `c 0` because every other term tends to zero.

This is the honest machinery for turning the ranks where symmetric-power automorphy *is* known
(`r ≤ 4`, Gelbart--Jacquet and Kim--Shahidi) into an unconditional upper bound on the empirical
mass of an interval.  The file proves only the machinery; it supplies no moment input and makes no
claim about any particular form.
-/

open Filter Topology Finset

namespace CriticalLinePhasor.FiniteMoment

/-- The prefix average of `f` along a sequence of sample points. -/
noncomputable def prefixAverage (a : ℕ → ℝ) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i : Fin (n + 1), f (a i)

/-- Prefix averages are monotone in the integrand. -/
theorem prefixAverage_mono (a : ℕ → ℝ) {f g : ℝ → ℝ} (h : ∀ x, f x ≤ g x) (n : ℕ) :
    prefixAverage a f n ≤ prefixAverage a g n := by
  unfold prefixAverage
  have hpos : (0 : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h (a i)) hpos

/-- Prefix averaging is additive over a finite sum of integrands. -/
theorem prefixAverage_sum (a : ℕ → ℝ) (s : Finset ℕ) (F : ℕ → ℝ → ℝ) (n : ℕ) :
    prefixAverage a (fun x => ∑ r ∈ s, F r x) n =
      ∑ r ∈ s, prefixAverage a (F r) n := by
  unfold prefixAverage
  rw [Finset.sum_comm, Finset.mul_sum]

/-- The prefix average of a constant is that constant. -/
theorem prefixAverage_const (a : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    prefixAverage a (fun _ => c) n = c := by
  unfold prefixAverage
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **The majorant bound.**  A pointwise majorant of the indicator, written in the test-function
basis whose prefix averages vanish above rank zero, bounds the empirical mass of `I` in the limit
by its constant coefficient. -/
theorem tendsto_prefixAverage_of_vanishing_moments
    (a : ℕ → ℝ) (N : ℕ) (c : ℕ → ℝ) (U : ℕ → ℝ → ℝ)
    (hU0 : ∀ x, U 0 x = 1)
    (hmom : ∀ r ∈ range (N + 1), r ≠ 0 →
      Tendsto (prefixAverage a (U r)) atTop (𝓝 0)) :
    Tendsto (prefixAverage a (fun x => ∑ r ∈ range (N + 1), c r * U r x)) atTop
      (𝓝 (c 0)) := by
  have hsplit : ∀ n : ℕ,
      prefixAverage a (fun x => ∑ r ∈ range (N + 1), c r * U r x) n =
        ∑ r ∈ range (N + 1), c r * prefixAverage a (U r) n := by
    intro n
    rw [prefixAverage_sum a (range (N + 1)) (fun r x => c r * U r x) n]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold prefixAverage
    rw [← Finset.mul_sum]
    ring
  have hterm : ∀ r ∈ range (N + 1),
      Tendsto (fun n => c r * prefixAverage a (U r) n) atTop
        (𝓝 (if r = 0 then c 0 else 0)) := by
    intro r hr
    by_cases h0 : r = 0
    · subst h0
      simp only [if_pos rfl]
      have hone : ∀ n, prefixAverage a (U 0) n = 1 := by
        intro n
        rw [show U 0 = fun _ => (1 : ℝ) from funext hU0]
        exact prefixAverage_const a 1 n
      simp [hone]
    · simp only [if_neg h0]
      simpa using (hmom r hr h0).const_mul (c r)
  have hsum := tendsto_finsetSum (range (N + 1)) hterm
  rw [Finset.sum_ite_eq' (range (N + 1)) 0 (fun _ => c 0)] at hsum
  rw [if_pos (Finset.mem_range.mpr (Nat.succ_pos N))] at hsum
  exact hsum.congr fun n => (hsplit n).symm

/-- **Finitely many vanishing moments give an eventual upper bound on empirical mass.**  For every
`ε > 0` the prefix average of the indicator of `I` is eventually at most `c 0 + ε`, where `c 0` is
the constant coefficient of any rank-`≤ N` majorant of the indicator. -/
theorem eventually_prefixAverage_indicator_le
    (a : ℕ → ℝ) (N : ℕ) (c : ℕ → ℝ) (U : ℕ → ℝ → ℝ) (I : Set ℝ)
    (hU0 : ∀ x, U 0 x = 1)
    (hdom : ∀ x, Set.indicator I (fun _ => (1 : ℝ)) x ≤
      ∑ r ∈ range (N + 1), c r * U r x)
    (hmom : ∀ r ∈ range (N + 1), r ≠ 0 →
      Tendsto (prefixAverage a (U r)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      prefixAverage a (Set.indicator I (fun _ => (1 : ℝ))) n ≤ c 0 + ε := by
  have hlim := tendsto_prefixAverage_of_vanishing_moments a N c U hU0 hmom
  have hev := hlim.eventually (eventually_lt_nhds (by linarith : c 0 < c 0 + ε))
  filter_upwards [hev] with n hn
  exact le_trans (prefixAverage_mono a hdom n) (le_of_lt hn)

end CriticalLinePhasor.FiniteMoment

#print axioms CriticalLinePhasor.FiniteMoment.prefixAverage_mono
#print axioms CriticalLinePhasor.FiniteMoment.tendsto_prefixAverage_of_vanishing_moments
#print axioms CriticalLinePhasor.FiniteMoment.eventually_prefixAverage_indicator_le
