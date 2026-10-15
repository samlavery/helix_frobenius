import Mathlib

/-!
# The tilted head is a convex mean of the native growth sequence (ledger 1327)

Geometry first (Sam, 2026-10-13: "banks grow one at a time"). At one height the native bank's phasors `a 0, a 1, …`
enter one at a time; the GROWTH SEQUENCE is the sequence of partial resultants `growth a k = Σ_{n<k} a n` — the
curve the resultant traces as the sites enter (1325, frame A: for the ζ-bank at height `e^γ` it is an outward
spiral about the native resultant). The chart's abscissa `σ = ½ + δ` tilts the projection plane and weights site `n`
by `(n+1)^{−δ}` (1325, frame B).

Compiled here, for ANY phasor sequence and every finite head:

* `tilted_eq_mean` — the tilted head `Σ_{n<N} (n+1)^{−δ} a n` equals `Σ_{k<N} meanWeight δ N k · growth a (k+1)`,
  summation by parts, exact.
* `meanWeight_nonneg`, `meanWeight_sum` — for `δ ≥ 0` the weights are nonnegative and sum to `1`: the tilted head is
  a CONVEX MEAN of the native growth sequence `growth a 1, …, growth a N`.
* `tilted_ne_zero_of_halfPlane` — if the native growth sequence lies in an open half-plane through the origin, no
  tilt `δ ≥ 0` cancels the head. Contrapositive: **a cancellation at a tilt requires the native growth curve to wind
  around the origin** — the spiral must surround `0`.

What this does and does not say. It is the exact geometric content of "the σ-family at one height is a family of
positive means of one native growth curve". For the infinite ζ-bank the growth spiral has radius `√N` and surrounds
the origin at every height, so the half-plane criterion never applies to the full bank: the exclusion of tilted
cancellations must come from the arithmetic of the heights `log n`, not from the mean structure (1325). Instrument,
not door. No `sorry`, no `axiom`.
-/

open Finset Complex
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixGrowthMean

/-- The native growth sequence: partial resultants as the sites enter one at a time. -/
def growth (a : ℕ → ℂ) (k : ℕ) : ℂ := ∑ n ∈ range k, a n

/-- The tilt weight of site `n` at tilt `δ`: `(n+1)^{−δ}`. -/
def tiltW (δ : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-δ)

/-- The head of the bank read through the tilt `δ`. -/
def tilted (a : ℕ → ℂ) (δ : ℝ) (N : ℕ) : ℂ := ∑ n ∈ range N, (tiltW δ n : ℂ) * a n

/-- The mean weights: `w_k − w_{k+1}` inside the head, `w_{N−1}` at its last site. -/
def meanWeight (δ : ℝ) (N k : ℕ) : ℝ :=
  if k + 1 < N then tiltW δ k - tiltW δ (k + 1) else tiltW δ k

theorem tiltW_zero (δ : ℝ) : tiltW δ 0 = 1 := by
  simp [tiltW]

theorem tiltW_pos (δ : ℝ) (n : ℕ) : 0 < tiltW δ n :=
  Real.rpow_pos_of_pos (by positivity) _

theorem tiltW_antitone {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) : tiltW δ (n + 1) ≤ tiltW δ n := by
  unfold tiltW
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  push_cast
  linarith

/-- **Summation by parts**: the tilted head is the weighted sum of the growth sequence. -/
theorem tilted_eq_mean (a : ℕ → ℂ) (δ : ℝ) (N : ℕ) :
    tilted a δ N = ∑ k ∈ range N, (meanWeight δ N k : ℂ) * growth a (k + 1) := by
  cases N with
  | zero => simp [tilted]
  | succ M =>
    have hbp := Finset.sum_range_by_parts (fun n => (tiltW δ n : ℂ)) a (M + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at hbp
    unfold tilted
    refine hbp.trans ?_
    have hlast : meanWeight δ (M + 1) M = tiltW δ M := by
      simp [meanWeight]
    have hrest : ∑ k ∈ range M, (meanWeight δ (M + 1) k : ℂ) * growth a (k + 1)
        = ∑ i ∈ range M, ((tiltW δ i : ℂ) - (tiltW δ (i + 1) : ℂ)) * ∑ j ∈ range (i + 1), a j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have : meanWeight δ (M + 1) i = tiltW δ i - tiltW δ (i + 1) := by
        simp [meanWeight, show i + 1 < M + 1 by omega]
      rw [this, growth]
      push_cast
      ring
    have hsplit : ∑ k ∈ range (M + 1), (meanWeight δ (M + 1) k : ℂ) * growth a (k + 1)
        = ∑ k ∈ range M, (meanWeight δ (M + 1) k : ℂ) * growth a (k + 1)
          + (meanWeight δ (M + 1) M : ℂ) * growth a (M + 1) :=
      Finset.sum_range_succ _ M
    rw [hsplit, hlast, hrest, sub_eq_add_neg, ← Finset.sum_neg_distrib, add_comm]
    unfold growth
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The mean weights are nonnegative for `δ ≥ 0`. -/
theorem meanWeight_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (N k : ℕ) : 0 ≤ meanWeight δ N k := by
  unfold meanWeight
  split_ifs
  · linarith [tiltW_antitone hδ k]
  · exact (tiltW_pos δ k).le

/-- Telescoping: `Σ_{i<n} (w i − w (i+1)) = w 0 − w n`. -/
theorem sum_tiltW_telescope (δ : ℝ) (n : ℕ) :
    ∑ i ∈ range n, (tiltW δ i - tiltW δ (i + 1)) = tiltW δ 0 - tiltW δ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- The mean weights sum to `1`: the tilted head is a CONVEX mean of the growth sequence. -/
theorem meanWeight_sum (δ : ℝ) {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ range N, meanWeight δ N k = 1 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ]
  have hlast : meanWeight δ (M + 1) M = tiltW δ M := by simp [meanWeight]
  have hrest : ∑ k ∈ range M, meanWeight δ (M + 1) k = ∑ i ∈ range M, (tiltW δ i - tiltW δ (i + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp [meanWeight, show i + 1 < M + 1 by omega]
  rw [hlast, hrest, sum_tiltW_telescope, tiltW_zero]
  ring

/-- The real part of the tilted head against a direction `u` is the mean of the growth sequence's real parts. -/
theorem re_tilted_eq (a : ℕ → ℂ) (δ : ℝ) (N : ℕ) (u : ℂ) :
    (conj u * tilted a δ N).re = ∑ k ∈ range N, meanWeight δ N k * (conj u * growth a (k + 1)).re := by
  rw [tilted_eq_mean, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show conj u * ((meanWeight δ N k : ℂ) * growth a (k + 1))
      = (meanWeight δ N k : ℂ) * (conj u * growth a (k + 1)) by ring, Complex.re_ofReal_mul]

/-- **No tilt cancels a head whose growth sequence lies in an open half-plane.** A cancellation at any tilt `δ ≥ 0`
requires the native growth curve to wind around the origin. -/
theorem tilted_ne_zero_of_halfPlane (a : ℕ → ℂ) {δ : ℝ} (hδ : 0 ≤ δ) {N : ℕ} (hN : 0 < N) (u : ℂ)
    (hsep : ∀ k < N, 0 < (conj u * growth a (k + 1)).re) : tilted a δ N ≠ 0 := by
  intro h0
  have hre : (conj u * tilted a δ N).re = 0 := by rw [h0, mul_zero, Complex.zero_re]
  rw [re_tilted_eq] at hre
  have hpos : 0 < ∑ k ∈ range N, meanWeight δ N k * (conj u * growth a (k + 1)).re := by
    -- some weight is positive, since they are nonnegative and sum to `1`
    have hex : ∃ k ∈ range N, 0 < meanWeight δ N k := by
      by_contra hcon
      have hle : ∀ k ∈ range N, meanWeight δ N k ≤ 0 :=
        fun k hk => not_lt.mp fun h => hcon ⟨k, hk, h⟩
      have hzero : ∑ k ∈ range N, meanWeight δ N k = 0 :=
        Finset.sum_eq_zero fun k hk => le_antisymm (hle k hk) (meanWeight_nonneg hδ N k)
      rw [meanWeight_sum δ hN] at hzero
      exact one_ne_zero hzero
    obtain ⟨k, hk, hkpos⟩ := hex
    apply Finset.sum_pos' (fun i hi => mul_nonneg (meanWeight_nonneg hδ N i)
      (hsep i (Finset.mem_range.mp hi)).le)
    exact ⟨k, hk, mul_pos hkpos (hsep k (Finset.mem_range.mp hk))⟩
  linarith

end CriticalLinePhasor.HelixGrowthMean

end

#print axioms CriticalLinePhasor.HelixGrowthMean.tilted_eq_mean
#print axioms CriticalLinePhasor.HelixGrowthMean.meanWeight_sum
#print axioms CriticalLinePhasor.HelixGrowthMean.tilted_ne_zero_of_halfPlane
