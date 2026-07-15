import RequestProject.CarrierThetaIdentification

/-!
# Rapid decay of coefficient-assembled carrier theta functions

A polynomial coefficient bound is absorbed by sufficiently rapid decay of the completion kernel.
The proof is uniform in the readout variable: after bounding the `n`th term by
`x^q (n+1)^(A+q)`, the shifted p-series closes the infinite carrier bank.
-/

open Complex Set Filter Topology MeasureTheory Asymptotics
open scoped BigOperators

namespace CriticalLinePhasor.CarrierTheta

/-- If the kernel is `O(x^q)` and `A + q < -1`, a coefficient theta with exponent `A` is also
`O(x^q)`. -/
theorem theta_isBigO_of_polynomial_of_kernel
    (a : ℕ → ℂ) (g : ℝ → ℂ) (C A q : ℝ)
    (hC : 0 ≤ C)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (((n + 1 : ℕ) : ℝ) ^ A))
    (hq : A + q < -1)
    (hg : g =O[atTop] (fun x : ℝ => x ^ q)) :
    theta a g =O[atTop] (fun x : ℝ => x ^ q) := by
  rw [isBigO_iff'] at hg ⊢
  obtain ⟨D, hDpos, hD⟩ := hg
  obtain ⟨b, hb⟩ := (eventually_atTop.1 hD)
  have hpow : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (A + q))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (A + q)) :=
      Real.summable_nat_rpow.mpr hq
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hbase
  let S : ℝ := ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (A + q))
  have hS : 0 ≤ S := tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
  refine ⟨1 + C * D * S, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max b 1)] with x hx
  have hx1 : 1 ≤ x := (le_max_right b 1).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hterm : ∀ n : ℕ,
      ‖a n * g ((n + 1 : ℕ) * x)‖ ≤
        (C * D * x ^ q) * (((n + 1 : ℕ) : ℝ) ^ (A + q)) := by
    intro n
    let N : ℝ := (n + 1 : ℕ)
    have hN : 0 < N := by dsimp [N]; positivity
    have hxN : b ≤ N * x := by
      apply (le_max_left b 1).trans
      calc
        max b 1 ≤ x := hx
        _ ≤ N * x := by
          have hN1 : 1 ≤ N := by
            dsimp [N]
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          nlinarith
    have hgN := hb (N * x) hxN
    have hNpow : 0 ≤ N ^ A := Real.rpow_nonneg hN.le _
    calc
      ‖a n * g ((n + 1 : ℕ) * x)‖ = ‖a n‖ * ‖g (N * x)‖ := by simp [N]
      _ ≤ (C * N ^ A) * (D * ‖(N * x) ^ q‖) :=
        mul_le_mul (ha n) hgN (norm_nonneg _) (mul_nonneg hC hNpow)
      _ = (C * D * x ^ q) * N ^ (A + q) := by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (mul_nonneg hN.le hx0.le) _),
          Real.mul_rpow hN.le hx0.le, Real.rpow_add hN]
        ring
      _ = (C * D * x ^ q) * (((n + 1 : ℕ) : ℝ) ^ (A + q)) := rfl
  have hmajor : Summable (fun n : ℕ =>
      (C * D * x ^ q) * (((n + 1 : ℕ) : ℝ) ^ (A + q))) :=
    hpow.mul_left (C * D * x ^ q)
  calc
    ‖theta a g x‖ ≤ ∑' n : ℕ,
        (C * D * x ^ q) * (((n + 1 : ℕ) : ℝ) ^ (A + q)) := by
      unfold theta
      exact tsum_of_norm_bounded hmajor.hasSum hterm
    _ = (C * D * S) * x ^ q := by
      rw [tsum_mul_left]
      dsimp [S]
      ring
    _ ≤ (1 + C * D * S) * x ^ q := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0.le _)
      linarith
    _ = (1 + C * D * S) * ‖x ^ q‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]

/-- On `x → +∞`, a smaller real-power exponent is big-O of a larger one. -/
theorem rpow_isBigO_rpow_atTop_of_le {q r : ℝ} (hqr : q ≤ r) :
    (fun x : ℝ => x ^ q) =O[atTop] (fun x : ℝ => x ^ r) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  exact Real.rpow_le_rpow_of_exponent_le hx.le hqr

/-- A kernel decaying faster than every power passes that rapid decay to a coefficient theta with
polynomially bounded coefficients. -/
theorem theta_rapid_of_polynomial_of_kernel_rapid
    (a : ℕ → ℂ) (g : ℝ → ℂ) (C A : ℝ)
    (hC : 0 ≤ C)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (((n + 1 : ℕ) : ℝ) ^ A))
    (hg : ∀ q : ℝ, g =O[atTop] (fun x : ℝ => x ^ q)) :
    ∀ r : ℝ, theta a g =O[atTop] (fun x : ℝ => x ^ r) := by
  intro r
  let q := min r (-A - 2)
  have hqr : q ≤ r := min_le_left _ _
  have hqsum : A + q < -1 := by
    have hqA : q ≤ -A - 2 := min_le_right _ _
    linarith
  exact (theta_isBigO_of_polynomial_of_kernel a g C A q hC ha hqsum (hg q)).trans
    (rpow_isBigO_rpow_atTop_of_le hqr)

end CriticalLinePhasor.CarrierTheta

#print axioms CriticalLinePhasor.CarrierTheta.theta_isBigO_of_polynomial_of_kernel
#print axioms CriticalLinePhasor.CarrierTheta.rpow_isBigO_rpow_atTop_of_le
#print axioms CriticalLinePhasor.CarrierTheta.theta_rapid_of_polynomial_of_kernel_rapid
