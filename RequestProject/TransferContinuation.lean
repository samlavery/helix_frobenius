import Mathlib

/-!
# The transfer, formalized: sub-random-walk continuation (sharp form)

`lem:transfer` of the manuscript: if the coefficient primitive is polynomially bounded,
`‖∑_{k<n} a k‖ ≤ C·n^θ`, then for `Re s > θ ≥ 0` the partial sums of the Dirichlet series
`∑ a n · (n+1)^{-s}` converge.  This is the arithmetic-sensitive continuation input of the
niceness chain in its provable form: no automorphy, no functional equation, no Poisson
summation is consumed.  `strip_contains_axis` records that the input `θ < κ/2` places both
completed readouts on a common open strip containing the weld axis; `dual_primitive_norm`
that the unitary dual carries the same exponent for free.

Main results:
* `TransferContinuation.cpow_sub_bound`   : MVT step, `‖(k+1)^{-s} − k^{-s}‖ ≤ ‖s‖·k^{-Re s-1}`;
* `TransferContinuation.transfer_tendsto` : the partial sums converge for `Re s > θ ≥ 0`;
* `TransferContinuation.dual_primitive_norm`, `TransferContinuation.strip_contains_axis`.
-/

namespace TransferContinuation

open Finset Filter Complex Topology

/-- Mean-value step: the difference of consecutive complex-power weights at exponent `-s`
is bounded by `‖s‖ · k^(-Re s - 1)` for `k ≥ 1`. -/
lemma cpow_sub_bound (s : ℂ) (hs : 0 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖((k + 1 : ℕ) : ℂ) ^ (-s) - ((k : ℕ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsne : -s ≠ 0 := by
    simp only [ne_eq, neg_eq_zero]
    intro h; rw [h] at hs; simp at hs
  have hderiv : ∀ x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1),
      HasDerivWithinAt (fun x : ℝ => (x : ℂ) ^ (-s))
        ((-s) * (x : ℂ) ^ (-s - 1)) (Set.Icc (k : ℝ) ((k : ℝ) + 1)) x := by
    intro x hx
    exact (hasDerivAt_ofReal_cpow_const
      (ne_of_gt (lt_of_lt_of_le hk0 hx.1)) hsne).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (k : ℝ) ((k : ℝ) + 1),
      ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
    intro x hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hk0 hx.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    have hre : (-s - 1 : ℂ).re = -s.re - 1 := by
      simp [Complex.sub_re, Complex.neg_re]
    rw [hre]
    have h2 : x ^ (-s.re - 1) ≤ (k : ℝ) ^ (-s.re - 1) := by
      apply Real.rpow_le_rpow_of_nonpos hk0 hx.1
      linarith
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg s)
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound
      ((k : ℝ) + 1) (Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩)
  have h0 : ((k + 1 : ℕ) : ℂ) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have h0' : ((k : ℕ) : ℂ) = (((k : ℝ) : ℝ) : ℂ) := by norm_cast
  rw [h0, h0']
  have heq : ‖s‖ * (k : ℝ) ^ (-s.re - 1) * (((k : ℝ) + 1) - (k : ℝ))
      = ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by ring
  exact le_trans key (le_of_eq heq)

/-- The unitary dual has the same primitive norm, hence the same transfer exponent. -/
theorem dual_primitive_norm (a : ℕ → ℂ) (n : ℕ) :
    ‖∑ k ∈ range n, (starRingEnd ℂ) (a k)‖ = ‖∑ k ∈ range n, a k‖ := by
  rw [← map_sum]
  exact RCLike.norm_conj _

/-- The exponent condition `θ < κ/2` places the weld axis inside the common analyticity
strip `(θ, κ−θ)` of the two completed readouts. -/
theorem strip_contains_axis {θ κ : ℝ} (h : θ < κ / 2) : θ < κ / 2 ∧ κ / 2 < κ - θ :=
  ⟨h, by linarith⟩

/-- THE TRANSFER (sharp form): a polynomially bounded primitive continues the Dirichlet
series.  If `‖∑_{k<n} a k‖ ≤ C·n^θ` and `Re s > θ ≥ 0`, the partial sums of
`∑ a n · (n+1)^{-s}` converge. -/
theorem transfer_tendsto (a : ℕ → ℂ) (C θ : ℝ) (hθ : 0 ≤ θ)
    (hA : ∀ n : ℕ, ‖∑ k ∈ range n, a k‖ ≤ C * (n : ℝ) ^ θ)
    (s : ℂ) (hs : θ < s.re) :
    ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ range N, a n * ((n + 1 : ℕ) : ℂ) ^ (-s))
      atTop (𝓝 L) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt hθ hs
  have hC : 0 ≤ C := by
    have h := hA 1
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
    exact le_trans (norm_nonneg _) h
  set f : ℕ → ℂ := fun i => ((i + 1 : ℕ) : ℂ) ^ (-s) with hf
  set A : ℕ → ℂ := fun n => ∑ k ∈ range n, a k with hAdef
  set d : ℕ → ℂ := fun i => (f (i + 1) - f i) * A (i + 1) with hd
  -- summation by parts, valid for every n (ℕ-subtraction conventions included)
  have key : ∀ n : ℕ, (∑ i ∈ range n, a i * f i)
      = f (n - 1) * A n - ∑ i ∈ range (n - 1), d i := by
    intro n
    have h := Finset.sum_range_by_parts f a n
    simp only [smul_eq_mul] at h
    have hcomm : (∑ i ∈ range n, a i * f i) = ∑ i ∈ range n, f i * a i :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hcomm, h]
  -- the difference series is absolutely summable
  have hmaj : Summable (fun i : ℕ => (C * ‖s‖) * ((i + 1 : ℕ) : ℝ) ^ (θ - s.re - 1)) := by
    apply Summable.mul_left
    have hp : θ - s.re - 1 < -1 := by linarith
    exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  have hdsum : Summable d := by
    refine Summable.of_norm_bounded hmaj ?_
    intro i
    have hbd : ‖f (i + 1) - f i‖ ≤ ‖s‖ * ((i + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by
      simp only [hf]
      exact cpow_sub_bound s hs0 (k := i + 1) (Nat.le_add_left 1 i)
    have hAb : ‖A (i + 1)‖ ≤ C * ((i + 1 : ℕ) : ℝ) ^ θ := hA (i + 1)
    have hpos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have hexp : (-s.re - 1) + θ = θ - s.re - 1 := by ring
    calc ‖d i‖ = ‖f (i + 1) - f i‖ * ‖A (i + 1)‖ := by rw [hd]; exact norm_mul _ _
      _ ≤ (‖s‖ * ((i + 1 : ℕ) : ℝ) ^ (-s.re - 1)) * (C * ((i + 1 : ℕ) : ℝ) ^ θ) := by
          apply mul_le_mul hbd hAb (norm_nonneg _)
          positivity
      _ = (C * ‖s‖) * (((i + 1 : ℕ) : ℝ) ^ (-s.re - 1) * ((i + 1 : ℕ) : ℝ) ^ θ) := by ring
      _ = (C * ‖s‖) * ((i + 1 : ℕ) : ℝ) ^ (θ - s.re - 1) := by
          rw [← Real.rpow_add hpos, hexp]
  -- the boundary term tends to zero
  have hupper : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (θ - s.re)) atTop (𝓝 0) := by
    have hneg : (0 : ℝ) < s.re - θ := by linarith
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ)) ^ (-(s.re - θ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hneg).comp tendsto_natCast_atTop_atTop
    have h3 := h2.const_mul C
    rw [mul_zero] at h3
    simpa [neg_sub] using h3
  have hB : Tendsto (fun n : ℕ => f (n - 1) * A n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
    · filter_upwards with n
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := hn
        exact_mod_cast this
      have hfe : f (n - 1) = ((n : ℕ) : ℂ) ^ (-s) := by
        simp only [hf]
        congr 2
        omega
      have h1 : ‖f (n - 1)‖ = (n : ℝ) ^ (-s.re) := by
        rw [hfe, Complex.norm_natCast_cpow_of_pos hn]
        simp
      calc ‖f (n - 1) * A n‖ = ‖f (n - 1)‖ * ‖A n‖ := norm_mul _ _
        _ ≤ (n : ℝ) ^ (-s.re) * (C * (n : ℝ) ^ θ) := by
            rw [h1]
            exact mul_le_mul_of_nonneg_left (hA n) (by positivity)
        _ = C * (n : ℝ) ^ (θ - s.re) := by
            rw [show θ - s.re = -s.re + θ by ring, Real.rpow_add hn0]
            ring
  -- assemble: partial sums = boundary − shifted partial sums of d
  refine ⟨0 - ∑' i, d i, ?_⟩
  have hT : Tendsto (fun m : ℕ => ∑ i ∈ range m, d i) atTop (𝓝 (∑' i, d i)) :=
    hdsum.hasSum.tendsto_sum_nat
  have hTshift : Tendsto (fun n : ℕ => ∑ i ∈ range (n - 1), d i)
      atTop (𝓝 (∑' i, d i)) :=
    hT.comp (Filter.tendsto_sub_atTop_nat 1)
  have hfinal := hB.sub hTshift
  exact hfinal.congr fun n => (key n).symm

end TransferContinuation
