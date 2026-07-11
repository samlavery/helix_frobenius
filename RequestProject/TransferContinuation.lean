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
* `TransferContinuation.transfer_tendsto_tsum` : the same convergence, with the Abel-summed limit
  named explicitly;
* `TransferContinuation.transfer_analytic` : the limit function is analytic (`DifferentiableOn ℂ`)
  on the open half-plane `{Re s > θ}` — the local-uniformity upgrade of `lem:transfer`, obtained
  from the Weierstrass M-test applied to the (locally normally convergent) Abel series;
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

/-- THE TRANSFER (sharp form), explicit limit: a polynomially bounded primitive continues the
Dirichlet series, and the limit is the Abel-summed value
`0 − ∑_i ((i+2)^{-s} − (i+1)^{-s})·(∑_{k<i+1} a k)`.  If `‖∑_{k<n} a k‖ ≤ C·n^θ` and
`Re s > θ ≥ 0`, the partial sums of `∑ a n · (n+1)^{-s}` converge to this value. -/
theorem transfer_tendsto_tsum (a : ℕ → ℂ) (C θ : ℝ) (hθ : 0 ≤ θ)
    (hA : ∀ n : ℕ, ‖∑ k ∈ range n, a k‖ ≤ C * (n : ℝ) ^ θ)
    (s : ℂ) (hs : θ < s.re) :
    Tendsto (fun N => ∑ n ∈ range N, a n * ((n + 1 : ℕ) : ℂ) ^ (-s)) atTop
      (𝓝 (0 - ∑' i : ℕ, (((i + 1 + 1 : ℕ) : ℂ) ^ (-s) - ((i + 1 : ℕ) : ℂ) ^ (-s))
              * (∑ k ∈ range (i + 1), a k))) := by
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
  have hT : Tendsto (fun m : ℕ => ∑ i ∈ range m, d i) atTop (𝓝 (∑' i, d i)) :=
    hdsum.hasSum.tendsto_sum_nat
  have hTshift : Tendsto (fun n : ℕ => ∑ i ∈ range (n - 1), d i)
      atTop (𝓝 (∑' i, d i)) :=
    hT.comp (Filter.tendsto_sub_atTop_nat 1)
  have hfinal := hB.sub hTshift
  exact hfinal.congr fun n => (key n).symm

/-- THE TRANSFER (sharp form): a polynomially bounded primitive continues the Dirichlet
series.  If `‖∑_{k<n} a k‖ ≤ C·n^θ` and `Re s > θ ≥ 0`, the partial sums of
`∑ a n · (n+1)^{-s}` converge. -/
theorem transfer_tendsto (a : ℕ → ℂ) (C θ : ℝ) (hθ : 0 ≤ θ)
    (hA : ∀ n : ℕ, ‖∑ k ∈ range n, a k‖ ≤ C * (n : ℝ) ^ θ)
    (s : ℂ) (hs : θ < s.re) :
    ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ range N, a n * ((n + 1 : ℕ) : ℂ) ^ (-s))
      atTop (𝓝 L) :=
  ⟨_, transfer_tendsto_tsum a C θ hθ hA s hs⟩

/-- ANALYTICITY UPGRADE of `lem:transfer`.  Under the same hypotheses as `transfer_tendsto`
(a primitive bound `‖∑_{k<n} a k‖ ≤ C·n^θ`, `0 ≤ θ`), the limit function `F` of the Dirichlet
partial sums is complex-analytic on the open half-plane `{Re s > θ}`, and the partial sums
converge to `F s` at every such `s`.  This is exactly the pointwise-to-analytic step: `F` is
realised as the Abel-summed series
`s ↦ 0 − ∑_i ((i+2)^{-s} − (i+1)^{-s})·(∑_{k<i+1} a k)`, whose terms are entire and which
converges normally on every closed ball inside the half-plane (Weierstrass M-test through
`Complex.differentiableOn_tsum_of_summable_norm`), hence is holomorphic there.  Does not assume
or prove RH/GRH; no automorphy, functional equation or Poisson summation is consumed. -/
theorem transfer_analytic (a : ℕ → ℂ) (C θ : ℝ) (hθ : 0 ≤ θ)
    (hA : ∀ n : ℕ, ‖∑ k ∈ range n, a k‖ ≤ C * (n : ℝ) ^ θ) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | θ < s.re} ∧
      ∀ s : ℂ, θ < s.re →
        Tendsto (fun N => ∑ n ∈ range N, a n * ((n + 1 : ℕ) : ℂ) ^ (-s)) atTop (𝓝 (F s)) := by
  have hC : 0 ≤ C := by
    have h := hA 1
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
    exact le_trans (norm_nonneg _) h
  -- `F` = the Abel-summed limit produced by `transfer_tendsto_tsum`
  refine ⟨fun s => 0 - ∑' i : ℕ,
      (((i + 1 + 1 : ℕ) : ℂ) ^ (-s) - ((i + 1 : ℕ) : ℂ) ^ (-s)) * (∑ k ∈ range (i + 1), a k),
      ?_, ?_⟩
  · -- analyticity: differentiability is local, so it suffices to differentiate `F` at each `z₀`
    intro z₀ hz₀
    have hz₀' : θ < z₀.re := hz₀
    -- a closed ball around `z₀` that stays strictly right of the abscissa `θ`
    set r : ℝ := (z₀.re - θ) / 2 with hr_def
    have hr : 0 < r := by rw [hr_def]; linarith
    set σ : ℝ := z₀.re - r with hσ_def
    have hσθ : θ < σ := by rw [hσ_def, hr_def]; linarith
    set M : ℝ := ‖z₀‖ + r with hM_def
    have hM : 0 ≤ M := by rw [hM_def]; positivity
    set B : Set ℂ := Metric.ball z₀ r with hB_def
    -- the Weierstrass majorant on `B`: `Re s ≥ σ > θ` and `‖s‖ ≤ M`
    have husum : Summable (fun i : ℕ => (M * C) * ((i + 1 : ℕ) : ℝ) ^ (θ - σ - 1)) := by
      apply Summable.mul_left
      have hp : θ - σ - 1 < -1 := by linarith
      exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
    -- each Abel term is entire, in particular differentiable on `B`
    have hdiff : ∀ i : ℕ, DifferentiableOn ℂ
        (fun s : ℂ => (((i + 1 + 1 : ℕ) : ℂ) ^ (-s) - ((i + 1 : ℕ) : ℂ) ^ (-s))
          * (∑ k ∈ range (i + 1), a k)) B := by
      intro i
      apply Differentiable.differentiableOn
      apply Differentiable.mul_const
      apply Differentiable.sub
      · exact (differentiable_id.neg).const_cpow (Or.inl (Nat.cast_ne_zero.mpr (by omega)))
      · exact (differentiable_id.neg).const_cpow (Or.inl (Nat.cast_ne_zero.mpr (by omega)))
    -- the uniform bound `‖term i w‖ ≤ (M·C)·(i+1)^{θ-σ-1}` on `B`
    have hbound : ∀ i : ℕ, ∀ w ∈ B,
        ‖(((i + 1 + 1 : ℕ) : ℂ) ^ (-w) - ((i + 1 : ℕ) : ℂ) ^ (-w))
            * (∑ k ∈ range (i + 1), a k)‖
          ≤ (M * C) * ((i + 1 : ℕ) : ℝ) ^ (θ - σ - 1) := by
      intro i w hw
      rw [hB_def, Metric.mem_ball, Complex.dist_eq] at hw
      have hwre : σ ≤ w.re := by
        have h1 : |w.re - z₀.re| ≤ ‖w - z₀‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z₀)
        have := (abs_le.mp h1).1
        rw [hσ_def]; linarith
      have hwnorm : ‖w‖ ≤ M := by
        have h2 : ‖w‖ - ‖z₀‖ ≤ ‖w - z₀‖ := norm_sub_norm_le w z₀
        rw [hM_def]; linarith
      have hwre0 : 0 < w.re := lt_of_lt_of_le (lt_of_le_of_lt hθ hσθ) hwre
      have hcpow : ‖((i + 1 + 1 : ℕ) : ℂ) ^ (-w) - ((i + 1 : ℕ) : ℂ) ^ (-w)‖
          ≤ ‖w‖ * ((i + 1 : ℕ) : ℝ) ^ (-w.re - 1) :=
        cpow_sub_bound w hwre0 (k := i + 1) (Nat.le_add_left 1 i)
      have hAb : ‖∑ k ∈ range (i + 1), a k‖ ≤ C * ((i + 1 : ℕ) : ℝ) ^ θ := hA (i + 1)
      have hpos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
      have hbase : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 i
      have hexp : (-w.re - 1) + θ = θ - w.re - 1 := by ring
      have e1 : ‖(((i + 1 + 1 : ℕ) : ℂ) ^ (-w) - ((i + 1 : ℕ) : ℂ) ^ (-w))
            * (∑ k ∈ range (i + 1), a k)‖
          ≤ (‖w‖ * C) * ((i + 1 : ℕ) : ℝ) ^ (θ - w.re - 1) := by
        calc ‖(((i + 1 + 1 : ℕ) : ℂ) ^ (-w) - ((i + 1 : ℕ) : ℂ) ^ (-w))
              * (∑ k ∈ range (i + 1), a k)‖
            = ‖((i + 1 + 1 : ℕ) : ℂ) ^ (-w) - ((i + 1 : ℕ) : ℂ) ^ (-w)‖
                * ‖∑ k ∈ range (i + 1), a k‖ := norm_mul _ _
          _ ≤ (‖w‖ * ((i + 1 : ℕ) : ℝ) ^ (-w.re - 1)) * (C * ((i + 1 : ℕ) : ℝ) ^ θ) := by
              apply mul_le_mul hcpow hAb (norm_nonneg _); positivity
          _ = (‖w‖ * C) * (((i + 1 : ℕ) : ℝ) ^ (-w.re - 1) * ((i + 1 : ℕ) : ℝ) ^ θ) := by ring
          _ = (‖w‖ * C) * ((i + 1 : ℕ) : ℝ) ^ (θ - w.re - 1) := by
              rw [← Real.rpow_add hpos, hexp]
      have e2 : (‖w‖ * C) * ((i + 1 : ℕ) : ℝ) ^ (θ - w.re - 1)
          ≤ (M * C) * ((i + 1 : ℕ) : ℝ) ^ (θ - σ - 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hwnorm hC)
          (Real.rpow_le_rpow_of_exponent_le hbase (by linarith))
          (Real.rpow_nonneg (le_of_lt hpos) _) (mul_nonneg hM hC)
      exact le_trans e1 e2
    -- Weierstrass M-test: the Abel series is holomorphic on the ball `B`
    have hDiffOn : DifferentiableOn ℂ (fun s : ℂ => ∑' i : ℕ,
        (((i + 1 + 1 : ℕ) : ℂ) ^ (-s) - ((i + 1 : ℕ) : ℂ) ^ (-s))
          * (∑ k ∈ range (i + 1), a k)) B :=
      Complex.differentiableOn_tsum_of_summable_norm husum hdiff
        (by rw [hB_def]; exact Metric.isOpen_ball) hbound
    have hAt : DifferentiableAt ℂ (fun s : ℂ => ∑' i : ℕ,
        (((i + 1 + 1 : ℕ) : ℂ) ^ (-s) - ((i + 1 : ℕ) : ℂ) ^ (-s))
          * (∑ k ∈ range (i + 1), a k)) z₀ :=
      hDiffOn.differentiableAt
        (by rw [hB_def]; exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
    exact (hAt.const_sub 0).differentiableWithinAt
  · -- agreement: `transfer_tendsto_tsum` already lands on the chosen `F s`
    intro s hs
    exact transfer_tendsto_tsum a C θ hθ hA s hs

end TransferContinuation

#print axioms TransferContinuation.transfer_analytic
