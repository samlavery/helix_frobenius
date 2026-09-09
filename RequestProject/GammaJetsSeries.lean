import RequestProject.ExplicitAnchor
import Zeta23.Analytic.Stirling

/-!
# The Γ jets as series to all orders (ledger 629)

The corpus has the digamma series (`Zeta23.DigammaSeries.hasSum_digamma_series`) and its first
derivative, the trigamma series (`Zeta23.Stirling.hasSum_trigamma`), the latter by termwise
differentiation on a ball with Mathlib's `hasSum_deriv_of_summable_norm`. This file iterates that
step to every order:

* `hasSum_deriv_inv_pow_series`: for `k ≥ 2` and `z` off the integers,
  `∂_z Σ_n (z+n)^{−k} = Σ_n −k (z+n)^{−(k+1)}`, termwise;
* **`iteratedDeriv_digamma_series`**: for `k ≥ 1`,
  `ψ^{(k)}(z) = (−1)^{k+1} k! Σ_{n≥0} (z+n)^{−(k+1)}` — the polygamma series;
* `hasSum_polygamma`: the same as a `HasSum`;
* `iteratedDeriv_digamma_half_one_sub`: the jets of `s ↦ ψ((1−s)/2)`, the Archimedean variable of the
  explicit anchor, are `(−½)^k ψ^{(k)}((1−s)/2)`.

Every Γ jet of the explicit anchor is therefore an absolutely convergent series over the Γ ticks.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.SeatingLedger

/-- **Termwise derivative of `Σ_n (w+n)^{−k}`** (`k ≥ 2`) at a point off the integers. -/
theorem hasSum_deriv_inv_pow_series {z : ℂ} (hz : z ∈ Complex.integerComplement) {k : ℕ}
    (hk : 2 ≤ k) :
    HasSum (fun n : ℕ => -(k : ℂ) / (z + n) ^ (k + 1))
      (deriv (fun w : ℂ => ∑' n : ℕ, (1 : ℂ) / (w + n) ^ k) z) := by
  obtain ⟨ε, hε0, hball⟩ := Metric.isOpen_iff.mp isOpen_compl_range_intCast z hz
  have hr0 : 0 < ε / 2 := by positivity
  set U : Set ℂ := Metric.ball z (ε / 2) with hU
  have hzU : z ∈ U := Metric.mem_ball_self hr0
  have hδ : ∀ n : ℕ, ε ≤ ‖z + n‖ := by
    intro n
    by_contra hlt
    push Not at hlt
    have hmem : (-(n : ℂ)) ∈ Metric.ball z ε := by
      rw [Metric.mem_ball, dist_eq_norm, show -(n : ℂ) - z = -(z + n) by ring, norm_neg]
      exact hlt
    exact hball hmem ⟨-(n : ℤ), by push_cast; ring⟩
  have hlow : ∀ (n : ℕ) (w : ℂ), w ∈ U → ‖z + n‖ - ε / 2 ≤ ‖w + n‖ := by
    intro n w hw
    have hwz : ‖z - w‖ < ε / 2 := by
      rw [norm_sub_rev, ← dist_eq_norm]; exact Metric.mem_ball.mp hw
    have : ‖z + n‖ ≤ ‖w + n‖ + ‖z - w‖ := by
      calc ‖z + n‖ = ‖(w + n) + (z - w)‖ := by ring_nf
        _ ≤ ‖w + n‖ + ‖z - w‖ := norm_add_le _ _
    linarith
  have hpos : ∀ n : ℕ, 0 < ‖z + n‖ - ε / 2 := fun n => by have := hδ n; linarith
  have hne : ∀ (n : ℕ) (w : ℂ), w ∈ U → w + n ≠ 0 := by
    intro n w hw h0
    have := hlow n w hw
    rw [h0, norm_zero] at this
    linarith [hpos n]
  set u : ℕ → ℝ := fun n => 1 / (‖z + n‖ - ε / 2) ^ k with hu
  have hFle : ∀ (n : ℕ) (w : ℂ), w ∈ U → ‖(1 : ℂ) / (w + n) ^ k‖ ≤ u n := by
    intro n w hw
    rw [norm_div, norm_one, norm_pow, hu]
    exact one_div_le_one_div_of_le (pow_pos (hpos n) k)
      (pow_le_pow_left₀ (hpos n).le (hlow n w hw) k)
  have husum : Summable u := by
    have hg : Summable (fun n : ℕ => (2 : ℝ) ^ k * (1 / ((n : ℝ) + 1) ^ k)) := by
      have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ k) :=
        Real.summable_one_div_nat_pow.mpr (by omega)
      have h2 := (summable_nat_add_iff 1).mpr h1
      exact (h2.congr (fun n => by rw [Nat.cast_add_one])).mul_left _
    refine Summable.of_norm_bounded_eventually hg ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop ⌈2 * (‖z‖ + ε / 2 + 1)⌉₊] with n hn
    have hn2 : 2 * (‖z‖ + ε / 2 + 1) ≤ (n : ℝ) := by
      calc 2 * (‖z‖ + ε / 2 + 1) ≤ (⌈2 * (‖z‖ + ε / 2 + 1)⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (n : ℝ) := by exact_mod_cast hn
    have hzn : ((n : ℝ) + 1) / 2 ≤ ‖z + n‖ - ε / 2 := by
      have h1 : ‖(n : ℂ)‖ - ‖z‖ ≤ ‖z + n‖ := by
        have h2 := norm_sub_le (z + n) z
        rw [show z + (n : ℂ) - z = (n : ℂ) by ring] at h2
        linarith
      rw [Complex.norm_natCast] at h1
      linarith [norm_nonneg z]
    rw [Real.norm_eq_abs, hu]
    simp only
    rw [abs_of_pos (one_div_pos.mpr (pow_pos (hpos n) k))]
    calc 1 / (‖z + n‖ - ε / 2) ^ k ≤ 1 / (((n : ℝ) + 1) / 2) ^ k :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hzn k)
      _ = (2 : ℝ) ^ k * (1 / ((n : ℝ) + 1) ^ k) := by rw [div_pow, one_div_div]; ring
  have hFdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun w : ℂ => (1 : ℂ) / (w + n) ^ k) U := by
    intro n w hw
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (w + n) ^ k) w :=
      (differentiableAt_id.add_const _).pow k
    exact (differentiableAt_const _).div h1 (pow_ne_zero k (hne n w hw))
  have hkey := hasSum_deriv_of_summable_norm husum hFdiff Metric.isOpen_ball hFle hzU
  have hderiv : ∀ n : ℕ,
      deriv (fun w : ℂ => (1 : ℂ) / (w + n) ^ k) z = -(k : ℂ) / (z + n) ^ (k + 1) := by
    intro n
    have h0 := hne n z hzU
    have h1 : HasDerivAt (fun w : ℂ => (w + n) ^ k) ((k : ℂ) * (z + n) ^ (k - 1) * 1) z :=
      ((hasDerivAt_id z).add_const _).pow k
    have h2 : HasDerivAt (fun w : ℂ => ((w + (n : ℂ)) ^ k)⁻¹)
        (-((k : ℂ) * (z + n) ^ (k - 1) * 1) / ((z + n) ^ k) ^ 2) z := h1.inv (pow_ne_zero k h0)
    rw [show (fun w : ℂ => (1 : ℂ) / (w + n) ^ k) = fun w : ℂ => ((w + (n : ℂ)) ^ k)⁻¹ by
      funext w; rw [one_div]]
    rw [h2.deriv]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  simp only [hderiv] at hkey
  exact hkey

/-- **The polygamma series, every order**: for `k ≥ 1` and `z` off the integers,
`ψ^{(k)}(z) = (−1)^{k+1} k! Σ_{n≥0} 1/(z+n)^{k+1}`. -/
theorem iteratedDeriv_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) {k : ℕ}
    (hk : 1 ≤ k) :
    iteratedDeriv k Complex.digamma z
      = (-1) ^ (k + 1) * (k.factorial : ℂ) * ∑' n : ℕ, (1 : ℂ) / (z + n) ^ (k + 1) := by
  induction k generalizing z with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      have h := (Zeta23.Stirling.hasSum_trigamma hz).tsum_eq
      show iteratedDeriv 1 Complex.digamma z
        = (-1) ^ 2 * ((Nat.factorial 1 : ℕ) : ℂ) * ∑' n : ℕ, (1 : ℂ) / (z + n) ^ 2
      rw [iteratedDeriv_one, ← h]
      norm_num
    · rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k Complex.digamma =ᶠ[nhds z]
          fun w => (-1) ^ (k + 1) * (k.factorial : ℂ) * ∑' n : ℕ, (1 : ℂ) / (w + n) ^ (k + 1) := by
        filter_upwards [isOpen_compl_range_intCast.mem_nhds hz] with w hw
        exact ih hw hpos
      rw [hev.deriv_eq, deriv_const_mul_field,
        ← (hasSum_deriv_inv_pow_series hz (by omega : 2 ≤ k + 1)).tsum_eq]
      rw [show (fun n : ℕ => -((k + 1 : ℕ) : ℂ) / (z + n) ^ (k + 1 + 1))
          = fun n : ℕ => (-((k + 1 : ℕ) : ℂ)) * ((1 : ℂ) / (z + n) ^ (k + 1 + 1)) from
        funext (fun n => by ring), tsum_mul_left, Nat.factorial_succ]
      push_cast
      ring

/-- The polygamma series as a `HasSum` (`k ≥ 1`). -/
theorem hasSum_polygamma {z : ℂ} (hz : z ∈ Complex.integerComplement) {k : ℕ} (hk : 1 ≤ k) :
    HasSum (fun n : ℕ => (1 : ℂ) / (z + n) ^ (k + 1))
      ((-1) ^ (k + 1) / (k.factorial : ℂ) * iteratedDeriv k Complex.digamma z) := by
  have hsum : Summable (fun n : ℕ => (1 : ℂ) / (z + n) ^ (k + 1)) := by
    rcases Nat.eq_zero_or_pos (k - 1) with h0 | hpos
    · have hk1 : k = 1 := by omega
      subst hk1
      exact (Zeta23.Stirling.hasSum_trigamma hz).summable
    · have h := (hasSum_deriv_inv_pow_series hz (k := k) (by omega)).summable
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      refine (h.mul_left (-(k : ℂ))⁻¹).congr (fun n => ?_)
      field_simp
  have hf : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hsq : ((-1 : ℂ) ^ (k + 1)) ^ 2 = 1 := by
    rw [← pow_mul]; exact Even.neg_one_pow ⟨k + 1, by ring⟩
  have hT : ∑' n : ℕ, (1 : ℂ) / (z + n) ^ (k + 1)
      = (-1) ^ (k + 1) / (k.factorial : ℂ) * iteratedDeriv k Complex.digamma z := by
    rw [iteratedDeriv_digamma_series hz hk,
      show (-1 : ℂ) ^ (k + 1) / (k.factorial : ℂ)
          * ((-1) ^ (k + 1) * (k.factorial : ℂ) * ∑' n : ℕ, (1 : ℂ) / (z + n) ^ (k + 1))
        = ((-1 : ℂ) ^ (k + 1)) ^ 2 * ((k.factorial : ℂ) / (k.factorial : ℂ))
          * ∑' n : ℕ, (1 : ℂ) / (z + n) ^ (k + 1) by ring, hsq, div_self hf, one_mul, one_mul]
  rw [← hT]
  exact hsum.hasSum

/-- The open set where the Archimedean variable `(1 − s)/2` is off the integers. -/
theorem isOpen_archDomain :
    IsOpen {s : ℂ | (1 - s) / 2 ∈ Complex.integerComplement} :=
  isOpen_compl_range_intCast.preimage (by fun_prop)

theorem digamma_contDiffOn :
    ContDiffOn ℂ (⊤ : ℕ∞) Complex.digamma Complex.integerComplement := by
  refine DifferentiableOn.contDiffOn ?_ isOpen_compl_range_intCast
  intro z hz
  exact (Zeta23.Stirling.differentiableAt_digamma hz).differentiableWithinAt

theorem iteratedDeriv_digamma_hasDerivAt (k : ℕ) {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasDerivAt (iteratedDeriv k Complex.digamma) (iteratedDeriv (k + 1) Complex.digamma z) z := by
  have hU := isOpen_compl_range_intCast
  have hd := (digamma_contDiffOn.differentiableOn_iteratedDerivWithin
    (by exact_mod_cast ENat.natCast_lt_top k) hU.uniqueDiffOn) z hz
  have hd' : HasDerivAt (iteratedDerivWithin k Complex.digamma Complex.integerComplement)
      (iteratedDeriv (k + 1) Complex.digamma z) z := by
    have h := (hd.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    rw [← iteratedDerivWithin_of_isOpen hU hz, iteratedDerivWithin_succ,
      derivWithin_of_isOpen hU hz]
    exact h
  have e : iteratedDerivWithin k Complex.digamma Complex.integerComplement
      =ᶠ[nhds z] iteratedDeriv k Complex.digamma := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact iteratedDerivWithin_of_isOpen hU hw
  exact hd'.congr_of_eventuallyEq e.symm

/-- **The jets of the explicit anchor's Archimedean variable**: on the open set where
`(1 − s)/2` is off the integers, `∂^k_s ψ((1−s)/2) = (−½)^k ψ^{(k)}((1−s)/2)`. -/
theorem iteratedDeriv_digamma_half_one_sub (k : ℕ) {s : ℂ}
    (hs : (1 - s) / 2 ∈ Complex.integerComplement) :
    iteratedDeriv k (fun s : ℂ => Complex.digamma ((1 - s) / 2)) s
      = (-1 / 2 : ℂ) ^ k * iteratedDeriv k Complex.digamma ((1 - s) / 2) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun s : ℂ => Complex.digamma ((1 - s) / 2)) =ᶠ[nhds s]
        fun s => (-1 / 2 : ℂ) ^ k * iteratedDeriv k Complex.digamma ((1 - s) / 2) := by
      filter_upwards [isOpen_archDomain.mem_nhds hs] with s' hs'
      exact ih hs'
    rw [hev.deriv_eq]
    have hin : HasDerivAt (fun s : ℂ => (1 - s) / 2) (-1 / 2) s := by
      have := ((hasDerivAt_id s).const_sub 1).div_const 2
      exact this.congr_deriv (by ring)
    have hfin : HasDerivAt (fun s : ℂ => (-1 / 2 : ℂ) ^ k * iteratedDeriv k Complex.digamma ((1 - s) / 2))
        ((-1 / 2 : ℂ) ^ k * (iteratedDeriv (k + 1) Complex.digamma ((1 - s) / 2) * (-1 / 2))) s :=
      ((iteratedDeriv_digamma_hasDerivAt k hs).comp s hin).const_mul _
    rw [hfin.deriv]
    ring

/-- The explicit anchor's Archimedean variable is off the integers at every positive height. -/
theorem archDomain_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    (1 - s) / 2 ∈ Complex.integerComplement := by
  rintro ⟨m, hm⟩
  have him := congrArg Complex.im hm
  simp only [Complex.intCast_im, Complex.div_ofNat_im, Complex.sub_im, Complex.one_im,
    zero_sub] at him
  apply hs
  linarith

/-- **The explicit anchor's Archimedean jets as series**: at any anchor of positive height,
`∂^k_s ψ((1−s)/2) = (−½)^k (−1)^{k+1} k! Σ_n ((1−s)/2 + n)^{−(k+1)}` for `k ≥ 1`. -/
theorem iteratedDeriv_digamma_half_one_sub_series {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : s.im ≠ 0) :
    iteratedDeriv k (fun s : ℂ => Complex.digamma ((1 - s) / 2)) s
      = (-1 / 2 : ℂ) ^ k * ((-1) ^ (k + 1) * (k.factorial : ℂ)
          * ∑' n : ℕ, (1 : ℂ) / ((1 - s) / 2 + n) ^ (k + 1)) := by
  rw [iteratedDeriv_digamma_half_one_sub k (archDomain_of_im_ne_zero hs),
    iteratedDeriv_digamma_series (archDomain_of_im_ne_zero hs) hk]

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.hasSum_deriv_inv_pow_series
#print axioms CriticalLinePhasor.SeatingLedger.iteratedDeriv_digamma_series
#print axioms CriticalLinePhasor.SeatingLedger.hasSum_polygamma
#print axioms CriticalLinePhasor.SeatingLedger.iteratedDeriv_digamma_half_one_sub_series
