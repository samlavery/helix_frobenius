import RequestProject.RSPositivity

/-!
# The local Cauchy step: the Rankin–Selberg local factor is a sum of squares

The named next brick of `RSPositivity`, discharged.  With
`S k := symmetricPowerSatakeTrace α k` the bilateral trace ladder and
`rsCoeff α k` the `k`-th power-series coefficient of the seed's local
Rankin–Selberg square factor `1/((1−α²x)(1−x)²(1−α⁻²x))` — the four channels
`α², 1, 1, α⁻²` of `std ⊗ std` at a self-dual strand, written as the literal
four-fold channel convolution (`rsCoeff_eq_fourfold_conv`) — the file proves:

* `chebyshev_trace` / `clebsch_gordan_trace` — the exact product law on the
  trace ladder: `S 1 · S (k+1) = S (k+2) + S k`, and in general
  `S k · S m = ∑_{j ≤ m} S (k+m−2j)` — the Clebsch–Gordan expansion, every
  term exact, no estimate anywhere;
* `trace_sq_expand` — the diagonal: `S k ² = ∑_{j ≤ k} S (2j)`;
* `rs_local_cauchy` — **the registered identity**: `rs_{k+2} − rs_k = S_{k+2}²`,
  with `rs_0 = S_0²` and `rs_1 = S_1²` the base cases — the two-variable
  Cauchy identity in telescoped form;
* `rsCoeff_eq_sum_sq` — **the closed form**: `rs_k = ∑_{j ≤ k/2} S_{k−2j}²` —
  every coefficient of the local Rankin–Selberg factor is a finite sum of
  squares of symmetric-power traces;
* `rs_local_positivity` — at a unit strand every `rs_k` is a nonnegative
  real: the Landau-ready **local** half of the Jacquet–Shalika engine, exact.

Harmonic register.  The object's scale is the trace ladder itself (unit
strand, values in `[−(k+1), k+1]`); the common mode is computed outright —
the identity is exact at every order and nothing is estimated.  The
difficulty of the program stays on the **global** side (the per-rung
one-sided continuation), which this file does not touch.

Register, scope.  This is the local/algebraic half of the native
Jacquet–Shalika engine: combined with the Landau singularity lemma and a
global continuation it yields the classical local bounds; the global
continuation per symmetric-power rung `r ≥ 5` is exactly the recorded A1
obstruction and is neither used nor supplied here.  No `axiom`, no `sorry`.
-/

open Finset Complex

namespace CriticalLinePhasor.RSLocalCauchy

open CriticalLinePhasor.SatoTateCarrier3D CriticalLinePhasor.RSPositivity

/-! ## The trace ladder: base values and the strip law -/

theorem trace_rank_zero (α : ℂ) : symmetricPowerSatakeTrace α 0 = 1 := by
  unfold symmetricPowerSatakeTrace
  simp

theorem trace_rank_one (α : ℂ) : symmetricPowerSatakeTrace α 1 = α + α⁻¹ := by
  unfold symmetricPowerSatakeTrace
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp

/-- **The strip law**: the rank-`(k+2)` trace is the rank-`k` trace plus the two
extreme channels. -/
theorem trace_strip {α : ℂ} (hα : α ≠ 0) (k : ℕ) :
    symmetricPowerSatakeTrace α (k + 2)
      = α ^ (k + 2) + (α⁻¹) ^ (k + 2) + symmetricPowerSatakeTrace α k := by
  unfold symmetricPowerSatakeTrace
  rw [Finset.sum_range_succ (fun j => α ^ (k + 2 - j) * (α⁻¹) ^ j) (k + 2),
    Finset.sum_range_succ' (fun j => α ^ (k + 2 - j) * (α⁻¹) ^ j) (k + 1)]
  have hmid : ∀ j ∈ Finset.range (k + 1),
      α ^ (k + 2 - (j + 1)) * (α⁻¹) ^ (j + 1) = α ^ (k - j) * (α⁻¹) ^ j := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h1 : k + 2 - (j + 1) = (k - j) + 1 := by omega
    rw [h1, pow_succ, pow_succ]
    calc α ^ (k - j) * α * ((α⁻¹) ^ j * α⁻¹)
        = α ^ (k - j) * (α⁻¹) ^ j * (α * α⁻¹) := by ring
      _ = α ^ (k - j) * (α⁻¹) ^ j := by rw [mul_inv_cancel₀ hα, mul_one]
  rw [Finset.sum_congr rfl hmid]
  simp
  ring

/-! ## The Chebyshev product law -/

theorem trace_mul_left {α : ℂ} (k : ℕ) :
    α * symmetricPowerSatakeTrace α (k + 1)
      = symmetricPowerSatakeTrace α (k + 2) - (α⁻¹) ^ (k + 2) := by
  unfold symmetricPowerSatakeTrace
  rw [Finset.mul_sum,
    Finset.sum_range_succ (fun j => α ^ (k + 2 - j) * (α⁻¹) ^ j) (k + 2)]
  have hterm : ∀ j ∈ Finset.range (k + 2),
      α * (α ^ (k + 1 - j) * (α⁻¹) ^ j) = α ^ (k + 2 - j) * (α⁻¹) ^ j := by
    intro j hj
    have hjk : j ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h1 : k + 2 - j = (k + 1 - j) + 1 := by omega
    rw [h1, pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm]
  simp

theorem trace_mul_right {α : ℂ} (k : ℕ) :
    α⁻¹ * symmetricPowerSatakeTrace α (k + 1)
      = symmetricPowerSatakeTrace α (k + 2) - α ^ (k + 2) := by
  unfold symmetricPowerSatakeTrace
  rw [Finset.mul_sum,
    Finset.sum_range_succ' (fun j => α ^ (k + 2 - j) * (α⁻¹) ^ j) (k + 2)]
  have hterm : ∀ j ∈ Finset.range (k + 2),
      α⁻¹ * (α ^ (k + 1 - j) * (α⁻¹) ^ j) = α ^ (k + 2 - (j + 1)) * (α⁻¹) ^ (j + 1) := by
    intro j _
    have h1 : k + 2 - (j + 1) = k + 1 - j := by omega
    rw [h1, pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm]
  simp

/-- **The Chebyshev product law**: `S 1 · S (k+1) = S (k+2) + S k`. -/
theorem chebyshev_trace {α : ℂ} (hα : α ≠ 0) (k : ℕ) :
    symmetricPowerSatakeTrace α 1 * symmetricPowerSatakeTrace α (k + 1)
      = symmetricPowerSatakeTrace α (k + 2) + symmetricPowerSatakeTrace α k := by
  rw [trace_rank_one, add_mul, trace_mul_left k, trace_mul_right k, trace_strip hα k]
  ring

/-! ## The Clebsch–Gordan expansion -/

/-- **Clebsch–Gordan on the trace ladder**: for `m ≤ k`,
`S k · S m = ∑_{j ≤ m} S (k + m − 2j)` — the exact product law, every term a
trace, no estimate. -/
theorem clebsch_gordan_trace {α : ℂ} (hα : α ≠ 0) :
    ∀ m k : ℕ, m ≤ k →
      symmetricPowerSatakeTrace α k * symmetricPowerSatakeTrace α m
        = ∑ j ∈ Finset.range (m + 1), symmetricPowerSatakeTrace α (k + m - 2 * j) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · intro k _
      simp
    rcases m with _ | m
    · intro k hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [mul_comm, chebyshev_trace hα k', Finset.sum_range_succ, Finset.sum_range_one]
      have e0 : k' + 1 + 1 - 2 * 0 = k' + 2 := by omega
      have e1 : k' + 1 + 1 - 2 * 1 = k' := by omega
      rw [e0, e1]
    · intro k hk
      have ih1 := ih (m + 1) (by omega) k (by omega)
      have ih0 := ih m (by omega) k (by omega)
      have hch : symmetricPowerSatakeTrace α (m + 2)
          = symmetricPowerSatakeTrace α 1 * symmetricPowerSatakeTrace α (m + 1)
            - symmetricPowerSatakeTrace α m := by
        linear_combination (chebyshev_trace hα m).symm
      rw [hch, mul_sub, show symmetricPowerSatakeTrace α k *
            (symmetricPowerSatakeTrace α 1 * symmetricPowerSatakeTrace α (m + 1))
          = symmetricPowerSatakeTrace α 1 *
            (symmetricPowerSatakeTrace α k * symmetricPowerSatakeTrace α (m + 1)) from by
        ring]
      rw [ih1, ih0, Finset.mul_sum]
      have hterm : ∀ j ∈ Finset.range (m + 2),
          symmetricPowerSatakeTrace α 1
              * symmetricPowerSatakeTrace α (k + (m + 1) - 2 * j)
            = symmetricPowerSatakeTrace α (k + (m + 2) - 2 * j)
              + symmetricPowerSatakeTrace α (k + m - 2 * j) := by
        intro j hj
        have hjm : j ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have h1 : k + (m + 1) - 2 * j = (k + m - 2 * j) + 1 := by omega
        have h2 : k + (m + 2) - 2 * j = (k + m - 2 * j) + 2 := by omega
        rw [h1, h2]
        exact chebyshev_trace hα (k + m - 2 * j)
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
        Finset.sum_range_succ (fun j => symmetricPowerSatakeTrace α (k + m - 2 * j)) (m + 1),
        Finset.sum_range_succ
          (fun j => symmetricPowerSatakeTrace α (k + (m + 2) - 2 * j)) (m + 2)]
      have h3 : k + (m + 2) - 2 * (m + 2) = k + m - 2 * (m + 1) := by omega
      rw [h3]
      ring

/-- **The diagonal**: `S k ² = ∑_{j ≤ k} S (2j)`. -/
theorem trace_sq_expand {α : ℂ} (hα : α ≠ 0) (k : ℕ) :
    symmetricPowerSatakeTrace α k ^ 2
      = ∑ j ∈ Finset.range (k + 1), symmetricPowerSatakeTrace α (2 * j) := by
  rw [sq, clebsch_gordan_trace hα k k le_rfl,
    ← Finset.sum_range_reflect (fun j => symmetricPowerSatakeTrace α (2 * j)) (k + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  congr 1
  omega

/-! ## The even-rank split into the `α²`-ladder -/

/-- The even-rank trace splits into two consecutive `α²`-ladder traces. -/
theorem even_trace_split {α : ℂ} (hα : α ≠ 0) (j : ℕ) :
    symmetricPowerSatakeTrace α (2 * (j + 1))
      = symmetricPowerSatakeTrace (α ^ 2) (j + 1) + symmetricPowerSatakeTrace (α ^ 2) j := by
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero 2 hα
  induction j with
  | zero =>
      rw [show (2 : ℕ) * (0 + 1) = 0 + 2 from by norm_num, trace_strip hα 0,
        trace_rank_zero, trace_rank_one, trace_rank_zero, inv_pow]
  | succ n ihn =>
      rw [show (2 : ℕ) * (n + 1 + 1) = 2 * (n + 1) + 2 from by ring,
        trace_strip hα (2 * (n + 1)), ihn,
        show n + 1 + 1 = n + 2 from rfl, trace_strip hα2 n]
      have i1 : 2 * (n + 1) + 2 = 2 * (n + 2) := by ring
      have e1 : α ^ (2 * (n + 1) + 2) = (α ^ 2) ^ (n + 2) := by
        rw [i1, pow_mul]
      have e2 : (α⁻¹) ^ (2 * (n + 1) + 2) = ((α ^ 2)⁻¹) ^ (n + 2) := by
        rw [i1, pow_mul, inv_pow]
      rw [e1, e2]
      ring

/-! ## The local Rankin–Selberg coefficient -/

/-- **The local Rankin–Selberg coefficient**: the `k`-th power-series coefficient
of `1/((1−α²x)(1−x)²(1−α⁻²x))` — the four channels `α², 1, 1, α⁻²` of
`std ⊗ std` at a self-dual strand — with the `α²/α⁻²` pair already convolved
into the `α²`-ladder trace and the two trivial channels into the count. -/
noncomputable def rsCoeff (α : ℂ) (k : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (k + 1),
    symmetricPowerSatakeTrace (α ^ 2) m * ((k - m + 1 : ℕ) : ℂ)

/-- The `α²`-ladder trace is literally the `α²/α⁻²` channel-pair convolution. -/
theorem sq_channel_conv {α : ℂ} (m : ℕ) :
    symmetricPowerSatakeTrace (α ^ 2) m
      = ∑ p ∈ Finset.range (m + 1), α ^ (2 * (m - p)) * (α⁻¹) ^ (2 * p) := by
  unfold symmetricPowerSatakeTrace
  apply Finset.sum_congr rfl
  intro p _
  simp only [pow_mul, inv_pow]

/-- **Honesty of the definition**: `rsCoeff` is the literal four-fold channel
convolution of `α², 1, 1, α⁻²`. -/
theorem rsCoeff_eq_fourfold_conv {α : ℂ} (k : ℕ) :
    rsCoeff α k
      = ∑ m ∈ Finset.range (k + 1),
          (∑ p ∈ Finset.range (m + 1), α ^ (2 * (m - p)) * (α⁻¹) ^ (2 * p))
            * (∑ _q ∈ Finset.range (k - m + 1), (1 : ℂ)) := by
  unfold rsCoeff
  apply Finset.sum_congr rfl
  intro m _
  rw [← sq_channel_conv, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-! ## The telescope and the registered identity -/

/-- The two-step telescope of the local coefficient. -/
theorem rs_telescope (α : ℂ) (k : ℕ) :
    rsCoeff α (k + 2) - rsCoeff α k
      = symmetricPowerSatakeTrace (α ^ 2) (k + 2)
        + 2 * ∑ m ∈ Finset.range (k + 2), symmetricPowerSatakeTrace (α ^ 2) m := by
  unfold rsCoeff
  rw [Finset.sum_range_succ
      (fun m => symmetricPowerSatakeTrace (α ^ 2) m * ((k + 2 - m + 1 : ℕ) : ℂ)) (k + 2),
    Finset.sum_range_succ
      (fun m => symmetricPowerSatakeTrace (α ^ 2) m * ((k + 2 - m + 1 : ℕ) : ℂ)) (k + 1),
    Finset.sum_range_succ (fun m => symmetricPowerSatakeTrace (α ^ 2) m) (k + 1)]
  have c1 : ((k + 2 - (k + 2) + 1 : ℕ) : ℂ) = 1 := by norm_num
  have c2 : ((k + 2 - (k + 1) + 1 : ℕ) : ℂ) = 2 := by
    have : (k + 2 - (k + 1) + 1 : ℕ) = 2 := by omega
    rw [this]
    norm_num
  rw [c1, c2]
  have hsplit :
      (∑ m ∈ Finset.range (k + 1),
          symmetricPowerSatakeTrace (α ^ 2) m * ((k + 2 - m + 1 : ℕ) : ℂ))
        - ∑ m ∈ Finset.range (k + 1),
            symmetricPowerSatakeTrace (α ^ 2) m * ((k - m + 1 : ℕ) : ℂ)
      = 2 * ∑ m ∈ Finset.range (k + 1), symmetricPowerSatakeTrace (α ^ 2) m := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hc : (k + 2 - m + 1 : ℕ) = (k - m + 1 : ℕ) + 2 := by omega
    rw [hc]
    push_cast
    ring
  linear_combination hsplit

theorem rs_cauchy_zero (α : ℂ) :
    rsCoeff α 0 = symmetricPowerSatakeTrace α 0 ^ 2 := by
  unfold rsCoeff
  rw [Finset.sum_range_one, trace_rank_zero, trace_rank_zero]
  norm_num

theorem rs_cauchy_one {α : ℂ} (hα : α ≠ 0) :
    rsCoeff α 1 = symmetricPowerSatakeTrace α 1 ^ 2 := by
  unfold rsCoeff
  rw [Finset.sum_range_succ, Finset.sum_range_one, trace_rank_zero, trace_rank_one,
    trace_rank_one]
  have h1 : ((1 - 0 + 1 : ℕ) : ℂ) = 2 := by norm_num
  have h2 : ((1 - 1 + 1 : ℕ) : ℂ) = 1 := by norm_num
  rw [h1, h2]
  have hmul : α * α⁻¹ = 1 := mul_inv_cancel₀ hα
  have hinv2 : (α ^ 2)⁻¹ = (α⁻¹) ^ 2 := by rw [inv_pow]
  rw [hinv2]
  ring_nf
  linear_combination (-2 : ℂ) * hmul

/-- **THE LOCAL CAUCHY STEP** (the registered identity):
`rs_{k+2} − rs_k = S_{k+2}²`. -/
theorem rs_local_cauchy {α : ℂ} (hα : α ≠ 0) (k : ℕ) :
    rsCoeff α (k + 2) - rsCoeff α k
      = symmetricPowerSatakeTrace α (k + 2) ^ 2 := by
  rw [rs_telescope, trace_sq_expand hα (k + 2),
    Finset.sum_range_succ' (fun j => symmetricPowerSatakeTrace α (2 * j)) (k + 2)]
  have hsplit : ∀ j ∈ Finset.range (k + 2),
      symmetricPowerSatakeTrace α (2 * (j + 1))
        = symmetricPowerSatakeTrace (α ^ 2) (j + 1)
          + symmetricPowerSatakeTrace (α ^ 2) j :=
    fun j _ => even_trace_split hα j
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have h2 := Finset.sum_range_succ' (fun j => symmetricPowerSatakeTrace (α ^ 2) j) (k + 2)
  have h3 := Finset.sum_range_succ (fun j => symmetricPowerSatakeTrace (α ^ 2) j) (k + 2)
  have h0 : symmetricPowerSatakeTrace (α ^ 2) 0 = 1 := trace_rank_zero (α ^ 2)
  have h4 : symmetricPowerSatakeTrace α (2 * 0) = 1 := by
    rw [show (2 : ℕ) * 0 = 0 from by norm_num, trace_rank_zero]
  rw [h4]
  rw [h0] at h2
  linear_combination h2 - h3

/-! ## The closed form: a sum of squares -/

/-- **The closed form**: every local Rankin–Selberg coefficient is a finite sum
of squares of symmetric-power traces: `rs_k = ∑_{j ≤ k/2} S_{k−2j}²`. -/
theorem rsCoeff_eq_sum_sq {α : ℂ} (hα : α ≠ 0) (k : ℕ) :
    rsCoeff α k
      = ∑ j ∈ Finset.range (k / 2 + 1), symmetricPowerSatakeTrace α (k - 2 * j) ^ 2 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · rw [rs_cauchy_zero]
      rw [show (0 : ℕ) / 2 + 1 = 1 from by norm_num, Finset.sum_range_one]
    rcases k with _ | k
    · rw [rs_cauchy_one hα]
      rw [show (1 : ℕ) / 2 + 1 = 1 from by norm_num, Finset.sum_range_one]
    · have hstep := rs_local_cauchy hα k
      have ihk := ih k (by omega)
      have hdiv : (k + 2) / 2 + 1 = (k / 2 + 1) + 1 := by omega
      rw [hdiv,
        Finset.sum_range_succ'
          (fun j => symmetricPowerSatakeTrace α (k + 2 - 2 * j) ^ 2) (k / 2 + 1)]
      have hterm : ∀ j ∈ Finset.range (k / 2 + 1),
          symmetricPowerSatakeTrace α (k + 2 - 2 * (j + 1)) ^ 2
            = symmetricPowerSatakeTrace α (k - 2 * j) ^ 2 := by
        intro j hj
        have hjk : j ≤ k / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        congr 2
        omega
      rw [Finset.sum_congr rfl hterm]
      have hz : k + 2 - 2 * 0 = k + 2 := by omega
      rw [hz]
      linear_combination hstep + ihk

/-! ## Positivity at the unit strand: the Landau-ready local statement -/

theorem rsCoeff_re_nonneg {α : ℂ} (hα : ‖α‖ = 1) (k : ℕ) :
    0 ≤ (rsCoeff α k).re := by
  have hne : α ≠ 0 := by
    intro h
    rw [h] at hα
    simp at hα
  rw [rsCoeff_eq_sum_sq hne k]
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro j _
  exact trace_sq_nonneg hα _

theorem rsCoeff_im_zero {α : ℂ} (hα : ‖α‖ = 1) (k : ℕ) :
    (rsCoeff α k).im = 0 := by
  have hne : α ≠ 0 := by
    intro h
    rw [h] at hα
    simp at hα
  rw [rsCoeff_eq_sum_sq hne k]
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro j _
  have him := trace_real_of_unit hα (k - 2 * j)
  rw [sq, Complex.mul_im, him]
  simp

/-- **The Landau-ready local statement**: at a unit strand every coefficient of
the local Rankin–Selberg factor is a nonnegative real — positivity is exact
(a sum of squares), not an estimate. -/
theorem rs_local_positivity {α : ℂ} (hα : ‖α‖ = 1) (k : ℕ) :
    0 ≤ (rsCoeff α k).re ∧ (rsCoeff α k).im = 0 :=
  ⟨rsCoeff_re_nonneg hα k, rsCoeff_im_zero hα k⟩

end CriticalLinePhasor.RSLocalCauchy

#print axioms CriticalLinePhasor.RSLocalCauchy.chebyshev_trace
#print axioms CriticalLinePhasor.RSLocalCauchy.clebsch_gordan_trace
#print axioms CriticalLinePhasor.RSLocalCauchy.trace_sq_expand
#print axioms CriticalLinePhasor.RSLocalCauchy.rsCoeff_eq_fourfold_conv
#print axioms CriticalLinePhasor.RSLocalCauchy.rs_local_cauchy
#print axioms CriticalLinePhasor.RSLocalCauchy.rsCoeff_eq_sum_sq
#print axioms CriticalLinePhasor.RSLocalCauchy.rs_local_positivity
