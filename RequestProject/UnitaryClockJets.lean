import RequestProject.SeatToeplitzReflection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# The unitary clock's jets on the channel: the symmetric sum over its line zeros (ledger 624, stage 1)

For `α = e^{iθ}` the symmetrized clock `symClock α ℓ` read in the `s`-chart through
`z = −i(s − ½)` has log-derivative `a · π cot(π x(s))` with `x(s) = a s + b`, `a = −iℓ/(2π)`,
`b = (iℓ/2 − θ)/(2π)`. On the channel `Re s < ½` the point `x(s)` lies in the upper half-plane,
where Mathlib's Mittag-Leffler expansion and its iterated derivatives are available. Hence

* `clockS_jet`: for `m ≥ 2` the `m`-th jet `(−1)^{m−1}/(m−1)! · ∂^{m−1} logDeriv` equals
  `Σ'_{n:ℤ} (s − tick n)^{−m}`, the absolutely convergent symmetric sum over the clock's zeros
  `tick n = ½ + i(θ − 2πn)/ℓ`, all on the line (`tick_re`);
* `clockS_mass`: the zeroth Toeplitz coefficient `2 Re logDeriv/(2σ − 1)` equals
  `Σ'_{n:ℤ} ‖s − tick n‖^{−2}`, the total mass of the transported atoms.

These are the constitutional facts behind the positivity of the clock faces: a unitary clock's
transported measure is a positive atomic measure on the circle.
-/

open Complex Finset Filter Topology Real
open scoped UpperHalfPlane
open CriticalLinePhasor.ChiralityHB

namespace CriticalLinePhasor.SeatingLedger

/-- The unitary clock in the `s`-chart. -/
noncomputable def clockS (θ ℓ : ℝ) (s : ℂ) : ℂ :=
  symClock (Complex.exp (I * θ)) ℓ (-I * (s - 1 / 2))

/-- The affine chart `x(s) = a s + b` sending the channel to the upper half-plane. -/
noncomputable def acoef (ℓ : ℝ) : ℂ := -I * ((ℓ / (2 * π) : ℝ) : ℂ)
noncomputable def bcoef (θ ℓ : ℝ) : ℂ := I * ((ℓ / (4 * π) : ℝ) : ℂ) - ((θ / (2 * π) : ℝ) : ℂ)
noncomputable def xvar (θ ℓ : ℝ) (s : ℂ) : ℂ := acoef ℓ * s + bcoef θ ℓ

/-- The zeros of the clock in the `s`-chart: `tick n = −(b + n)/a = ½ + i(θ − 2πn)/ℓ`. -/
noncomputable def tick (θ ℓ : ℝ) (n : ℤ) : ℂ := -(bcoef θ ℓ + n) / acoef ℓ

/-- `π cot(π x)`, Mathlib's normalization. -/
noncomputable def gcot (x : ℂ) : ℂ := π * Complex.cot (π * x)

theorem acoef_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) : acoef ℓ ≠ 0 := by
  unfold acoef
  have : ((ℓ / (2 * π) : ℝ) : ℂ) ≠ 0 := by
    have := Real.pi_pos
    exact_mod_cast (div_pos hℓ (by positivity)).ne'
  exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) this

theorem xvar_im (θ : ℝ) (ℓ : ℝ) (s : ℂ) :
    (xvar θ ℓ s).im = ℓ / (2 * π) * (1 / 2 - s.re) := by
  unfold xvar acoef bcoef
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.neg_re,
    Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem xvar_mem_upperHalfPlane {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) :
    xvar θ ℓ s ∈ UpperHalfPlane.upperHalfPlaneSet := by
  show 0 < (xvar θ ℓ s).im
  rw [xvar_im]
  have := Real.pi_pos
  exact mul_pos (div_pos hℓ (by positivity)) (by linarith)

theorem xvar_mem_integerComplement {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) :
    xvar θ ℓ s ∈ Complex.integerComplement :=
  UpperHalfPlane.coe_mem_integerComplement ⟨xvar θ ℓ s, xvar_mem_upperHalfPlane hℓ hs⟩

/-- `(x(s) + n)/a = s − tick n`. -/
theorem xvar_add_div (θ : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℂ) (n : ℤ) :
    (xvar θ ℓ s + n) / acoef ℓ = s - tick θ ℓ n := by
  unfold xvar tick
  have ha := acoef_ne_zero hℓ
  field_simp
  ring

/-- The clock's zeros in closed form. -/
theorem tick_eq (θ : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℤ) :
    tick θ ℓ n = 1 / 2 + I * (((θ - 2 * π * n) / ℓ : ℝ) : ℂ) := by
  unfold tick
  rw [div_eq_iff (acoef_ne_zero hℓ)]
  unfold acoef bcoef
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hℓ' : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  push_cast
  field_simp
  linear_combination (8 * ((θ : ℂ) - 2 * (π : ℂ) * (n : ℂ))) * Complex.I_sq

/-- The clock's zeros lie on the line. -/
theorem tick_re (θ : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℤ) : (tick θ ℓ n).re = 1 / 2 := by
  rw [tick_eq θ hℓ n]
  simp

/-- The clock does not vanish on the channel. -/
theorem clockS_ne_zero {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) : clockS θ ℓ s ≠ 0 := by
  unfold clockS
  apply symClock_ne_zero_off_axis _ hℓ
  · simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.sub_re, Complex.sub_im]
    norm_num
    linarith
  · rw [Complex.norm_exp]
    simp

/-- **The clock's log-derivative in the `s`-chart is `a · π cot(π x(s))`.** -/
theorem clockS_logDeriv_eq {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) :
    logDeriv (clockS θ ℓ) s = acoef ℓ * gcot (xvar θ ℓ s) := by
  have hφ : HasDerivAt (fun s : ℂ => -I * (s - 1 / 2)) (-I) s := by
    simpa using ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_mul (-I)
  have hcomp : logDeriv (clockS θ ℓ) s
      = logDeriv (symClock (Complex.exp (I * θ)) ℓ) (-I * (s - 1 / 2)) * (-I) := by
    have := logDeriv_comp (f := symClock (Complex.exp (I * θ)) ℓ)
      (g := fun s : ℂ => -I * (s - 1 / 2)) (x := s) (symClock_differentiableAt _ _ _)
      hφ.differentiableAt
    rw [hφ.deriv] at this
    exact this
  have hne : symClock (Complex.exp (I * θ)) ℓ (-I * (s - 1 / 2)) ≠ 0 := clockS_ne_zero hℓ hs
  rw [hcomp, symClock_logDeriv_eq_cot θ ℓ _ hne]
  unfold gcot xvar acoef bcoef
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have harg : ((-I * (s - 1 / 2)) * ℓ - θ) / 2
      = π * (-I * ((ℓ / (2 * π) : ℝ) : ℂ) * s + (I * ((ℓ / (4 * π) : ℝ) : ℂ) - ((θ / (2 * π) : ℝ) : ℂ))) := by
    push_cast
    field_simp
    ring
  rw [harg]
  push_cast
  field_simp

/-! ## Stage 1b: the jets on the channel are the symmetric sums over the line zeros -/

/-- The channel is open. -/
theorem isOpen_channel : IsOpen {s : ℂ | s.re < 1 / 2} :=
  isOpen_lt Complex.continuous_re continuous_const

/-- `π cot(π x)` is smooth on the upper half-plane. -/
theorem gcot_contDiffOn : ContDiffOn ℂ (⊤ : ℕ∞) gcot UpperHalfPlane.upperHalfPlaneSet := by
  intro x hx
  have hx' : x ∈ Complex.integerComplement := UpperHalfPlane.coe_mem_integerComplement ⟨x, hx⟩
  exact contDiffWithinAt_const.mul (cot_pi_mul_contDiffWithinAt ⊤ hx')

theorem gcot_iter_differentiableOn (k : ℕ) :
    DifferentiableOn ℂ (iteratedDerivWithin k gcot UpperHalfPlane.upperHalfPlaneSet)
      UpperHalfPlane.upperHalfPlaneSet :=
  gcot_contDiffOn.differentiableOn_iteratedDerivWithin (by exact_mod_cast ENat.natCast_lt_top k)
    UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn

theorem gcot_iter_hasDerivAt (k : ℕ) {x : ℂ} (hx : x ∈ UpperHalfPlane.upperHalfPlaneSet) :
    HasDerivAt (iteratedDerivWithin k gcot UpperHalfPlane.upperHalfPlaneSet)
      (iteratedDerivWithin (k + 1) gcot UpperHalfPlane.upperHalfPlaneSet x) x := by
  have hd := ((gcot_iter_differentiableOn k) x hx).differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hx)
  rw [iteratedDerivWithin_succ, derivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hx]
  exact hd.hasDerivAt

/-- **The clock's iterated log-derivatives in the `s`-chart.** -/
theorem clockS_iteratedDeriv {θ ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) {s : ℂ} (hs : s.re < 1 / 2) :
    iteratedDeriv k (logDeriv (clockS θ ℓ)) s
      = acoef ℓ ^ (k + 1) * iteratedDerivWithin k gcot UpperHalfPlane.upperHalfPlaneSet (xvar θ ℓ s) := by
  induction k generalizing s with
  | zero =>
    simp only [iteratedDeriv_zero, iteratedDerivWithin_zero, zero_add, pow_one]
    exact clockS_logDeriv_eq hℓ hs
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (logDeriv (clockS θ ℓ))
        =ᶠ[𝓝 s] fun s => acoef ℓ ^ (k + 1)
          * iteratedDerivWithin k gcot UpperHalfPlane.upperHalfPlaneSet (xvar θ ℓ s) := by
      filter_upwards [isOpen_channel.mem_nhds hs] with s' hs'
      exact ih hs'
    rw [hev.deriv_eq]
    have hx : HasDerivAt (fun s => xvar θ ℓ s) (acoef ℓ) s := by
      unfold xvar
      simpa using ((hasDerivAt_id s).const_mul (acoef ℓ)).add_const (bcoef θ ℓ)
    have hg := (gcot_iter_hasDerivAt k (xvar_mem_upperHalfPlane (θ := θ) hℓ hs)).comp s hx
    have hfin : HasDerivAt
        (fun s => acoef ℓ ^ (k + 1)
          * iteratedDerivWithin k gcot UpperHalfPlane.upperHalfPlaneSet (xvar θ ℓ s))
        (acoef ℓ ^ (k + 1)
          * (iteratedDerivWithin (k + 1) gcot UpperHalfPlane.upperHalfPlaneSet (xvar θ ℓ s) * acoef ℓ)) s :=
      hg.const_mul _
    rw [hfin.deriv]
    ring

/-- **The clock's jets are the symmetric sums over its line zeros.** For `k ≥ 1`,
`∂^k logDeriv(clock)(s) = (−1)^k k! Σ_{n∈ℤ} (s − tick n)^{−(k+1)}`. -/
theorem clockS_jet {θ ℓ : ℝ} (hℓ : 0 < ℓ) {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : s.re < 1 / 2) :
    iteratedDeriv k (logDeriv (clockS θ ℓ)) s
      = (-1) ^ k * (k.factorial : ℂ) * ∑' n : ℤ, ((s - tick θ ℓ n)⁻¹) ^ (k + 1) := by
  rw [clockS_iteratedDeriv hℓ k hs]
  have hx := xvar_mem_upperHalfPlane (θ := θ) hℓ hs
  have h := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow hk hx
  have hg : gcot = fun x : ℂ => π * Complex.cot (π * x) := rfl
  rw [hg, h, ← mul_assoc, mul_comm (acoef ℓ ^ (k + 1)), mul_assoc, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  rw [← xvar_add_div θ hℓ s n, inv_div, div_pow]
  ring

/-- The weight of a line zero seen from `s`: `1/|s − tick n|²`. -/
noncomputable def tickWeight (θ ℓ : ℝ) (s : ℂ) (n : ℤ) : ℝ := 1 / Complex.normSq (s - tick θ ℓ n)

theorem tickWeight_nonneg (θ ℓ : ℝ) (s : ℂ) (n : ℤ) : 0 ≤ tickWeight θ ℓ s n :=
  div_nonneg zero_le_one (Complex.normSq_nonneg _)

theorem re_inv_sub_tick (θ : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℂ) (n : ℤ) :
    ((s - tick θ ℓ n)⁻¹).re = (s.re - 1 / 2) * tickWeight θ ℓ s n := by
  rw [Complex.inv_re, Complex.sub_re, tick_re θ hℓ n]
  unfold tickWeight
  ring

theorem normSq_sub_tick (θ : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℂ) (n : ℤ) :
    Complex.normSq (s - tick θ ℓ n) = (s.re - 1 / 2) ^ 2 + (s.im - (θ - 2 * π * n) / ℓ) ^ 2 := by
  have : s - tick θ ℓ n
      = ((s.re - 1 / 2 : ℝ) : ℂ) + ((s.im - (θ - 2 * π * n) / ℓ : ℝ) : ℂ) * I := by
    rw [tick_eq θ hℓ n]
    apply Complex.ext <;> simp
  rw [this, Complex.normSq_add_mul_I]

/-- The line-zero weights are summable. -/
theorem summable_tickWeight (θ : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℂ) :
    Summable (tickWeight θ ℓ s) := by
  have hπ := Real.pi_pos
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  have hπ0 : π ≠ 0 := hπ.ne'
  set a : ℝ := (s.im * ℓ - θ) / (2 * π) with ha
  have hg : Summable (fun n : ℤ => (ℓ / (2 * π)) ^ 2 * (1 / |(n : ℝ) + a| ^ (2 : ℝ))) :=
    ((Real.summable_one_div_int_add_rpow a 2).mpr (by norm_num)).mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Filter.eventually_cofinite]
  refine ((Set.finite_singleton (-a)).preimage Int.cast_injective.injOn).subset ?_
  intro n hn
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  by_contra hne
  refine hn ?_
  have hna : (n : ℝ) + a ≠ 0 := fun h => hne (by linarith)
  have hsplit : s.im - (θ - 2 * π * n) / ℓ = (2 * π / ℓ) * ((n : ℝ) + a) := by
    rw [ha]; field_simp; ring
  have hB : 0 < (s.im - (θ - 2 * π * n) / ℓ) ^ 2 := by
    rw [hsplit]
    exact lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (mul_ne_zero (by positivity) hna)).symm
  rw [Real.norm_eq_abs, abs_of_nonneg (tickWeight_nonneg θ ℓ s n)]
  unfold tickWeight
  rw [normSq_sub_tick θ hℓ s n, Real.rpow_two, sq_abs]
  calc 1 / ((s.re - 1 / 2) ^ 2 + (s.im - (θ - 2 * π * n) / ℓ) ^ 2)
      ≤ 1 / (s.im - (θ - 2 * π * n) / ℓ) ^ 2 :=
        one_div_le_one_div_of_le hB (le_add_of_nonneg_left (sq_nonneg _))
    _ = (ℓ / (2 * π)) ^ 2 * (1 / ((n : ℝ) + a) ^ 2) := by
        rw [hsplit]; field_simp

/-- **The clock's mass is the sum of its line-zero weights.**
`Re logDeriv(clock)(s) = (σ − ½) Σ_{n∈ℤ} 1/|s − tick n|²` on the channel. -/
theorem clockS_re_logDeriv {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) :
    (logDeriv (clockS θ ℓ) s).re = (s.re - 1 / 2) * ∑' n : ℤ, tickWeight θ ℓ s n := by
  rw [clockS_logDeriv_eq hℓ hs]
  have hx : xvar θ ℓ s ∈ Complex.integerComplement := xvar_mem_integerComplement hℓ hs
  have hrep : gcot (xvar θ ℓ s) = 1 / xvar θ ℓ s
      + ∑' n : ℕ, (1 / (xvar θ ℓ s - (n + 1)) + 1 / (xvar θ ℓ s + (n + 1))) := by
    have h := cot_series_rep' hx
    unfold gcot
    rw [← h]; ring
  have hterm : ∀ n : ℤ, acoef ℓ * (1 / (xvar θ ℓ s + n)) = (s - tick θ ℓ n)⁻¹ := by
    intro n
    rw [← xvar_add_div θ hℓ s n, inv_div]
    ring
  have hsum : Summable (fun n : ℕ =>
      acoef ℓ * (1 / (xvar θ ℓ s - (n + 1)) + 1 / (xvar θ ℓ s + (n + 1)))) :=
    (summable_cotTerm hx).mul_left _
  rw [hrep, mul_add, ← tsum_mul_left, Complex.add_re, Complex.re_tsum hsum]
  have h0 : (acoef ℓ * (1 / xvar θ ℓ s)).re = (s.re - 1 / 2) * tickWeight θ ℓ s 0 := by
    have := hterm 0
    simp only [Int.cast_zero, add_zero] at this
    rw [this, re_inv_sub_tick θ hℓ]
  have hpair : ∀ n : ℕ,
      (acoef ℓ * (1 / (xvar θ ℓ s - (n + 1)) + 1 / (xvar θ ℓ s + (n + 1)))).re
        = (s.re - 1 / 2) * (tickWeight θ ℓ s (n + 1) + tickWeight θ ℓ s (-(n + 1))) := by
    intro n
    have h1 := hterm (n + 1)
    have h2 := hterm (-(n + 1))
    push_cast at h1 h2
    rw [mul_add, h1, show xvar θ ℓ s - ((n : ℂ) + 1) = xvar θ ℓ s + -((n : ℂ) + 1) by ring, h2,
      Complex.add_re, re_inv_sub_tick θ hℓ, re_inv_sub_tick θ hℓ]
    ring
  simp_rw [hpair]
  rw [h0]
  have hw := summable_tickWeight θ hℓ s
  have hw1 : Summable (fun n : ℕ => tickWeight θ ℓ s (n + 1)) :=
    hw.comp_injective (fun a b h => by simpa using h)
  have hw2 : Summable (fun n : ℕ => tickWeight θ ℓ s (-(n + 1))) :=
    hw.comp_injective (fun a b h => by simpa using h)
  rw [tsum_mul_left, hw1.tsum_add hw2, tsum_of_add_one_of_neg_add_one hw1 hw2]
  ring

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.clockS_jet
#print axioms CriticalLinePhasor.SeatingLedger.clockS_re_logDeriv
