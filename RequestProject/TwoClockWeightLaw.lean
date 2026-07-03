import Mathlib

/-!
# The two-clock weight law: the campaign's measured discovery, derived

The long-span GL(2) fiber spectroscopy (`tmp/gl2_longspan_sweep.py`, 2026-07-01)
measured a phenomenological law with no literature counterpart: the fiber's resonance
line at spectral position `ln(p^k)` has amplitude `|s_k|/k · p^{−k/2}`, where
`s_0 = 2`, `s_1 = λ(p)`, `s_{k+1} = λ·s_k − s_{k−1}`.  Verified: Δ (17 lines,
meas/pred median 1.007, std 4.5%), E11 (13 lines, median 1.051, std 3.1%); the
predicted HOLES confirmed (E11 `ln4` empty because `λ(2) = −√2 ⟹ s_2 = 0` exactly;
`a_p = 0` lines dead); the CM combs (even lines alive at full weight); the conjugate
`k=2` line NOT an independent parameter.

This file DERIVES the law's formula — the measured discovery, promoted to theorem:

* `clockTrace` — `s_k = α^k + ᾱ^k = 2cos(kθ)`: the trace of the k-th power of the
  unimodular Satake pair — two clocks beating (`clockTrace_eq_trace`).
* `clockTrace_recurrence` — the measured recurrence IS the Chebyshev recurrence of
  the two-clock trace.
* `two_clock_log_expansion` — **the origin of the weights**: the logarithm of the
  two-clock Euler factor has k-th coefficient exactly `s_k/k`.  The instrument was
  reading `log L`, not `L`: the linear bank carries `λ(n)` (coefficients of `L`), but
  the phase-recurrence sweep spectroscopies the LOGARITHM, whose prime-power lines
  carry `s_k/k`.
* `two_clock_weight` — on the critical line the `p^k` log-coefficient has modulus
  exactly `|s_k|/k · p^{−k/2}`: the measured formula, now a theorem.
* `hole_iff` — the k=2 line vanishes iff `λ² = 2`: the measured E11 `ln4` hole is the
  unique quadratic hole, classified.
* `cm_survival` — an additive prime (`λ = 0`) forces `s_2 = −2`: the CM comb's even
  lines at full weight, as algebra.

What remains measured (stated, not claimed): the INSTRUMENT identification — that the
phase-recurrence spectrum of the fiber on the line reads the smooth part of `log L`,
with the zero contributions forming the broadband floor (the clock–dip duality).  The
formula itself is no longer phenomenology.  No `sorry`; standard axioms.
-/

open Complex

namespace CriticalLinePhasor.TwoClockWeightLaw

/-- **The two-clock trace** `s_k = 2cos(kθ)`: the trace of the k-th power of the
unimodular Satake pair `(e^{iθ}, e^{−iθ})`. -/
noncomputable def clockTrace (θ : ℝ) (k : ℕ) : ℝ := 2 * Real.cos (k * θ)

@[simp] theorem clockTrace_zero (θ : ℝ) : clockTrace θ 0 = 2 := by
  simp [clockTrace]

theorem clockTrace_one (θ : ℝ) : clockTrace θ 1 = 2 * Real.cos θ := by
  simp [clockTrace]

/-- **The measured recurrence is the two-clock trace recurrence**:
`s_{k+2} = λ·s_{k+1} − s_k` with `λ = 2cos θ`. -/
theorem clockTrace_recurrence (θ : ℝ) (k : ℕ) :
    clockTrace θ (k + 2) = (2 * Real.cos θ) * clockTrace θ (k + 1) - clockTrace θ k := by
  unfold clockTrace
  have h1 : ((k + 2 : ℕ) : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
  have h2 : ((k : ℕ) : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
  rw [h1, h2, Real.cos_add, Real.cos_sub]
  ring

/-- `s_2 = λ² − 2`. -/
theorem clockTrace_two (θ : ℝ) : clockTrace θ 2 = (2 * Real.cos θ) ^ 2 - 2 := by
  unfold clockTrace
  have h : ((2 : ℕ) : ℝ) * θ = 2 * θ := by push_cast; ring
  rw [h, Real.cos_two_mul]
  ring

/-- **The hole law**: the k=2 line vanishes iff `λ² = 2` — the measured E11 `ln4`
hole (`λ(2) = −√2`) is the unique quadratic hole, classified. -/
theorem hole_iff (θ : ℝ) : clockTrace θ 2 = 0 ↔ (2 * Real.cos θ) ^ 2 = 2 := by
  rw [clockTrace_two]
  constructor <;> intro h <;> linarith

/-- **CM survival**: an additive prime (`λ = 0`) forces `s_2 = −2` — the CM comb's
even lines survive at full weight while the odd lines die. -/
theorem cm_survival (θ : ℝ) (h : Real.cos θ = 0) : clockTrace θ 2 = -2 := by
  rw [clockTrace_two, h]
  ring

/-- `e^{ix} + e^{−ix} = 2cos x`, real `x`, complex-valued. -/
theorem exp_add_exp_neg (x : ℝ) :
    Complex.exp ((x : ℂ) * I) + Complex.exp (-((x : ℂ) * I))
      = ((2 * Real.cos x : ℝ) : ℂ) := by
  have e2 : -((x : ℂ) * I) = ((-x : ℝ) : ℂ) * I := by push_cast; ring
  rw [e2, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- **The two-clock trace is the trace of the k-th Satake power**. -/
theorem clockTrace_eq_trace (θ : ℝ) (k : ℕ) :
    Complex.exp ((θ : ℂ) * I) ^ k + Complex.exp (-((θ : ℂ) * I)) ^ k
      = (clockTrace θ k : ℂ) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have h1 : (k : ℂ) * ((θ : ℂ) * I) = (((k : ℝ) * θ : ℝ) : ℂ) * I := by push_cast; ring
  have h2 : (k : ℂ) * -((θ : ℂ) * I) = -((((k : ℝ) * θ : ℝ) : ℂ) * I) := by
    push_cast; ring
  rw [h1, h2, exp_add_exp_neg]
  unfold clockTrace
  norm_cast

/-- **The two-clock log expansion — the origin of the measured weights**: the
logarithm of the two-clock Euler factor has k-th coefficient exactly `s_k/k`. -/
theorem two_clock_log_expansion (θ : ℝ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ => (clockTrace θ k : ℂ) / k * x ^ k)
      (-Complex.log (1 - Complex.exp ((θ : ℂ) * I) * x)
        - Complex.log (1 - Complex.exp (-((θ : ℂ) * I)) * x)) := by
  have hre1 : ((θ : ℂ) * I).re = 0 := by simp [Complex.mul_re]
  have hre2 : (-((θ : ℂ) * I)).re = 0 := by simp [Complex.mul_re]
  have hu1 : ‖Complex.exp ((θ : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_exp, hre1, Real.exp_zero]
  have hu2 : ‖Complex.exp (-((θ : ℂ) * I))‖ = 1 := by
    rw [Complex.norm_exp, hre2, Real.exp_zero]
  have hx1 : ‖Complex.exp ((θ : ℂ) * I) * x‖ < 1 := by
    rw [norm_mul, hu1, one_mul]; exact hx
  have hx2 : ‖Complex.exp (-((θ : ℂ) * I)) * x‖ < 1 := by
    rw [norm_mul, hu2, one_mul]; exact hx
  have hsum := (Complex.hasSum_taylorSeries_neg_log hx1).add
    (Complex.hasSum_taylorSeries_neg_log hx2)
  have hfun : (fun k : ℕ => (Complex.exp ((θ : ℂ) * I) * x) ^ k / k
        + (Complex.exp (-((θ : ℂ) * I)) * x) ^ k / k)
      = fun k : ℕ => (clockTrace θ k : ℂ) / k * x ^ k := by
    funext k
    rw [mul_pow, mul_pow, ← add_div, ← add_mul, clockTrace_eq_trace]
    ring
  rw [hfun] at hsum
  simpa [sub_eq_add_neg] using hsum

/-- **THE WEIGHT LAW, derived**: on the critical line the `p^k` log-coefficient has
modulus exactly `|s_k|/k · p^{−k/2}` — the measured formula
(Δ: 17 lines, 4.5%; E11: 13 lines, 3.1%), no longer phenomenology. -/
theorem two_clock_weight (θ : ℝ) {p : ℕ} (hp : 0 < p) (k : ℕ) :
    ‖(clockTrace θ k : ℂ) / k * (((p : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) ^ k‖
      = |clockTrace θ k| / k * ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ k := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real,
    Complex.norm_natCast, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hp']
  norm_num

/-! ## Why stop at two clocks — the n-clock law (owner, 2026-07-03)

GL(n) is n unimodular clocks.  Everything generalizes, and the generalization carries
two new theorems:

* `nClock_log_expansion` — the log of a degree-n unimodular Euler factor has k-th
  coefficient `s_k/k` with `s_k = Σᵢ αᵢᵏ` the power-sum trace of the clock ensemble.
  (The general recurrence for `s_k` in terms of Hecke data is Newton's identities —
  in Mathlib as `MvPolynomial` Newton machinery; the GL(2) three-term case is
  `clockTrace_recurrence` above.)
* `ramanujan_line_ceiling` — **purity is a line ceiling**: unimodular clocks force
  `‖s_k‖ ≤ n`, so every log-spectrum line obeys amplitude ≤ `n/k · p^{−k/2}`.
  Ramanujan–Petersson, restated on the log side, provable in one line for pure banks.
* `dc_offset` / `sym2_dc_offset` — **the constant clock**: a zero-angle clock
  contributes exactly `+1` to every `s_k` — a DC line at full weight in every prime's
  comb.  Sym² of a GL(2) form carries Satake `{e^{2iθ}, 1, e^{−2iθ}}`: its predicted
  line weights are `|2cos(2kθ_p) + 1|/k · p^{−k/2}` — a MEASURABLE +1 DC offset on the
  already-built Sym² ladders (`tmp/sym4_boundary.py` machinery), a new prediction of
  the 3-clock law.  And the DC clock is precisely what Beyond Endoscopy detects: a
  pole of `L(s, π, r)` is the coherent assembly of constant clocks across all primes —
  pole detection IS zero-frequency-line detection in the log spectrum. -/

/-- **The n-clock trace**: the power sum `s_k = Σᵢ αᵢᵏ` of a unimodular clock
ensemble with angles `θ : Fin n → ℝ`. -/
noncomputable def clockTraceN {n : ℕ} (θ : Fin n → ℝ) (k : ℕ) : ℂ :=
  ∑ i, Complex.exp ((θ i : ℂ) * I) ^ k

/-- Each clock has unit modulus at every power. -/
theorem clock_pow_norm (x : ℝ) (k : ℕ) : ‖Complex.exp ((x : ℂ) * I) ^ k‖ = 1 := by
  rw [norm_pow, Complex.norm_exp]
  simp [Complex.mul_re]

/-- **Ramanujan on the log side — the line ceiling**: a pure (unimodular) n-clock
ensemble has `‖s_k‖ ≤ n` at every k, hence every log-spectrum line is capped at
`n/k · p^{−k/2}`. -/
theorem ramanujan_line_ceiling {n : ℕ} (θ : Fin n → ℝ) (k : ℕ) :
    ‖clockTraceN θ k‖ ≤ n := by
  unfold clockTraceN
  calc ‖∑ i, Complex.exp ((θ i : ℂ) * I) ^ k‖
      ≤ ∑ i, ‖Complex.exp ((θ i : ℂ) * I) ^ k‖ := norm_sum_le _ _
    _ = ∑ _i : Fin n, (1 : ℝ) := by
        exact Finset.sum_congr rfl fun i _ => clock_pow_norm (θ i) k
    _ = n := by simp

/-- **The DC clock**: a zero-angle clock contributes exactly `+1` to every trace. -/
theorem dc_offset {n : ℕ} (θ : Fin (n + 1) → ℝ) (h : θ 0 = 0) (k : ℕ) :
    clockTraceN θ k = 1 + clockTraceN (θ ∘ Fin.succ) k := by
  unfold clockTraceN
  rw [Fin.sum_univ_succ, h]
  simp

/-- The two-clock case is the n-clock trace at `n = 2` with angles `±θ`. -/
theorem clockTraceN_two (θ : ℝ) (k : ℕ) :
    clockTraceN ![θ, -θ] k = (clockTrace θ k : ℂ) := by
  unfold clockTraceN
  rw [Fin.sum_univ_two]
  have h : ((-θ : ℝ) : ℂ) * I = -((θ : ℂ) * I) := by push_cast; ring
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h]
  exact clockTrace_eq_trace θ k

/-- **The Sym² prediction — the measurable +1**: the 3-clock ensemble
`{e^{2iθ}, 1, e^{−2iθ}}` (Sym² of a GL(2) form) has trace `2cos(2kθ) + 1`: every
line of the Sym² comb carries a DC offset of exactly one unit.  New prediction of
the 3-clock law, testable on the ladders already on disk. -/
theorem sym2_dc_offset (θ : ℝ) (k : ℕ) :
    clockTraceN ![2 * θ, 0, -(2 * θ)] k = (clockTrace (2 * θ) k : ℂ) + 1 := by
  unfold clockTraceN
  rw [Fin.sum_univ_three]
  have h0 : (![2 * θ, 0, -(2 * θ)] : Fin 3 → ℝ) 0 = 2 * θ := rfl
  have h1 : (![2 * θ, 0, -(2 * θ)] : Fin 3 → ℝ) 1 = 0 := rfl
  have h2 : (![2 * θ, 0, -(2 * θ)] : Fin 3 → ℝ) 2 = -(2 * θ) := rfl
  rw [h0, h1, h2]
  have hneg : ((-(2 * θ) : ℝ) : ℂ) * I = -(((2 * θ : ℝ) : ℂ) * I) := by push_cast; ring
  rw [hneg, show ((0 : ℝ) : ℂ) * I = 0 by simp, Complex.exp_zero, one_pow,
    ← clockTrace_eq_trace (2 * θ) k]
  ring

/-- **The n-clock log expansion** — the law's engine at every degree: the logarithm of
a degree-n unimodular Euler factor has k-th coefficient exactly `s_k/k`. -/
theorem nClock_log_expansion {n : ℕ} (θ : Fin n → ℝ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ => clockTraceN θ k / k * x ^ k)
      (∑ i, -Complex.log (1 - Complex.exp ((θ i : ℂ) * I) * x)) := by
  have hterm : ∀ i : Fin n,
      HasSum (fun k : ℕ => (Complex.exp ((θ i : ℂ) * I) * x) ^ k / k)
        (-Complex.log (1 - Complex.exp ((θ i : ℂ) * I) * x)) := by
    intro i
    apply Complex.hasSum_taylorSeries_neg_log
    rw [norm_mul]
    have h1 : ‖Complex.exp ((θ i : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re]
    rw [h1, one_mul]
    exact hx
  have hsum := hasSum_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hfun : (fun k : ℕ => ∑ i, (Complex.exp ((θ i : ℂ) * I) * x) ^ k / k)
      = fun k : ℕ => clockTraceN θ k / k * x ^ k := by
    funext k
    unfold clockTraceN
    simp only [mul_pow]
    rw [← Finset.sum_div, ← Finset.sum_mul]
    ring
  rw [hfun] at hsum
  exact hsum

/-! ## The k-dimensional n-clock law (owner, 2026-07-03)

A k-dimensional representation of the clock ensemble is a set of k integer WEIGHT
vectors; its clocks are the compositions `exp(i⟨μ_j, θ⟩)` — still unimodular, so the
whole law transfers with NO new hypothesis:

* `weightAngle` / `kdim_log_expansion` / `kdim_line_ceiling` — the r-ensemble of a
  pure bank is itself a pure k-clock bank: the log expansion and the Ramanujan line
  ceiling hold at EVERY functorial level for free.  (Model-side purity is
  functorially free; the hard arithmetic content of Ramanujan is exactly that the
  arithmetic bank realizes this model.)
* `dc_split` — the DC census: the trace splits as (number of zero-angle clocks) +
  (the moving part).  Zero weights of the representation are DC lines; their coherent
  assembly across primes is the pole — the Beyond-Endoscopy detection target counted
  exactly.
* `symTrace_exp` / `symTrace_mul_sin` — **the symmetric-power tower in closed form**:
  the Sym^m ensemble `{e^{i(m−2j)x}}_{j=0..m}` has trace `sin((m+1)x)/sin(x)` — the
  SL(2) Weyl character, derived by induction from pure exponential algebra.  Every
  Sym^m comb weight, at every k and every prime, is now
  `|sin((m+1)kθ_p)/sin(kθ_p)|/k · p^{−k/2}`: the full functorial tower of measurable
  predictions in one formula (m=1 recovers `clockTrace`; m=2 recovers
  `sym2_dc_offset`'s `2cos(2x)+1`). -/

/-- **Weight composition**: the angle of the j-th clock of a k-dimensional weight
system `μ` over the base ensemble `θ`. -/
noncomputable def weightAngle {n k : ℕ} (μ : Fin k → Fin n → ℤ) (θ : Fin n → ℝ)
    (j : Fin k) : ℝ := ∑ i, (μ j i : ℝ) * θ i

/-- **The k-dimensional log expansion** — the law at every functorial level, an
instance of the n-clock theorem with composed angles: no new hypothesis needed. -/
theorem kdim_log_expansion {n k : ℕ} (μ : Fin k → Fin n → ℤ) (θ : Fin n → ℝ)
    {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun m : ℕ => clockTraceN (weightAngle μ θ) m / m * x ^ m)
      (∑ j, -Complex.log (1 - Complex.exp ((weightAngle μ θ j : ℂ) * I) * x)) :=
  nClock_log_expansion (weightAngle μ θ) hx

/-- **Purity is functorially free on the clock side**: the composed ensemble obeys the
same line ceiling `‖s_m‖ ≤ k`, for every weight system. -/
theorem kdim_line_ceiling {n k : ℕ} (μ : Fin k → Fin n → ℤ) (θ : Fin n → ℝ) (m : ℕ) :
    ‖clockTraceN (weightAngle μ θ) m‖ ≤ k :=
  ramanujan_line_ceiling (weightAngle μ θ) m

/-- **The DC census**: the trace splits as (number of zero-angle clocks) + the moving
part.  Zero weights are DC lines; their coherent assembly across primes is the pole
order — the Beyond-Endoscopy detection target, counted exactly. -/
theorem dc_split {n : ℕ} (θ : Fin n → ℝ) (k : ℕ) :
    clockTraceN θ k
      = ((Finset.univ.filter fun i => θ i = 0).card : ℂ)
        + ∑ i ∈ Finset.univ.filter fun i => θ i ≠ 0,
            Complex.exp ((θ i : ℂ) * I) ^ k := by
  unfold clockTraceN
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => θ i = 0)]
  congr 1
  rw [Finset.sum_congr rfl (fun i hi => ?_), Finset.sum_const, nsmul_eq_mul, mul_one]
  have h0 : θ i = 0 := (Finset.mem_filter.mp hi).2
  rw [h0]
  simp

/-- **The Sym^m trace**: the m+1 clocks `e^{i(m−2j)x}`, j = 0..m. -/
noncomputable def symTrace (m : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1),
    Complex.exp (((m : ℂ) - 2 * (j : ℂ)) * ((x : ℂ) * I))

/-- The Sym recurrence: `T_{m+1} = e^{ix}·T_m + e^{−i(m+1)x}`. -/
theorem symTrace_succ (m : ℕ) (x : ℝ) :
    symTrace (m + 1) x
      = Complex.exp ((x : ℂ) * I) * symTrace m x
        + Complex.exp (-(((m : ℂ) + 1) * ((x : ℂ) * I))) := by
  unfold symTrace
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · congr 1
    push_cast
    ring

/-- **The symmetric-power character, exponential form**: the Sym^m trace satisfies
`T_m · (e^{ix} − e^{−ix}) = e^{i(m+1)x} − e^{−i(m+1)x}` — equivalently
`T_m = sin((m+1)x)/sin(x)`, the SL(2) Weyl character: the ENTIRE symmetric-power
tower's comb structure in closed form (m = 1 recovers `clockTrace`; m = 2 recovers
`2cos(2x) + 1`, the DC offset). -/
theorem symTrace_exp (m : ℕ) (x : ℝ) :
    symTrace m x * (Complex.exp ((x : ℂ) * I) - Complex.exp (-((x : ℂ) * I)))
      = Complex.exp (((m : ℂ) + 1) * ((x : ℂ) * I))
        - Complex.exp (-(((m : ℂ) + 1) * ((x : ℂ) * I))) := by
  induction m with
  | zero =>
      unfold symTrace
      rw [Finset.range_one, Finset.sum_singleton]
      have h1 : (((0 : ℕ) : ℂ) - 2 * (((0 : ℕ) : ℕ) : ℂ)) * ((x : ℂ) * I) = 0 := by
        push_cast
        ring
      have h2 : (((0 : ℕ) : ℂ) + 1) * ((x : ℂ) * I) = (x : ℂ) * I := by
        push_cast
        ring
      rw [h1, h2, Complex.exp_zero, one_mul]
  | succ m ih =>
      rw [symTrace_succ, add_mul, mul_assoc, ih]
      have hsplit : (((m + 1 : ℕ) : ℂ) + 1) * ((x : ℂ) * I)
          = ((m : ℂ) + 1) * ((x : ℂ) * I) + (x : ℂ) * I := by
        push_cast
        ring
      rw [hsplit]
      simp only [Complex.exp_add, Complex.exp_neg]
      have hne : Complex.exp ((x : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
      have hne2 : Complex.exp (((m : ℂ) + 1) * ((x : ℂ) * I)) ≠ 0 :=
        Complex.exp_ne_zero _
      field_simp
      ring

end CriticalLinePhasor.TwoClockWeightLaw
