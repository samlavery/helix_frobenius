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
formula itself is no longer phenomenology.  No proof placeholders; standard axioms.
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

/-! ## The tail laws (owner: "go go", 2026-07-03)

The BE instruments measured tail-mass growth 0.042→0.256 across Sym^0..Sym^4 and
fit it at R² = 0.977 by ceiling × √(harmonic count) — both quantities read off the
Weyl character.  The provable core, proven here:

* `symTrace_ceiling` — `‖U_r‖_∞ ≤ r+1`: the comb's height is its clock count.
* `windowed_tail_bound` — **the tail-mass ceiling law**: any windowed tail of the
  Sym^m comb is ≤ (m+1) × (the window's own tail mass).  The measured growth sits
  under this proven linear envelope; the √harmonics refinement (how much of the
  envelope the comb actually fills) is the measured half.
* `symTrace_energy` — **energy = clock count** (Parseval): the mean-square of the
  Sym^m trace over a full period is exactly `2π(m+1)` — the comb's total power is its
  dimension.  Distinct clock frequencies are orthogonal; nothing interferes in the
  energy norm (the cup principle, on the circle). -/

/-- **The comb ceiling**: `‖symTrace m x‖ ≤ m + 1` — the Sym^m comb's height is its
clock count. -/
theorem symTrace_ceiling (m : ℕ) (x : ℝ) : ‖symTrace m x‖ ≤ m + 1 := by
  unfold symTrace
  calc ‖∑ j ∈ Finset.range (m + 1),
        Complex.exp (((m : ℂ) - 2 * (j : ℂ)) * ((x : ℂ) * I))‖
      ≤ ∑ j ∈ Finset.range (m + 1),
        ‖Complex.exp (((m : ℂ) - 2 * (j : ℂ)) * ((x : ℂ) * I))‖ := norm_sum_le _ _
    _ = ∑ _j ∈ Finset.range (m + 1), (1 : ℝ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Complex.norm_exp]
        have h : ((((m : ℂ) - 2 * (j : ℂ)) * ((x : ℂ) * I)).re) = 0 := by
          simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
        rw [h, Real.exp_zero]
    _ = m + 1 := by simp
    
/-- **The tail-mass ceiling law**: any windowed tail of the Sym^m comb is bounded by
`(m+1) ×` (the window's own tail mass) — the proven linear envelope under which the
measured tail growth sits. -/
theorem windowed_tail_bound (m : ℕ) (θ : ℕ → ℝ) (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (S : Finset ℕ) :
    ‖∑ k ∈ S, (w k : ℂ) * symTrace m (θ k)‖ ≤ (m + 1) * ∑ k ∈ S, w k := by
  calc ‖∑ k ∈ S, (w k : ℂ) * symTrace m (θ k)‖
      ≤ ∑ k ∈ S, ‖(w k : ℂ) * symTrace m (θ k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ S, w k * (m + 1) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw k)]
        exact mul_le_mul_of_nonneg_left (symTrace_ceiling m (θ k)) (hw k)
    _ = (m + 1) * ∑ k ∈ S, w k := by
        rw [← Finset.sum_mul, mul_comm]

/-- **Circle orthogonality**: a nonzero integer frequency integrates to zero over a
full period. -/
theorem circle_orthogonality {d : ℤ} (hd : d ≠ 0) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (((d : ℂ) * I) * x) = 0 := by
  have hc : ((d : ℂ) * I) ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr hd) Complex.I_ne_zero
  rw [integral_exp_mul_complex hc]
  have h1 : (d : ℂ) * I * ((2 * Real.pi : ℝ) : ℂ) = (d : ℂ) * (2 * Real.pi * I) := by
    push_cast
    ring
  have h2 : (d : ℂ) * I * ((0 : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  rw [h1, h2, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_zero, sub_self, zero_div]

/-- **Energy = clock count** (Parseval for the Sym^m comb): the mean-square over a
full period is exactly `2π(m+1)` — the comb's total power is its dimension.  Distinct
clock frequencies are orthogonal: nothing interferes in the energy norm (the cup
principle, on the circle). -/
theorem symTrace_energy (m : ℕ) :
    ∫ x in (0 : ℝ)..(2 * Real.pi),
        symTrace m x * (starRingEnd ℂ) (symTrace m x)
      = ((2 * Real.pi * (m + 1) : ℝ) : ℂ) := by
  have key : ∀ x : ℝ, symTrace m x * (starRingEnd ℂ) (symTrace m x)
      = ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (m + 1),
          Complex.exp ((((2 * ((k : ℤ) - (j : ℤ)) : ℤ) : ℂ) * I) * x) := by
    intro x
    unfold symTrace
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I,
      Complex.conj_natCast, map_ofNat]
    push_cast
    ring
  have hint : ∀ (f : ℝ → ℂ), Continuous f →
      IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi) :=
    fun f hf => hf.intervalIntegrable _ _
  calc ∫ x in (0 : ℝ)..(2 * Real.pi),
          symTrace m x * (starRingEnd ℂ) (symTrace m x)
      = ∫ x in (0 : ℝ)..(2 * Real.pi), ∑ j ∈ Finset.range (m + 1),
          ∑ k ∈ Finset.range (m + 1),
            Complex.exp ((((2 * ((k : ℤ) - (j : ℤ)) : ℤ) : ℂ) * I) * x) := by
        refine intervalIntegral.integral_congr fun x _ => key x
    _ = ∑ j ∈ Finset.range (m + 1), ∫ x in (0 : ℝ)..(2 * Real.pi),
          ∑ k ∈ Finset.range (m + 1),
            Complex.exp ((((2 * ((k : ℤ) - (j : ℤ)) : ℤ) : ℂ) * I) * x) := by
        have hcont : ∀ j : ℕ, Continuous fun x : ℝ =>
            ∑ k ∈ Finset.range (m + 1),
              Complex.exp ((((2 * ((k : ℤ) - (j : ℤ)) : ℤ) : ℂ) * I) * x) := by
          intro j
          exact continuous_finsetSum _ fun k _ => by fun_prop
        exact intervalIntegral.integral_finsetSum
          fun j _ => ((hcont j).intervalIntegrable _ _)
    _ = ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (m + 1),
          ∫ x in (0 : ℝ)..(2 * Real.pi),
            Complex.exp ((((2 * ((k : ℤ) - (j : ℤ)) : ℤ) : ℂ) * I) * x) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact intervalIntegral.integral_finsetSum
          fun k _ => ((by fun_prop : Continuous fun x : ℝ =>
            Complex.exp ((((2 * ((k : ℤ) - (j : ℤ)) : ℤ) : ℂ) * I) * x)).intervalIntegrable _ _)
    _ = ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (m + 1),
          (if k = j then ((2 * Real.pi : ℝ) : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        by_cases hjk : k = j
        · subst hjk
          rw [if_pos rfl]
          have harg : ∀ x : ℝ,
              Complex.exp ((((2 * ((k : ℤ) - (k : ℤ)) : ℤ) : ℂ) * I) * x) = 1 := by
            intro x
            rw [show (((2 * ((k : ℤ) - (k : ℤ)) : ℤ) : ℂ) * I) * x = 0 by push_cast; ring,
              Complex.exp_zero]
          rw [intervalIntegral.integral_congr fun x _ => harg x,
            intervalIntegral.integral_const]
          rw [sub_zero, Complex.real_smul, mul_one]
        · rw [if_neg hjk]
          refine circle_orthogonality ?_
          intro h
          apply hjk
          omega
    _ = ((2 * Real.pi * (m + 1) : ℝ) : ℂ) := by
        have hrow : ∀ j ∈ Finset.range (m + 1),
            (∑ k ∈ Finset.range (m + 1),
              if k = j then ((2 * Real.pi : ℝ) : ℂ) else 0)
              = ((2 * Real.pi : ℝ) : ℂ) := by
          intro j hj
          rw [Finset.sum_ite_eq' (Finset.range (m + 1)) j
            fun _ => ((2 * Real.pi : ℝ) : ℂ)]
          exact if_pos hj
        rw [Finset.sum_congr rfl hrow, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        push_cast
        ring

/-! ## The window-edge clock (MB emergent K, 2026-07-03)

The MB beat gate (`tmp/mb_beat.py`, `tmp/mb_beat_results.txt`) found that the comb
spacing is the chart's own edge clock.  The Lean core is just the phase bookkeeping:
for a phase kernel with denominator `4 * lf2`, the number of edge-to-edge turns across
a window span `S` at frequency spacing `ν` is `ν * S / (4 * lf2)`.  One full turn
therefore selects `ν = 4 * lf2 / S`.  The measured effective MB span is `(47/50) * X`,
so the exact model readout is

`4 * lf2 / ((47/50) * X) = (25/47) * lf2 * (X/8)⁻¹`.

The switch variable records whether the second edge component is audible; it does not
enter the spacing once the edge clock is on. -/

/-- Edge-to-edge phase turns across a window span `span` at spacing `ν`, in the MB
normalization with phase denominator `4 * lf2`. -/
noncomputable def edgePhaseTurns (lf2 span ν : ℝ) : ℝ := ν * span / (4 * lf2)

/-- The edge-clock spacing selected by one full edge-to-edge turn. -/
noncomputable def edgeBeatSpacing (lf2 span : ℝ) : ℝ := 4 * lf2 / span

/-- The MB window-edge clock with effective span `κ * X`. -/
noncomputable def windowEdgeClock (lf2 X κ : ℝ) : ℝ := edgeBeatSpacing lf2 (κ * X)

/-- The edge-clock spacing makes exactly one edge-to-edge phase turn. -/
theorem edgeBeatSpacing_phase_turns {lf2 span : ℝ} (hlf2 : lf2 ≠ 0)
    (hspan : span ≠ 0) :
    edgePhaseTurns lf2 span (edgeBeatSpacing lf2 span) = 1 := by
  unfold edgePhaseTurns edgeBeatSpacing
  field_simp [hlf2, hspan]

/-- The one-turn condition determines the edge-clock spacing uniquely. -/
theorem edgeBeatSpacing_unique {lf2 span ν : ℝ} (hlf2 : lf2 ≠ 0)
    (hspan : span ≠ 0) (hν : edgePhaseTurns lf2 span ν = 1) :
    ν = edgeBeatSpacing lf2 span := by
  unfold edgePhaseTurns at hν
  unfold edgeBeatSpacing
  field_simp [hlf2, hspan] at hν ⊢
  linarith

/-- Rewriting an endpoint span as an effective `κ * X` span gives the window-edge
clock. -/
theorem edgeBeatSpacing_of_effective_window {lf2 left right X κ : ℝ}
    (hspan : right - left = κ * X) :
    edgeBeatSpacing lf2 (right - left) = windowEdgeClock lf2 X κ := by
  simp [windowEdgeClock, hspan]

/-- The measured MB span coefficient is `0.94 = 47/50`. -/
theorem windowEdgeClock_measured_span (lf2 X : ℝ) :
    windowEdgeClock lf2 X (47 / 50) = 4 * lf2 / ((47 / 50) * X) := rfl

/-- The measured MB edge clock in dispersion-law coordinates:
`Dν = (25/47) * lf2 * (X/8)⁻¹`. -/
theorem windowEdgeClock_measured_dispersion {lf2 X : ℝ} (hX : X ≠ 0) :
    windowEdgeClock lf2 X (47 / 50) = (25 / 47) * lf2 * (X / 8)⁻¹ := by
  unfold windowEdgeClock edgeBeatSpacing
  field_simp [hX]
  ring

/-- Positivity of the edge clock under positive scale and positive span. -/
theorem windowEdgeClock_pos {lf2 X κ : ℝ} (hlf2 : 0 < lf2) (hX : 0 < X)
    (hκ : 0 < κ) : 0 < windowEdgeClock lf2 X κ := by
  unfold windowEdgeClock edgeBeatSpacing
  positivity

/-- A minimal switch predicate: positive second-component prominence means the
window-edge beat is audible. -/
def BimodalSwitch (prominence : ℝ) : Prop := 0 < prominence

/-- The MB window-edge readout: once the switch is on, the spacing is the window-edge
clock.  The switch is kept separate from the spacing formula. -/
def WindowEdgeClockReadout (lf2 X κ prominence spacing : ℝ) : Prop :=
  BimodalSwitch prominence ∧ spacing = windowEdgeClock lf2 X κ

/-- Any readout carries the edge-clock spacing. -/
theorem WindowEdgeClockReadout.spacing {lf2 X κ prominence spacing : ℝ}
    (h : WindowEdgeClockReadout lf2 X κ prominence spacing) :
    spacing = windowEdgeClock lf2 X κ :=
  h.2

/-- A zero-prominence profile has no audible second edge component in this model. -/
theorem no_WindowEdgeClockReadout_of_zero_prominence {lf2 X κ spacing : ℝ} :
    ¬ WindowEdgeClockReadout lf2 X κ 0 spacing := by
  intro h
  exact (lt_irrefl (0 : ℝ)) h.1

/-- The measured dispersion law is independent of the switch parameter: the exponent
of `(1 + ξ)` is zero. -/
theorem windowEdgeClock_measured_dispersion_with_switch {lf2 X ξ : ℝ} (hX : X ≠ 0) :
    windowEdgeClock lf2 X (47 / 50)
      = (25 / 47) * lf2 * (X / 8)⁻¹ * (1 + ξ) ^ 0 := by
  rw [windowEdgeClock_measured_dispersion hX]
  ring

/-! ## The gamma-spread bound from the clock readout

The measured invariant is the clock-readout band `0.441 +- 0.058`.  The theorem below
records the exact proof shape used by the campaign: once the gamma spread is identified
with the emergent clock readout, a certified band around `0.441` gives the upper bound
`0.499` by interval arithmetic. -/

/-- A readout value is in the measured gamma-spread clock band `0.441 +- 0.058`. -/
def CertifiedGammaSpreadBand (value : ℝ) : Prop :=
  |value - 441 / 1000| ≤ 58 / 1000

/-- The gamma spread is read by the emergent window-edge clock. -/
def GammaSpreadClockReadout (lf2 X κ prominence gammaSpread : ℝ) : Prop :=
  WindowEdgeClockReadout lf2 X κ prominence gammaSpread

/-- Any scalar certified in the `0.441 +- 0.058` band is bounded by `0.499`. -/
theorem gammaSpread_le_of_certified_band {gammaSpread : ℝ}
    (hband : CertifiedGammaSpreadBand gammaSpread) :
    gammaSpread ≤ 499 / 1000 := by
  unfold CertifiedGammaSpreadBand at hband
  rw [abs_sub_le_iff] at hband
  linarith

/-- **Gamma-spread bound from the emergent clock law.**  If the gamma spread is the
window-edge clock readout and that clock is certified in the measured band, then the
gamma spread is bounded by `0.499`. -/
theorem gammaSpread_bound_from_windowEdgeClock {lf2 X κ prominence gammaSpread : ℝ}
    (hread : GammaSpreadClockReadout lf2 X κ prominence gammaSpread)
    (hband : CertifiedGammaSpreadBand (windowEdgeClock lf2 X κ)) :
    gammaSpread ≤ 499 / 1000 := by
  unfold GammaSpreadClockReadout at hread
  rw [WindowEdgeClockReadout.spacing hread]
  exact gammaSpread_le_of_certified_band hband

/-- A finite family whose entries all lie within `radius` of the same clock center has
pairwise spread at most `2 * radius`.  This is the finite-grid version of the same
clock-band argument. -/
theorem pairwise_spread_bound_of_clock_band {ι : Type*} (s : Finset ι) (gamma : ι → ℝ)
    {center radius : ℝ} (hband : ∀ i ∈ s, |gamma i - center| ≤ radius) :
    ∀ i ∈ s, ∀ j ∈ s, |gamma i - gamma j| ≤ 2 * radius := by
  intro i hi j hj
  calc
    |gamma i - gamma j| = |(gamma i - center) + (center - gamma j)| := by ring_nf
    _ ≤ |gamma i - center| + |center - gamma j| := abs_add_le _ _
    _ = |gamma i - center| + |gamma j - center| := by rw [abs_sub_comm center (gamma j)]
    _ ≤ radius + radius := add_le_add (hband i hi) (hband j hj)
    _ = 2 * radius := by ring

end CriticalLinePhasor.TwoClockWeightLaw
