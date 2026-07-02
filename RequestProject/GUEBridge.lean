import RequestProject.ReverbResidue

/-!
# The GUE bridge, cell-closure arithmetic, and Satake silence

Three formal counterparts to the reverb synthesis (see `ReverbResidue.lean` and the numerical
record): GUE is correct bookkeeping with no mechanism inside it — the mechanism is the analytic
product law, shared *identically* by random-matrix theory, and the medium (not repulsion)
carries the arithmetic.

## 1. The CUE bridge (`cue_reopening_rate`)

In random-matrix theory the "derivative statistic" |P′(λ_k)| at an eigenvalue of the
characteristic polynomial is **literally the product of distances to the other eigenvalues** —
the very same object as the fiber's reopening rate in `ReverbResidue.cluster_product_law_norm`.
We prove it here for any complex matrix:

* `derivative_prod_roots_eval` — for `P = ∏ (X − r)` over a root multiset, `P′(μ)` at a root
  `μ` equals `∏_{r ∈ roots ∖ μ} (μ − r)` (multiplicities included);
* `cue_derivative_at_eigenvalue`, `cue_rate_eq_distance_product` — instantiated at
  `Matrix.charpoly` over `ℂ`, in value and in norm;
* `cue_reopening_slope` — the characteristic polynomial, viewed as a fiber, satisfies the SAME
  reopening law (`ReverbResidue.reopening_slope`) at each eigenvalue.

Hence "GUE-like derivative statistics" at zeros need no repulsion mechanism: both sides compute
the identical distance product; the statistics differ only through the configurations.

## 2. Cell-closure arithmetic (`step_closes_iff`, `integer_step_never_closes`)

Sam's scaling hypothesis, as a theorem: a carrier cell step `c` closes (some positive number of
steps returns the phase to `1`) **iff** `c` is a rational multiple of `2π`.  Root-of-unity
steps `2π/m` close in `m` steps (`root_of_unity_step_closes`; the Eisenstein π/3 = 2π/6 case is
`eisenstein_step_closes`), while an **integer** step in radians *never* closes
(`integer_step_never_closes`) — because `π` is irrational.  Exact μ_m harmonics are exactly the
`2π·ℚ` gauge choices; whole-integer scaling is structurally incapable of closure.

## 3. Satake silence (`satake_newton_two`, `e11_ln4_silent`)

The spectroscopy of the ambient field reads the Satake parameters: the `p²`-clock has amplitude
`|α² + β²|/2`, and Newton's identity gives `α² + β² = λ² − 2` for `α + β = λ`, `αβ = 1`.  Hence
the `p²`-line is silent **iff** `λ² = 2` (`satake_silence_iff`) — realized by elliptic curve
11.a at `p = 2` (`a₂ = −2`, so `λ = −√2`): `e11_ln4_silent`, the exact null measured in the
ambient spectrum.

The general weight law `|αᵖᵏ + βᵖᵏ|/k · p^{−k/2}` (whose `k = 2` silence these theorems prove
algebraically) is a *measured* envelope, not a theorem here.  Its clean regeneration
(`tmp/satake_clean.py`, unclipped windowed projection, per-run calibration = `1.00000` on the
exact truncated explicit series, bank `N = 1.5·10⁶`) reads, on calibration-gated `k = 1` lines:
Δ `0.9997 ± 1.1%`, level-11 `0.9636 ± 1.0%` (degree 2); and for `Sym²Δ` (degree 3) `1.0006 ± 0.2%`
at a height the degree-3 bank supports — retiring the historical `±4%`/`0.82` as finite-bank and
clip method.  The `k = 2` and supersingular silences (`e11_ln4_silent` here; `ln19`, `ln29`)
sit at the detection floor in that run, as the algebra requires.

Everything is unconditional; nothing assumes GRH/RH or zero locations.  Mathlib-only;
no `sorry`, no `axiom`.
-/

open Polynomial Filter Topology

namespace CriticalLinePhasor.GUEBridge

/-! ## 1. The CUE bridge -/

/-- **Derivative of a split polynomial at a root is the distance product.**  For
`P = ∏_{r ∈ R} (X − r)` and `μ ∈ R`, `P′(μ) = ∏_{r ∈ R ∖ μ} (μ − r)` (one copy of `μ`
removed; repeated roots make both sides `0`). -/
theorem derivative_prod_roots_eval (R : Multiset ℂ) (μ : ℂ) (hμ : μ ∈ R) :
    (derivative (R.map (fun r => X - C r)).prod).eval μ
      = ((R.erase μ).map (fun r => μ - r)).prod := by
  classical
  conv_lhs => rw [← Multiset.cons_erase hμ, Multiset.map_cons, Multiset.prod_cons]
  rw [derivative_mul]
  simp only [derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  rw [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero,
    eval_multiset_prod, Multiset.map_map]
  simp

variable {n : ℕ}

/-- The characteristic polynomial over `ℂ` is the product over its eigenvalue multiset. -/
theorem charpoly_eq_prod_roots (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly = (M.charpoly.roots.map (fun r => X - C r)).prod :=
  (IsAlgClosed.splits M.charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic M)

/-- **CUE bridge (value form).**  The derivative of the characteristic polynomial at an
eigenvalue is the product of distances to the other eigenvalues. -/
theorem cue_derivative_at_eigenvalue (M : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ}
    (hμ : μ ∈ M.charpoly.roots) :
    (derivative M.charpoly).eval μ
      = ((M.charpoly.roots.erase μ).map (fun r => μ - r)).prod := by
  conv_lhs => rw [charpoly_eq_prod_roots M]
  exact derivative_prod_roots_eval _ μ hμ

/-- The norm of a multiset product in `ℂ` is the product of norms. -/
theorem norm_multiset_prod' (s : Multiset ℂ) : ‖s.prod‖ = (s.map (fun z => ‖z‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih => simp [ih]

/-- **CUE bridge (norm form)** — the random-matrix "derivative statistic" IS the distance
product: `‖P′(μ)‖ = ∏ ‖μ − r‖`, the same object as the fiber's reopening rate in
`ReverbResidue.cluster_product_law_norm`. -/
theorem cue_rate_eq_distance_product (M : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ}
    (hμ : μ ∈ M.charpoly.roots) :
    ‖(derivative M.charpoly).eval μ‖
      = ((M.charpoly.roots.erase μ).map (fun r => ‖μ - r‖)).prod := by
  rw [cue_derivative_at_eigenvalue M hμ, norm_multiset_prod', Multiset.map_map]
  simp

/-- **The characteristic polynomial obeys the fiber's reopening law.**  Viewed as a fiber,
the char poly's local slope at an eigenvalue tends to its derivative there — the identical
statement to `ReverbResidue.reopening_slope` for the L-fiber; the two "universes" share one
mechanism. -/
theorem cue_reopening_slope (M : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ}
    (hμ : μ ∈ M.charpoly.roots) :
    Tendsto (fun z => M.charpoly.eval z / (z - μ)) (𝓝[≠] μ)
      (𝓝 ((derivative M.charpoly).eval μ)) :=
  CriticalLinePhasor.ReverbResidue.reopening_slope (Polynomial.hasDerivAt _ μ)
    (isRoot_of_mem_roots hμ)

/-! ## 2. Cell-closure arithmetic -/

/-- **A cell step closes iff it is a rational multiple of `2π`** (stated with the integer
witnesses: some positive number of steps lands exactly on a full number of turns). -/
theorem step_closes_iff (c : ℝ) :
    (∃ k : ℕ, 0 < k ∧ Complex.exp ((k : ℂ) * (c : ℂ) * Complex.I) = 1)
      ↔ ∃ (k : ℕ) (m : ℤ), 0 < k ∧ (k : ℝ) * c = 2 * Real.pi * m := by
  constructor
  · rintro ⟨k, hk, h⟩
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    refine ⟨k, m, hk, ?_⟩
    have := congrArg Complex.im hm
    simpa [Complex.mul_im, mul_comm, mul_left_comm] using this
  · rintro ⟨k, m, hk, h⟩
    refine ⟨k, hk, ?_⟩
    rw [Complex.exp_eq_one_iff]
    refine ⟨m, ?_⟩
    have hC : ((k : ℂ) * (c : ℂ)) = 2 * (Real.pi : ℂ) * (m : ℂ) := by exact_mod_cast h
    rw [hC]; ring

/-- **Integer steps never close** — Sam's hypothesis as a theorem.  For any positive integer
step `q` (radians), no positive number of steps returns the carrier phase to `1`, because `π`
is irrational. -/
theorem integer_step_never_closes (q : ℕ) (hq : 0 < q) :
    ¬ ∃ k : ℕ, 0 < k ∧ Complex.exp ((k : ℂ) * (q : ℂ) * Complex.I) = 1 := by
  intro h
  obtain ⟨k, m, hk, hm⟩ := (step_closes_iff (q : ℝ)).mp (by exact_mod_cast h)
  have hkq : (0 : ℝ) < (k : ℝ) * q := by positivity
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [hm] at hkq
    simp at hkq
  refine irrational_pi ⟨(k * q : ℚ) / (2 * m), ?_⟩
  have h2m : (2 * (m : ℝ)) ≠ 0 := by
    simp [hm0]
  push_cast
  rw [div_eq_iff h2m]
  linarith [hm]

/-- **Root-of-unity steps close**: step `2π/m` returns to `1` after exactly `m` steps —
the μ_m (cyclotomic) cell harmonics. -/
theorem root_of_unity_step_closes (m : ℕ) (hm : 0 < m) :
    Complex.exp ((m : ℂ) * ((2 * Real.pi / m : ℝ) : ℂ) * Complex.I) = 1 := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have : (m : ℂ) * ((2 * Real.pi / m : ℝ) : ℂ) = 2 * Real.pi := by
    push_cast
    field_simp
  rw [this]
  simpa [mul_assoc] using Complex.exp_two_pi_mul_I

/-- **The Eisenstein cell closes in six steps**: `π/3 = 2π/6`, the ℤ[ζ₆] harmonics of the
carrier.  (Instance of `root_of_unity_step_closes`.) -/
theorem eisenstein_step_closes :
    Complex.exp ((6 : ℂ) * ((Real.pi / 3 : ℝ) : ℂ) * Complex.I) = 1 := by
  have h := root_of_unity_step_closes 6 (by norm_num)
  have : ((2 * Real.pi / (6 : ℕ) : ℝ) : ℂ) = ((Real.pi / 3 : ℝ) : ℂ) := by
    push_cast; ring
  rw [this] at h
  exact_mod_cast h

/-! ## 3. Satake silence -/

/-- **Newton's identity for the Satake pair**: with `α + β = λ` and `αβ = 1`
(unitary local parameters), `α² + β² = λ² − 2`. -/
theorem satake_newton_two (α β lam : ℂ) (hsum : α + β = lam) (hprod : α * β = 1) :
    α ^ 2 + β ^ 2 = lam ^ 2 - 2 := by
  subst hsum
  linear_combination (-2 : ℂ) * hprod

/-- **The `p²`-clock is silent iff `λ(p)² = 2`**: the ambient line at `ln p²` has amplitude
`|α² + β²|/2`, which vanishes exactly at Satake angle `±π/4, ±3π/4`. -/
theorem satake_silence_iff (α β lam : ℂ) (hsum : α + β = lam) (hprod : α * β = 1) :
    α ^ 2 + β ^ 2 = 0 ↔ lam ^ 2 = 2 := by
  rw [satake_newton_two α β lam hsum hprod, sub_eq_zero]

/-- **Elliptic curve 11.a at `p = 2`**: `a₂ = −2` gives `λ(2) = −2/√2 = −√2`, hence the
exact silence `α² + β² = 0` — the null line measured in the ambient spectrum. -/
theorem e11_ln4_silent (α β : ℂ) (hsum : α + β = -((Real.sqrt 2 : ℝ) : ℂ))
    (hprod : α * β = 1) :
    α ^ 2 + β ^ 2 = 0 := by
  rw [satake_newton_two α β _ hsum hprod]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  rw [neg_pow, h2]
  norm_num

end CriticalLinePhasor.GUEBridge
