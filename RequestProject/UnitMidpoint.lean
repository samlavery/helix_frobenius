import Mathlib

/-!
# UNIT/2: criticality is midpointness, and RH's native chart contains no number

Sam's reframing, formalized.  The Riemann Hypothesis in Riemann's own variable (`Ξ(t)`,
`s = 1/2 + i·t`) never mentions `1/2`: it says the roots are **real** — on the fixed axis of
complex conjugation, the midpoint of the fundamental involution.  The number `1/2` is only
the **translation constant** between the arithmetic counting chart (where the unit is set by
the normalization) and the centered symmetry chart.  In a base-`b` counting system the same
locus reads `log b / 2`; in the π/3 helix cell the mirror sits at `π/6`; over `𝔽_q` it is
`|Frobenius| = q^{1/2}` (the repo's `midpoint_forcing`).  The invariant is *midpointness of an
involution*; the coordinate is gauge.

* `real_axis_is_conjugation_midpoint` — the fixed locus of conjugation is exactly `ℝ`
  (`im = 0`): the centered chart's statement, containing no number.
* `centered_chart` — for any unit `c`, reality in the centered variable `t = −i(ρ − c/2)`
  is exactly `Re ρ = c/2`; `riemann_chart` is the `c = 1` case: **"roots real" ⇔
  "Re = 1/2" is a change of chart, not new content.**
* `affine_reflection_fixed_iff` — the fixed point of the involution `x ↦ c − x` is `c/2`:
  UNIT/2 for every unit.
* `mirror_fixed_iff`, `eisenstein_mirror` — the unit-circle/hexagon form: the anti-involution
  `z ↦ e^{iΔ}·conj z` fixes exactly the half-unit direction `Δ/2`; for the Eisenstein cell
  `Δ = π/3` the mirror is the `π/6` axis (the hexagon's edge-midpoint line).
* `criticality_is_half_unit` — base covariance: `σ = 1/2` in unit-1 counting is
  `σ·log b = log b / 2` in base-`b` counting (the log-7 system's midpoint is `log 7 / 2 =
  log √7`; the base-free statement is that the critical amplitude `n^{-1/2}` is the geometric
  mean of the dual pair `1` and `n^{-1}`).
* `prime_clocks_incommensurable` — in the base-`q` system prime `q` ticks at unit rate and
  every other prime's rate `log p / log q` is **irrational**: the mutual incommensurability
  of the prime clocks is unique factorization, and is why the ambient spectral lines never
  collide.

Mathlib-only; unconditional; no `sorry`, no `axiom`; no zero-location claims.
-/

open Complex

namespace CriticalLinePhasor.UnitMidpoint

/-! ## 1. The centered chart: conjugation's fixed axis, and the 1/2-free form of criticality -/

/-- **The real axis is the midpoint locus of conjugation**: `conj z = z ↔ Im z = 0`.
The centered chart's criticality statement — no number appears. -/
theorem real_axis_is_conjugation_midpoint (z : ℂ) :
    (starRingEnd ℂ) z = z ↔ z.im = 0 :=
  Complex.conj_eq_iff_im

/-- **Change of chart**: for any unit `c`, reality of the centered variable
`t = −i·(ρ − c/2)` is exactly `Re ρ = c/2`.  Criticality is "t is real"; the coordinate
`c/2` is the chart, not the content. -/
theorem centered_chart (c : ℝ) (ρ : ℂ) :
    (-(Complex.I * (ρ - (c / 2 : ℝ)))).im = 0 ↔ ρ.re = c / 2 := by
  simp [Complex.mul_im, Complex.sub_re, Complex.ofReal_re, sub_eq_zero]
  constructor <;> intro h <;> linarith

/-- **Riemann's chart** (`c = 1`): the roots of `Ξ` are real ⇔ the zeros have `Re = 1/2`.
RH's native statement mentions no `1/2`; the `1/2` is this translation. -/
theorem riemann_chart (ρ : ℂ) :
    (-(Complex.I * (ρ - ((1 : ℝ) / 2 : ℝ)))).im = 0 ↔ ρ.re = 1 / 2 := by
  simpa using centered_chart 1 ρ

/-! ## 2. UNIT/2 on the line and on the circle -/

/-- **The fixed point of the involution `x ↦ c − x` is `c/2`**: the midpoint of the unit,
for every unit.  (`c = 1` recovers the critical abscissa; the "1" is the reflection unit.) -/
theorem affine_reflection_fixed_iff (c x : ℝ) : c - x = x ↔ x = c / 2 := by
  constructor <;> intro h <;> linarith

/-- **The half-unit mirror on the circle**: the anti-involution `z ↦ e^{iΔ}·conj z` fixes
`z` exactly when `z` lies on the `Δ/2` axis (i.e. `z·e^{−iΔ/2}` is real).  The unit circle's
"midpoint formula": a rotation-unit `Δ` reflects about its half-unit direction. -/
theorem mirror_fixed_iff (Δ : ℝ) (z : ℂ) :
    Complex.exp (Complex.I * Δ) * (starRingEnd ℂ) z = z ↔
      (z * Complex.exp (-(Complex.I * ((Δ / 2 : ℝ) : ℂ)))).im = 0 := by
  set u := Complex.exp (Complex.I * ((Δ / 2 : ℝ) : ℂ)) with hu
  have hune : u ≠ 0 := Complex.exp_ne_zero _
  have hcu : (starRingEnd ℂ) u = u⁻¹ := by
    rw [hu, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
      ← Complex.exp_neg]
    ring_nf
  have hu2 : Complex.exp (Complex.I * Δ) = u * u := by
    rw [hu, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hexpneg : Complex.exp (-(Complex.I * ((Δ / 2 : ℝ) : ℂ))) = u⁻¹ := by
    rw [Complex.exp_neg, ← hu]
  rw [hexpneg, ← Complex.conj_eq_iff_im, map_mul, map_inv₀, hcu, inv_inv, hu2]
  constructor
  · intro h
    have hsub : z * u⁻¹ = (u * u * (starRingEnd ℂ) z) * u⁻¹ := by rw [h]
    rw [hsub]
    symm
    rw [mul_inv_eq_iff_eq_mul₀ hune]
    ring
  · intro h
    have h2 := congrArg (· * u) h
    rw [mul_assoc z, inv_mul_cancel₀ hune, mul_one] at h2
    calc u * u * (starRingEnd ℂ) z = (starRingEnd ℂ) z * u * u := by ring
      _ = z := h2

/-- **The Eisenstein cell's mirror is at π/6** — the half of the π/3 cell unit: the hexagon's
edge-midpoint axis.  The same UNIT/2 formula as the critical line, in the carrier's own
geometry. -/
theorem eisenstein_mirror (z : ℂ) :
    Complex.exp (Complex.I * (Real.pi / 3 : ℝ)) * (starRingEnd ℂ) z = z ↔
      (z * Complex.exp (-(Complex.I * ((Real.pi / 6 : ℝ) : ℂ)))).im = 0 := by
  have h := mirror_fixed_iff (Real.pi / 3) z
  rw [show (Real.pi / 3) / 2 = Real.pi / 6 by ring] at h
  exact h

/-! ## 3. Base covariance: UNIT/2 in every counting system -/

/-- **`1/2` is `UNIT/2`**: in base-`b` counting (unit `log b` on the log-height axis) the
critical abscissa reads `log b / 2`.  The log-7 system's midpoint is `log 7 / 2 = log √7`;
the base-free content is the geometric-mean amplitude `n^{-1/2} = √(1 · n^{-1})`. -/
theorem criticality_is_half_unit {b : ℝ} (hb : 1 < b) (σ : ℝ) :
    σ = 1 / 2 ↔ σ * Real.log b = Real.log b / 2 := by
  have hlb : Real.log b ≠ 0 := ne_of_gt (Real.log_pos hb)
  constructor
  · intro h
    rw [h]; ring
  · intro h
    have h2 : σ * Real.log b = (1 / 2) * Real.log b := by rw [h]; ring
    exact mul_right_cancel₀ hlb h2

/-- **The prime clocks are mutually incommensurable** — unique factorization as spectral
non-collision: for distinct primes, `log p / log q` is irrational.  In the base-`q` system
prime `q` is the unit metronome and every other prime ticks at an irrational rate; no two
ambient lines can ever coincide. -/
theorem prime_clocks_incommensurable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Irrational (Real.log p / Real.log q) := by
  rintro ⟨r, hr⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hlq : 0 < Real.log q := Real.log_pos hq1
  have hrpos : (0 : ℝ) < (r : ℝ) := hr ▸ div_pos hlp hlq
  have hrpos' : 0 < r := by exact_mod_cast hrpos
  have hnum : 0 < r.num := Rat.num_pos.mpr hrpos'
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  -- den · log p = num · log q
  have hkey : (r.den : ℝ) * Real.log p = (r.num : ℝ) * Real.log q := by
    have hcast : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := Rat.cast_def r
    have h1 : (r.num : ℝ) / (r.den : ℝ) = Real.log p / Real.log q := by
      rw [← hcast, hr]
    field_simp at h1
    linarith
  -- p ^ den = q ^ num  in ℕ
  have hm : (r.num.toNat : ℝ) = (r.num : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hnum.le)
  have hlogeq : Real.log ((p : ℝ) ^ r.den) = Real.log ((q : ℝ) ^ r.num.toNat) := by
    rw [Real.log_pow, Real.log_pow, hm]
    exact hkey
  have hexp : ((p : ℝ)) ^ r.den = ((q : ℝ)) ^ r.num.toNat := by
    have := congrArg Real.exp hlogeq
    rwa [Real.exp_log (by positivity), Real.exp_log (by positivity)] at this
  have hnat : p ^ r.den = q ^ r.num.toNat := by exact_mod_cast hexp
  -- unique factorization: p ∣ q^m → p = q
  have hdvd : p ∣ q ^ r.num.toNat := by
    rw [← hnat]
    exact dvd_pow_self p r.den_nz
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))

end CriticalLinePhasor.UnitMidpoint
