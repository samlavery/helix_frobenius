import Mathlib
import RequestProject.MomentLaw

/-!
# The Sato–Tate/Catalan moment identity — the measure-theoretic half of the moment law

`MomentLaw.lean` proves the tensor-tower channel second moment on its exact rational closed form
as a **finite combinatorial fact**, taking the three single-clock Sato–Tate scalar moments
`m 0 = 1`, `m (±2) = −1/2` (and `else 0`) as *scalar hypotheses* — the measure theory that makes
those the true moments of an `SU(2)`-equidistributed angle is cited there, not formalised.  This
file supplies that missing half: it computes the moments of the **Sato–Tate measure**
`dST = (2/π)·sin²θ dθ` on `[0, π]` directly and proves they are exactly those scalars, so the two
files compose.

The **single-clock trace** is `2 cos θ`.  Under `dST` its even moments are the Catalan numbers and
its odd moments vanish; the Fourier picture is that the measure kills every harmonic `cos(2kθ)` for
`k ≥ 2`, leaves `cos 2θ` with weight `−1/2`, and has total mass `1`.

* `integral_cos_pow_even`, `integral_cos_pow_odd_zero` — the pure cosine-power integrals over
  `[0, π]`: `∫ cos^{2m} = π·C(2m,m)/4ᵐ` (central binomial) and `∫ cos^{odd} = 0`.  Both are proved
  by the Mathlib reduction formula `integral_cos_pow` (the boundary term vanishes since `sin` does
  at `0` and `π`), with the central-binomial recursion `Nat.succ_mul_centralBinom_succ` closing the
  even case.
* `stMoment_even` — **the headline**: `(2/π)·∫₀^π (2cos θ)^{2m}·sin²θ dθ = C(2m,m)/(m+1)`, the
  `m`-th Catalan number.  The odd moments vanish (`stMoment_odd`).
* `integral_cos_int_mul` — the atomic harmonic integral `∫₀^π cos(kθ) dθ = π·[k = 0]` for `k : ℤ`.
* `stFourierMoment` — **the composition glue**: `(2/π)·∫₀^π cos(dθ)·sin²θ dθ = MomentLaw.stMoment d`
  for every integer harmonic `d`, certifying MomentLaw's scalar inputs as the genuine `dST` moments.
  Named specialisations `stFourierMoment_zero/two/neg_two` are its `d = 0, 2, −2` cases.
* `channelMoment_theorem` — MomentLaw's `stChannelMoment_closedForm` re-exported: the atlas channel
  rationals now stand as a theorem of the Sato–Tate **measure**, its moment hypotheses discharged
  by `stFourierMoment`.

**Scope.**  This is the measure-theoretic content: the moments of the one-dimensional Sato–Tate law
`dST`.  That `2 cos θ` is genuinely `dST`-distributed for the constituent curves (Sato–Tate) and
that distinct legs are jointly independent (distinct conductors) are the equidistribution theorems'
territory — cited in the atlas, neither assumed nor proven here.  Nothing here assumes or proves
RH/GRH.  No `axiom`, no `sorry`.
-/

open scoped Real
open MeasureTheory

namespace CatalanMoment

/-! ### The pure cosine-power integrals over `[0, π]` -/

/-- `∫₀^π cos^{2m} θ dθ = π · C(2m, m) / 4ᵐ`.  Proved from the Mathlib reduction formula
`integral_cos_pow`, whose boundary term vanishes at `0` and `π` (where `sin = 0`); the induction step
is exactly the central-binomial recursion `Nat.succ_mul_centralBinom_succ`. -/
theorem integral_cos_pow_even (m : ℕ) :
    ∫ x in (0:ℝ)..π, Real.cos x ^ (2 * m) = π * (Nat.centralBinom m : ℝ) / 4 ^ m := by
  induction m with
  | zero => simp [Nat.centralBinom_zero]
  | succ k ih =>
    have hrec := integral_cos_pow (a := (0:ℝ)) (b := π) (n := 2 * k)
    rw [Real.sin_pi, Real.sin_zero] at hrec
    simp only [mul_zero, sub_zero, zero_div, zero_add] at hrec
    have hstep : (∫ x in (0:ℝ)..π, Real.cos x ^ (2 * (k + 1)))
        = ((2 * (k:ℝ) + 1) / (2 * k + 2)) * ∫ x in (0:ℝ)..π, Real.cos x ^ (2 * k) := by
      rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
      push_cast at hrec ⊢
      linarith [hrec]
    rw [hstep, ih]
    have hkey : ((k:ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ)
        = 2 * (2 * (k:ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    have hpi : (π:ℝ) ≠ 0 := Real.pi_ne_zero
    have h4 : (4:ℝ) ^ k ≠ 0 := by positivity
    have h2k2 : (2 * (k:ℝ) + 2) ≠ 0 := by positivity
    rw [pow_succ]
    field_simp
    linear_combination (-2 : ℝ) * hkey

/-- `∫₀^π cos^{2m+1} θ dθ = 0`: odd cosine powers integrate to zero over `[0, π]` by the reduction
formula (base case `∫ cos = sin π − sin 0 = 0`). -/
theorem integral_cos_pow_odd_zero (m : ℕ) :
    ∫ x in (0:ℝ)..π, Real.cos x ^ (2 * m + 1) = 0 := by
  induction m with
  | zero => simp [integral_cos]
  | succ k ih =>
    have hrec := integral_cos_pow (a := (0:ℝ)) (b := π) (n := 2 * k + 1)
    rw [Real.sin_pi, Real.sin_zero] at hrec
    simp only [mul_zero, sub_zero, zero_div, zero_add] at hrec
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring, hrec, ih, mul_zero]

/-! ### The Sato–Tate polynomial moments: Catalan and vanishing -/

/-- **The even Sato–Tate moment is the Catalan number**:
`(2/π)·∫₀^π (2 cos θ)^{2m}·sin²θ dθ = C(2m, m)/(m+1) = Cₘ`.  The integrand is
`4ᵐ·(cos^{2m} − cos^{2m+2})`, so the value is `2·C(2m,m) − ½·C(2m+2,m+1)`, which the central-binomial
recursion collapses to the Catalan number. -/
theorem stMoment_even (m : ℕ) :
    (2 / π) * ∫ θ in (0:ℝ)..π, (2 * Real.cos θ) ^ (2 * m) * (Real.sin θ) ^ 2
      = (Nat.centralBinom m : ℝ) / (m + 1) := by
  have hpt : ∀ θ : ℝ, (2 * Real.cos θ) ^ (2 * m) * (Real.sin θ) ^ 2
      = 4 ^ m * (Real.cos θ ^ (2 * m) - Real.cos θ ^ (2 * (m + 1))) := by
    intro θ
    have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ; linarith
    have hpow : Real.cos θ ^ (2 * (m + 1)) = Real.cos θ ^ (2 * m) * Real.cos θ ^ 2 := by
      rw [show 2 * (m + 1) = 2 * m + 2 from by ring, pow_add]
    have h4 : (2:ℝ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
    rw [mul_pow, h4, hs, hpow]; ring
  have hI : (∫ θ in (0:ℝ)..π, (2 * Real.cos θ) ^ (2 * m) * (Real.sin θ) ^ 2)
      = 4 ^ m * ((∫ θ in (0:ℝ)..π, Real.cos θ ^ (2 * m))
                  - ∫ θ in (0:ℝ)..π, Real.cos θ ^ (2 * (m + 1))) := by
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [hI, integral_cos_pow_even m, integral_cos_pow_even (m + 1)]
  have hkey : ((m:ℝ) + 1) * (Nat.centralBinom (m + 1) : ℝ)
      = 2 * (2 * (m:ℝ) + 1) * (Nat.centralBinom m : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ m
  have hpi : (π:ℝ) ≠ 0 := Real.pi_ne_zero
  have h4 : (4:ℝ) ^ m ≠ 0 := by positivity
  have hm1 : ((m:ℝ) + 1) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp
  linear_combination (-2 : ℝ) * hkey

/-- **The odd Sato–Tate moments vanish**: `(2/π)·∫₀^π (2 cos θ)^{2m+1}·sin²θ dθ = 0`.  The integrand
is `2^{2m+1}·(cos^{2m+1} − cos^{2m+3})`, a difference of odd cosine powers, each with zero integral. -/
theorem stMoment_odd (m : ℕ) :
    (2 / π) * ∫ θ in (0:ℝ)..π, (2 * Real.cos θ) ^ (2 * m + 1) * (Real.sin θ) ^ 2 = 0 := by
  have hpt : ∀ θ : ℝ, (2 * Real.cos θ) ^ (2 * m + 1) * (Real.sin θ) ^ 2
      = 2 ^ (2 * m + 1) * (Real.cos θ ^ (2 * m + 1) - Real.cos θ ^ (2 * (m + 1) + 1)) := by
    intro θ
    have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ; linarith
    have hpow : Real.cos θ ^ (2 * (m + 1) + 1) = Real.cos θ ^ (2 * m + 1) * Real.cos θ ^ 2 := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 from by ring, pow_add]
    rw [mul_pow, hs, hpow]; ring
  have hI : (∫ θ in (0:ℝ)..π, (2 * Real.cos θ) ^ (2 * m + 1) * (Real.sin θ) ^ 2)
      = 2 ^ (2 * m + 1) * ((∫ θ in (0:ℝ)..π, Real.cos θ ^ (2 * m + 1))
                  - ∫ θ in (0:ℝ)..π, Real.cos θ ^ (2 * (m + 1) + 1)) := by
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [hI, integral_cos_pow_odd_zero m, integral_cos_pow_odd_zero (m + 1)]
  simp

/-! ### The Fourier coefficients of the Sato–Tate measure -/

/-- The **atomic harmonic integral**: `∫₀^π cos(kθ) dθ = π` if `k = 0` and `0` otherwise, for any
integer `k` (since `sin(kπ) = 0`).  This is the only genuine antiderivative computation the whole
Fourier picture rests on. -/
theorem integral_cos_int_mul (k : ℤ) :
    ∫ θ in (0:ℝ)..π, Real.cos ((k:ℝ) * θ) = if k = 0 then π else 0 := by
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk]
    have hkr : (k:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have h := intervalIntegral.mul_integral_comp_mul_left (a := (0:ℝ)) (b := π)
      (f := Real.cos) (k:ℝ)
    rw [mul_zero, integral_cos, Real.sin_int_mul_pi, Real.sin_zero, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hkr

/-- Product-to-sum for the Sato–Tate integrand: `cos(dθ)·sin²θ = ½cos(dθ) − ¼cos((d+2)θ) −
¼cos((d−2)θ)`.  Turns the harmonic moment into a combination of the atomic integrals. -/
theorem cos_mul_sin_sq_expand (d : ℤ) (θ : ℝ) :
    Real.cos ((d:ℝ) * θ) * (Real.sin θ) ^ 2
      = (1/2) * Real.cos ((d:ℝ) * θ)
        - (1/4) * Real.cos (((d + 2 : ℤ):ℝ) * θ)
        - (1/4) * Real.cos (((d - 2 : ℤ):ℝ) * θ) := by
  have e1 : ((d + 2 : ℤ):ℝ) * θ = (d:ℝ) * θ + 2 * θ := by push_cast; ring
  have e2 : ((d - 2 : ℤ):ℝ) * θ = (d:ℝ) * θ - 2 * θ := by push_cast; ring
  have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ; linarith
  rw [e1, e2, Real.cos_add, Real.cos_sub, Real.cos_two_mul, Real.sin_two_mul, hs]; ring

/-- **The Fourier–moment identity (the composition glue)**: for every integer harmonic `d`, the
Sato–Tate measure's `d`-th Fourier moment `(2/π)·∫₀^π cos(dθ)·sin²θ dθ` equals `MomentLaw.stMoment d`
— `1` at `d = 0`, `−1/2` at `d = ±2`, and `0` at every other harmonic.  This certifies MomentLaw's
scalar moment hypotheses as the genuine moments of `dST`. -/
theorem stFourierMoment (d : ℤ) :
    (2 / π) * ∫ θ in (0:ℝ)..π, Real.cos ((d:ℝ) * θ) * (Real.sin θ) ^ 2
      = ((MomentLaw.stMoment d : ℚ) : ℝ) := by
  have hint : (∫ θ in (0:ℝ)..π, Real.cos ((d:ℝ) * θ) * (Real.sin θ) ^ 2)
      = (1/2) * (∫ θ in (0:ℝ)..π, Real.cos ((d:ℝ) * θ))
        - (1/4) * (∫ θ in (0:ℝ)..π, Real.cos (((d + 2 : ℤ):ℝ) * θ))
        - (1/4) * (∫ θ in (0:ℝ)..π, Real.cos (((d - 2 : ℤ):ℝ) * θ)) := by
    rw [intervalIntegral.integral_congr (fun θ _ => cos_mul_sin_sq_expand d θ)]
    rw [intervalIntegral.integral_sub
          ((Continuous.intervalIntegrable (by fun_prop) _ _).sub
            (Continuous.intervalIntegrable (by fun_prop) _ _))
          (Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
  rw [hint, integral_cos_int_mul d, integral_cos_int_mul (d + 2), integral_cos_int_mul (d - 2)]
  have hpi : (π:ℝ) ≠ 0 := Real.pi_ne_zero
  by_cases h0 : d = 0
  · subst h0; norm_num [MomentLaw.stMoment]; field_simp
  · by_cases h2 : d = 2
    · subst h2
      rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
      rw [MomentLaw.stMoment_two]; push_cast; field_simp; ring
    · by_cases h2' : d = -2
      · subst h2'
        rw [if_neg (by decide), if_pos (by decide), if_neg (by decide)]
        rw [MomentLaw.stMoment_neg_two]; push_cast; field_simp; ring
      · rw [if_neg h0, if_neg (by omega : d + 2 ≠ 0), if_neg (by omega : d - 2 ≠ 0)]
        rw [MomentLaw.stMoment_other h0 h2 h2']; push_cast; ring

/-- `dST`-mass one: the `d = 0` Fourier moment. -/
theorem stFourierMoment_zero :
    (2 / π) * ∫ θ in (0:ℝ)..π, (Real.sin θ) ^ 2 = 1 := by
  have h := stFourierMoment 0
  simp only [Int.cast_zero, zero_mul, Real.cos_zero, one_mul, MomentLaw.stMoment_zero,
    Rat.cast_one] at h
  exact h

/-- The `cos 2θ` weight: the `d = 2` Fourier moment is `−1/2`. -/
theorem stFourierMoment_two :
    (2 / π) * ∫ θ in (0:ℝ)..π, Real.cos (2 * θ) * (Real.sin θ) ^ 2 = -(1/2) := by
  have h := stFourierMoment 2
  norm_num [MomentLaw.stMoment] at h
  simpa using h

/-- The `cos 2θ` weight from the other side: the `d = −2` Fourier moment is `−1/2`. -/
theorem stFourierMoment_neg_two :
    (2 / π) * ∫ θ in (0:ℝ)..π, Real.cos (-2 * θ) * (Real.sin θ) ^ 2 = -(1/2) := by
  have h := stFourierMoment (-2)
  norm_num [MomentLaw.stMoment] at h
  simpa using h

/-! ### Composition with the combinatorial moment law -/

variable {g : ℕ}

/-- **The channel-moment law as a theorem of the Sato–Tate measure.**  MomentLaw's
`stChannelMoment_closedForm` states the tensor-tower channel second moment on the atlas' rational
closed form using the scalar single-clock moments `m 0 = 1`, `m (±2) = −1/2` as inputs.  Those inputs
are now discharged by `stFourierMoment` (they are the genuine `dST` Fourier moments), so the closed
form stands as a theorem about the moments of the one-dimensional Sato–Tate law.  Joint independence
across distinct legs remains the cited equidistribution input (scope line in the header). -/
theorem channelMoment_theorem (μ : ℕ) :
    MomentLaw.channelMoment (g := g) MomentLaw.stMoment ((g : ℤ) - 2 * μ)
      = (g.choose μ : ℚ) *
        ∑ i ∈ Finset.range (μ + 1),
          (μ.choose i : ℚ) * ((g - μ).choose i : ℚ) * (1 / 4) ^ i :=
  MomentLaw.stChannelMoment_closedForm μ

end CatalanMoment

-- Sato–Tate moment sanity: `C₀ = 1, C₁ = 1, C₂ = 2, C₃ = 5, C₄ = 14` are the central-binomial
-- ratios `C(2m,m)/(m+1)`, and the odd moments vanish.
#eval (List.range 5).map (fun m => Nat.centralBinom m / (m + 1))     -- [1, 1, 2, 5, 14]

#print axioms CatalanMoment.stMoment_even
#print axioms CatalanMoment.stMoment_odd
#print axioms CatalanMoment.stFourierMoment
#print axioms CatalanMoment.channelMoment_theorem
