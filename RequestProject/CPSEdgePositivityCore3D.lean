import Mathlib

/-!
# The edge-positivity core: 3–4–1 at the tempered Satake level

The finite heart of the de la Vallée Poussin edge-nonvanishing argument, at
exactly the level the CPS tower supplies it.  Temperedness (compiled from the
tower ceiling by the bounded-powers argument) puts every Satake root on the
unit circle; there the classical inequality `3 + 4cos x + cos 2x = 2(1+cos x)²`
needs no trigonometry at all — for a unit complex number `u` one has
`(u²).re = 2·u.re² − 1` by pure algebra, so the inequality is a square.

`satake_three_four_one` is the per-prime-power positivity: for any finite
family of unit roots (the `Sym^r` Satake bank at a prime) and any unit twist
phase (`n^{-it₀}` at a hypothetical boundary zero `1 + it₀`), the ζ-side
constant, the twisted power sum, and the doubled twisted power sum combine
nonnegatively.  Summed against `Λ`-weights over prime powers this is the
statement `Re log(ζ(σ)³·L(σ+it₀)⁴·L₂(σ+2it₀)) ≥ 0` that forces the
order-counting contradiction at a boundary zero.  No `axiom`, no `sorry`.
-/

namespace CriticalLinePhasor.ThreeDConverse

/-- The scalar 3–4–1 inequality: `3 + 4cos x + cos 2x = 2(1 + cos x)² ≥ 0`. -/
theorem three_four_one (x : ℝ) :
    0 ≤ 3 + 4 * Real.cos x + Real.cos (2 * x) := by
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (1 + Real.cos x)]

/-- For a unit complex number, the real part of the square is determined by
the real part alone: `(u²).re = 2·u.re² − 1` — the angle-doubling law with no
trigonometry. -/
theorem sq_re_of_norm_one {u : ℂ} (hu : ‖u‖ = 1) :
    (u ^ 2).re = 2 * u.re ^ 2 - 1 := by
  have h1 : Complex.normSq u = 1 := by
    have h2 : ‖u‖ ^ 2 = 1 := by rw [hu]; norm_num
    rwa [← Complex.normSq_eq_norm_sq] at h2
  have h3 : u.re * u.re + u.im * u.im = 1 := by
    rwa [Complex.normSq_apply] at h1
  rw [pow_two, Complex.mul_re]
  nlinarith

/-- The unit-circle 3–4–1 inequality: for `‖u‖ = 1`,
`3 + 4·u.re + (u²).re = 2(1 + u.re)² ≥ 0`. -/
theorem three_four_one_of_norm_one {u : ℂ} (hu : ‖u‖ = 1) :
    0 ≤ 3 + 4 * u.re + (u ^ 2).re := by
  rw [sq_re_of_norm_one hu]
  nlinarith [sq_nonneg (1 + u.re)]

/-- **Per-prime-power 3–4–1 positivity for a tempered Satake bank.**  For any
finite family of unit roots and any unit twist phase, the ζ-side constant
(one per root), the twisted power sum, and the doubled twisted power sum
combine nonnegatively.  This is the coefficient-level positivity consumed by
the edge-nonvanishing (de la Vallée Poussin) argument at every symmetric-power
rank. -/
theorem satake_three_four_one {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (hw : ∀ i, ‖w i‖ = 1) (z : ℂ) (hz : ‖z‖ = 1) :
    0 ≤ 3 * (Fintype.card ι : ℝ) + 4 * (z * ∑ i, w i).re
      + (z ^ 2 * ∑ i, w i ^ 2).re := by
  have hterm : ∀ i : ι, 0 ≤ 3 + 4 * (z * w i).re + ((z * w i) ^ 2).re := by
    intro i
    have huv : ‖z * w i‖ = 1 := by rw [norm_mul, hz, hw i, one_mul]
    exact three_four_one_of_norm_one huv
  have hsum : (0 : ℝ) ≤ ∑ i, (3 + 4 * (z * w i).re + ((z * w i) ^ 2).re) :=
    Finset.sum_nonneg fun i _ => hterm i
  have hre1 : (z * ∑ i, w i).re = ∑ i, (z * w i).re := by
    rw [Finset.mul_sum, Complex.re_sum]
  have hre2 : (z ^ 2 * ∑ i, w i ^ 2).re = ∑ i, ((z * w i) ^ 2).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    congr 1
    funext i
    congr 1
    ring
  rw [hre1, hre2]
  calc (0 : ℝ)
      ≤ ∑ i, (3 + 4 * (z * w i).re + ((z * w i) ^ 2).re) := hsum
    _ = 3 * (Fintype.card ι : ℝ) + 4 * ∑ i, (z * w i).re
        + ∑ i, ((z * w i) ^ 2).re := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, ← Finset.mul_sum]
        push_cast
        ring

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.three_four_one
#print axioms CriticalLinePhasor.ThreeDConverse.sq_re_of_norm_one
#print axioms CriticalLinePhasor.ThreeDConverse.three_four_one_of_norm_one
#print axioms CriticalLinePhasor.ThreeDConverse.satake_three_four_one
