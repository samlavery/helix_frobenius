import RequestProject.PrimeSymbolClock

/-!
# The actual two-degree jet block

Unfolded target: for moments z0,z1, the (1,2) block of the compiled pairing has
determinant ((2 Re z0)^2-d^2 |z1|^2)/d^4. With d>0 and Re z0>=0 its nonnegative
determinant is equivalent to |z1|<=2 Re z0/d. This computes the full jet block,
not an individual prime's symbol.

Expectation-free route A: `norm_num [pairFunctional, pf_succ]` computes the
four actual entries. Route B: `rw [Matrix.det_fin_two]` computes the determinant
before taking its real part. The scalar inequality is then checked separately.

Searches: `rg -n -i 'degree_?two|degree2|minor.?12|det.*S_?2|anchor.*square|square.*anchor|monomial.*(form|symbol)|symbol.*monomial' RequestProject --glob '*.lean'`;
`rg -n 'posSemidef.*iff|posSemidef.*two|posSemidef.*det|det_fin_two|normSq.*norm'
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean`.
LeanSearch: determinant of a two by two Hermitian complex matrix.
Loogle: `Complex.normSq, _ ^ 2`.
-/

open Complex Matrix

namespace CriticalLinePhasor.ContourArgument.SeatDegreeTwo

open PrimeClock

noncomputable def block (d : ℝ) (z : ℕ → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => pairFunctional (d : ℂ) 6 (i.val + 1) (j.val + 1) z

theorem block_primeMoment_eq (d : ℝ) (s : ℂ) (i j : Fin 2) :
    block d (primeMoment s) i j = jetValueP s (d : ℂ) 6 (i.val + 1) (j.val + 1) :=
  pairFunctional_primeMoment s (d : ℂ) 6 (i.val + 1) (j.val + 1)

theorem entries (d : ℝ) (hd : d ≠ 0) (z : ℕ → ℂ) :
    block d z 0 0 = (z 0 + (starRingEnd ℂ) (z 0)) / (d : ℂ) ∧
    block d z 0 1 = (starRingEnd ℂ) (z 1) / (d : ℂ) +
      (z 0 + (starRingEnd ℂ) (z 0)) / (d : ℂ) ^ 2 ∧
    block d z 1 0 = z 1 / (d : ℂ) + (z 0 + (starRingEnd ℂ) (z 0)) / (d : ℂ) ^ 2 ∧
    block d z 1 1 = (z 1 + (starRingEnd ℂ) (z 1)) / (d : ℂ) ^ 2 +
      2 * (z 0 + (starRingEnd ℂ) (z 0)) / (d : ℂ) ^ 3 := by
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  norm_num [block, pairFunctional, pf_succ, pf_zero_right, pf_zero_left,
    Finset.sum_range_succ]
  constructor
  · field_simp
  constructor
  · field_simp; ring
  constructor <;> field_simp <;> ring

theorem det_re (d : ℝ) (hd : d ≠ 0) (z : ℕ → ℂ) :
    (block d z).det.re = ((2 * (z 0).re) ^ 2 - d ^ 2 * Complex.normSq (z 1)) / d ^ 4 := by
  obtain ⟨h00, h01, h10, h11⟩ := entries d hd z
  rw [Matrix.det_fin_two, h00, h01, h10, h11]
  simp only [← Complex.ofReal_pow, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re,
    Complex.conj_im, Complex.mul_im, Complex.normSq_apply]
  norm_num
  field_simp
  ring

theorem det_nonneg_iff (d : ℝ) (hd : 0 < d) (z : ℕ → ℂ) (hz : 0 ≤ (z 0).re) :
    0 ≤ (block d z).det.re ↔ ‖z 1‖ ≤ 2 * (z 0).re / d := by
  rw [det_re d hd.ne' z, Complex.normSq_eq_norm_sq,
    le_div_iff₀ (pow_pos hd 4), zero_mul, le_div_iff₀ hd]
  have hx : 0 ≤ ‖z 1‖ * d := mul_nonneg (norm_nonneg _) hd.le
  have hy : 0 ≤ 2 * (z 0).re := by positivity
  constructor
  · intro h
    have hsq : (‖z 1‖ * d) ^ 2 ≤ (2 * (z 0).re) ^ 2 := by nlinarith
    nlinarith
  · intro h
    have hsq : (‖z 1‖ * d) ^ 2 ≤ (2 * (z 0).re) ^ 2 := pow_le_pow_left₀ hx h 2
    nlinarith

theorem prime_det_re (d : ℝ) (hd : d ≠ 0) (s : ℂ) :
    (block d (primeMoment s)).det.re =
      ((2 * (primeLogDeriv s).re) ^ 2 - d ^ 2 * Complex.normSq (primeJet s 1)) / d ^ 4 := by
  simpa [primeMoment] using det_re d hd (primeMoment s)

theorem prime_det_nonneg_iff (d : ℝ) (hd : 0 < d) (s : ℂ)
    (hz : 0 ≤ (primeLogDeriv s).re) :
    0 ≤ (block d (primeMoment s)).det.re ↔
      ‖primeJet s 1‖ ≤ 2 * (primeLogDeriv s).re / d := by
  simpa [primeMoment] using det_nonneg_iff d hd (primeMoment s) hz

end CriticalLinePhasor.ContourArgument.SeatDegreeTwo

#print axioms CriticalLinePhasor.ContourArgument.SeatDegreeTwo.entries
#print axioms CriticalLinePhasor.ContourArgument.SeatDegreeTwo.block_primeMoment_eq
#print axioms CriticalLinePhasor.ContourArgument.SeatDegreeTwo.det_re
#print axioms CriticalLinePhasor.ContourArgument.SeatDegreeTwo.det_nonneg_iff
#print axioms CriticalLinePhasor.ContourArgument.SeatDegreeTwo.prime_det_re
#print axioms CriticalLinePhasor.ContourArgument.SeatDegreeTwo.prime_det_nonneg_iff
