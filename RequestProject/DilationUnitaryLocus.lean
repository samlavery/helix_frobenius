import Mathlib

/-!
# The critical line is the unitary locus of the weight-½ involution

The dilation ring of the carrier (RH_LEDGER 722k; *Feynman's Quiver*, `HelixLogFreeFTA.lean`) carries the
involution `T_q^† = q⁻¹ T_{1/q}`.  A character `χ_s(T_q) = q^{-s}` respects it — i.e. is a `*`-character,
`χ(a^†) = conj (χ a)` — exactly when `Re s = ½`.

Written out on the generators: `χ_s(T_q^†) = q⁻¹ · χ_s(T_{1/q}) = q^{s-1}` and `conj (χ_s(T_q)) = q^{-\bar s}`,
so the condition is `q^{s-1} = q^{-\bar s}` for every `q > 0`.  In the additive variable `u = log q` that is
`exp((s-1)u) = conj (exp(-s u))` for every real `u`, and this file proves it holds **iff** `Re s = ½`.

The content is the forward direction, and it is one line of norms: `‖exp((s-1)u)‖ = exp((Re s - 1) u)` while
`‖conj (exp(-s u))‖ = exp(-(Re s) u)`, so equality at `u = 1` forces `Re s - 1 = -Re s`.  The converse is the
identity `s - 1 = -conj s` on the line.  No analysis beyond `Complex.exp`.
-/

open Complex

namespace CriticalLinePhasor.DilationUnitaryLocus

/-- The `*`-character condition on the generators, in the additive variable `u = log q`. -/
def IsStarCharacter (s : ℂ) : Prop :=
  ∀ u : ℝ, Complex.exp ((s - 1) * u) = (starRingEnd ℂ) (Complex.exp (-s * u))

/-- `conj (exp (-s u)) = exp (-conj s * u)` for real `u`. -/
theorem conj_exp_neg_mul (s : ℂ) (u : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-s * u)) = Complex.exp (-((starRingEnd ℂ) s) * u) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.ext_iff]

/-- **The unitary locus.**  A character of the dilation ring respects the weight-½ involution
exactly on the critical line. -/
theorem isStarCharacter_iff_re_eq_half (s : ℂ) : IsStarCharacter s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have h1 := h 1
    have e1 : ‖Complex.exp ((s - 1) * (1:ℝ))‖ = Real.exp ((s-1).re) := by
      simp [Complex.norm_exp]
    have e2 : ‖Complex.exp (-((starRingEnd ℂ) s) * (1:ℝ))‖ = Real.exp ((-((starRingEnd ℂ) s)).re) := by
      simp [Complex.norm_exp]
    have hnorm : ‖Complex.exp ((s - 1) * (1:ℝ))‖ = ‖Complex.exp (-((starRingEnd ℂ) s) * (1:ℝ))‖ := by
      rw [← conj_exp_neg_mul, ← h1]
    rw [e1, e2] at hnorm
    have : (s - 1).re = (-((starRingEnd ℂ) s)).re := Real.exp_injective hnorm
    simp [Complex.sub_re, Complex.neg_re, Complex.conj_re] at this
    linarith
  · intro h u
    rw [conj_exp_neg_mul]
    congr 1
    have : s - 1 = -((starRingEnd ℂ) s) := by
      apply Complex.ext
      · simp [Complex.sub_re, Complex.neg_re, Complex.conj_re, h]; linarith
      · simp [Complex.sub_im, Complex.neg_im, Complex.conj_im]
    rw [this]

end CriticalLinePhasor.DilationUnitaryLocus

#print axioms CriticalLinePhasor.DilationUnitaryLocus.isStarCharacter_iff_re_eq_half
