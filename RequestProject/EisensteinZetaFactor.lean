import RequestProject.EisensteinConvergence

/-!
# The `ζ(2s)` factor at the Eisenstein summand

Instantiation of `tsum_nonzero_eq_zeta_factor` at the real-analytic Eisenstein summand

  `E(z,s;c,d) = y^s · ‖cz+d‖^{-2s}`,

whose value at a bottom row `(c,d)` is exactly `Im(γ·z)^s`.

Writing the summand with the *modulus* `‖cz+d‖` rather than `cz+d` itself is what makes the
homogeneity a one-line application: the base is a nonnegative real, so `Complex.mul_cpow_ofReal_nonneg`
splits the scaling with no branch bookkeeping.  This is the same discipline as everywhere in this
campaign — put the object on its own scale and the identity is exact rather than estimated.

Result: `tsum_nonzero_eisRealSummand`, the Epstein lattice sum over *all* nonzero pairs equals
`(∑_{k>0} k^{-2s})` times the sum over primitive pairs — `ζ(2s)` times the Eisenstein sum.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open EisensteinSeries UpperHalfPlane Complex

namespace CriticalLinePhasor.Unfolding

/-- The real-analytic Eisenstein summand, written on the modulus. -/
noncomputable def eisRealSummand (z : ℍ) (s : ℂ) (p : ℤ × ℤ) : ℂ :=
  ((z.im : ℝ) : ℂ) ^ s * ((‖(p.1 : ℂ) * (z : ℂ) + (p.2 : ℂ)‖ : ℝ) : ℂ) ^ (-(2 * s))

/-- **The summand is homogeneous of degree `-2s`.**  One application of
`mul_cpow_ofReal_nonneg`, because the base is a nonnegative real. -/
lemma eisRealSummand_homog (z : ℍ) (s : ℂ) (k c d : ℤ) (hk : 0 < k) :
    eisRealSummand z s (k * c, k * d) = (k : ℂ) ^ (-(2 * s)) * eisRealSummand z s (c, d) := by
  have hk0 : (0:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.le
  have hnorm : ‖((k * c : ℤ) : ℂ) * (z : ℂ) + ((k * d : ℤ) : ℂ)‖ =
      (k : ℝ) * ‖(c : ℂ) * (z : ℂ) + (d : ℂ)‖ := by
    have : ((k * c : ℤ) : ℂ) * (z : ℂ) + ((k * d : ℤ) : ℂ) =
        (k : ℂ) * ((c : ℂ) * (z : ℂ) + (d : ℂ)) := by push_cast; ring
    rw [this, norm_mul, Complex.norm_intCast,
      abs_of_pos (by exact_mod_cast hk : (0:ℝ) < (k : ℝ))]
  unfold eisRealSummand
  simp only
  rw [hnorm, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hk0 (norm_nonneg _)]
  norm_cast
  ring

/-- The norm of the summand is the majorant `summable_eisenstein_real` controls. -/
lemma norm_eisRealSummand (z : ℍ) (s : ℂ) (p : ℤ × ℤ)
    (hp : 0 < ‖(p.1 : ℂ) * (z : ℂ) + (p.2 : ℂ)‖) :
    ‖eisRealSummand z s p‖ =
      z.im ^ s.re * ‖(p.1 : ℂ) * (z : ℂ) + (p.2 : ℂ)‖ ^ (-(2 * s.re)) := by
  unfold eisRealSummand
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos hp]
  congr 2
  simp

/-- For a nonzero integer pair and `z` off the real axis, `cz+d` does not vanish. -/
lemma norm_pos_of_ne_zero (z : ℍ) {p : ℤ × ℤ} (hp : ¬(p.1 = 0 ∧ p.2 = 0)) :
    0 < ‖(p.1 : ℂ) * (z : ℂ) + (p.2 : ℂ)‖ := by
  rw [norm_pos_iff]
  intro hzero
  by_cases hc : p.1 = 0
  · rw [hc] at hzero
    simp only [Int.cast_zero, zero_mul, zero_add] at hzero
    exact hp ⟨hc, by exact_mod_cast hzero⟩
  · have him : ((p.1 : ℂ) * (z : ℂ) + (p.2 : ℂ)).im = (p.1 : ℝ) * (z : ℂ).im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
        zero_mul, add_zero, zero_add]
    rw [hzero] at him
    have : (p.1 : ℝ) * (z : ℂ).im = 0 := him.symm
    rcases mul_eq_zero.mp this with h | h
    · exact hc (by exact_mod_cast h)
    · exact absurd h z.im_pos.ne'

/-- **The direction side is summable at the Eisenstein summand**, for `Re s > 1`. -/
lemma summable_norm_eisRealSummand_coprime (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun q : {q : ℤ × ℤ // IsCoprime q.1 q.2} => ‖eisRealSummand z s q.1‖ := by
  have h2 : Summable fun p : ℤ × ℤ =>
      z.im ^ s.re * ‖(p.1 : ℂ) * (z : ℂ) + (p.2 : ℂ)‖ ^ (-(2 * s.re)) := by
    rw [← (finTwoArrowEquiv ℤ).summable_iff]
    exact summable_eisenstein_real z hs
  refine (h2.subtype _).congr fun q => ?_
  refine (norm_eisRealSummand z s q.1 (norm_pos_of_ne_zero z ?_)).symm
  rintro ⟨h0, h1⟩
  have := q.2
  rw [h0, h1] at this
  exact not_isCoprime_zero_zero this

/-- **The `ζ(2s)` factor at the Eisenstein summand.**  The Epstein lattice sum over all nonzero
pairs is `(∑_{k>0} k^{-2s})` times the sum over primitive pairs — item (1) of the Eisenstein
continuation, assembled. -/
theorem tsum_nonzero_eisRealSummand (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    ∑' p : {p : ℤ × ℤ // ¬(p.1 = 0 ∧ p.2 = 0)}, eisRealSummand z s p.1 =
      (∑' k : {k : ℤ // 0 < k}, (k.1 : ℂ) ^ (-(2 * s))) *
        (∑' q : {q : ℤ × ℤ // IsCoprime q.1 q.2}, eisRealSummand z s q.1) := by
  refine tsum_nonzero_eq_zeta_factor (w := 2 * s)
    (fun k c d hk => eisRealSummand_homog z s k c d hk) ?_
    (summable_norm_eisRealSummand_coprime z hs)
  refine summable_pos_int_cpow ?_
  have : (2 * s).re = 2 * s.re := by simp
  rw [this]; linarith

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.norm_pos_of_ne_zero
#print axioms CriticalLinePhasor.Unfolding.summable_norm_eisRealSummand_coprime
#print axioms CriticalLinePhasor.Unfolding.tsum_nonzero_eisRealSummand
#print axioms CriticalLinePhasor.Unfolding.eisRealSummand_homog
#print axioms CriticalLinePhasor.Unfolding.norm_eisRealSummand
