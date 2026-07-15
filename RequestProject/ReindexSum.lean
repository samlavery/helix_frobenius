import RequestProject.ReindexEquivs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The lattice Dirichlet series factors: `ζ(2s)` times twice the coset series

Bookkeeping, second half, part two.  Pushing the Gram Dirichlet series through the two
compiled bijections: the gcd stratification turns the nonzero-lattice sum into the
`ζ(2s)`-series times the coprime series (quadratic scaling of the Gram form), and the
signed-row bijection folds the coprime series onto twice the coset series (parity of the Gram
form).  Master summability (`summable_gram_rpow`) is by comparison with the Eisenstein box
bound through the compiled trace estimate.  The result (`gram_sum_factor`):

  `∑'_{p≠0} gram(z,p)^{-s} = ζ(2s) · (2 · ∑'_q gram(z, row γ_q)^{-s})`,   `Re s > 1`

— the full lattice series of the compiled `Λ_z` against the coset series of the compiled
Rankin–Selberg equation.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta

/-- Gram values are positive away from the origin. -/
lemma gram_pos (z : ℍ) {p : ℤ × ℤ} (hp : p ≠ 0) : 0 < gram z p := by
  have hc : (0 : ℝ) < z.im / (z.re ^ 2 + z.im ^ 2 + 1) := by
    have := z.im_pos
    positivity
  exact lt_of_lt_of_le hc (gram_ge_const z hp)

/-- Coprime pairs are nonzero. -/
lemma coprimePair_ne_zero (c : CoprimePair) : c.1 ≠ 0 := by
  intro h
  have hc := c.2
  rw [h] at hc
  exact not_isCoprime_zero_zero (by simpa using hc)

/-- **Master summability** of the Gram Dirichlet series, by comparison with the Eisenstein
box bound. -/
lemma summable_gram_rpow (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : NZ => (gram z p.1) ^ (-σ) := by
  set c : ℝ := z.im / (z.re ^ 2 + z.im ^ 2 + 1) with hc
  have hcpos : 0 < c := by
    have := z.im_pos
    rw [hc]
    positivity
  have h1 : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * σ)) :=
    EisensteinSeries.summable_one_div_norm_rpow (by linarith)
  have h2 : Summable fun p : ℤ × ℤ => ‖(finTwoArrowEquiv ℤ).symm p‖ ^ (-(2 * σ)) :=
    ((finTwoArrowEquiv ℤ).symm.summable_iff
      (f := fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * σ)))).mpr h1
  have h3 : Summable fun p : NZ =>
      c ^ (-σ) * ‖(finTwoArrowEquiv ℤ).symm p.1‖ ^ (-(2 * σ)) :=
    ((h2.subtype _).mul_left _)
  refine Summable.of_nonneg_of_le (fun p => Real.rpow_nonneg (gram_pos z p.2).le _)
    (fun p => ?_) h3
  obtain ⟨⟨m, n⟩, hp⟩ := p
  set x : Fin 2 → ℤ := (finTwoArrowEquiv ℤ).symm (m, n) with hx
  have hxnz : x ≠ 0 := by
    intro h
    apply hp
    have h4 := congrArg (finTwoArrowEquiv ℤ) h
    rw [hx, Equiv.apply_symm_apply] at h4
    exact h4
  have hxpos : (0 : ℝ) < ‖x‖ := by
    rw [norm_pos_iff]
    exact hxnz
  have hx0 : x 0 = m := by
    rw [hx, finTwoArrowEquiv_symm_apply]
    rfl
  have hx1 : x 1 = n := by
    rw [hx, finTwoArrowEquiv_symm_apply]
    rfl
  have hbound : ‖x‖ ^ 2 ≤ (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
    have hnormle : ‖x‖ ≤ Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) := by
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro i
      fin_cases i
      · rw [show x ⟨0, by norm_num⟩ = x 0 from rfl, hx0, Int.norm_eq_abs]
        push_cast
        apply Real.abs_le_sqrt
        nlinarith [sq_nonneg (n : ℝ)]
      · rw [show x ⟨1, by norm_num⟩ = x 1 from rfl, hx1, Int.norm_eq_abs]
        push_cast
        apply Real.abs_le_sqrt
        nlinarith [sq_nonneg (m : ℝ)]
    calc ‖x‖ ^ 2 ≤ Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnormle 2
      _ = (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := Real.sq_sqrt (by positivity)
  have hgram : c * ‖x‖ ^ 2 ≤ gram z (m, n) := by
    have hge := gram_ge z (m, n)
    calc c * ‖x‖ ^ 2 ≤ c * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hbound hcpos.le
      _ = ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) * z.im / (z.re ^ 2 + z.im ^ 2 + 1) := by
          rw [hc]
          ring
      _ ≤ gram z (m, n) := hge
  have hcx : (0 : ℝ) < c * ‖x‖ ^ 2 := by positivity
  calc (gram z (m, n)) ^ (-σ) ≤ (c * ‖x‖ ^ 2) ^ (-σ) := by
        rw [Real.rpow_neg (gram_pos z hp).le, Real.rpow_neg hcx.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hcx σ)
          (Real.rpow_le_rpow hcx.le hgram (by linarith))
    _ = c ^ (-σ) * ‖x‖ ^ (-(2 * σ)) := by
        rw [Real.mul_rpow hcpos.le (by positivity)]
        congr 1
        rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        push_cast
        ring

/-- Master summability in complex form. -/
lemma summable_gram_cpow (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : NZ => ((gram z p.1 : ℝ) : ℂ) ^ (-s) := by
  apply Summable.of_norm
  refine (summable_gram_rpow z (σ := s.re) hs).congr fun p => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (gram_pos z p.2), Complex.neg_re]

/-- **The lattice Dirichlet series factors as `ζ(2s)` times twice the coset series.** -/
theorem gram_sum_factor (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    ∑' p : NZ, ((gram z p.1 : ℝ) : ℂ) ^ (-s) =
      riemannZeta (2 * s) *
        (2 * ∑' q : CosetQ, ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s)) := by
  have hmaster := summable_gram_cpow z hs
  -- gcd stratification
  rw [← gcdEquiv.tsum_eq (fun p : NZ => ((gram z p.1 : ℝ) : ℂ) ^ (-s))]
  have hcomp : Summable fun nc : {n : ℕ // n ≠ 0} × CoprimePair =>
      ((gram z (gcdEquiv nc).1 : ℝ) : ℂ) ^ (-s) :=
    (gcdEquiv.summable_iff (f := fun p : NZ => ((gram z p.1 : ℝ) : ℂ) ^ (-s))).mpr hmaster
  have hterm : ∀ nc : {n : ℕ // n ≠ 0} × CoprimePair,
      ((gram z (gcdEquiv nc).1 : ℝ) : ℂ) ^ (-s) =
        ((nc.1.1 : ℂ)) ^ (-(2 * s)) * ((gram z nc.2.1 : ℝ) : ℂ) ^ (-s) := by
    rintro ⟨⟨n, hn⟩, ⟨c, hc⟩⟩
    have hn1 : (1 : ℕ) ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnC : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnR.ne'
    have hcne : c ≠ 0 := coprimePair_ne_zero ⟨c, hc⟩
    show ((gram z ((n : ℤ) * c.1, (n : ℤ) * c.2) : ℝ) : ℂ) ^ (-s) = _
    rw [gram_mul_left, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (gram_pos z hcne).le]
    congr 1
    rw [Complex.ofReal_pow, pow_two,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      ← Complex.cpow_add _ _ (by exact_mod_cast hnR.ne' :
        ((((n : ℤ) : ℝ)) : ℂ) ≠ 0)]
    push_cast
    congr 1
    ring
  rw [tsum_congr hterm]
  have hcomp2 : Summable fun nc : {n : ℕ // n ≠ 0} × CoprimePair =>
      ((nc.1.1 : ℂ)) ^ (-(2 * s)) * ((gram z nc.2.1 : ℝ) : ℂ) ^ (-s) :=
    hcomp.congr hterm
  rw [hcomp2.tsum_prod' fun n => hcomp2.prod_factor n]
  simp_rw [tsum_mul_left, tsum_mul_right]
  -- the two factors
  have hzeta : ∑' n : {n : ℕ // n ≠ 0}, ((n : ℕ) : ℂ) ^ (-(2 * s)) =
      riemannZeta (2 * s) := by
    have hs2 : 1 < (2 * s).re := by
      have : (2 * s).re = 2 * s.re := by simp
      rw [this]
      linarith
    rw [zeta_eq_tsum_one_div_nat_cpow hs2]
    have hvanish : Function.support (fun x : ℕ => 1 / (x : ℂ) ^ (2 * s)) ⊆
        Set.range (Subtype.val : {n : ℕ // n ≠ 0} → ℕ) := by
      intro x hx
      by_contra hxr
      have hx0 : x = 0 := by
        by_contra hne
        exact hxr ⟨⟨x, hne⟩, rfl⟩
      subst hx0
      apply hx
      show 1 / ((0 : ℕ) : ℂ) ^ (2 * s) = 0
      rw [Nat.cast_zero, Complex.zero_cpow (by
        intro h
        have h2 : (2 * s).re = 0 := by rw [h]; simp
        rw [show (2 * s).re = 2 * s.re by simp] at h2
        linarith), div_zero]
    rw [← Function.Injective.tsum_eq Subtype.val_injective hvanish]
    refine tsum_congr fun n => ?_
    rw [Complex.cpow_neg, one_div]
  -- the coset folding
  have hcosum : Summable fun c : CoprimePair => ((gram z c.1 : ℝ) : ℂ) ^ (-s) := by
    apply Summable.of_norm
    refine ((summable_gram_rpow z (σ := s.re) hs).comp_injective
      (i := fun c : CoprimePair => (⟨c.1, coprimePair_ne_zero c⟩ : NZ)) ?_).congr fun c => ?_
    · intro a b hab
      have h5 : (a.1 : ℤ × ℤ) = b.1 := congrArg (fun w : NZ => w.1) hab
      exact Subtype.ext h5
    · rw [Function.comp_apply]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (gram_pos z (coprimePair_ne_zero c)),
        Complex.neg_re]
  have hcoset : ∑' c : CoprimePair, ((gram z c.1 : ℝ) : ℂ) ^ (-s) =
      2 * ∑' q : CosetQ, ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s) := by
    rw [← cosetRowEquiv.tsum_eq (fun c : CoprimePair => ((gram z c.1 : ℝ) : ℂ) ^ (-s))]
    have hterm2 : ∀ bq : Bool × CosetQ,
        ((gram z (cosetRowEquiv bq).1 : ℝ) : ℂ) ^ (-s) =
          ((gram z ((rep bq.2).1 1 0, (rep bq.2).1 1 1) : ℝ) : ℂ) ^ (-s) := by
      rintro ⟨b, q⟩
      rcases b
      · show ((gram z ((-1 : ℤ) * (rep q).1 1 0, (-1 : ℤ) * (rep q).1 1 1) : ℝ) : ℂ)
            ^ (-s) = _
        rw [show ((-1 : ℤ) * (rep q).1 1 0, (-1 : ℤ) * (rep q).1 1 1) =
            -(((rep q).1 1 0, (rep q).1 1 1)) by
          rw [Prod.neg_mk]
          exact Prod.ext (by ring) (by ring), gram_neg]
      · show ((gram z ((1 : ℤ) * (rep q).1 1 0, (1 : ℤ) * (rep q).1 1 1) : ℝ) : ℂ)
            ^ (-s) = _
        rw [one_mul, one_mul]
    rw [tsum_congr hterm2]
    have hsum3 : Summable fun bq : Bool × CosetQ =>
        ((gram z ((rep bq.2).1 1 0, (rep bq.2).1 1 1) : ℝ) : ℂ) ^ (-s) := by
      refine ((cosetRowEquiv.summable_iff
        (f := fun c : CoprimePair => ((gram z c.1 : ℝ) : ℂ) ^ (-s))).mpr hcosum).congr
        fun bq => ?_
      exact (hterm2 bq)
    rw [hsum3.tsum_prod' fun b => hsum3.prod_factor b, tsum_bool]
    ring
  rw [hzeta, hcoset]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.summable_gram_rpow
#print axioms CriticalLinePhasor.Unfolding.gram_sum_factor
