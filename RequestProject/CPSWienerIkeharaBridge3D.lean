import RequestProject.Vendored.Wiener
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# A kernel-clean Wiener--Ikehara bridge for CPS prime coefficients

The imported theorem is the machine-checked Wiener--Ikehara implementation at the same Lean/mathlib
release as this project.  This file records the zero-residue and signed-positive-majorant forms used
by the automorphic-prime step.
-/

open Filter Topology Asymptotics
open scoped ArithmeticFunction

set_option maxHeartbeats 800000

namespace CriticalLinePhasor.ThreeDConverse

/-- A nonnegative Dirichlet series continuous through `Re s = 1` with zero residue has summatory
function `o(N)`. -/
theorem wienerIkehara_zeroResidue_littleO
    {G : ℂ → ℂ} {f : ℕ → ℝ}
    (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ (f n : ℂ)) σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries (fun n ↦ (f n : ℂ)) s)
      {s | 1 < s.re}) :
    (fun N : ℕ ↦ cumsum f N) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  apply isLittleO_of_tendsto
  · intro N hN
    have : N = 0 := by exact_mod_cast hN
    subst N
    simp [cumsum]
  · simpa using (WienerIkeharaTheorem'' (A := 0) hpos hf hG (by
      intro s hs
      simpa using hG' hs))

/-- Signed Wiener--Ikehara by a common positive majorant: if `b+a` and `b-a` are nonnegative and
their Dirichlet series have the same boundary residue, subtraction gives `sum a = o(N)`. -/
theorem wienerIkehara_signed_littleO_of_positive_pair
    {a b : ℕ → ℝ} {A : ℝ} {Gplus Gminus : ℂ → ℂ}
    (hplus : 0 ≤ fun n ↦ b n + a n) (hminus : 0 ≤ fun n ↦ b n - a n)
    (hsplus : ∀ (σ' : ℝ), 1 < σ' →
      Summable (nterm (fun n ↦ ((b n + a n : ℝ) : ℂ)) σ'))
    (hsminus : ∀ (σ' : ℝ), 1 < σ' →
      Summable (nterm (fun n ↦ ((b n - a n : ℝ) : ℂ)) σ'))
    (hGplus : ContinuousOn Gplus {s | 1 ≤ s.re})
    (hGminus : ContinuousOn Gminus {s | 1 ≤ s.re})
    (hidplus : Set.EqOn Gplus
      (fun s ↦ LSeries (fun n ↦ ((b n + a n : ℝ) : ℂ)) s - (A : ℂ) / (s - 1))
      {s | 1 < s.re})
    (hidminus : Set.EqOn Gminus
      (fun s ↦ LSeries (fun n ↦ ((b n - a n : ℝ) : ℂ)) s - (A : ℂ) / (s - 1))
      {s | 1 < s.re}) :
    (fun N : ℕ ↦ cumsum a N) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  have hp := WienerIkeharaTheorem'' hplus hsplus hGplus hidplus
  have hm := WienerIkeharaTheorem'' hminus hsminus hGminus hidminus
  apply isLittleO_of_tendsto
  · intro N hN
    have : N = 0 := by exact_mod_cast hN
    subst N
    simp [cumsum]
  · have hsub := hp.sub hm
    convert hsub.const_mul (1 / 2 : ℝ) using 1
    · funext N
      simp only [cumsum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
    · norm_num

/-- A genuine continuous boundary value for a real Dirichlet coefficient sequence.  This is the
analytic output supplied by automorphic nonvanishing on `Re(s) = 1`; it is strictly weaker than
the summatory conclusion and retains the exact initial Dirichlet series. -/
structure ContinuousLSeriesBoundary3D (a : ℕ → ℝ) where
  continuation : ℂ → ℂ
  continuousOn : ContinuousOn continuation {s | 1 ≤ s.re}
  eqOn : Set.EqOn continuation (fun s ↦ LSeries (fun n ↦ (a n : ℂ)) s) {s | 1 < s.re}
  summable : ∀ (sigma : ℝ), 1 < sigma →
    Summable (nterm (fun n ↦ (a n : ℂ)) sigma)

/-- A continuous zero-residue boundary source plus the pointwise automorphic von Mangoldt bound
implies `o(N)`.  The proof applies Wiener--Ikehara to the positive pair
`d · Λ ± a`; the pole is supplied by the ordinary zeta logarithmic derivative and cancels on
subtraction. -/
theorem boundedByVonMangoldt_cumsum_isLittleO
    {a : ℕ → ℝ} {d : ℝ} (hd : 0 ≤ d)
    (hbound : ∀ n, |a n| ≤ d * ArithmeticFunction.vonMangoldt n)
    (B : ContinuousLSeriesBoundary3D a) :
    (fun N : ℕ ↦ cumsum a N) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  let b : ℕ → ℝ := fun n ↦ d * ArithmeticFunction.vonMangoldt n
  have hb (n : ℕ) : 0 ≤ b n := mul_nonneg hd ArithmeticFunction.vonMangoldt_nonneg
  have hplus : 0 ≤ fun n ↦ b n + a n := by
    intro n
    change 0 ≤ b n + a n
    have ha := hbound n
    rw [abs_le] at ha
    dsimp [b]
    linarith
  have hminus : 0 ≤ fun n ↦ b n - a n := by
    intro n
    change 0 ≤ b n - a n
    have ha := hbound n
    rw [abs_le] at ha
    dsimp [b]
    linarith
  have hs (sign : ℕ → ℝ) (hsign : ∀ n, 0 ≤ sign n)
      (hle : ∀ n, sign n ≤ 2 * b n) (sigma : ℝ) (hsigma : 1 < sigma) :
      Summable (nterm (fun n ↦ (sign n : ℂ)) sigma) := by
    have hLambda : Summable
        (nterm (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) sigma) := by
      simpa only [← nterm_eq_norm_term] using
        (@ArithmeticFunction.LSeriesSummable_vonMangoldt (sigma : ℂ) (by simpa using hsigma)).norm
    have hmajor : Summable (fun n ↦ (2 * d) *
        nterm (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) sigma n) :=
      hLambda.mul_left (2 * d)
    apply hmajor.of_nonneg_of_le
    · intro n
      simp only [nterm]
      positivity
    · intro n
      by_cases hn : n = 0
      · simp [hn, nterm]
      · simp only [nterm, hn, if_false, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (hsign n), abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have hnnonneg : 0 ≤ (n : ℝ) ^ sigma := Real.rpow_nonneg (Nat.cast_nonneg n) _
        calc
          sign n / (n : ℝ) ^ sigma ≤ (2 * b n) / (n : ℝ) ^ sigma :=
            div_le_div_of_nonneg_right (hle n) hnnonneg
          _ = (2 * d) * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ sigma) := by
            simp only [b]
            ring
  have hsplus : ∀ sigma : ℝ, 1 < sigma →
      Summable (nterm (fun n ↦ ((b n + a n : ℝ) : ℂ)) sigma) := by
    intro sigma hsigma
    apply hs (fun n ↦ b n + a n) hplus
    · intro n
      have ha := hbound n
      rw [abs_le] at ha
      dsimp [b]
      linarith
    · exact hsigma
  have hsminus : ∀ sigma : ℝ, 1 < sigma →
      Summable (nterm (fun n ↦ ((b n - a n : ℝ) : ℂ)) sigma) := by
    intro sigma hsigma
    apply hs (fun n ↦ b n - a n) hminus
    · intro n
      have ha := hbound n
      rw [abs_le] at ha
      dsimp [b]
      linarith
    · exact hsigma
  let F := ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  let Gplus : ℂ → ℂ := fun s ↦ (d : ℂ) * F s + B.continuation s
  let Gminus : ℂ → ℂ := fun s ↦ (d : ℂ) * F s - B.continuation s
  have hFcont : ContinuousOn F {s | 1 ≤ s.re} :=
    ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have hGplus : ContinuousOn Gplus {s | 1 ≤ s.re} :=
    continuousOn_const.mul hFcont |>.add B.continuousOn
  have hGminus : ContinuousOn Gminus {s | 1 ≤ s.re} :=
    continuousOn_const.mul hFcont |>.sub B.continuousOn
  have hF (s : ℂ) (hsone : 1 < s.re) :
      F s = LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s - 1 / (s - 1) := by
    have h := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux
      (q := 1) (a := 1) isUnit_one hsone
    simp only [F, h, ArithmeticFunction.vonMangoldt.residueClass, Nat.totient_one,
      Nat.cast_one, inv_one, one_div, sub_left_inj]
    apply LSeries_congr
    intro n _
    simp only [Complex.ofReal_inj, Set.indicator_apply_eq_self, Set.mem_setOf_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have hLscale (s : ℂ) :
      LSeries (fun n ↦ (b n : ℂ)) s =
        (d : ℂ) * LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    rw [show (fun n ↦ (b n : ℂ)) =
      (d : ℂ) • fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) by
        funext n
        simp [b]]
    exact LSeries_smul (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) (d : ℂ) s
  have hidplus : Set.EqOn Gplus
      (fun s ↦ LSeries (fun n ↦ ((b n + a n : ℝ) : ℂ)) s - (d : ℂ) / (s - 1))
      {s | 1 < s.re} := by
    intro s hsone
    have hbSum : LSeriesSummable (fun n ↦ (b n : ℂ)) s := by
      apply Summable.of_norm
      simpa only [norm_term_eq_nterm_re] using
        hs b hb (fun n ↦ by nlinarith [hb n]) s.re hsone
    have haSum : LSeriesSummable (fun n ↦ (a n : ℂ)) s := by
      apply Summable.of_norm
      simpa only [norm_term_eq_nterm_re] using B.summable s.re hsone
    have hfun : (fun n ↦ ((b n + a n : ℝ) : ℂ)) =
        (fun n ↦ (b n : ℂ)) + fun n ↦ (a n : ℂ) := by
      funext n
      push_cast
      rfl
    change (d : ℂ) * F s + B.continuation s =
      LSeries (fun n ↦ ((b n + a n : ℝ) : ℂ)) s - (d : ℂ) / (s - 1)
    rw [hF s hsone, B.eqOn hsone, hfun, LSeries_add hbSum haSum, hLscale]
    ring
  have hidminus : Set.EqOn Gminus
      (fun s ↦ LSeries (fun n ↦ ((b n - a n : ℝ) : ℂ)) s - (d : ℂ) / (s - 1))
      {s | 1 < s.re} := by
    intro s hsone
    have hbSum : LSeriesSummable (fun n ↦ (b n : ℂ)) s := by
      apply Summable.of_norm
      simpa only [norm_term_eq_nterm_re] using
        hs b hb (fun n ↦ by nlinarith [hb n]) s.re hsone
    have haSum : LSeriesSummable (fun n ↦ (a n : ℂ)) s := by
      apply Summable.of_norm
      simpa only [norm_term_eq_nterm_re] using B.summable s.re hsone
    have hfun : (fun n ↦ ((b n - a n : ℝ) : ℂ)) =
        (fun n ↦ (b n : ℂ)) - fun n ↦ (a n : ℂ) := by
      funext n
      push_cast
      rfl
    change (d : ℂ) * F s - B.continuation s =
      LSeries (fun n ↦ ((b n - a n : ℝ) : ℂ)) s - (d : ℂ) / (s - 1)
    rw [hF s hsone, B.eqOn hsone, hfun, LSeries_sub hbSum haSum, hLscale]
    ring
  exact wienerIkehara_signed_littleO_of_positive_pair hplus hminus hsplus hsminus
    hGplus hGminus hidplus hidminus

end CriticalLinePhasor.ThreeDConverse

#print axioms WienerIkeharaTheorem'
#print axioms WienerIkeharaTheorem''
#print axioms CriticalLinePhasor.ThreeDConverse.wienerIkehara_zeroResidue_littleO
#print axioms CriticalLinePhasor.ThreeDConverse.wienerIkehara_signed_littleO_of_positive_pair
#print axioms CriticalLinePhasor.ThreeDConverse.boundedByVonMangoldt_cumsum_isLittleO
