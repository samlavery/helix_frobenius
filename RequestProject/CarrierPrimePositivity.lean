import Mathlib

/-!
# The positive teeth: the prime side of the carrier readout is nonnegative

The first compiled consumer of `Λ ≥ 0` — the input Phase B's transport is
forced to use.  The carrier class (absolutely convergent Dirichlet
log-derivative + FE) is inhabited by RH-false objects (Davenport–Heilbronn:
signed teeth, measured in the comb campaign), so class + FE cannot close the
channel; what ζ has and DH lacks is the SIGN of the teeth.  Compiled here:

* `neg_zeta_logDeriv_re_nonneg` — on the real ray `σ > 1`,
  `Re[−ζ′/ζ(σ)] ≥ 0`: the readout's teeth are nonnegative, via Mathlib's
  `L ↗Λ = −ζ′/ζ` and termwise `Λ(n)/n^σ ≥ 0`.

This is the seed of [B★]: FE + carrier class + positive teeth (+ pole)
⟹ channel mass — the finish-form of Phase B.

No `sorry`, no `axiom`.
-/

open Complex ArithmeticFunction

noncomputable section

namespace CriticalLinePhasor.PrimePositivity

/-- **The teeth are nonnegative**: on the real ray `σ > 1` the prime side
of the carrier readout, `−ζ′/ζ(σ)`, has nonnegative real part — each mode
contributes `Λ(n)/n^σ ≥ 0`. -/
theorem neg_zeta_logDeriv_re_nonneg {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (- deriv riemannZeta (σ:ℂ) / riemannZeta (σ:ℂ)).re := by
  have hs : 1 < ((σ:ℂ)).re := by
    simpa using hσ
  have hid := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hsum := LSeriesSummable_vonMangoldt hs
  have hgoal : (- deriv riemannZeta (σ:ℂ) / riemannZeta (σ:ℂ))
      = LSeries (fun n => ((Λ n : ℝ) : ℂ)) (σ:ℂ) := by
    rw [hid]
  rw [hgoal]
  unfold LSeries
  rw [Complex.re_tsum hsum]
  apply tsum_nonneg
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    simp
  · rw [LSeries.term_of_ne_zero hn]
    have hn0 : (0:ℝ) < (n:ℝ) := by
      have := Nat.pos_of_ne_zero hn
      exact_mod_cast this
    have hpow : ((n:ℂ))^((σ:ℂ)) = (((n:ℝ)^σ : ℝ) : ℂ) := by
      rw [show ((n:ℂ)) = (((n:ℝ)):ℂ) by push_cast; rfl]
      exact (Complex.ofReal_cpow hn0.le σ).symm
    rw [hpow,
      show ((Λ n : ℝ) : ℂ) / (((n:ℝ)^σ : ℝ) : ℂ)
        = (((Λ n / (n:ℝ)^σ : ℝ)) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
    apply div_nonneg vonMangoldt_nonneg
    positivity

end CriticalLinePhasor.PrimePositivity

#print axioms CriticalLinePhasor.PrimePositivity.neg_zeta_logDeriv_re_nonneg
