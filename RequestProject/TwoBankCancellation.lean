import RequestProject.FocalMassFreedom
import RequestProject.FocalCancellationEigenstate

/-!
# Which two objects do the cancelling (ledger 1230)

Sam (2026-10-11): for two things cancelling each other, `A + B = 0`, so `A = −B` and `|A| = |B|`. Two unequal-magnitude
vectors cannot cancel each other. The question is only which two objects are doing the cancelling.

* `exactCancellation_norm_eq`, `exactCancellation_amp_eq`: the house primitive `ExactCancellation p q`
  (`plane p + plane q = 0`) forces equal magnitude; for two charged phasors, equal amplitude.
* `partner_amplitudes_cancel`: two charged phasors carrying the same-height transverse-partner amplitudes
  `n^{−σ}`, `n^{−(1−σ)}` (`n ≥ 2`) cancel each other only if `σ = ½`. DEMOTED / AUXILIARY (ledgers 1232, 1237):
  true, but it concerns a site-by-site mechanism the conductor does not perform. It is not part of the
  canonical route.
* `split_resultants_norm_eq`: for a cancelling configuration, ANY split into two banks gives two mutually
  cancelling resultants of equal magnitude. With the split = the conductor's positive bank, this is the focal
  cancellation as the geometry has it: positive-bank resultant against negative-bank resultant (ledger 1231).

The equal-magnitude requirement says something about `σ` only when the two mutually cancelling objects carry the
partner amplitudes. The conductor's positive and negative banks carry the fiber's common amplitude law on disjoint
integers, so for them it is automatic and says nothing about `σ`.
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.TwoBank

open CriticalLinePhasor CriticalLinePhasor.Phasor3D CriticalLinePhasor.FocalCancellation
open CriticalLinePhasor.LFunctionPhasor CriticalLinePhasor.FocalFeet

/-- **Two phasors that cancel each other have equal magnitude.** -/
theorem exactCancellation_norm_eq {p q : Vec3} (h : ExactCancellation p q) :
    ‖plane p‖ = ‖plane q‖ := by
  rw [eq_neg_of_add_eq_zero_left h, norm_neg]

/-- **Two charged phasors cancel each other only at equal amplitude.** -/
theorem exactCancellation_amp_eq {p q : Vec3} {r r' : ℝ} (hp : IsChargedPhasor p r)
    (hq : IsChargedPhasor q r') (h : ExactCancellation p q) : r = r' := by
  rw [← hp.2, ← hq.2]
  exact exactCancellation_norm_eq h

/-- **Two charged phasors with same-height transverse-partner amplitudes `n^{−σ}`, `n^{−(1−σ)}` cancel
each other only at `σ = ½`.** -/
theorem partner_amplitudes_cancel {p q : Vec3} (σ : ℝ) {n : ℕ} (hn : 2 ≤ n)
    (hp : IsChargedPhasor p ((n : ℝ) ^ (-σ))) (hq : IsChargedPhasor q ((n : ℝ) ^ (-(1 - σ))))
    (h : ExactCancellation p q) : σ = 1 / 2 := by
  have heq := exactCancellation_amp_eq hp hq h
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := Real.rpow_lt_rpow_of_exponent_lt hn1 (show -(1 - σ) < -σ by linarith)
    linarith
  · have := Real.rpow_lt_rpow_of_exponent_lt hn1 (show -σ < -(1 - σ) by linarith)
    linarith

/-- **Any split of a cancelling configuration into two banks gives equal resultant magnitudes.** -/
theorem split_resultants_norm_eq {c : PhasorConfig} (hc : c.Cancels) (S : Finset (Fin c.size)) :
    ‖∑ k ∈ S, c.phasor k‖ = ‖∑ k ∈ Sᶜ, c.phasor k‖ := by
  have h : ∑ k ∈ S, c.phasor k + ∑ k ∈ Sᶜ, c.phasor k = 0 := by
    rw [Finset.sum_add_sum_compl]
    exact hc
  rw [eq_neg_of_add_eq_zero_left h, norm_neg]

end CriticalLinePhasor.TwoBank

end

#print axioms CriticalLinePhasor.TwoBank.exactCancellation_norm_eq
#print axioms CriticalLinePhasor.TwoBank.exactCancellation_amp_eq
#print axioms CriticalLinePhasor.TwoBank.partner_amplitudes_cancel
#print axioms CriticalLinePhasor.TwoBank.split_resultants_norm_eq
