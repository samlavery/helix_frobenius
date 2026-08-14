import RequestProject.EisensteinHeightCoset
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# Eisenstein convergence at the real-analytic threshold, imported

The direction-side summability of the Eisenstein–Epstein identity.  Mathlib's
`EisensteinSeries.Summable` already carries both ingredients, and crucially carries them at **real**
exponents rather than integer weights:

* `summand_bound` — `‖cz+d‖^{-k} ≤ r(z)^{-k}·‖(c,d)‖^{-k}`, separating the `z`-dependence from the
  lattice norm;
* `summable_one_div_norm_rpow` — `∑_{(c,d)} ‖(c,d)‖^{-k} < ∞` for `k > 2`.

The threshold matches exactly: the real-analytic summand is `y^σ‖cz+d‖^{-2σ}`, so `k = 2σ` and the
condition `k > 2` is `σ > 1` — the same half-plane the Rankin–Selberg unfolding converges on.  That
is not a coincidence but the same DC/AC split seen throughout: `r(z)` carries the `z`-dependence
(the carrier), `‖(c,d)‖^{-2σ}` carries the lattice sum (the fiber), and they factor.

**Method note.**  These bounds were re-derived by hand earlier in this campaign before the Mathlib
namespace was searched.  They are imported here instead.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open EisensteinSeries UpperHalfPlane

namespace CriticalLinePhasor.Unfolding

/-- **Eisenstein convergence for the real-analytic summand.**  Converges exactly on `σ > 1`. -/
lemma summable_eisenstein_real (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun x : Fin 2 → ℤ =>
      z.im ^ σ * ‖(x 0 : ℂ) * (z : ℂ) + (x 1 : ℂ)‖ ^ (-(2 * σ)) := by
  have h2 : (2:ℝ) < 2 * σ := by linarith
  have hk : (0:ℝ) ≤ 2 * σ := by linarith
  have hzim : (0:ℝ) < z.im := z.im_pos
  have hr : (0:ℝ) < r z := r_pos z
  have hmaj : Summable fun x : Fin 2 → ℤ =>
      z.im ^ σ * ((r z) ^ (-(2 * σ)) * ‖x‖ ^ (-(2 * σ))) :=
    ((summable_one_div_norm_rpow h2).mul_left _).mul_left _
  refine hmaj.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact summand_bound (z := z) hk x

/-- The same bound restricted to any subfamily — in particular to the coprime pairs, which is the
form `tsum_nonzero_eq_zeta_factor` consumes on the direction side. -/
lemma summable_eisenstein_real_subtype (z : ℍ) {σ : ℝ} (hσ : 1 < σ)
    (P : (Fin 2 → ℤ) → Prop) :
    Summable fun x : {x : Fin 2 → ℤ // P x} =>
      z.im ^ σ * ‖(x.1 0 : ℂ) * (z : ℂ) + (x.1 1 : ℂ)‖ ^ (-(2 * σ)) :=
  (summable_eisenstein_real z hσ).subtype _

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.summable_eisenstein_real
#print axioms CriticalLinePhasor.Unfolding.summable_eisenstein_real_subtype
