import RequestProject.HerglotzSweep
import RequestProject.ConductionClockToeplitz
import RequestProject.SeatingMassWrap

/-!
# Sweep geometry and normalization

For c = 1-conj(s), the inverse Cayley coordinate of u is (s-u)/(u-c).
When Re s, Re u < 1/2 it lies in the disc and maps back to u.
For q = (1-|z|²)/|1+z|², Re Phi_s(z) = q * seatMass(s_z).
The conduction kernel G_beta has strictly positive real part in this channel.

Construction: clear the inverse's denominators (`field_simp`), or use the squared-distance
identity (`have hnorm := normSq_sub_mirror s u`). For normalization use the already compiled
`movedAnchor_re` and `xiHerglotz_re`; independently the Poisson kernel gives the same factor.

Searches: `rg -n 'movedAnchor|sweepAnchor|seatMass|normSq_sub_mirror|Gclock|hker' RequestProject`;
`rg -n 'Herglotz|herglotz|poissonKernel|div_re|normSq' .lake/packages/mathlib/Mathlib/Analysis`.
Semantic searches: LeanSearch for the Herglotz/Poisson real-part identity;
Loogle `Complex.re, _ / _`. The summed sweep is reused from `HerglotzSweep`.
-/

open Complex

namespace CriticalLinePhasor.SeatingLedger

theorem movedAnchor_inverse {s u : ℂ} (hs : s.re < 1 / 2) (hu : u.re < 1 / 2) :
    ‖(s - u) / (u - (1 - (starRingEnd ℂ) s))‖ < 1 ∧
      movedAnchor s ((s - u) / (u - (1 - (starRingEnd ℂ) s))) = u := by
  have hc : u - (1 - (starRingEnd ℂ) s) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hd : s - (1 - (starRingEnd ℂ) s) ≠ 0 := by
    rw [mirror_d]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hpos : 0 < (2 * u.re - 1) * (2 * s.re - 1) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hnorm := normSq_sub_mirror s u
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hnorm
  have hlt : ‖s - u‖ < ‖u - (1 - (starRingEnd ℂ) s)‖ := by
    nlinarith [norm_nonneg (s - u), norm_nonneg (u - (1 - (starRingEnd ℂ) s))]
  have hz : ‖(s - u) / (u - (1 - (starRingEnd ℂ) s))‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hc)]
    exact hlt
  refine ⟨hz, ?_⟩
  have hz' : 1 + (s - u) / (u - (1 - (starRingEnd ℂ) s)) ≠ 0 := by
    intro h
    apply hd
    field_simp at h
    linear_combination h
  apply sub_eq_zero.mp
  have hzero : (1 + (s - u) / (u - (1 - (starRingEnd ℂ) s))) *
      (movedAnchor s ((s - u) / (u - (1 - (starRingEnd ℂ) s))) - u) = 0 := by
    rw [← movedAnchor_sub s _ u hz', div_mul_cancel₀ _ hc, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left hz'

theorem xiHerglotz_re_eq_scaled_seatMass {s z : ℂ} (hsre : s.re < 1 / 2)
    (hz : ‖z‖ < 1) (hs : s ∉ ZD.NontrivialZeros)
    (hc : 1 - (starRingEnd ℂ) s ∉ ZD.NontrivialZeros)
    (hu : movedAnchor s z ∉ ZD.NontrivialZeros) :
    (xiHerglotz s z).re = ((1 - ‖z‖ ^ 2) / ‖1 + z‖ ^ 2) *
      seatMass (movedAnchor s z) := by
  have hz' : 1 + z ≠ 0 := by
    intro h
    have he : z = -1 := by linear_combination h
    simpa [he] using hz
  have ha : s.re - 1 / 2 ≠ 0 := by linarith
  have hq : (1 - ‖z‖ ^ 2) / ‖1 + z‖ ^ 2 ≠ 0 := by
    apply ne_of_gt
    exact div_pos (by nlinarith [norm_nonneg z]) (pow_pos (norm_pos_iff.mpr hz') 2)
  have hdepth : (movedAnchor s z).re - 1 / 2 =
      (s.re - 1 / 2) * ((1 - ‖z‖ ^ 2) / ‖1 + z‖ ^ 2) := by
    rw [movedAnchor_re s z hz', Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    ring
  rw [xiHerglotz_re hs hc hz' hu (by linarith)]
  unfold seatMass
  rw [hdepth, show 2 * s.re - 1 = 2 * (s.re - 1 / 2) by ring]
  have halg (L a q : ℝ) (ha : a ≠ 0) (hq : q ≠ 0) :
      2 * L / (2 * a) = q * (L / (a * q)) := by field_simp
  exact halg _ _ _ ha hq

theorem hker_re_pos {x : ℂ} (hx : ‖x‖ < 1) : 0 < (hker x).re := by
  have hx' : 1 - x ≠ 0 := by
    apply one_sub_ne_zero_of_mem_ball
    simpa [Metric.mem_ball, dist_zero_right] using hx
  have hformula : (hker x).re = (1 - ‖x‖ ^ 2) / ‖1 - x‖ ^ 2 := by
    have h := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := x)) 1
    simpa [poissonKernel, herglotzRieszKernel, hker] using h.symm
  rw [hformula]
  exact div_pos (by nlinarith [norm_nonneg x]) (pow_pos (norm_pos_iff.mpr hx') 2)

theorem Gclock_re_pos {ℓ : ℝ} (hℓ : 0 < ℓ) {β : ℂ} (hβ : ‖β‖ ≤ 1)
    {s : ℂ} (hs : s.re < 1 / 2) : 0 < (Gclock ℓ β s).re := by
  have h := hker_re_pos (norm_mul_dvar_lt_one hℓ hβ hs)
  unfold Gclock
  rw [show (ℓ : ℂ) / 2 = ((ℓ / 2 : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul]
  exact mul_pos (by positivity) h

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.movedAnchor_inverse
#print axioms CriticalLinePhasor.SeatingLedger.xiHerglotz_re_eq_scaled_seatMass
#print axioms CriticalLinePhasor.SeatingLedger.hker_re_pos
#print axioms CriticalLinePhasor.SeatingLedger.Gclock_re_pos
