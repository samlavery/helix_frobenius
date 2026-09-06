import RequestProject.RegistrationRemainderIntegrable
import RequestProject.RegistrationDC

/-!
# The master registration identity on any height interval (ledger 611)

No stations. For every Riesz scale `L > 0` and every `0 < a ≤ b`:

  `N(a, b] = (ϑ(b) − ϑ(a))/π + (Ŝ_L(b) − Ŝ_L(a)) + (1/π)∫_a^b rem_L + boundaryTerm L a b`

(`count_identity`), the sharp zero count with multiplicity over `(a, b]` against the Riesz-strained
clock, with the archimedean remainder and the Fejér boundary term `Σ'_ρ m_ρ(1_{(a,b]}(γ_ρ) − w_ρ)`
explicit. At good heights this is the identity for the argument (`S_identity`):

  `S(b) − S(a) = (Ŝ_L(b) − Ŝ_L(a)) + (1/π)∫_a^b rem_L + boundaryTerm L a b`,

Selberg's formula for `S(t)` with Riesz weights, exact. Every station theorem is this identity
evaluated at two stations of some clock; the stations of the fixed-`L` clock (608–610) and of the
height-matched clock (`RegistrationWarp.lean`) are both instances.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real
open CriticalLinePhasor.CarrierScale (theta clockRate continuous_clockRate)

namespace CriticalLinePhasor.ContourArgument

/-- The integrated density over any interval of positive base height. -/
theorem smoothed_count_interval {L : ℝ} (hL : 0 < L) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (1 / Real.pi) * ∫ t in a..b, rieszZeroDensity L t
      = (theta b - theta a) / Real.pi + (rieszStrain L b - rieszStrain L a)
        + (1 / Real.pi) * ∫ t in a..b, rieszRemainder L t := by
  have hπ := Real.pi_pos
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b →
      rieszZeroDensity L t
        = clockRate t - (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re + rieszRemainder L t := by
    filter_upwards [goodHeight_ae (a := a) (b := b) ha (by linarith)] with t ht htI
    exact rieszZeroDensity_eq hL (ht htI)
  rw [intervalIntegral.integral_congr_ae hae]
  have i1 : IntervalIntegrable clockRate volume a b := continuous_clockRate.intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t : ℝ => (rieszPrimeSum L (1 / 2 + (t : ℂ) * I)).re) volume a b :=
    (rieszPrimeSum_re_continuous hL).intervalIntegrable _ _
  have hrem := rieszRemainder_intervalIntegrable hL ha hab
  rw [intervalIntegral.integral_add (i1.sub i2) hrem, intervalIntegral.integral_sub i1 i2,
    ← CriticalLinePhasor.ResidueJump.theta_sub_theta, integral_rieszPrimeSum_re hL]
  field_simp
  ring

/-- **The master registration identity.** -/
theorem count_identity {L : ℝ} (hL : 0 < L) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (bandCountMult a b : ℝ)
      = (theta b - theta a) / Real.pi + (rieszStrain L b - rieszStrain L a)
        + (1 / Real.pi) * (∫ t in a..b, rieszRemainder L t) + boundaryTerm L a b := by
  unfold boundaryTerm
  rw [← smoothed_count_eq_tsum_weights hL hab, smoothed_count_interval hL ha hab]
  ring

/-- **Selberg's formula for `S` with Riesz weights, exact.** -/
theorem S_identity {L : ℝ} (hL : 0 < L) {a b : ℝ} (ha : GoodHeight a) (hb : GoodHeight b)
    (hab : a ≤ b) :
    classicalSContour hb - classicalSContour ha
      = (rieszStrain L b - rieszStrain L a) + (1 / Real.pi) * (∫ t in a..b, rieszRemainder L t)
        + boundaryTerm L a b := by
  have h1 := stripZeroCountMult_eq_S ha
  have h2 := stripZeroCountMult_eq_S hb
  have h3 : (bandCountMult a b : ℝ) + stripZeroCountMult a = stripZeroCountMult b := by
    exact_mod_cast bandCountMult_add hab
  have h4 := count_identity hL ha.1 hab
  have h5 : (theta b - theta a) / Real.pi = theta b / Real.pi - theta a / Real.pi := by ring
  linarith

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.count_identity
#print axioms CriticalLinePhasor.ContourArgument.S_identity
