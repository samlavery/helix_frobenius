import RequestProject.CarrierSignFlip

/-!
# Off-line pairing: zeros away from the critical line come in pairs at the same ordinate

This is the first of the two leaves that ledger 814 named as standing between the compiled parity
bit and the count congruence `N(T) ≡ Ψ(T)/π + c (mod 2)`.

The compiled sign law reads the parity of the **odd-order events on the line**.  The counting
function `N` counts **every** zero in the strip.  For the bit to carry `N mod 2` unconditionally,
the zeros off the line must contribute an even amount at each ordinate — and they do, because they
pair.

## The pairing is conjugation, once the variable is right

In the `s` picture the relevant reflection is `s ↦ 1 - conj s`: it fixes exactly the critical line,
preserves the height, and carries zeros to zeros by the functional equation together with Schwarz
reflection.  In the **ordinate variable** `s = ½+iz` that reflection is simply `z ↦ conj z`
(`crit_is_conj`), which is why the statement is short here and awkward in the chart.  The ordinate
of `z` is `Re z` (`ordinate_eq`), conjugation preserves it, and the fixed points of conjugation are
exactly the real ordinates, i.e. exactly the critical line (`offCriticalLine_iff`).

* `xiEntire_conj` — the readout intertwines conjugation: `ξ(conj z) = conj(ξ z)`.  Proved from the
  compiled Schwarz reflection of `Λ₀` together with `Λ₀(1-s) = Λ₀(s)`; both symmetries are needed
  and neither alone suffices.
* `xiEntire_order_conj` — **the orders agree**, which is the part that makes the contribution even
  rather than merely paired.  Proved by transporting the local factorization through conjugation.
* `offAxis_pairs` — the packaged statement: an off-line zero has a distinct partner at the same
  ordinate with the same multiplicity.

What is still missing for the count congruence is the other leaf: the global induction from the
local sign law to a count over an interval.  That is not in this file.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.CarrierParity

/-- The ordinate of the line point `½+iz` is `Re z`. -/
theorem ordinate_eq (z : ℂ) : ((1 : ℂ) / 2 + z * I).im = z.re := by
  simp [Complex.add_im, Complex.mul_im]

/-- Off the critical line is exactly off the real ordinate axis. -/
theorem offCriticalLine_iff (z : ℂ) : ((1 : ℂ) / 2 + z * I).re ≠ 1 / 2 ↔ z.im ≠ 0 := by
  constructor <;> intro h hc <;> apply h
  · simp [Complex.add_re, Complex.mul_re, hc]
  · have : ((1 : ℂ) / 2 + z * I).re = 1 / 2 - z.im := by
      simp [Complex.add_re, Complex.mul_re]
      ring
    rw [this] at hc
    linarith

/-- **The reflection that fixes the critical line is conjugation of the ordinate.** -/
theorem crit_is_conj (z : ℂ) :
    1 - (starRingEnd ℂ) (1 / 2 + z * I) = 1 / 2 + (starRingEnd ℂ) z * I := by
  simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I]
  ring

/-- Conjugate ordinates sit at the same ordinate. -/
theorem conj_same_ordinate (z : ℂ) : ((starRingEnd ℂ) z).re = z.re := Complex.conj_re z

/-- Conjugation moves an ordinate exactly when it is off the axis. -/
theorem conj_ne_self_iff (z : ℂ) : (starRingEnd ℂ) z ≠ z ↔ z.im ≠ 0 := by
  rw [Ne, Ne, not_iff_not, Complex.conj_eq_iff_im]

/-- Schwarz reflection for `Λ₀`, in the form used below. -/
theorem completedZeta₀_conj' (w : ℂ) :
    (starRingEnd ℂ) (completedRiemannZeta₀ w) = completedRiemannZeta₀ ((starRingEnd ℂ) w) := by
  have h := HelixCollapse.completedRiemannZeta₀_conj ((starRingEnd ℂ) w)
  rwa [Complex.conj_conj] at h

/-- **The readout intertwines conjugation.**  Both the conjugation symmetry of `Λ₀` and its
functional equation are used; neither alone gives this. -/
theorem xiEntire_conj (z : ℂ) :
    xiEntire ((starRingEnd ℂ) z) = (starRingEnd ℂ) (xiEntire z) := by
  have key : (starRingEnd ℂ) (1 / 2 + z * I) = 1 - (1 / 2 + (starRingEnd ℂ) z * I) := by
    rw [← crit_is_conj]; ring
  rw [xiEntire, xiEntire, map_sub, map_mul, map_mul, map_one, completedZeta₀_conj', key,
    completedRiemannZeta₀_one_sub]
  simp only [map_sub, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I]
  ring

/-- Conjugate ordinates are zeros together. -/
theorem xiEntire_zero_conj (z : ℂ) :
    xiEntire ((starRingEnd ℂ) z) = 0 ↔ xiEntire z = 0 := by
  rw [xiEntire_conj, map_eq_zero]

/-- Conjugation is continuous as a map of ordinates, in the form needed to pull filters back. -/
theorem tendsto_conj_nhds (z : ℂ) :
    Filter.Tendsto (starRingEnd ℂ) (nhds ((starRingEnd ℂ) z)) (nhds z) := by
  have h : Filter.Tendsto (starRingEnd ℂ) (nhds ((starRingEnd ℂ) z))
      (nhds ((starRingEnd ℂ) ((starRingEnd ℂ) z))) := Complex.continuous_conj.continuousAt
  rwa [Complex.conj_conj] at h

/-- **The orders agree across a conjugate pair.**  This is the clause that makes an off-line pair
contribute an EVEN amount, rather than merely being paired. -/
theorem xiEntire_order_conj (z : ℂ) :
    analyticOrderNatAt xiEntire ((starRingEnd ℂ) z) = analyticOrderNatAt xiEntire z := by
  obtain ⟨g, hg, hg0, hev⟩ :=
    ((xiEntire_analyticAt z).analyticOrderNatAt_eq_iff (xiEntire_analyticOrderAt_ne_top z)).mp rfl
  refine ((xiEntire_analyticAt ((starRingEnd ℂ) z)).analyticOrderNatAt_eq_iff
    (xiEntire_analyticOrderAt_ne_top _)).mpr
      ⟨fun w => (starRingEnd ℂ) (g ((starRingEnd ℂ) w)), ?_, ?_, ?_⟩
  · rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have hgd : ∀ᶠ w in nhds z, DifferentiableAt ℂ g w :=
      Complex.analyticAt_iff_eventually_differentiableAt.mp hg
    filter_upwards [(tendsto_conj_nhds z).eventually hgd] with w hw
    have h2 := hw.conj_conj
    rw [Complex.conj_conj] at h2
    simpa [Function.comp_def] using h2
  · simp only [Complex.conj_conj]
    exact fun h => hg0 (map_eq_zero _ |>.mp h)
  · filter_upwards [(tendsto_conj_nhds z).eventually hev] with w hw
    have h1 : xiEntire w = (starRingEnd ℂ) (xiEntire ((starRingEnd ℂ) w)) := by
      rw [xiEntire_conj, Complex.conj_conj]
    rw [h1, hw, smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj, smul_eq_mul]

/-- **OFF-LINE PAIRING.**  A zero of the carrier's entire readout that is off the critical line has
a DISTINCT partner at the SAME ordinate with the SAME multiplicity.  So the zeros off the line
contribute an even amount to the count at each ordinate, and the readout's sign bit — which cannot
see them at all — is not thereby wrong about `N mod 2`. -/
theorem offAxis_pairs {z : ℂ} (hz : z.im ≠ 0) (h0 : xiEntire z = 0) :
    xiEntire ((starRingEnd ℂ) z) = 0
      ∧ ((starRingEnd ℂ) z).re = z.re
      ∧ (starRingEnd ℂ) z ≠ z
      ∧ analyticOrderNatAt xiEntire ((starRingEnd ℂ) z) = analyticOrderNatAt xiEntire z :=
  ⟨(xiEntire_zero_conj z).mpr h0, conj_same_ordinate z, (conj_ne_self_iff z).mpr hz,
    xiEntire_order_conj z⟩

/-- The same statement read in the `s` chart: the partner of a zero at `s` is at `1 - conj s`,
which has the same imaginary part and is distinct exactly when `Re s ≠ ½`. -/
theorem offCriticalLine_partner {z : ℂ} (hz : ((1 : ℂ) / 2 + z * I).re ≠ 1 / 2)
    (h0 : xiEntire z = 0) :
    xiEntire ((starRingEnd ℂ) z) = 0
      ∧ ((1 : ℂ) / 2 + (starRingEnd ℂ) z * I) = 1 - (starRingEnd ℂ) (1 / 2 + z * I)
      ∧ ((1 : ℂ) / 2 + (starRingEnd ℂ) z * I).im = ((1 : ℂ) / 2 + z * I).im
      ∧ analyticOrderNatAt xiEntire ((starRingEnd ℂ) z) = analyticOrderNatAt xiEntire z := by
  obtain ⟨hz1, hz2, _, hz4⟩ := offAxis_pairs ((offCriticalLine_iff z).mp hz) h0
  exact ⟨hz1, (crit_is_conj z).symm, by rw [ordinate_eq, ordinate_eq, hz2], hz4⟩

end CriticalLinePhasor.CarrierParity
