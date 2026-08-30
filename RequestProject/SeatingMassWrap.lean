import RequestProject.SeatingFloorOdd

/-!
# The wrap: RH from mass nonnegativity, as one statement

The campaign's capstone.  The **seat mass** is the even factor of the
valley floor, `seatMass s = Re[ξ′/ξ(s)] / (σ − ½)`.  Compiled here:

* `seatMass_mirror` — the mass is exactly EVEN under the σ-mirror at fixed
  height (`s ↦ 1 − s̄`): the floor's odd symmetry divided by the odd
  prefactor.
* `rh_of_channel_mass` — **RH from one hypothesis**: there is a compiled
  `A > 0` such that `seatMass ≥ 0` on the high left channel
  (`|Im s| > 1269/2`, `A/log⁹|Im s| < Re s < ½`) forces every nontrivial
  zero onto the critical line.

Everything else — the ladder below 634.5, the shell margins, the sign
door, the factorization — is compiled upstream.  Measured support
(tmp/att546/547): the mass equals the Poisson-smoothed zero density
(π per event), DC = the χ-clock rate `½log(t/2π)`, positive; the
hypothesis is the statement that the mirror clock's fluctuation never
overwhelms it.

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- **The seat mass**: the even factor of the valley floor. -/
def seatMass (s : ℂ) : ℝ := (logDeriv ZD.riemannXi s).re / (s.re - 1/2)

/-- **The mass is even** under the σ-mirror at fixed height: odd floor over
odd prefactor. -/
theorem seatMass_mirror (s : ℂ) : seatMass (1 - conj s) = seatMass s := by
  unfold seatMass
  rw [floor_mirror]
  have h1 : (1 - conj s).re = 1 - s.re := by
    simp [Complex.sub_re, Complex.conj_re]
  rw [h1]
  have h2 : (1:ℝ) - s.re - 1/2 = -(s.re - 1/2) := by ring
  rw [h2, div_neg, neg_div, neg_neg]

/-- **RH from channel mass nonnegativity** — the campaign wrapped to one
statement with one hypothesis. -/
theorem rh_of_channel_mass :
    ∃ A : ℝ, 0 < A ∧
      ((∀ s : ℂ, 1269/2 < |s.im| →
          A / (Real.log |s.im|)^9 < s.re → s.re < 1/2 →
          0 ≤ seatMass s) →
        ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2) := by
  obtain ⟨A, hA0, hsign⟩ := rh_of_high_sign
  refine ⟨A, hA0, fun hM => hsign ?_⟩
  intro s him hlow hhigh
  have hM' := hM s him hlow hhigh
  unfold seatMass at hM'
  have hb : s.re - 1/2 < 0 := by linarith
  rcases div_nonneg_iff.mp hM' with ⟨_, hb'⟩ | ⟨ha', _⟩
  · linarith
  · exact ha'

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.seatMass_mirror
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_channel_mass
