import RequestProject.HerglotzSweep

/-!
# The mirror pair under transport (ledger 646)

At an anchor `s` the transport is `w_ρ = (ρ − c)/(s − ρ)`, `c = 1 − s̄`, with weight
`ω_ρ = 1/((s − ρ)(ρ − c))`.  The functional-equation mirror of a zero is `ρ′ = 1 − ρ̄`.

* `transport_mirror`:  `w_{ρ′} = (w̄_ρ)⁻¹` — the mirror pair transports to the face-inversion pair
  through the unit circle;
* `atomWeight_mirror`: `ω_{ρ′} = ω̄_ρ`;
* `pairCoeff_conj`: the pair's coefficient sequence `ω w^k + ω̄ (w̄⁻¹)^k` is Hermitian in `k`;
* `pairCoeff_of_norm_one`: on the circle the two atoms coincide and the pair's coefficient is
  `2 Re(ω) · w^k`.

So an off-line pair sits at `(w, 1/w̄)`, one atom strictly outside the circle, and its contribution
to the seat form on a test vector `C` is `2 Re[ω · C(w) · conj C(1/w̄)]`, which becomes
`2 Re(ω) |C(w)|²` on the circle, where the on-line weight `ω = 1/‖s − ρ‖²` is positive.  No positivity
is claimed here; these are the identities the seat form consumes for a mirror pair.
-/

open Complex

namespace CriticalLinePhasor.SeatingLedger

theorem transport_mirror (s ρ : ℂ) :
    transport s (1 - (starRingEnd ℂ) ρ) = ((starRingEnd ℂ) (transport s ρ))⁻¹ := by
  simp only [transport, map_div₀, map_sub, map_one, Complex.conj_conj, inv_div]
  congr 1 <;> ring

theorem atomWeight_mirror (s ρ : ℂ) :
    atomWeight s (1 - (starRingEnd ℂ) ρ) = (starRingEnd ℂ) (atomWeight s ρ) := by
  simp only [atomWeight, map_inv₀, map_mul, map_sub, map_one, Complex.conj_conj]
  congr 1
  ring

/-- The `k`-th coefficient of a mirror pair: `ω w^k + ω̄ (w̄⁻¹)^k`. -/
noncomputable def pairCoeff (ω w : ℂ) (k : ℤ) : ℂ :=
  ω * w ^ k + (starRingEnd ℂ) ω * ((starRingEnd ℂ) w)⁻¹ ^ k

/-- The pair's coefficient sequence is Hermitian: `conj (pairCoeff k) = pairCoeff (−k)`. -/
theorem pairCoeff_conj (ω w : ℂ) (k : ℤ) :
    (starRingEnd ℂ) (pairCoeff ω w k) = pairCoeff ω w (-k) := by
  simp only [pairCoeff, map_add, map_mul, map_zpow₀, map_inv₀, Complex.conj_conj, zpow_neg,
    inv_zpow, inv_inv]
  ring

/-- On the circle the mirror atom coincides with the atom: `(w̄)⁻¹ = w` when `‖w‖ = 1`. -/
theorem conj_inv_of_norm_one {w : ℂ} (h : ‖w‖ = 1) : ((starRingEnd ℂ) w)⁻¹ = w := by
  have hn : Complex.normSq w = 1 := by
    rw [Complex.normSq_eq_norm_sq, h, one_pow]
  have hmul : w * (starRingEnd ℂ) w = 1 := by
    rw [Complex.mul_conj, hn, Complex.ofReal_one]
  exact inv_eq_of_mul_eq_one_left hmul

/-- On the circle the pair's coefficient is `2 Re(ω) · w^k`: the two atoms coincide. -/
theorem pairCoeff_of_norm_one (ω : ℂ) {w : ℂ} (h : ‖w‖ = 1) (k : ℤ) :
    pairCoeff ω w k = 2 * (ω.re : ℂ) * w ^ k := by
  simp only [pairCoeff, conj_inv_of_norm_one h]
  rw [← add_mul, Complex.add_conj]
  push_cast
  ring

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.transport_mirror
#print axioms CriticalLinePhasor.SeatingLedger.atomWeight_mirror
#print axioms CriticalLinePhasor.SeatingLedger.pairCoeff_conj
#print axioms CriticalLinePhasor.SeatingLedger.pairCoeff_of_norm_one
