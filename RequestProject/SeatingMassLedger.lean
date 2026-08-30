import RequestProject.SeatingMassWrap

/-!
# The mass ledger, termwise: on-line zeros never obstruct

Attack notes for the leaf (`0 ≤ seatMass` on the channel), route 1 —
termwise Hadamard.  The unconditional brick: an on-line FE-pair
`{½+iγ, ½−iγ}` contributes

  `Re[(s−ρ)⁻¹ + (s−ρ′)⁻¹] = (σ−½)·(1/|s−ρ|² + 1/|s−ρ′|²)`

— its floor term carries the sign of `σ−½` and its mass term is
`1/|s−ρ|² + 1/|s−ρ′|² ≥ 0` with NO hypothesis, at EVERY strip point.  So
the compiled ⅔-density of on-line zeros (Zeta23) pushes the mass the right
way termwise, everywhere; the only possible violators of the mass
hypothesis are the off-line zeros whose nonexistence is its content, and
(pencil, quadruple computation) a violator can push the mass negative only
inside its own depth-disk `|t−γ| < |β−½|`.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- The floor term of a point-mass: `Re[(s−w)⁻¹] = (σ−Re w)/|s−w|²`. -/
theorem point_floor_re (s w : ℂ) :
    ((s - w)⁻¹).re = (s.re - w.re) / Complex.normSq (s - w) := by
  rw [Complex.inv_re, Complex.sub_re]

/-- **The on-line pair's ledger line**: floor = `(σ−½)` times a manifestly
nonnegative mass. -/
theorem online_pair_ledger (γ : ℝ) (s : ℂ) :
    ((s - (1/2 + γ * I))⁻¹ + (s - (1/2 - γ * I))⁻¹).re
      = (s.re - 1/2) *
        (1 / Complex.normSq (s - (1/2 + γ * I))
          + 1 / Complex.normSq (s - (1/2 - γ * I))) := by
  rw [Complex.add_re, point_floor_re, point_floor_re]
  have h1 : ((1:ℂ)/2 + γ * I).re = 1/2 := by simp
  have h2 : ((1:ℂ)/2 - γ * I).re = 1/2 := by simp
  rw [h1, h2]
  ring

/-- **On-line zeros never obstruct the mass hypothesis**: the pair's even
factor is nonnegative at every point of the plane, unconditionally. -/
theorem online_pair_mass_nonneg (γ : ℝ) (s : ℂ) :
    0 ≤ ((s - (1/2 + γ * I))⁻¹ + (s - (1/2 - γ * I))⁻¹).re
        / (s.re - 1/2) := by
  rw [online_pair_ledger]
  rcases eq_or_ne (s.re - 1/2) 0 with h0 | h0
  · rw [h0]
    simp
  · rw [mul_div_cancel_left₀ _ h0]
    have g1 := Complex.normSq_nonneg (s - (1/2 + γ * I))
    have g2 := Complex.normSq_nonneg (s - (1/2 - γ * I))
    positivity

/-- **The left-channel floor form**: on-line pairs push the floor down
everywhere left of the line — the sign the seat door demands. -/
theorem online_pair_re_nonpos (γ : ℝ) {s : ℂ} (hσ : s.re < 1/2) :
    ((s - (1/2 + γ * I))⁻¹ + (s - (1/2 - γ * I))⁻¹).re ≤ 0 := by
  rw [online_pair_ledger]
  apply mul_nonpos_of_nonpos_of_nonneg
  · linarith
  · have g1 := Complex.normSq_nonneg (s - (1/2 + γ * I))
    have g2 := Complex.normSq_nonneg (s - (1/2 - γ * I))
    positivity

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.online_pair_ledger
#print axioms CriticalLinePhasor.SeatingLedger.online_pair_mass_nonneg
#print axioms CriticalLinePhasor.SeatingLedger.online_pair_re_nonpos
