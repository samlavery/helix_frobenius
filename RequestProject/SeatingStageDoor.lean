import RequestProject.SeatingMassRH

/-!
# The stage door: RH from pointwise stage approximation — arrow [A3] compiled

The limit-transfer arrow of the kill tree, as a door.  If some stage family
`G n` matches `ξ` and `ξ′` in the limit at each channel point, and the stage
masses are EVENTUALLY nonnegative there, the seat mass is nonnegative on the
channel and the compiled mass door fires.  Pointwise and eventual is all the
limit needs (`ge_of_tendsto`); no compacts, no uniformity, no rate.

Two structural freebies:
* at a hypothetical zero of `ξ` the seat mass vanishes by the quotient
  convention (`seatMass_eq_zero_of_zero`), so the door demands NOTHING there —
  no zero-avoidance hypothesis;
* `finiteBank_seatMass_nonneg` already supplies the eventual-sign clause for
  every finite unitary bank, for EVERY index unconditionally — after this
  door, the chain to RH is machine-checked modulo exactly [M2] (convergence
  of a registered family) and [M1] (its stage-mass sign, the three-regime
  escort law) at whatever family is chosen.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- At a zero of `ξ` the seat mass vanishes identically (Lean's quotient
convention `x/0 = 0`): the stage door needs no zero-avoidance hypothesis. -/
theorem seatMass_eq_zero_of_zero {s : ℂ} (h : ZD.riemannXi s = 0) :
    seatMass s = 0 := by
  unfold seatMass
  rw [logDeriv_apply, h, div_zero, Complex.zero_re, zero_div]

/-- **Stage-mass convergence**: value and derivative convergence at a
nonvanishing point carry the stage masses to the seat mass. -/
theorem stage_mass_tendsto {s : ℂ} (hne : ZD.riemannXi s ≠ 0)
    {G : ℕ → ℂ → ℂ}
    (hval : Tendsto (fun n => G n s) atTop (𝓝 (ZD.riemannXi s)))
    (hder : Tendsto (fun n => deriv (G n) s) atTop
      (𝓝 (deriv ZD.riemannXi s))) :
    Tendsto (fun n => (logDeriv (G n) s).re / (s.re - 1/2)) atTop
      (𝓝 (seatMass s)) := by
  have hdiv : Tendsto (fun n => deriv (G n) s / G n s) atTop
      (𝓝 (deriv ZD.riemannXi s / ZD.riemannXi s)) := hder.div hval hne
  have hre : Tendsto (fun n => (deriv (G n) s / G n s).re) atTop
      (𝓝 ((deriv ZD.riemannXi s / ZD.riemannXi s).re)) :=
    (Complex.continuous_re.tendsto _).comp hdiv
  have hfin := hre.div_const (s.re - 1/2)
  unfold seatMass
  simp only [logDeriv_apply]
  exact hfin

/-- **RH from stages** — arrow [A3] as a door: a stage family per channel
point with value+derivative convergence and eventual mass sign forces every
nontrivial zero onto the critical line. -/
theorem rh_of_stage_mass :
    ∃ A : ℝ, 0 < A ∧
      ((∀ s : ℂ, 1269/2 < |s.im| →
          A / (Real.log |s.im|)^9 < s.re → s.re < 1/2 →
          ZD.riemannXi s ≠ 0 →
          ∃ G : ℕ → ℂ → ℂ,
            Tendsto (fun n => G n s) atTop (𝓝 (ZD.riemannXi s)) ∧
            Tendsto (fun n => deriv (G n) s) atTop
              (𝓝 (deriv ZD.riemannXi s)) ∧
            ∀ᶠ n in atTop, 0 ≤ (logDeriv (G n) s).re / (s.re - 1/2)) →
        ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2) := by
  obtain ⟨A, hA0, hdoor⟩ := rh_of_channel_mass
  refine ⟨A, hA0, fun h => hdoor ?_⟩
  intro s him hlo hhi
  by_cases hz : ZD.riemannXi s = 0
  · rw [seatMass_eq_zero_of_zero hz]
  · obtain ⟨G, hval, hder, hev⟩ := h s him hlo hhi hz
    exact ge_of_tendsto (stage_mass_tendsto hz hval hder) hev

/-- **Mathlib RH from stages.** -/
theorem riemannHypothesis_of_stage_mass :
    ∃ A : ℝ, 0 < A ∧
      ((∀ s : ℂ, 1269/2 < |s.im| →
          A / (Real.log |s.im|)^9 < s.re → s.re < 1/2 →
          ZD.riemannXi s ≠ 0 →
          ∃ G : ℕ → ℂ → ℂ,
            Tendsto (fun n => G n s) atTop (𝓝 (ZD.riemannXi s)) ∧
            Tendsto (fun n => deriv (G n) s) atTop
              (𝓝 (deriv ZD.riemannXi s)) ∧
            ∀ᶠ n in atTop, 0 ≤ (logDeriv (G n) s).re / (s.re - 1/2)) →
        RiemannHypothesis) := by
  obtain ⟨A, hA0, h⟩ := rh_of_stage_mass
  exact ⟨A, hA0, fun hyp => RHBridge.no_offline_zeros_implies_rh (h hyp)⟩

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.seatMass_eq_zero_of_zero
#print axioms CriticalLinePhasor.SeatingLedger.stage_mass_tendsto
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_stage_mass
#print axioms CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_stage_mass
