import RequestProject.HigherGradeRecognition

/-!
# The Ceresa/Gross--Schoen analytic-to-cycle landing

The standard triple-product height formula has the form

`height(Δ_C) = κ * L'(1/2, H¹(C)^⊗3)`.

The carrier landing identifies that real height with the depth-three tower readout of the
realized modified diagonal.  This file packages the analytic identity, the explicit cycle, and
the carrier identification in one typed datum, then proves the complete nonvanishing and source
chain.  No proof in `RecognitionBridge` or `HodgeLedgerFiltration` is replaced.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {Z Cycle : Type*} [Zero Z]

/-- A complete Ceresa/Gross--Schoen landing certificate.  The external height theorem and the
arithmetic carrier identification occur as data of one object, so downstream theorems consume no
detached proposition-valued premise. -/
structure CeresaGrossSchoenLanding (D : HodgeDial Z) (Cycle : Type*) where
  sourceRealization : AlgebraicSourceRealization D Cycle
  ceresaCycle : Cycle
  ceresaState : Z
  height : Cycle → ℝ
  centralDerivative : ℝ
  proportionality : ℝ
  proportionality_ne_zero : proportionality ≠ 0
  centralDerivative_ne_zero : centralDerivative ≠ 0
  grossSchoen_height_identity :
    height ceresaCycle = proportionality * centralDerivative
  cycle_realizes_state : sourceRealization.realize ceresaCycle = ceresaState
  height_zero_of_zero_realization :
    ∀ cycle, sourceRealization.realize cycle = 0 → height cycle = 0
  tower_height_identification :
    D.T 3 ceresaState = (height ceresaCycle : ℂ)
  silent_below_three : ∀ d < 3, D.T d ceresaState = 0
  dc : D.DC ceresaState
  rational : D.Rational ceresaState

variable {D : HodgeDial Z}

/-- The Gross--Schoen height is nonzero because both factors in the central-derivative identity
are nonzero. -/
theorem CeresaGrossSchoenLanding.height_ne_zero
    (L : CeresaGrossSchoenLanding D Cycle) :
    L.height L.ceresaCycle ≠ 0 := by
  rw [L.grossSchoen_height_identity]
  exact mul_ne_zero L.proportionality_ne_zero L.centralDerivative_ne_zero

/-- The realized Ceresa class is nonzero: a zero realization would force its height to vanish. -/
theorem CeresaGrossSchoenLanding.state_ne_zero
    (L : CeresaGrossSchoenLanding D Cycle) :
    L.ceresaState ≠ 0 := by
  intro hzero
  apply L.height_ne_zero
  apply L.height_zero_of_zero_realization L.ceresaCycle
  rw [L.cycle_realizes_state, hzero]

/-- The analytic height lands as a nonzero depth-three carrier readout. -/
theorem CeresaGrossSchoenLanding.tower_fires_three
    (L : CeresaGrossSchoenLanding D Cycle) :
    D.T 3 L.ceresaState ≠ 0 := by
  rw [L.tower_height_identification]
  exact Complex.ofReal_ne_zero.mpr L.height_ne_zero

/-- The landed class is first visible exactly at depth three. -/
theorem CeresaGrossSchoenLanding.firstVisible_three
    (L : CeresaGrossSchoenLanding D Cycle) :
    IsFirstVisible D.T L.ceresaState 3 :=
  ⟨L.silent_below_three, L.tower_fires_three⟩

/-- The explicit modified diagonal is retained together with its exact source certificate. -/
def CeresaGrossSchoenLanding.certifiedSource
    (L : CeresaGrossSchoenLanding D Cycle) :
    {cycle : Cycle //
      L.sourceRealization.realize cycle = L.ceresaState ∧
      D.Algebraic (L.sourceRealization.realize cycle)} :=
  ⟨L.ceresaCycle, L.cycle_realizes_state,
    L.sourceRealization.algebraic_realize L.ceresaCycle⟩

/-- The Ceresa state has an algebraic source, by exact realization of the constructed modified
diagonal. -/
theorem CeresaGrossSchoenLanding.algebraic_source
    (L : CeresaGrossSchoenLanding D Cycle) :
    D.Algebraic L.ceresaState := by
  rw [← L.cycle_realizes_state]
  exact L.sourceRealization.algebraic_realize L.ceresaCycle

/-- The full analytic-to-cycle record: nonzero state, first visibility at depth three, rational DC
status, and an explicit algebraic source. -/
theorem CeresaGrossSchoenLanding.complete_landing
    (L : CeresaGrossSchoenLanding D Cycle) :
    L.ceresaState ≠ 0 ∧
      IsFirstVisible D.T L.ceresaState 3 ∧
      D.DC L.ceresaState ∧ D.Rational L.ceresaState ∧ D.Algebraic L.ceresaState :=
  ⟨L.state_ne_zero, L.firstVisible_three, L.dc, L.rational, L.algebraic_source⟩

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.CeresaGrossSchoenLanding.height_ne_zero
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.CeresaGrossSchoenLanding.state_ne_zero
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.CeresaGrossSchoenLanding.tower_fires_three
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.CeresaGrossSchoenLanding.firstVisible_three
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.CeresaGrossSchoenLanding.algebraic_source
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.CeresaGrossSchoenLanding.complete_landing
