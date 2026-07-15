import RequestProject.CPSArithmeticTwist3D

/-!
# One arithmetic CPS theta source for completion, reflection, and niceness

The polynomial Satake bank and its prescribed conductor/Gamma completion were previously read by
one pair of three-dimensional banks, while analytic continuation and the functional equation were
read from a second synthesized strong pair.  This file gives the exact typed unification point: a
single `StrongFEPair` whose primal and dual functions are the prescribed arithmetic 3D banks.

Once that source object is constructed, its Mellin transforms are the literal completed arithmetic
Euler readouts on the common initial half-plane, and the same object supplies the pointwise
reflection, entire continuation, vertical-strip bounds, and functional equation.
-/

open Complex Set MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

/-- A single reflected theta source carried by the literal arithmetic CPS 3D banks.  This is a
`Type`-valued source object, not a proposition equating an analytic zero set with a carrier set. -/
structure ArithmeticCPSReflectedThetaSource
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m))
    (D : ArithmeticCPSCompletionData r m) where
  pair : StrongFEPair ℂ
  primal_source : pair.f =
    cpsPolynomialFullPrimal3DBankReadout
      (arithmeticCPSPolynomialTwist r m pi tau) D.conductor D.tensorShifts
  dual_source : pair.g = fun x : ℝ =>
    cpsPolynomialFullDual3DTransformedReadout
      (arithmeticCPSPolynomialTwist r m pi tau) D.conductor D.tensorShifts (1 / x)

/-- The analytic datum consumed by a CPS converse theorem, with the continued functions tied on
their common initial domain to the literal arithmetic Euler products.  The continuation, its dual,
the root number, weight, strip bounds, functional equation, and native 3D reflection are fields of
one object. -/
structure ArithmeticCPSAnalyticCandidate3D
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m))
    (D : ArithmeticCPSCompletionData r m) where
  primalContinuation : ℂ → ℂ
  dualContinuation : ℂ → ℂ
  weight : ℝ
  weight_pos : 0 < weight
  rootNumber : ℂ
  rootNumber_ne_zero : rootNumber ≠ 0
  primal_entire : Differentiable ℂ primalContinuation
  dual_entire : Differentiable ℂ dualContinuation
  primal_boundedOn_verticalStrip : ∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
    u ≤ s.re → s.re ≤ v → ‖primalContinuation s‖ ≤ B
  dual_boundedOn_verticalStrip : ∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
    u ≤ s.re → s.re ≤ v → ‖dualContinuation s‖ ≤ B
  functionalEquation : ∀ s : ℂ,
    primalContinuation (weight - s) = rootNumber • dualContinuation s
  primal_initial : ∀ (hm : 0 < m)
      (point : CPSCompletionPoint
        (arithmeticCPSPolynomialTwist r m pi tau) (D.clock hm)),
    primalContinuation point.s =
      cpsPolynomialFullPrimalCompletedReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts point.s
  dual_initial : ∀ (hm : 0 < m)
      (point : CPSCompletionPoint
        (arithmeticCPSPolynomialTwist r m pi tau) (D.clock hm)),
    dualContinuation point.s =
      cpsPolynomialFullDualCompletedReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts point.s
  native3DReflection : ∀ x : ℝ, 0 < x →
    cpsPolynomialFullPrimal3DBankReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts (1 / x) =
      (rootNumber * (x ^ weight : ℝ)) •
        cpsPolynomialFullDual3DTransformedReadout
          (arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts (1 / x)

namespace ArithmeticCPSReflectedThetaSource

variable {r m : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
  {tau : PolynomialSatakeDualPair (Fin m)}
  {D : ArithmeticCPSCompletionData r m}

/-- The primal local-integrability field required by the strong source is derived from the literal
arithmetic coefficient bank and its prescribed tensor-shift Gamma completion. -/
theorem prescribedPrimal_locallyIntegrableOn (hm : 0 < m) :
    LocallyIntegrableOn
      (cpsPolynomialFullPrimal3DBankReadout
        (arithmeticCPSPolynomialTwist r m pi tau) D.conductor D.tensorShifts)
      (Ioi 0) := by
  have hne : D.tensorShifts ≠ [] := by
    simpa [ArithmeticCPSCompletionData.clock] using (D.clock hm).shifts_nonempty
  exact cpsPolynomialFullPrimal3DBankReadout_locallyIntegrableOn
    (arithmeticCPSPolynomialTwist r m pi tau)
    D.conductor D.conductor_pos D.tensorShifts hne

/-- The dual local-integrability field is derived for the exact reciprocal-height transformed
contragredient bank used by `ArithmeticCPSReflectedThetaSource`. -/
theorem prescribedDual_locallyIntegrableOn (hm : 0 < m) :
    LocallyIntegrableOn
      (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout
        (arithmeticCPSPolynomialTwist r m pi tau) D.conductor D.tensorShifts (1 / x))
      (Ioi 0) := by
  have hne : D.tensorShifts ≠ [] := by
    simpa [ArithmeticCPSCompletionData.clock] using (D.clock hm).shifts_nonempty
  exact cpsPolynomialFullDual3DReflectedReadout_locallyIntegrableOn
    (arithmeticCPSPolynomialTwist r m pi tau)
    D.conductor D.conductor_pos D.tensorShifts hne

/-- Canonical one-source construction from the assembled arithmetic analytic candidate.  Its
pointwise native reflection becomes the `StrongFEPair` reflection field, while local integrability
and rapid decay are derived independently from the literal prescribed primal and dual banks. -/
noncomputable def ofAnalyticCandidate
    (hm : 0 < m) (A : ArithmeticCPSAnalyticCandidate3D r m pi tau D) :
    ArithmeticCPSReflectedThetaSource r m pi tau D where
  pair := {
    toWeakFEPair := {
      f := cpsPolynomialFullPrimal3DBankReadout
        (arithmeticCPSPolynomialTwist r m pi tau) D.conductor D.tensorShifts
      g := fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout
        (arithmeticCPSPolynomialTwist r m pi tau) D.conductor D.tensorShifts (1 / x)
      k := A.weight
      ε := A.rootNumber
      f₀ := 0
      g₀ := 0
      hf_int := prescribedPrimal_locallyIntegrableOn hm
      hg_int := prescribedDual_locallyIntegrableOn hm
      hk := A.weight_pos
      hε := A.rootNumber_ne_zero
      h_feq := A.native3DReflection
      hf_top := fun q => by
        simpa using cpsPolynomialFullPrimal3DBankReadout_rapid
          (arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.conductor_pos D.tensorShifts q
      hg_top := fun q => by
        simpa using cpsPolynomialFullDual3DReflectedReadout_rapid
          (arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.conductor_pos D.tensorShifts q
    }
    hf₀ := rfl
    hg₀ := rfl
  }
  primal_source := rfl
  dual_source := rfl

/-- The canonical source reads back the candidate's exact off-weld reflection with no change of
coefficient bank, completion kernel, conductor, weight, or root number. -/
theorem ofAnalyticCandidate_prescribed3D_reflection
    (hm : 0 < m) (A : ArithmeticCPSAnalyticCandidate3D r m pi tau D) :
    ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout
          (arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts (1 / x) =
        (A.rootNumber * (x ^ A.weight : ℝ)) •
          cpsPolynomialFullDual3DTransformedReadout
            (arithmeticCPSPolynomialTwist r m pi tau)
            D.conductor D.tensorShifts (1 / x) := by
  intro x hx
  exact (ofAnalyticCandidate hm A).pair.h_feq x hx

/-- The primal Mellin transform of the unified source is the prescribed completed arithmetic
Euler readout. -/
theorem primal_initialIdentification
    (S : ArithmeticCPSReflectedThetaSource r m pi tau D)
    (hm : 0 < m)
    (point : CPSCompletionPoint (arithmeticCPSPolynomialTwist r m pi tau) (D.clock hm)) :
    S.pair.Λ point.s =
      cpsPolynomialFullPrimalCompletedReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts point.s := by
  calc
    S.pair.Λ point.s = mellin S.pair.f point.s := (S.pair.hasMellin point.s).2.symm
    _ = mellin (cpsPolynomialFullPrimal3DBankReadout
          (arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts) point.s := by rw [S.primal_source]
    _ = cpsPolynomialFullPrimalCompletedReadout
          (arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts point.s :=
      (arithmeticCPSFullCompletion3D_identification r m hm pi tau D point).1

/-- The dual Mellin transform of the same source is the prescribed completed contragredient Euler
readout. -/
theorem dual_initialIdentification
    (S : ArithmeticCPSReflectedThetaSource r m pi tau D)
    (hm : 0 < m)
    (point : CPSCompletionPoint (arithmeticCPSPolynomialTwist r m pi tau) (D.clock hm)) :
    S.pair.symm.Λ point.s =
      cpsPolynomialFullDualCompletedReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts point.s := by
  calc
    S.pair.symm.Λ point.s = mellin S.pair.g point.s := by
      exact (S.pair.symm.hasMellin point.s).2.symm
    _ = mellin (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout
          (arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts (1 / x)) point.s := by rw [S.dual_source]
    _ = cpsPolynomialFullDualCompletedReadout
          (arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts point.s :=
      (arithmeticCPSFullCompletion3D_identification r m hm pi tau D point).2

/-- The strong-pair reflection is a pointwise reflection of the same prescribed arithmetic 3D
banks; no second coefficient or completion kernel occurs. -/
theorem prescribed3D_reflection
    (S : ArithmeticCPSReflectedThetaSource r m pi tau D) :
    ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout
          (arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts (1 / x) =
        (S.pair.ε * (x ^ S.pair.k : ℝ)) •
          cpsPolynomialFullDual3DTransformedReadout
            (arithmeticCPSPolynomialTwist r m pi tau)
            D.conductor D.tensorShifts (1 / x) := by
  intro x hx
  have h := S.pair.h_feq x hx
  rw [S.primal_source, S.dual_source] at h
  exact h

/-- Entire continuation, vertical-strip boundedness, and the functional equation all belong to the
same prescribed arithmetic theta source. -/
theorem analyticPayload
    (S : ArithmeticCPSReflectedThetaSource r m pi tau D) :
    Differentiable ℂ S.pair.Λ ∧
    Differentiable ℂ S.pair.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖S.pair.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖S.pair.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, S.pair.Λ (S.pair.k - s) = S.pair.ε • S.pair.symm.Λ s) := by
  exact ⟨S.pair.differentiable_Λ, S.pair.symm.differentiable_Λ,
    fun u v =>
      CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
        S.pair u v,
    fun u v =>
      CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
        S.pair.symm u v,
    S.pair.functional_equation⟩

/-- The single reflected arithmetic 3D source constructs the complete analytic input expected by
the CPS converse theorem.  In particular, the entire functions are not free replacements for the
Euler products: `primal_initial` and `dual_initial` identify them with the prescribed arithmetic
completions wherever those products are initially defined. -/
noncomputable def analyticCandidate
    (S : ArithmeticCPSReflectedThetaSource r m pi tau D) :
    ArithmeticCPSAnalyticCandidate3D r m pi tau D where
  primalContinuation := S.pair.Λ
  dualContinuation := S.pair.symm.Λ
  weight := S.pair.k
  weight_pos := S.pair.hk
  rootNumber := S.pair.ε
  rootNumber_ne_zero := S.pair.hε
  primal_entire := S.pair.differentiable_Λ
  dual_entire := S.pair.symm.differentiable_Λ
  primal_boundedOn_verticalStrip := fun u v =>
    CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
      S.pair u v
  dual_boundedOn_verticalStrip := fun u v =>
    CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip
      S.pair.symm u v
  functionalEquation := S.pair.functional_equation
  primal_initial := S.primal_initialIdentification
  dual_initial := S.dual_initialIdentification
  native3DReflection := S.prescribed3D_reflection

/-- One-source capstone: literal arithmetic local/global coefficients, both standard completed
Mellin identifications, pointwise 3D reflection, entirety, strip bounds, and the functional equation
are assembled without changing the Satake input. -/
theorem unified
    (S : ArithmeticCPSReflectedThetaSource r m pi tau D)
    (hm : 0 < m)
    (point : CPSCompletionPoint (arithmeticCPSPolynomialTwist r m pi tau) (D.clock hm)) :
    ArithmeticCPSCoefficientPassport r m pi tau ∧
    S.pair.Λ point.s =
      cpsPolynomialFullPrimalCompletedReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts point.s ∧
    S.pair.symm.Λ point.s =
      cpsPolynomialFullDualCompletedReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts point.s ∧
    (∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout
          (arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts (1 / x) =
        (S.pair.ε * (x ^ S.pair.k : ℝ)) •
          cpsPolynomialFullDual3DTransformedReadout
            (arithmeticCPSPolynomialTwist r m pi tau)
            D.conductor D.tensorShifts (1 / x)) ∧
    Differentiable ℂ S.pair.Λ ∧
    Differentiable ℂ S.pair.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖S.pair.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖S.pair.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, S.pair.Λ (S.pair.k - s) = S.pair.ε • S.pair.symm.Λ s) := by
  refine ⟨arithmeticCPSCoefficientPassport r m pi tau,
    S.primal_initialIdentification hm point,
    S.dual_initialIdentification hm point,
    S.prescribed3D_reflection, ?_⟩
  exact S.analyticPayload

/-- The canonical source constructed from the assembled candidate discharges the complete
one-source payload for every common initial-half-plane point. -/
theorem ofAnalyticCandidate_unified
    (hm : 0 < m) (A : ArithmeticCPSAnalyticCandidate3D r m pi tau D)
    (point : CPSCompletionPoint
      (arithmeticCPSPolynomialTwist r m pi tau) (D.clock hm)) :
    let S := ofAnalyticCandidate hm A
    ArithmeticCPSCoefficientPassport r m pi tau ∧
    S.pair.Λ point.s =
      cpsPolynomialFullPrimalCompletedReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts point.s ∧
    S.pair.symm.Λ point.s =
      cpsPolynomialFullDualCompletedReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts point.s ∧
    (∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout
          (arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts (1 / x) =
        (S.pair.ε * (x ^ S.pair.k : ℝ)) •
          cpsPolynomialFullDual3DTransformedReadout
            (arithmeticCPSPolynomialTwist r m pi tau)
            D.conductor D.tensorShifts (1 / x)) ∧
    Differentiable ℂ S.pair.Λ ∧
    Differentiable ℂ S.pair.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖S.pair.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖S.pair.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, S.pair.Λ (S.pair.k - s) = S.pair.ε • S.pair.symm.Λ s) := by
  exact (ofAnalyticCandidate hm A).unified hm point

/-- Reassemble the analytic candidate from the canonical literal-bank source.  The resulting
entire functions and strip bounds are those constructed by the prescribed-bank `StrongFEPair`. -/
noncomputable def reassembledAnalyticCandidate
    (hm : 0 < m) (A : ArithmeticCPSAnalyticCandidate3D r m pi tau D) :
    ArithmeticCPSAnalyticCandidate3D r m pi tau D :=
  (ofAnalyticCandidate hm A).analyticCandidate

end ArithmeticCPSReflectedThetaSource

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticCPSReflectedThetaSource.primal_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticCPSReflectedThetaSource.prescribedPrimal_locallyIntegrableOn
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticCPSReflectedThetaSource.prescribedDual_locallyIntegrableOn
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticCPSReflectedThetaSource.ofAnalyticCandidate
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticCPSReflectedThetaSource.ofAnalyticCandidate_prescribed3D_reflection
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticCPSReflectedThetaSource.dual_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticCPSReflectedThetaSource.prescribed3D_reflection
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticCPSReflectedThetaSource.analyticPayload
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticCPSReflectedThetaSource.analyticCandidate
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticCPSReflectedThetaSource.unified
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticCPSReflectedThetaSource.ofAnalyticCandidate_unified
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticCPSReflectedThetaSource.reassembledAnalyticCandidate
