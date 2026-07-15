import RequestProject.GeneralExtensionRetention
import RequestProject.CeresaGrossSchoenLanding

/-!
# Assembly into unrestricted source exhaustion

The finite-extension tower supplies retention at every finite jet order.  The grade-zero/one source
constructor and the higher-grade radial--Torelli--cycle package supply recognition on the two
exhaustive grade cases.  This file performs the final specialization to the general extension dial.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- The complete finite-extension capstone.  There is no semisimple restriction and no singled-out
grade in the conclusion: every nonzero rational DC state in the general extension dial has an
algebraic source. -/
theorem generalExtension_sourceExhaustion_of_gradeSplit_sourceConstruction
    {order m : ℕ} (bank : DistinctClockBank m)
    (Algebraic : GeneralExtensionData order m → Prop)
    {AngularDossier RadialDossier Curve Cycle IsogClass LowSource : Type*}
    (higher : HigherGradeRecognitionPackage
      (generalExtensionDial bank Algebraic)
      AngularDossier RadialDossier Curve Cycle IsogClass)
    (lower : AtMostGradeOneSourceConstructor
      (generalExtensionDial bank Algebraic) higher.grade LowSource) :
    SourceExhaustion (generalExtensionDial bank Algebraic) :=
  sourceExhaustion_of_retention_gradeSplit_sourceConstruction
    (generalExtension_retention bank Algebraic) higher lower

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.generalExtension_sourceExhaustion_of_gradeSplit_sourceConstruction
