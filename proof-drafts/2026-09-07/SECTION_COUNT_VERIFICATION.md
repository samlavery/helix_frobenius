# Section-count verification — September 7

All four commands below returned exit code **0**. Output blocks reproduce the complete captured stdout/stderr. The package-local-changes warning was present before these edits.

## Generic finite sections

```sh
lake env lean RequestProject/FiniteCellSections.lean
```

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.FiniteCellSections.finrank_jetKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.FiniteCellSections.finrank_jetRange' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.FiniteCellSections.jetEvaluation_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.FiniteCellSections.vanishing_forces_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.FiniteCellSections.exists_nonzero_section_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 3D carrier attachment

```sh
lake env lean RequestProject/HelixCellSections3D.lean
```

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.HelixCellSections3D.finrank_cellJets_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.HelixCellSections3D.cellJets_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.HelixCellSections3D.antiHelix_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.HelixCellSections3D.finrank_antiHelix_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Existing route consumers and geometric prerequisites

```sh
lake env lean proof-drafts/2026-09-07/RouteAxiomAudit.lean
```

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_explicit_stage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_explicit_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.CaptureInterfaceAudit.riemannHypothesis_of_integratedDefectSublinear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.CaptureInterfaceAudit.grh_of_regularCorrectionTraceLimit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.Cascade.rh_of_sourceLabelled_cascade' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.WeilDuality.purity_from_castelnuovo' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ChiralCup.cup_positive_semidefinite' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.HodgeLedgerFiltration.NeronSeveriRung.pairCoord_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.HodgeLedgerFiltration.NeronSeveriRung.readout_is_pairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiChannel.semiconj_of_ledger_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.Pencil3D.eigenvalue_real_of_pencil_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.GlobalHelix.circleReadout_globalHelixInvolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.GlobalHelix.circleReadout_norm_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.GlobalHelix.analyticOrdinate_eq_height' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Targeted build including both new modules

```sh
lake build RequestProject.HelixCellSections3D
```

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
ℹ [8697/8708] Replayed RequestProject.ClosedForm
info: RequestProject/ClosedForm.lean:232:378: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:233:49: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:234:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:261:75: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:262:36: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:276:79: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:443:86: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:444:29: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:668:74: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:670:93: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:690:183: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:694:193: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:695:206: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:696:103: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:696:131: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:697:66: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:697:94: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:698:99: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:698:127: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:702:66: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:703:48: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:712:135: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:845:85: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:860:100: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:861:160: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:862:161: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:1297:74: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:1306:8: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:1318:6: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:1320:61: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:1321:131: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:1322:145: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:1323:97: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:1453:115: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/ClosedForm.lean:1555:24: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [8698/8708] Replayed RequestProject.LFunctionPhasor
warning: RequestProject/LFunctionPhasor.lean:1059:19: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: RequestProject/LFunctionPhasor.lean:1060:55: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: RequestProject/LFunctionPhasor.lean:1061:56: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: RequestProject/LFunctionPhasor.lean:1063:19: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: RequestProject/LFunctionPhasor.lean:1065:19: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: RequestProject/LFunctionPhasor.lean:1067:19: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: RequestProject/LFunctionPhasor.lean:1077:46: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
ℹ [8699/8708] Replayed RequestProject.CriticalLineBridge
info: RequestProject/CriticalLineBridge.lean:118:60: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [8701/8708] Replayed RequestProject.FocalEigenheight
info: RequestProject/FocalEigenheight.lean:191:153: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/FocalEigenheight.lean:193:78: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/FocalEigenheight.lean:237:51: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/FocalEigenheight.lean:238:88: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [8704/8708] Replayed RequestProject.GeometricReadout
info: RequestProject/GeometricReadout.lean:69:65: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/GeometricReadout.lean:102:36: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [8706/8708] Replayed RequestProject.GlobalHelixIntertwiner
warning: RequestProject/GlobalHelixIntertwiner.lean:116:42: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
warning: RequestProject/GlobalHelixIntertwiner.lean:116:42: 'norm_num' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
warning: RequestProject/GlobalHelixIntertwiner.lean:123:38: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
info: RequestProject/GlobalHelixIntertwiner.lean:139:0: 'CriticalLinePhasor.GlobalHelix.globalHelixInvolution_involutive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/GlobalHelixIntertwiner.lean:140:0: 'CriticalLinePhasor.GlobalHelix.realize_globalHelixInvolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/GlobalHelixIntertwiner.lean:141:0: 'CriticalLinePhasor.GlobalHelix.reconstruct_record_globalHelixInvolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/GlobalHelixIntertwiner.lean:142:0: 'CriticalLinePhasor.GlobalHelix.circleReadout_globalHelixInvolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/GlobalHelixIntertwiner.lean:143:0: 'CriticalLinePhasor.GlobalHelix.circleReadout_norm_one' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/GlobalHelixIntertwiner.lean:144:0: 'CriticalLinePhasor.GlobalHelix.multiplicativeHeight_globalHelixInvolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/GlobalHelixIntertwiner.lean:145:0: 'CriticalLinePhasor.GlobalHelix.analyticOrdinate_globalHelixInvolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/GlobalHelixIntertwiner.lean:146:0: 'CriticalLinePhasor.GlobalHelix.stripReadout_globalHelixInvolution_conj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/GlobalHelixIntertwiner.lean:147:0: 'CriticalLinePhasor.GlobalHelix.stripReadout_globalHelixInvolution_one_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/GlobalHelixIntertwiner.lean:148:0: 'CriticalLinePhasor.GlobalHelix.stripReadout_fixed_iff_half' depends on axioms: [propext, Classical.choice, Quot.sound]
ℹ [8707/8708] Built RequestProject.FiniteCellSections (6.2s)
info: RequestProject/FiniteCellSections.lean:214:0: 'CriticalLinePhasor.FiniteCellSections.finrank_jetKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/FiniteCellSections.lean:215:0: 'CriticalLinePhasor.FiniteCellSections.finrank_jetRange' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/FiniteCellSections.lean:216:0: 'CriticalLinePhasor.FiniteCellSections.jetEvaluation_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/FiniteCellSections.lean:217:0: 'CriticalLinePhasor.FiniteCellSections.vanishing_forces_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/FiniteCellSections.lean:218:0: 'CriticalLinePhasor.FiniteCellSections.exists_nonzero_section_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
ℹ [8708/8708] Built RequestProject.HelixCellSections3D (18s)
info: RequestProject/HelixCellSections3D.lean:109:0: 'CriticalLinePhasor.HelixCellSections3D.finrank_cellJets_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/HelixCellSections3D.lean:110:0: 'CriticalLinePhasor.HelixCellSections3D.cellJets_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/HelixCellSections3D.lean:111:0: 'CriticalLinePhasor.HelixCellSections3D.antiHelix_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/HelixCellSections3D.lean:112:0: 'CriticalLinePhasor.HelixCellSections3D.finrank_antiHelix_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Build completed successfully (8708 jobs).
```

## Source scan

```sh
rg -n 'axiom |sorry|admit|@\[implemented_by\]|exact\?' RequestProject/FiniteCellSections.lean RequestProject/HelixCellSections3D.lean proof-drafts/2026-09-07/RouteAxiomAudit.lean
```

No output; exit code **1**, the `rg` no-match result.

## SHA-256 of the verified source files

```text
d8c05f00c430b6dd817c29373d228dbb32c5da1230356974cc39b28147fd5a0b  RequestProject/FiniteCellSections.lean
c8bfcd710c0d10295753cef88eb13b1572ef3cd8a41a690c15d2b8c1c2724441  RequestProject/HelixCellSections3D.lean
256d4a8a60940068bc14499d1e0b3c249d7778c8b3a3651f98bfa8e788dbf8f9  proof-drafts/2026-09-07/RouteAxiomAudit.lean
```

The final targeted build rebuilt the generic module after the explicit nonzero-section criterion was added, then built the unchanged 3D attachment against that module. The direct checks above verified the final source of each file. No RH/GRH declaration or executable unfinished target was changed.

