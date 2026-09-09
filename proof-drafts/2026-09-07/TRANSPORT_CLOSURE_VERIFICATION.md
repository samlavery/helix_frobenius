# Transport closure verification

The two new library modules pass direct Lean checks and the targeted build. The arithmetic draft returns exit code 1 at the three recorded closure errors. Its RH declarations are unfinished.

## Geometric transport

```sh
lake env lean RequestProject/HelixSectionTransport.lean
```

Exit code: **0**.

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.HelixSectionTransport.phaseTransport_power_norm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.HelixSectionTransport.twoJetTransport_taylor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.HelixSectionTransport.twoJetTransport_not_power_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.HelixSectionTransport.twoJetTransport_power_sq_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Polynomial-growth purity

```sh
lake env lean RequestProject/WeilPolynomialGrowth.lean
```

Exit code: **0**.

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.WeilDuality.tensor_power_purity_of_polynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.WeilDuality.cup_polynomial_growth_gives_purity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.WeilDuality.purity_from_polynomial_castelnuovo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Targeted library build

```sh
lake build RequestProject.HelixSectionTransport RequestProject.WeilPolynomialGrowth
```

Exit code: **0**.

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
ℹ [3005/3176] Replayed RequestProject.FiniteCellSections
info: RequestProject/FiniteCellSections.lean:214:0: 'CriticalLinePhasor.FiniteCellSections.finrank_jetKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/FiniteCellSections.lean:215:0: 'CriticalLinePhasor.FiniteCellSections.finrank_jetRange' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/FiniteCellSections.lean:216:0: 'CriticalLinePhasor.FiniteCellSections.jetEvaluation_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/FiniteCellSections.lean:217:0: 'CriticalLinePhasor.FiniteCellSections.vanishing_forces_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/FiniteCellSections.lean:218:0: 'CriticalLinePhasor.FiniteCellSections.exists_nonzero_section_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
ℹ [8698/8712] Replayed RequestProject.ClosedForm
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
⚠ [8699/8712] Replayed RequestProject.LFunctionPhasor
warning: RequestProject/LFunctionPhasor.lean:1059:19: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: RequestProject/LFunctionPhasor.lean:1060:55: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: RequestProject/LFunctionPhasor.lean:1061:56: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: RequestProject/LFunctionPhasor.lean:1063:19: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: RequestProject/LFunctionPhasor.lean:1065:19: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: RequestProject/LFunctionPhasor.lean:1067:19: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: RequestProject/LFunctionPhasor.lean:1077:46: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
ℹ [8700/8712] Replayed RequestProject.CriticalLineBridge
info: RequestProject/CriticalLineBridge.lean:118:60: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
ℹ [8702/8712] Replayed RequestProject.FocalEigenheight
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
ℹ [8705/8712] Replayed RequestProject.GeometricReadout
info: RequestProject/GeometricReadout.lean:69:65: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: RequestProject/GeometricReadout.lean:102:36: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [8707/8712] Replayed RequestProject.GlobalHelixIntertwiner
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
ℹ [8708/8712] Replayed RequestProject.HelixCellSections3D
info: RequestProject/HelixCellSections3D.lean:109:0: 'CriticalLinePhasor.HelixCellSections3D.finrank_cellJets_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/HelixCellSections3D.lean:110:0: 'CriticalLinePhasor.HelixCellSections3D.cellJets_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/HelixCellSections3D.lean:111:0: 'CriticalLinePhasor.HelixCellSections3D.antiHelix_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/HelixCellSections3D.lean:112:0: 'CriticalLinePhasor.HelixCellSections3D.finrank_antiHelix_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
⚠ [8710/8712] Replayed RequestProject.WeilDuality
warning: RequestProject/WeilDuality.lean:129:4: `push_neg` has been deprecated. Prefer using `push Not` instead.
If you'd rather continue using `push_neg` in your project, you can implement it as follows:
```
open Lean.Parser.Tactic in
macro "push_neg" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| push $cfg:optConfig Not $[$loc]?)
```
ℹ [8711/8712] Built RequestProject.WeilPolynomialGrowth (12s)
info: RequestProject/WeilPolynomialGrowth.lean:75:0: 'CriticalLinePhasor.WeilDuality.tensor_power_purity_of_polynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/WeilPolynomialGrowth.lean:76:0: 'CriticalLinePhasor.WeilDuality.cup_polynomial_growth_gives_purity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/WeilPolynomialGrowth.lean:77:0: 'CriticalLinePhasor.WeilDuality.purity_from_polynomial_castelnuovo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
ℹ [8712/8712] Built RequestProject.HelixSectionTransport (12s)
info: RequestProject/HelixSectionTransport.lean:103:0: 'CriticalLinePhasor.HelixSectionTransport.phaseTransport_power_norm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/HelixSectionTransport.lean:104:0: 'CriticalLinePhasor.HelixSectionTransport.twoJetTransport_taylor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/HelixSectionTransport.lean:105:0: 'CriticalLinePhasor.HelixSectionTransport.twoJetTransport_not_power_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: RequestProject/HelixSectionTransport.lean:106:0: 'CriticalLinePhasor.HelixSectionTransport.twoJetTransport_power_sq_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Build completed successfully (8712 jobs).
```

## Unconditional arithmetic closure attempts

```sh
lake env lean proof-drafts/2026-09-07/TransportClosureAttempts.lean
```

Exit code: **1**.

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
proof-drafts/2026-09-07/TransportClosureAttempts.lean:36:4: error: linarith failed to find a contradiction
case hsim.h1
P : ℂ → ℝ :=
  fun ρ => ↑(Module.finrank ℂ ↥(sections (cellDivisor (fun x => GlobalHelix.circleReadout (1, 0, ρ.im)) fun x => 1) 2))
hP : ∀ (ρ : ℂ), P ρ = 1
ρ : ℂ
hρ : ρ ∈ ZD.NontrivialZeros
hdet : endPairFace ρ * endPairFace (1 - (starRingEnd ℂ) ρ) = 1
a✝ : Real.exp (ρ.re - 1 / 2) ^ 2 < 1
⊢ False
failed
case hsim
P : ℂ → ℝ :=
  fun ρ => ↑(Module.finrank ℂ ↥(sections (cellDivisor (fun x => GlobalHelix.circleReadout (1, 0, ρ.im)) fun x => 1) 2))
hP : ∀ (ρ : ℂ), P ρ = 1
ρ : ℂ
hρ : ρ ∈ ZD.NontrivialZeros
hdet : endPairFace ρ * endPairFace (1 - (starRingEnd ℂ) ρ) = 1
⊢ Real.exp (ρ.re - 1 / 2) ^ 2 = 1
proof-drafts/2026-09-07/TransportClosureAttempts.lean:52:6: error: Type mismatch: After simplification, term
  Eq.le (hphase k)
 has type
  ‖(phaseTransport (1, 0, ρ.im) ^ k) 1‖ ≤ 1
but is expected to have type
  ‖endPairFace ρ‖ ^ (2 * k) ≤ 1
proof-drafts/2026-09-07/TransportClosureAttempts.lean:55:6: error: Type mismatch: After simplification, term
  Eq.le (hphase k)
 has type
  ‖(phaseTransport (1, 0, ρ.im) ^ k) 1‖ ≤ 1
but is expected to have type
  ‖endPairFace (endExchange ρ)‖ ^ (2 * k) ≤ 1
case neg.refine_1
ρ : ℂ
hρ : ρ ∈ ZD.NontrivialZeros
hh : ¬|ρ.im| ≤ 1269 / 2
hphase : ∀ (k : ℕ), ‖(phaseTransport (1, 0, ρ.im) ^ k) 1‖ ^ 2 = 1
k : ℕ
⊢ ‖endPairFace ρ‖ ^ (2 * k) ≤ 1
case neg.refine_2
ρ : ℂ
hρ : ρ ∈ ZD.NontrivialZeros
hh : ¬|ρ.im| ≤ 1269 / 2
hphase : ∀ (k : ℕ), ‖(phaseTransport (1, 0, ρ.im) ^ k) 1‖ ^ 2 = 1
k : ℕ
⊢ ‖endPairFace (endExchange ρ)‖ ^ (2 * k) ≤ 1
'CriticalLinePhasor.CellEdgeDoor.riemannHypothesis_of_frobenius_weight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.FrobeniusWeightCandidateAudit.riemannHypothesis_of_two_sided_face_power_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Source scan

```sh
rg -n 'axiom |sorry|admit|@\[implemented_by\]|exact\?' RequestProject/HelixSectionTransport.lean RequestProject/WeilPolynomialGrowth.lean proof-drafts/2026-09-07/TransportClosureAttempts.lean
```

No matches. The arithmetic draft remains outside the library build glob and is explicitly incomplete; a clean source scan does not make its proof goals complete.

## Source hashes

```text
be74daa78410452765a9552566ba643d7c807e71739fa23bc0b7f1a68abd8cac  RequestProject/HelixSectionTransport.lean
61735a3966b99a6806967f9b125cd0bbd87b6c4ac6a35da57761cb0f93962c30  RequestProject/WeilPolynomialGrowth.lean
6245944d9befd40885f93d31ab3b5237f582493b48a9b7338964684d9dbad5f0  proof-drafts/2026-09-07/TransportClosureAttempts.lean
```

