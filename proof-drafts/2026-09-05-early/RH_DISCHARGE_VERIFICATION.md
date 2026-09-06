# RH/GRH draft verification — September 5, 2026

The four companion proof files below passed their direct compiler gates. The RH/GRH drafts retain explicitly marked unfinished leaves.

## StationRegistrationScopeAudit.lean

Command: `lake env lean RequestProject/StationRegistrationScopeAudit.lean`

Exit code: `0`.

Source SHA-256: `efac3e4fda71d19ae2ff9069eb6c08c224289356e6ce1b8bce02186afc207ef9`.

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.XiChannel.StationRegistration.ordinate_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiChannel.stationRegistration_not_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## RegistrationResidualSupport.lean

Command: `lake env lean RequestProject/RegistrationResidualSupport.lean`

Exit code: `0`.

Source SHA-256: `610e2281b9fdcc0cacfc7adde4a6060c55cc5429f709f6d4e4c8354770af276b`.

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.ContourArgument.primeStation_le_58_of_level_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.resid_eq_classicalS_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.adjacent_resid_eq_band_sub_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.onePerGap_of_adjacent_resid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.prime_gap_count_of_adjacent_resid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## PositiveStationRegistration.lean

Command: `lake env lean RequestProject/PositiveStationRegistration.lean`

Exit code: `0`.

Source SHA-256: `f9ba650de1be42b27cfa4debf6b977948fca5a91f4d87ca72330a0c06e30ab1a`.

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.XiChannel.PositiveStationRegistration.ordinate_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiChannel.PositiveStationRegistration.online_simple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiChannel.PositiveStationRegistration.all_online_simple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiChannel.PositiveStationRegistration.semiconj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## StripTraceCapture.lean

Command: `lake env lean RequestProject/StripTraceCapture.lean`

Exit code: `0`.

Source SHA-256: `d27f214e6ab8c4908d0c5af8aa98323c5a13cd4c59dcc7f23c48a824af8e7263`.

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.CaptureInterfaceAudit.isOpen_stripOffReal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.CaptureInterfaceAudit.normalizedLTrace_resonates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.CaptureInterfaceAudit.grh_of_stripTraceLimit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Source scan

Command:

```sh
rg 'axiom |sorry|admit|@\[implemented_by\]' RequestProject/StationRegistrationScopeAudit.lean RequestProject/RegistrationResidualSupport.lean RequestProject/PositiveStationRegistration.lean RequestProject/StripTraceCapture.lean
```

Exit code: `1` (no matches); output empty.

## Targeted builds

Command: `lake build RequestProject.RegistrationDC RequestProject.PrimeStrain RequestProject.StationRegistrationIntertwining RequestProject.PrimeSymbolReconciliation RequestProject.XiStageMass`

Exit code: `0`. Completion output (excerpt):

```text
Build completed successfully (9570 jobs).
```

Command: `lake build RequestProject.RegistrationResidualSupport RequestProject.StationRegistrationScopeAudit`

Exit code: `0`. Completion output (excerpt):

```text
Build completed successfully (9556 jobs).
```

Command: `lake build RequestProject.PositiveStationRegistration RequestProject.StripTraceCapture`

Exit code: `0`. Completion output (excerpt):

```text
Build completed successfully (9552 jobs).
```

## Dependency audit

Command: `lake env lean /private/tmp/rh-draft-dependency-audit.lean`

Exit code: `0`. All 19 printed footprints have exactly the three standard axioms below. These checks concern the statements as declared, including their explicit hypotheses.

Audit source:

```lean
import RequestProject.RegistrationDC
import RequestProject.PrimeStrain
import RequestProject.PrimeSymbolReconciliation
import RequestProject.XiStageMass
import RequestProject.HelixHeightDischarge
import RequestProject.HelixLineTowerCapture

#print axioms CriticalLinePhasor.ContourArgument.nontrivialZeros_online_of_primeResid
#print axioms CriticalLinePhasor.ContourArgument.nontrivialZeros_online_of_onePerGap_of_le_58
#print axioms CriticalLinePhasor.ContourArgument.resid_station_abs_le
#print axioms CriticalLinePhasor.ContourArgument.net_defect_le
#print axioms CriticalLinePhasor.ContourArgument.rh_iff_prime_jets_nonneg
#print axioms CriticalLinePhasor.ContourArgument.rh_iff_prime_symbol_nonneg
#print axioms CriticalLinePhasor.ContourArgument.PrimeClock.primeJetsForm_eq_dc_add_phase
#print axioms CriticalLinePhasor.ContourArgument.PrimeClock.primeSymbol_actual_minor12_neg
#print axioms CriticalLinePhasor.ContourArgument.PrimeClock.quadraticSymbol_not_scalar_square
#print axioms CriticalLinePhasor.ContourArgument.PrimeSymbolReconciliation.clock_primeSymbol_eq
#print axioms CriticalLinePhasor.XiKernelBridge.xiArithmeticStage_tendsto
#print axioms CriticalLinePhasor.XiKernelBridge.deriv_xiArithmeticStage_tendsto
#print axioms CriticalLinePhasor.XiKernelBridge.xiArithmeticStage_mass_formula
#print axioms CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_stage_mass
#print axioms CriticalLinePhasor.XiChannel.semiconj_of_kernel_descent
#print axioms CriticalLinePhasor.XiChannel.semiconj_of_green_transport
#print axioms CriticalLinePhasor.XiChannel.semiconj_of_ledger_symmetric
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.re_half_of_traceLimit
#print axioms HelixLimit.resonates_of_traceIdentity
```

Literal output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
'CriticalLinePhasor.ContourArgument.nontrivialZeros_online_of_primeResid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.nontrivialZeros_online_of_onePerGap_of_le_58' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.resid_station_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.net_defect_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.rh_iff_prime_jets_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.ContourArgument.rh_iff_prime_symbol_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.PrimeClock.primeJetsForm_eq_dc_add_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.PrimeClock.primeSymbol_actual_minor12_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.PrimeClock.quadraticSymbol_not_scalar_square' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.ContourArgument.PrimeSymbolReconciliation.clock_primeSymbol_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiKernelBridge.xiArithmeticStage_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.XiKernelBridge.deriv_xiArithmeticStage_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiKernelBridge.xiArithmeticStage_mass_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_stage_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiChannel.semiconj_of_kernel_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.XiChannel.semiconj_of_green_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.XiChannel.semiconj_of_ledger_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.CaptureInterfaceAudit.re_half_of_traceLimit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'HelixLimit.resonates_of_traceIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Draft elaboration probes

These runs intentionally exit with code `1` at the named `fail` command. An isolated named-leaf error verifies the surrounding assembly only; it is not a proof of the remaining goal. The executable snippets are in `RH_DISCHARGE_DRAFTS.md`.

### Draft A

Command: `lake env lean /private/tmp/rh-discharge-draft-1.lean`

Exit code: `1`. Literal output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
/private/tmp/rh-discharge-draft-1.lean:20:2: error: A: construct the cutoff, start index, and strict adjacent residual estimate
⊢ ∃ X n₀,
    regClock (primeStrain X) 10 < stationLevel n₀ ∧
      stationLevel n₀ ≤ regClock (primeStrain X) 58 ∧
        ∀ (n : ℕ),
          n₀ ≤ n → |resid (primeStrain X) (primeStation X (n + 1)) - resid (primeStrain X) (primeStation X n)| < 1
```

### Draft B

Command: `lake env lean /private/tmp/rh-discharge-draft-2.lean`

Exit code: `1`. Literal output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
/private/tmp/rh-discharge-draft-2.lean:13:2: error: B: nonnegativity of the full DC plus correlated prime-power phase sum
γ σ : ℝ
hσ : 1 < σ
hσupper : σ < 3 / 2
R : Polynomial ℂ
hR : R.coeff 0 = 0
⊢ 0 ≤
    PrimeClock.dcForm R (↑σ + ↑γ * I) ↑(2 * σ - 1) +
      ∑' (n : ℕ),
        ArithmeticFunction.vonMangoldt n * ↑n ^ (-σ) *
          (PrimeClock.phase γ (Real.log ↑n) * PrimeClock.primeSymbol R (2 * σ - 1) (Real.log ↑n)).re
```

### Draft C

Command: `lake env lean /private/tmp/rh-discharge-draft-3.lean`

Exit code: `1`. Literal output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
/private/tmp/rh-discharge-draft-3.lean:12:2: error: C: eventual theta-stage mass sign at this channel point
A : ℝ
hA : 0 < A
hdoor :
  (∀ (s : ℂ),
      1269 / 2 < |s.im| →
        A / Real.log |s.im| ^ 9 < s.re →
          s.re < 1 / 2 →
            ZD.riemannXi s ≠ 0 →
              ∃ G,
                Tendsto (fun n => G n s) atTop (𝓝 (ZD.riemannXi s)) ∧
                  Tendsto (fun n => deriv (G n) s) atTop (𝓝 (deriv ZD.riemannXi s)) ∧
                    ∀ᶠ (n : ℕ) in atTop, 0 ≤ (logDeriv (G n) s).re / (s.re - 1 / 2)) →
    RiemannHypothesis
s : ℂ
him : 1269 / 2 < |s.im|
hlo : A / Real.log |s.im| ^ 9 < s.re
hhi : s.re < 1 / 2
hxi : ZD.riemannXi s ≠ 0
⊢ ∀ᶠ (n : ℕ) in atTop, 0 ≤ (logDeriv ((fun n => xiArithmeticStage ↑n) n) s).re / (s.re - 1 / 2)
```

### Draft D

Command: `lake env lean /private/tmp/rh-discharge-draft-4.lean`

Exit code: `1`. Literal output:

```text
warning: PrimeNumberTheoremAnd: repository '/Users/samuellavery/work/helix_frobenius/.lake/packages/PrimeNumberTheoremAnd' has local changes
/private/tmp/rh-discharge-draft-4.lean:16:2: error: D: arithmetic finite spectra, normalization, strip-holomorphic correction, and local uniform limit
N : ℕ
inst✝ : NeZero N
χ : DirichletCharacter ℂ N
⊢ ∃ r d c E,
    DifferentiableOn ℂ E stripOffReal ∧
      TendstoLocallyUniformlyOn (fun n => normalizedSpectrumTrace (d n) (c n)) (fun z => normalizedLTrace χ z - E z)
        atTop stripOffReal
```
