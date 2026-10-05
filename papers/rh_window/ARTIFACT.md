# Artifact: "The Riemann hypothesis up to height 634.5, checked by the Lean kernel"

## What is checked

| Theorem | Lean name | File |
|---|---|---|
| Window: every nontrivial zero with \|Im ρ\| ≤ 634.5 has Re ρ = 1/2 | `CriticalLinePhasor.DVP.online_below_1269o2` | `RequestProject/DVPLadder1269o2.lean` |
| Census: 366 zeros with 0 < Im ρ ≤ 634.5, counted with multiplicity | `CriticalLinePhasor.DVP.stripZeroCountMult_1269o2` | `RequestProject/DVPLift1269o2.lean` |
| Simplicity: every such zero has ξ-order 1 | `VerifiedWindow.xiOrder_eq_one_below_1269o2` | `RequestProject/PNTWindowBridge.lean` |
| PNT+'s `riemannZeta.RH_up_to (1269/2)` | `VerifiedWindow.pnt_RH_up_to_1269o2` | `RequestProject/PNTWindowBridge.lean` |
| Interface: `OneVanishingPerHeight3D → RiemannHypothesis` | `OneAssumptionRH.riemannHypothesis_of_oneAssumption` | `RequestProject/OneAssumptionRH.lean` |
| Interface, restricted to \|y\| ≤ 634.5 | `CarrierReadout.oneVanishingPerHeight3D_below` | `RequestProject/FiberZeroMidpointWindow.lean` |
| Fast slice: \|Im ρ\| ≤ 58 | `CriticalLinePhasor.DVP.online_below_58` | `RequestProject/DVPLadder.lean` |

## Axioms (printed by `papers/rh_window/Check.lean`, run 2026-09-29, exit 0; log `tmp/att931_check.log`)

    CriticalLinePhasor.DVP.online_below_1269o2 : ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 1269 / 2 → ρ.re = 1 / 2
    'CriticalLinePhasor.DVP.online_below_1269o2' depends on axioms: [propext, Classical.choice, Quot.sound]
    CriticalLinePhasor.DVP.online_below_58 : ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 58 → ρ.re = 1 / 2
    'CriticalLinePhasor.DVP.online_below_58' depends on axioms: [propext, Classical.choice, Quot.sound]
    CriticalLinePhasor.DVP.stripZeroCountMult_1269o2 : CriticalLinePhasor.ContourArgument.stripZeroCountMult (1269 / 2) = 366
    'CriticalLinePhasor.DVP.stripZeroCountMult_1269o2' depends on axioms: [propext, Classical.choice, Quot.sound]
    @VerifiedWindow.xiOrder_eq_one_below_1269o2 : ∀ {ρ : ℂ}, ρ ∈ ZD.NontrivialZeros → 0 < ρ.im → ρ.im ≤ 1269 / 2 → ZD.xiOrderNat ρ = 1
    'VerifiedWindow.xiOrder_eq_one_below_1269o2' depends on axioms: [propext, Classical.choice, Quot.sound]
    VerifiedWindow.pnt_RH_up_to_1269o2 : riemannZeta.RH_up_to (1269 / 2)
    'VerifiedWindow.pnt_RH_up_to_1269o2' depends on axioms: [propext, Classical.choice, Quot.sound]
    OneAssumptionRH.riemannHypothesis_of_oneAssumption : CarrierReadout.OneVanishingPerHeight3D → RiemannHypothesis
    'OneAssumptionRH.riemannHypothesis_of_oneAssumption' depends on axioms: [propext, Classical.choice, Quot.sound]
    @CarrierReadout.oneVanishingPerHeight3D_below : ∀ {y : ℝ}, |y| ≤ 1269 / 2 → ∀ {σ₁ σ₂ : ℝ}, 0 < σ₁ → σ₁ < 1 → 0 < σ₂ → σ₂ < 1 →
        CarrierReadout.laneChart3D σ₁ y = 0 → CarrierReadout.laneChart3D σ₂ y = 0 → σ₁ = σ₂
    'CarrierReadout.oneVanishingPerHeight3D_below' depends on axioms: [propext, Classical.choice, Quot.sound]

No `sorry`, no user `axiom`. No module of the ladder (`DVPStation*`, `DVPLadder*`, `DVPExhaustion*`, `DVPLift*`,
`DVPSegment*`) contains `native_decide` (grep count 0), so `Lean.ofReduceBool` does not appear.

## Trust base

- Lean 4 kernel, toolchain `leanprover/lean4:v4.34.0`.
- Mathlib at tag `v4.34.0` (definitions of `riemannZeta`, `completedRiemannZeta`, `Gamma`, `Real.log`, `Real.cos`,
  `Real.sin`, `Real.pi`, `analyticOrderNatAt`, `RiemannHypothesis`).
- For `pnt_RH_up_to_1269o2` only: PrimeNumberTheoremAnd (PNT+) at revision `21998bb6196b56789f72a52656a781a75e134eb0`,
  definitions `riemannZeta.zeroes`, `riemannZeta.zeroes_rect`, `riemannZeta.RH_up_to` (`IEANTN/ZetaDefinitions.lean`).
- Untrusted: the Python emitter `tmp/att271_station_emitter.py` and the witness tables `tmp/att*_cos*_witnesses.txt`.
  They produce the station heights, rational proxy phases and rational bounds. The kernel re-checks every one; a bad
  witness makes a module fail to compile.

## Size

- 367 generated station modules `RequestProject/DVPStation*.lean` (excluding `DVPStationSign.lean`), 546.2 MB of Lean
  source in total, heights 11 to 634.25. Median module size 0.17 MB below height 100 and 1.84 MB between 500 and 634.5;
  largest 8.43 MB.
- 31 rungs (`DVPExhaustion*.lean`), top heights 58, 63, 74, 81, 91, 109, 126, 144.5, …, 607.5, 634.5.
- Euler–Maclaurin truncation length N per station between 200 and 4000 (most common: 900 and 250).

## Build recipe (laptop-safe)

Never run a bare `lake build`: at default parallelism (one module per core) the station modules exhausted a 32 GB
machine. Use

    env LEAN_NUM_THREADS=2 nice -n 10 lake build RequestProject.PNTWindowBridge
    env LEAN_NUM_THREADS=2 nice -n 10 lake build RequestProject.OneAssumptionRH
    env LEAN_NUM_THREADS=2 nice -n 10 lake env lean papers/rh_window/Check.lean

`LEAN_NUM_THREADS=2` caps Lake at about two concurrent modules (about 11 GB peak while station modules build).
Watch `memory_pressure` and `sysctl vm.swapusage`.

## Measured costs

Apple M2 Max, 12 cores, 32 GB RAM, macOS. Wall time and peak RSS from `/usr/bin/time -l`.

| Task | Wall time | Peak RSS |
|---|---|---|
| `lake build PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions` (builds PNT+ `Defs` and `ZetaDefinitions`) | 35.6 s | 3.7 GB |
| `lake env lean RequestProject/PNTWindowBridge.lean` (loads the full window, checks both new theorems) | 282.6 s | 5.9 GB |
| Load the full window and print axioms only | 280.3 s | 6.2 GB |
| Re-check a station module from source (60 modules flagged out of date by Lake, heights 150–256; `lake build` log `tmp/att931_bridge_build.log`) | 51–247 s each, median 75 s, 5286 s summed | — |
| Fast slice: re-check the 15 height-58 modules from source, one at a time (see below) | 741.6 s total (31–72 s each) | 6.5 GB |
| Rebuild the two station modules interrupted when that `lake build` was stopped | 201.0 s | 8.6 GB |
| Write the bridge olean: `lake env lean -o …/PNTWindowBridge.olean RequestProject/PNTWindowBridge.lean` | 257.8 s | 9.1 GB |
| Run `papers/rh_window/Check.lean` | 251.3 s | 8.8 GB |

## Build state of this working tree (read before trusting the oleans)

`lake build RequestProject.PNTWindowBridge` found station oleans whose Lake traces were out of date with respect to
their sources. It re-checked 60 of them from the current sources without error (heights 150–256), and was then stopped
to free the machine. Stopping it mid-module removed two oleans, `DVPStation259` and `DVPStation521o2`; both were
rebuilt. The rest of the out-of-date set has not been re-checked. Importing an olean does not re-run the kernel on its
proofs, so certify the artifact by one of:

1. a complete build from a clean checkout,
   `env LEAN_NUM_THREADS=2 nice -n 10 lake build RequestProject.PNTWindowBridge RequestProject.OneAssumptionRH`
   (resuming here costs about 75 s per remaining out-of-date station at two modules in parallel); or
2. `lean4checker` over the relevant oleans, which replays the kernel.

Neither has been run for this draft.

## Fast slice

The height-58 rung (`online_below_58`) depends on 13 station modules (`DVPStation11` … `DVPStation58`, 0.17 MB each)
plus the shared census, theta and contour machinery. Re-checking the slice's own 15 modules from source
(`DVPStation11` … `DVPStation58`, `DVPExhaustion58`, `DVPLadder`), one `lake env lean` at a time against existing
oleans, took 741.6 s in total with no errors; per-module times and peak RSS are in `tmp/att931_fast_slice.log`. Peak RSS
per process (5.2–6.5 GB) is dominated by loading Mathlib, not by the station. The measurement ran while a separate
two-module `lake build` was active, so the times are upper bounds for an idle machine.

    for m in DVPStation11 DVPStation18 DVPStation23 DVPStation28 DVPStation32 DVPStation35 DVPStation39 \
             DVPStation42 DVPStation46 DVPStation49 DVPStation52 DVPStation55 DVPStation58 DVPExhaustion58 DVPLadder; do
      env LEAN_NUM_THREADS=2 nice -n 10 lake env lean RequestProject/$m.lean
    done
