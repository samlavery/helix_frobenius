# Connecting local warp residues to the radial ledger

## Statements unfolded

The target remains the existing `DVP.RadialNoResidue`:
for every `0 < a ≤ b`,
`π ∫[a,b] Smult = radialLogMass b - radialLogMass a`.

The new input `WarpNoResidue.warpedSeat_no_residue` states, for fixed nonzero L
and each actual zero ρ of multiplicity m,

`lim[s→ρ, s≠ρ] (s-ρ) (ξ′/ξ(s) + m K_L(ρ-s)) = 0`.

`warpedSeat` is the expression inside those parentheses. The local correction
is its literal difference from `logDeriv ZD.riemannXi`, not a replacement seat.
The radial quantity remains
`δ(a,b) = π ∫[a,b] Smult - (radialLogMass b - radialLogMass a)`.

Expectation-free construction: compute the pole coefficients of each actual
summand, then apply the already proved window identity without dropping terms.

Two decompositions, with first Lean steps:

1. Compute the correction pole directly:
   `have h := (kernel_residue hL ρ).const_mul (ZD.xiOrderNat ρ : ℂ)`.
2. Integrate the multiplicity ledger first:
   `rw [radialResidue_eq_neg_defect ha hb hab]`.

The resulting bridge retains the correction residues. The zero-residue
conclusion for the full warped seat and the correction coefficient `-m` hold
simultaneously; `local_seat_and_correction` records both.

## Searches performed

```sh
rg -n 'warpedSeat|warped_seat|WarpNoResidue|kernelResidue|kernel_residue' RequestProject --glob '*.lean'
rg -n 'warpedSeat|warped_seat|WarpNoResidue|RadialNoResidue|radialResidue' .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n 'limUnder|lim_under|residue.*warp|warp.*residue|radial.*warp|warp.*radial' RequestProject --glob '*.lean'
rg -n 'limUnder_eq|lim_under|limUnder|tendsto_finset_sum|sum_filter' .lake/packages/mathlib/Mathlib/Topology/Separation/Hausdorff.lean .lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean
rg -n 'RadialNoResidue|radialResidue|warpedSeat|warped_seat|kernel_residue|primes_fuel_seat|xi_logDeriv_residue|cubicG_zero|def cubicKernel|def cubicG' RequestProject/WarpNoResidue.lean RequestProject/RadialLogMass.lean RequestProject/RadialCellBalance.lean RequestProject/RadialResidueLimit.lean RequestProject/SeatingRDefect.lean RequestProject/TruncatedExplicitFormula.lean
```

LeanSearch: `limit of a finite sum of functions at a filter`.
Loogle: `Filter.Tendsto, Filter.limUnder`.

The latter found `Filter.Tendsto.limUnder_eq`. All uses of `limUnder` in the
bridge have a proved punctured limit; no arbitrary value of a nonexistent
limit is used.

## Exact connection

Let `C_L(ρ)` be the punctured limit of
`(s-ρ) (warpedSeat L ρ s - ξ′/ξ(s))`. Then

* `C_L(ρ) = -mρ`;
* its real parts sum over the off-line strip window to `-N_off(t)`;
* on good windows, `δ(a,b) = π ∫[a,b] Σ_off C_L(ρ).re`;
* the same identity holds with `L = log (physicalHead t)` inside the integral.

The local theorem does not set `C_L(ρ)` to zero. It sets the residue of the
*sum* of the log derivative and its correction to zero. The constructed
bridge therefore does not claim `RadialNoResidue` or real-rootedness.

## Import integration

The first combined compile exposed a real module conflict:

```text
RequestProject/WarpRadialBridge.lean:1:0: error: import RequestProject.RegisterIdentity failed, environment already contains 'CriticalLinePhasor.DVP.LadderData' from RequestProject.DVPExhaustion58
```

`RegisterIdentity.lean` defines a height/count-parametrized `DVP.LadderData`;
`DVPExhaustion58.lean` defines a constant proposition with the same name.
The two imported branches had previously compiled separately.

`LittlewoodRegisterDoor.lean` uses no declaration from `RegisterIdentity`.
Its import was replaced with `DoubleCoshProgram` and `DVPArgumentPrinciple`.
The latter provides `zeta_ne_zero_of_real_unit`. No mathematical declaration
or proof body in the radial door was changed, and neither ladder was renamed.

## Verification

`lake build RequestProject.WarpRadialBridge` exited 0:

```text
Build completed successfully (9570 jobs).
```

`lake env lean RequestProject.WarpRadialBridge.lean` exited 0:

```text
'CriticalLinePhasor.WarpNoResidue.warpCorrectionResidue_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.WarpNoResidue.local_seat_and_correction' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.WarpNoResidue.radialResidue_eq_integrated_warpCorrections' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.WarpNoResidue.radialResidue_eq_integrated_carrierCorrections' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The source scan for `axiom |sorry|admit|@\[implemented_by\]` returned no matches
in `WarpRadialBridge.lean` or `LittlewoodRegisterDoor.lean`.

## Closure attempts executed after the import repair

The LSP reported stale imports, so these checks were run directly with
`lake env lean /private/tmp/WarpRadialClosureAttempts.lean` (exit 1).

```lean
import RequestProject.WarpNoResidue
import RequestProject.RadialCellBalance
open Complex Filter Topology MeasureTheory Set
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.ResidueJump
open CriticalLinePhasor.DVP CriticalLinePhasor.WarpNoResidue
example {L : ℝ} (hL : L ≠ 0) {a b : ℝ}
    (ha : GoodHeight a) (hb : GoodHeight b) (hab : a ≤ b) :
    radialResidue a b = 0 := by
  have hlocal : ∀ ρ ∈ ZD.NontrivialZeros,
      limUnder (𝓝[≠] ρ) (fun s => (s - ρ) * warpedSeat L ρ s) = 0 :=
    fun ρ hρ => (warpedSeat_no_residue hL hρ).limUnder_eq
  rw [radialResidue_eq_neg_defect ha hb hab]
  have hmass : 0 ≤ ∫ t in a..b, (offLineStripZeroCountMult t : ℝ) :=
    intervalIntegral.integral_nonneg hab (fun _ _ => Nat.cast_nonneg _)
  nlinarith [Real.pi_pos]

example {L : ℝ} (hL : L ≠ 0) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (hoff : ρ.re ≠ 1 / 2) :
    limUnder (𝓝[≠] ρ) (fun s => (s - ρ) *
      (warpedSeat L ρ s - logDeriv ZD.riemannXi s)) = 0 := by
  have hcancel := warpedSeat_no_residue hL hρ
  have hmass := CriticalLinePhasor.SeatingLedger.xi_logDeriv_residue hρ
  have hd := hcancel.sub hmass
  have ht : Tendsto (fun s => (s - ρ) *
      (warpedSeat L ρ s - logDeriv ZD.riemannXi s)) (𝓝[≠] ρ)
      (𝓝 (0 - (ZD.xiOrderNat ρ : ℂ))) := by
    convert hd using 1 <;> ext s <;> ring
  simpa using ht.limUnder_eq
```

Literal mathematical diagnostics:

```text
/private/tmp/WarpRadialClosureAttempts.lean:15:2: error: linarith failed to find a contradiction
case h1
L : ℝ
hL : L ≠ 0
a b : ℝ
ha : GoodHeight a
hb : GoodHeight b
hab : a ≤ b
hlocal : ∀ ρ ∈ ZD.NontrivialZeros, ((𝓝[≠] ρ).limUnder fun s => (s - ρ) * warpedSeat L ρ s) = 0
hmass : 0 ≤ ∫ (t : ℝ) in a..b, ↑(offLineStripZeroCountMult t)
a✝ : -(Real.pi * ∫ (t : ℝ) in a..b, ↑(offLineStripZeroCountMult t)) < 0
⊢ False
failed
/private/tmp/WarpRadialClosureAttempts.lean:28:2: error: Type mismatch: After simplification, term
  Tendsto.limUnder_eq ht
 has type
  ((𝓝[≠] ρ).limUnder fun s => (s - ρ) * (warpedSeat L ρ s - logDeriv ZD.riemannXi s)) = -↑(ZD.xiOrderNat ρ)
but is expected to have type
  ((𝓝[≠] ρ).limUnder fun s => (s - ρ) * (warpedSeat L ρ s - logDeriv ZD.riemannXi s)) = 0
```

The latter calculation is retained with its actual limit `-mρ` in the
compiled bridge. These failures are not counterexamples to real-rootedness.
The remaining intermediate goal is `radialResidue a b = 0` on good windows;
the original all-positive-window `RadialNoResidue` target also retains its
endpoint extension requirement.
