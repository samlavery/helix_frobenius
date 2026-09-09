# Radial cell balance construction

## Fixed target, unfolded before construction

The requested target remains `CriticalLinePhasor.DVP.RadialNoResidue`.
For all real a, b with 0 < a ≤ b, it states

π ∫[a,b] (N_on(t) − 1 − θ(t)/π) dt = R(b) − R(a),

where N_on is `zeroEventCountMult`, retaining analytic multiplicities, and
R(t) = ∫[x > 1/2] log ‖ζ(x + it)‖ dx is the existing `radialLogMass`.
Neither function was changed.

## Search and audit

Commands executed from the repository root included:

```sh
rg -n 'RadialNoResidue|radialNoResidue|radial_no_residue|radialResidue|radial_residue|radialLogMass|radial_log_mass|residue_identity|residue_nonpos' RequestProject .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n 'theorem.*(cell|Cell).*(integral|residue|boundary|telescope)|theorem.*(integral|residue|boundary).*(cell|Cell)' RequestProject/HarmonizedCell* RequestProject/*Residue*.lean RequestProject/*Warp*.lean
rg -n 'sum_integral_adjacent|sum_integral|sum.*telescope|sum_range_sub|integral_add_adjacent_intervals' .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset
rg -n 'def (Smult|SAll)|noncomputable def (Smult|SAll)|def GoodHeight' RequestProject --glob '*.lean'
rg -n 'noOfflineZeros_holds|noOffline_holds|radialNoResidue_holds|RadialNoResidue|radialResidue.*nonneg|radialResidue.*zero' RequestProject --glob '*.lean'
```

LeanSearch: finite sums of interval integrals over adjacent intervals.
Loogle: `"sum_eq_zero", "nonpos"`.
Used `intervalIntegral.sum_integral_adjacent_intervals` and
`Finset.sum_eq_zero_iff_of_nonpos` from these searches.

The matching existing radial implication consumes `RadialNoResidue`; no
unconditional producer of that predicate was found. Its existing input
`residue_identity` was audited, together with
`integrated_defect_pair_lower_bound`, `registrationHelix_injective`,
`focal_residual_vanishes_at_represented_zero`, and
`cell_normalized_scalar_exact`. Literal printed footprints were the standard
three: `[propext, Classical.choice, Quot.sound]`.

## Constructed code

`RequestProject/RadialCellBalance.lean` defines the literal residue
δ(a,b) = π ∫[a,b] Smult − (R(b) − R(a)).

Expectation-free next step: expand both quantities, split the interval, and
retain every resulting term. Two decomposition strategies used in compiling
the transport layer:

* Additivity first: `have hi := intervalIntegral.integral_add_adjacent_intervals
  (smult_intervalIntegrable a b) (smult_intervalIntegrable b c)`.
* Finite cells first: `rw [intervalIntegral.sum_integral_adjacent_intervals
  (fun k _ => sall_intervalIntegrable (c k) (c (k + 1)))]`.

The file proves exact telescoping, the exact final partial-cell term,
nonpositivity and monotonicity on good windows, preservation of the residue
in the integrated third coordinate of the registration lift, and explicit
limit transport with a boundary-convergence premise. It does not identify
that registration lift with any additional spectral-fiber structure.

The file also proves that a zero total residue on good cells means every
cell residue is zero: negative residues cannot cancel. A nonzero
off-carrier count at a gives δ(a,b) ≤ −2π(b−a).

## Closure attempts actually executed in Lean

### 1. Integrate the cell-normalized identities

```lean
example {a b : ℝ} (ha : GoodHeight a) (hb : GoodHeight b) (hab : a ≤ b) :
    Real.pi * (∫ t in a..b, Smult t) = radialLogMass b - radialLogMass a := by
  apply le_antisymm (residue_nonpos ha hb hab)
  have hcellA := cell_normalized_scalar_exact (1 : DirichletCharacter ℂ 1) (Real.exp a)
  have hcellB := cell_normalized_scalar_exact (1 : DirichletCharacter ℂ 1) (Real.exp b)
  have hsplit := residue_identity ha hb hab
  have hmass : 0 ≤ ∫ t in a..b, (offLineStripZeroCountMult t : ℝ) :=
    intervalIntegral.integral_nonneg hab (fun _ _ => Nat.cast_nonneg _)
  nlinarith [Real.pi_pos]
```

Compiler: `linarith failed to find a contradiction`. The unresolved reverse
inequality is `radialLogMass b - radialLogMass a ≤ π * ∫[a,b] Smult`.

### 2. Lift equality through the injective registration helix

```lean
example {T : ℝ} (hT : GoodHeight T) : classicalSContour hT = Smult T := by
  apply registrationHelix_injective
  apply Prod.ext
  · exact contour_registrationPhase_eq_native hT
  · change classicalSContour hT = Smult T
    have hphase := contour_registrationPhase_eq_native hT
    have hthird := contour_registrationHelix_third_gap hT
    have hpair := offLineStripZeroCountMult_eq_two_mul_right T
    rw [classicalSContour_eq_Smult_add_offLine hT]
    simp only [add_eq_left, Nat.cast_eq_zero]
    omega
```

Literal compiler diagnostic:

```text
omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a ≥ 1
where
 a := ↑(rightHalfCountMult T)
```

This is a diagnostic for the tactic's arithmetic constraints, not an
assertion that an off-carrier zero exists.

### 3. Back up to the signed radial-pair conservation law

```lean
example {a b : ℝ} (ha : GoodHeight a) (hb : GoodHeight b) (hab : a ≤ b) :
    0 ≤ Real.pi * (∫ t in a..b, Smult t) - (radialLogMass b - radialLogMass a) := by
  have hpair : ∀ ρ : ℂ,
      Real.log ‖endPairFace ρ‖ +
        Real.log ‖endPairFace (1 - (starRingEnd ℂ) ρ)‖ = 0 := endPair_radial_ledger_zero
  rw [residue_identity ha hb hab]
  have hnonneg : 0 ≤ ∫ t in a..b, (offLineStripZeroCountMult t : ℝ) :=
    intervalIntegral.integral_nonneg hab (fun _ _ => Nat.cast_nonneg _)
  nlinarith [Real.pi_pos]
```

Compiler: `linarith failed to find a contradiction`, retaining the goal
`0 ≤ -(π * ∫[a,b] offLineStripZeroCountMult)`.

## Exact remaining construction

Produce a geometric proof of `0 ≤ radialResidue a b` on good windows,
or prove the actual boundary-limit premise in
`radialResidue_zero_of_boundary_limit`. Neither has been established here.
The all-positive-window target additionally includes nongood endpoint
values of the existing radial integral. The file's additivity identities
hold at those endpoints, but its sign and limit-transport results retain
their stated `GoodHeight` conditions.

`RadialNoResidue` is not proved by this patch. No target declaration was
replaced by a theorem with an extra premise.
