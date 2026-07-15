import RequestProject.CPSUnitTransvection3D
import RequestProject.CPSUnconditionalSatakePayload3D

/-!
# The tower `htrans` assembly: self-dual-point reflection to full `GL` invariance

This file assembles the in-tree proofs that close the tower's `htrans` (invariance under every
transvection direction) from carrier-native inputs, eliminating the Mellin-inversion hypothesis
block entirely.

The one-dimensional route to transvection invariance (the converse-theorem route of
`CPSFiniteQuotientLocalUnit3D`) needs the full Mellin-inversion package — convergence, vertical
integrability, continuity — because the projected chart only holds the completed functional
equation of the `L`-readout.  The carrier holds more: the **pointwise theta reflection itself**
(`cpsDualPair3D_globalHelixReflection`, proven unconditionally for every CPS twist degree and
every unitary Satake family by `cpsAllTwists_unconditional3DAnalyticPayload`).  Evaluating that
reflection at the self-dual point `x = 1` gives the twisted primal/dual profile equality directly,
with no inversion; finite Fourier separation (`finiteAbelianCell_eq_of_all_twists_eq`) then forces
the unit winding, and the unit engine (`cps3D_readout_invariant_of_unit`) conjugates the unit
winding through the diagonal clocks to every transvection and hence to all of `GL(n, L)`.

`TowerThetaPackage` bundles exactly what a carrier must supply: the diagonal clocks, the
per-direction per-character profile pair, the pointwise reflection, and the two orbit-readout
identifications at the self-dual point.  `TowerThetaPackage.landing` proves full `GL(n, L)`
invariance of the readout from the package — no Mellin convergence, no vertical integrability, no
continuity hypotheses anywhere.

`cpsDualPair_selfDualPointIdentity` specializes the payload reflection to `x = 1`: for every rank,
prime phase, and unitary Satake family, the primal and contragredient bank readouts agree at the
self-dual point.  This is the exact value the package's reflection field consumes on the twisted
symmetric-power bank.

Scope: what remains for the tower bank is the carrier state space realizing the two orbit-readout
identifications (`primal_readout`/`dual_readout`) for the Satake data — a named construction, not
open mathematics.  This file does not assume or prove RH/GRH, and it asserts no classical
automorphy: the conclusion is carrier readout invariance, with the classical discrimination living
in the identification layer as recorded in the manuscript.
-/

namespace CriticalLinePhasor.ThreeDConverse

/-- The carrier-native input package for the tower `htrans`: diagonal clocks, a per-direction
per-character theta profile pair, the pointwise reflection, and the orbit-readout identifications
at the self-dual point.  No Mellin-inversion data is carried. -/
structure TowerThetaPackage
    (n K L X : Type*) [Fintype n] [DecidableEq n]
    [Field K] [Finite K] [Field L]
    [MulAction (Matrix.GeneralLinearGroup n L) X] where
  /-- the carrier readout. -/
  readout : X → ℂ
  /-- representatives of the finite winding cell inside the carrier field. -/
  lift : K → L
  /-- zero has its standard representative. -/
  lift_zero : lift 0 = 0
  /-- one has its standard representative. -/
  lift_one : lift 1 = 1
  /-- invariance under the diagonal completion clocks. -/
  hdiag : ∀ (D : n → L) (hD : Matrix.det (Matrix.diagonal D) ≠ 0) (x : X),
    readout (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD • x) = readout x
  /-- the primal theta profile of each winding direction, state, and finite character. -/
  primal : ∀ (i j : n), i ≠ j → X → AddChar K ℂ → ℝ → ℂ
  /-- the dual (contragredient) theta profile. -/
  dual : ∀ (i j : n), i ≠ j → X → AddChar K ℂ → ℝ → ℂ
  /-- **the pointwise global reflection** — for the twisted symmetric-power bank this is
  `cpsDualPair3D_globalHelixReflection`, supplied hypothesis-free by
  `cpsAllTwists_unconditional3DAnalyticPayload`. -/
  reflection : ∀ (i j : n) (hij : i ≠ j) (x : X) (character : AddChar K ℂ)
    {t : ℝ}, 0 < t →
    primal i j hij x character (1 / t) = (t : ℂ) * dual i j hij x character t
  /-- at the self-dual point the primal profile reads the shifted twisted orbit. -/
  primal_readout : ∀ (i j : n) (hij : i ≠ j) (x : X) (character : AddChar K ℂ),
    primal i j hij x character 1 =
      finiteAbelianTwistReadout K
        (fun c => readout (transvectionGL i j hij (lift (c + 1)) • x)) character
  /-- at the self-dual point the dual profile reads the unshifted twisted orbit. -/
  dual_readout : ∀ (i j : n) (hij : i ≠ j) (x : X) (character : AddChar K ℂ),
    dual i j hij x character 1 =
      finiteAbelianTwistReadout K
        (fun c => readout (transvectionGL i j hij (lift c) • x)) character

namespace TowerThetaPackage

variable {n K L X : Type*} [Fintype n] [DecidableEq n]
  [Field K] [Finite K] [Field L]
  [MulAction (Matrix.GeneralLinearGroup n L) X]
  (P : TowerThetaPackage n K L X)

/-- The reflection at the self-dual point equates every character twist of the shifted and
unshifted orbit readouts — no Mellin inversion is consumed. -/
theorem htwist (i j : n) (hij : i ≠ j) (x : X) (character : AddChar K ℂ) :
    finiteAbelianTwistReadout K
        (fun c => P.readout (transvectionGL i j hij (P.lift (c + 1)) • x)) character =
      finiteAbelianTwistReadout K
        (fun c => P.readout (transvectionGL i j hij (P.lift c) • x)) character := by
  have h := P.reflection i j hij x character (t := 1) one_pos
  rw [one_div_one, Complex.ofReal_one, one_mul,
    P.primal_readout i j hij x character, P.dual_readout i j hij x character] at h
  exact h

/-- Finite Fourier separation turns the twist equalities into the unit winding law. -/
theorem hunit (i j : n) (hij : i ≠ j) (x : X) :
    P.readout (transvectionGL i j hij (1 : L) • x) = P.readout x := by
  have hcell :
      (fun c => P.readout (transvectionGL i j hij (P.lift (c + 1)) • x)) =
        (fun c => P.readout (transvectionGL i j hij (P.lift c) • x)) :=
    finiteAbelianCell_eq_of_all_twists_eq (fun character => P.htwist i j hij x character)
  have hzero := congrFun hcell 0
  simpa [P.lift_zero, P.lift_one, transvectionGL_zero] using hzero

/-- The tower `htrans`: invariance under every transvection winding, from the unit law and the
diagonal clocks. -/
theorem htrans (i j : n) (hij : i ≠ j) (q : L) (x : X) :
    P.readout (transvectionGL i j hij q • x) = P.readout x :=
  all_transvection_readout_invariant_of_unit P.readout P.hdiag
    (fun i j hij x => P.hunit i j hij x) i j hij q x

/-- **The tower landing.** Full `GL(n, L)` invariance of the readout from the package — the
self-dual-point reflection replaces the entire Mellin-inversion hypothesis block. -/
theorem landing (g : Matrix.GeneralLinearGroup n L) (x : X) :
    P.readout (g • x) = P.readout x :=
  cps3D_readout_invariant_of_unit P.readout P.hdiag
    (fun i j hij x => P.hunit i j hij x) g x

end TowerThetaPackage

/-- **The self-dual-point identity of the twisted symmetric-power bank.**  For every rank, prime
phase, and unitary Satake family the primal and contragredient bank readouts agree at `x = 1` ---
the payload reflection evaluated where the package consumes it.  Unconditional; no hypotheses. -/
theorem cpsDualPair_selfDualPointIdentity
    {κ : Type*} [Fintype κ] (r : ℕ) (α : GlobalHelix.UnitaryPrimePhase)
    (τ : GlobalHelix.UnitarySatakeFamily κ) :
    GlobalHelix.cpsPrimal3DBankReadout r α τ 1 =
      GlobalHelix.cpsDual3DBankReadout r α τ 1 := by
  have h := GlobalHelix.cpsDualPair3D_globalHelixReflection r α τ (x := 1) one_pos
  simpa using h

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.TowerThetaPackage.htwist
#print axioms CriticalLinePhasor.ThreeDConverse.TowerThetaPackage.hunit
#print axioms CriticalLinePhasor.ThreeDConverse.TowerThetaPackage.htrans
#print axioms CriticalLinePhasor.ThreeDConverse.TowerThetaPackage.landing
#print axioms CriticalLinePhasor.ThreeDConverse.cpsDualPair_selfDualPointIdentity
