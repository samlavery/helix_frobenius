import RequestProject.CPSConverse3DReadout

/-!
# The tower converse landing, reduced to its two carrier inputs

`cpsCarrierLanding3D` reduces the three-dimensional converse for the rank-`r+1` carrier to its
two named generator inputs.  Everything downstream of the two generator invariances is the audited engine
(`cps3D_readout_invariant`, `glCarrierGenerators_closure`, Mathlib's diagonal/transvection
generation), which is unconditional.  What remains, for a concrete carrier state space with a
genuine `GL(r+1,K)`-action and readout, is exactly:

* `hdiag` --- invariance under the diagonal completion clocks;
* `htrans` --- invariance under **every** transvection direction.

`htrans` is the whole arithmetic content: it is the all-directions winding invariance, i.e. the
Cogdell--Piatetski-Shapiro basic identity / the niceness of the full twist family.

## Adjudication: does `htrans` close carrier-natively, or does it need a further input?

**GL(2) / level one (`r = 1`): it closes.** Here Hecke's `⟨S,T⟩ = SL(2,ℤ)` reduces `htrans`
to the single reflection `S` (the theta functional equation) and the winding `T` (periodicity), both
carrier-native.  This is realized *non-vacuously on a genuine automorphic object* in
`CPSModularSeed3D` (`seedReadout_landing`): the weight-zero readout of a level-one modular form is
`SL(2,ℤ)`-invariant, proved from Mathlib's real modular transformation law, and the audited engine
lifts the two generator invariances to the full group.

**The tower (`r ≥ 2`): the closure is an assembly of in-tree proofs, not a new input.** For
`r ≥ 2`, `htrans` is invariance under every transvection direction.  The tree already contains the
reduction engine: `cpsLocal3D_invariant_of_finiteQuotientMellin` derives full `GL(n)` invariance
from the diagonal clocks plus a finite-quotient Mellin (theta) package --- the unit transvection
from Fourier separation, every direction from diagonal and permutation conjugation.  The carrier
supplies the package's ingredients: the compiled reflection
`GlobalHelix.twistedSymmetricPowerCarrier3D_globalHelixReflection` (which holds for an *arbitrary*
unimodular Satake family), the winding periodicity of the lattice, and the strand-exchange symmetry
of the bank.  That the reflection is angle-agnostic is the carrier-generic *feature*, not a
refutation: carrier invariance is universal across admissible banks --- the finite model of
`CPSLatticeInstance3D` proves its own invariance by pure reindexing --- and the classical
discrimination between automorphic and non-automorphic angle data lives entirely in the downstream
identification of the carrier object with the classical completed `L` (the named identification
layer, where Newton--Thorne for the holomorphic tower and the adelic Poisson of Tate's thesis are
consumed, cited not formalized).  Reading the 1D fact "not every unimodular bank is classically
automorphic" as an obstruction to the 3D closure would import a projection-chart artifact onto the
carrier.  What remains for `htrans` on the twisted symmetric-power bank is therefore assembly ---
constructing the bank's theta profile pair and discharging the Mellin-package hypotheses --- plus
the identification layer, named.  No automorphic-realization input enters the carrier landing.

This file states the reduction; it introduces no axioms and asserts no automorphy.
-/

open Matrix CriticalLinePhasor.ThreeDConverse

namespace CriticalLinePhasor.CPSCarrierLanding

/-- **The rank-`r+1` carrier converse landing, modulo its two generator invariances.** Given a
carrier state space with a `GL(r+1,K)`-action and a readout that is invariant under the diagonal
completion clocks (`hdiag`) and under every transvection winding (`htrans`), the readout is
invariant under all of `GL(r+1,K)`.  The proof is the audited generator engine; `hdiag` and `htrans`
are the
only inputs, and `htrans` is the assembly target discussed in the module docstring. -/
theorem cpsCarrierLanding3D {r : ℕ} {K X Y : Type*} [Field K]
    [MulAction (Matrix.GeneralLinearGroup (Fin (r + 1)) K) X] (readout : X → Y)
    (hdiag : ∀ (D : Fin (r + 1) → K) (hD : Matrix.det (Matrix.diagonal D) ≠ 0) (x : X),
      readout (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal D) hD • x) = readout x)
    (htrans : ∀ (t : Matrix.TransvectionStruct (Fin (r + 1)) K) (x : X),
      readout (Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix (by simp) • x) = readout x)
    (g : Matrix.GeneralLinearGroup (Fin (r + 1)) K) (x : X) :
    readout (g • x) = readout x :=
  cps3D_readout_invariant readout hdiag htrans g x

end CriticalLinePhasor.CPSCarrierLanding

#print axioms CriticalLinePhasor.CPSCarrierLanding.cpsCarrierLanding3D
