import RequestProject.CPSRemainingObligationsAudit3D
import RequestProject.MaassStructureEmpty

/-!
# The Maass endpoint has no inhabited type

`CPSRemainingObligationsAudit3D` established one half of a boundary: the `MaassEigenData` signature
is **too weak** to carry Sato--Tate, because the divisor function `d(n)` satisfies it and its first
symmetric-power prime average is constantly `2`
(`divisorMaass_no_primeCancellation`).  That file's conclusion was that "a completed endpoint must
consume a type that also identifies the coefficients with a genuine cuspidal Maass automorphic
representation."

`GenuineMaassCuspForm3D` is that type.  It once carried a `radial_equation` missing the Whittaker
first-order term `y·K'`, which made it **empty**; that field now carries the modified Bessel
equation, and the old hypotheses survive as `FirstOrderFreeRadialData`, which
`firstOrderFreeRadialData_false` shows is uninhabited.  So the emptiness is a theorem about the
defective equation, not about the structure.

What remains after the repair is the honest half of the pincer, recorded here:

* the weak type admits an explicit counterexample to the cancellation field, and
* the strengthening built to fix that has no *supply* — nothing in the corpus constructs one.

**Consequence.**  The boundary the audit file describes has not been crossed.  The Sato--Tate
closure theorems of `MaassSatoTateClosure` are genuine implications over `MaassEigenData`, and are
**not** vacuous; what they lack is a cuspidal instance, and building one means exhibiting a
`K_{ir}(2πy)` in Lean, which Mathlib does not yet supply.

**Scope.**  This file states the weak half and the missing supply.  It does not narrow the
classical gap: per-rank cancellation for a genuine Maass form remains open (`L(Sym^r)` is
classically unavailable beyond `r = 4`), as does Ramanujan--Petersson.
-/

open Filter Topology

namespace CriticalLinePhasor.ThreeDConverse

/-- **The Maass endpoint gap.**  The weak coefficient signature admits an explicit counterexample
to the cancellation field, and the radial equation that once strengthened it — the modified Bessel
equation with its first-order term dropped — is inconsistent. -/
theorem maass_endpoint_gap :
    (¬ CriticalLinePhasor.SatoTateCarrier3D.ArithmeticSymmetricPowerPrimeCancellation
        (CriticalLinePhasor.MaassSatoTate.maassSatoTateFamily
          divisorMaassEigenData divisorMaassTowerCeiling))
      ∧ IsEmpty FirstOrderFreeRadialData :=
  ⟨divisorMaass_no_primeCancellation, ⟨firstOrderFreeRadialData_false⟩⟩

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.maass_endpoint_gap
