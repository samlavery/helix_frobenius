import RequestProject.FiberZeroMidpointRoute
import RequestProject.RiemannHypothesisBridge

/-!
# Mathlib's `RiemannHypothesis` from one assumption (ledger 929)

The one assumption is `CarrierReadout.OneVanishingPerHeight3D`: at every height, the 3-D fiber
`laneChart3D` vanishes for at most one drift `σ ∈ (0, 1)`.

The chain, every other link compiled:
* `fiber3D_vanishes_of_zero` — a strip zero of `ζ` is a vanishing of the 3-D fiber at its height;
* `fiber3D_vanishes_at_partner` — the fiber also vanishes at the partner drift `1 − σ`, same height;
* the assumption — the two drifts coincide, so `σ = 1 − σ`, i.e. `σ = ½`
  (`rh_of_oneVanishingPerHeight3D`);
* `RHBridge.no_offline_zeros_implies_rh` — the on-line placement of the strip zeros is Mathlib's
  `RiemannHypothesis`.

No `sorry`, no `axiom`.
-/

namespace OneAssumptionRH

/-- **`RiemannHypothesis` from one assumption.** -/
theorem riemannHypothesis_of_oneAssumption (h : CarrierReadout.OneVanishingPerHeight3D) :
    RiemannHypothesis :=
  RHBridge.no_offline_zeros_implies_rh (CarrierReadout.rh_of_oneVanishingPerHeight3D h)

end OneAssumptionRH

#print axioms OneAssumptionRH.riemannHypothesis_of_oneAssumption
