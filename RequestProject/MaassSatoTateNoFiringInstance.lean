import RequestProject.MaassEndpointGap
import RequestProject.MaassSatoTateClosure

/-!
# The Sato--Tate machinery has no firing instance

`maass_satoTate` is a genuine implication over `MaassEigenData` — it is **not** vacuous, and
`maass_satoTate_exact` shows both of its inputs are individually equivalent to the conclusion they
feed.  This file records what is nevertheless missing: no `M` in the corpus makes the conclusion
fire.

Three compiled facts, assembled:

* **Input one is satisfiable.**  `MaassPolyCeiling divisorMaassEigenData` is inhabited — the
  divisor system is tempered (`divisorMaassEigenData_satake` gives `α_p = 1`), and
  `temperedness_iff_polyCeiling` turns temperedness into the ceiling constructively.
* **Input two is refutable at that instance.**  The first symmetric-power prime average of the
  divisor system is constantly `2`, so the cancellation fails
  (`divisorMaass_no_primeCancellation_ofCeiling`).  This is the Eisenstein point `θ_p ≡ 0`, which
  is exactly what Sato--Tate must exclude.
* **There is no other supply.**  The type built to identify coefficients with a genuine cuspidal
  Maass representation, `GenuineMaassCuspForm3D`, has no construction anywhere in the corpus.  It
  was formerly *empty* — its `radial_equation` dropped the Whittaker term `y·K'`; that is repaired,
  and the defect survives as the uninhabited `FirstOrderFreeRadialData`.  Inhabiting the repaired
  structure means exhibiting `K_{ir}(2πy)` in Lean, which Mathlib does not yet supply.

So the machinery is well-formed, discriminating, and starved: its first hypothesis holds at the
only inhabitant, its second provably fails there, and the intended source of a different inhabitant
has no construction.  That is the precise sense in which the Maass endpoint is open in this corpus
— and it separates cleanly from the classical obstruction, which is that per-rank cancellation for
a genuine Maass form needs `L(Sym^r)` beyond `r = 4`.

**Scope.**  This narrows nothing classically.  It states where the corpus stands.
-/

open Filter Topology

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.MaassSatoTate
open CriticalLinePhasor.SatoTateCarrier3D CriticalLinePhasor.PolyCeiling
open CriticalLinePhasor.MaassSatoTateClosure

/-- **Input one is satisfiable**: the divisor system carries the polynomial tower ceiling. -/
theorem divisorMaass_polyCeiling_nonempty :
    Nonempty (MaassPolyCeiling divisorMaassEigenData) :=
  (temperedness_iff_polyCeiling divisorMaassEigenData).mp fun p => by
    rw [divisorMaassSatakeSeed_satake p, norm_one]

/-- **Input two fails there**, in exactly the form `maass_satoTate` consumes. -/
theorem divisorMaass_cancellation_false
    (hC : MaassTowerCeiling divisorMaassEigenData) :
    ¬ (∀ r : ℕ, 1 ≤ r →
        Tendsto (fun n =>
          arithmeticSymmetricPowerPrimeAverage
            (maassSatoTateFamily divisorMaassEigenData hC) r n) atTop (nhds 0)) :=
  fun h => divisorMaass_no_primeCancellation_ofCeiling hC ⟨h⟩

/-- **The machinery has no firing instance.**  Input one holds at the corpus's only
`MaassEigenData` inhabitant, input two fails there, and the radial equation that was meant to
supply a cuspidal inhabitant — before its Whittaker term was restored — is inconsistent. -/
theorem maass_satoTate_no_firing_instance :
    Nonempty (MaassPolyCeiling divisorMaassEigenData)
      ∧ (∀ hC : MaassTowerCeiling divisorMaassEigenData,
          ¬ (∀ r : ℕ, 1 ≤ r →
              Tendsto (fun n =>
                arithmeticSymmetricPowerPrimeAverage
                  (maassSatoTateFamily divisorMaassEigenData hC) r n) atTop (nhds 0)))
      ∧ IsEmpty FirstOrderFreeRadialData :=
  ⟨divisorMaass_polyCeiling_nonempty, divisorMaass_cancellation_false,
    ⟨firstOrderFreeRadialData_false⟩⟩

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.maass_satoTate_no_firing_instance
