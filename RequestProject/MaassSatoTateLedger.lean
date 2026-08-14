import RequestProject.WitnessFamily
import RequestProject.MaassSatoTateNoFiringInstance

/-!
# The Maass Sato--Tate ledger

One statement recording where the corpus's Sato--Tate endpoint stands, with all three parts
compiled.

* **Too weak.**  The bare coefficient signature `MaassEigenData` cannot carry Sato--Tate: the
  divisor function satisfies it and its cancellation field is false
  (`divisorMaass_no_primeCancellation`, pre-existing).
* **Too strong.**  The type built to fix that — `GenuineMaassCuspForm3D`, which identifies the
  coefficients with a cuspidal Maass form — has no construction in the corpus.  It was formerly
  *uninhabited*, because its `radial_equation` dropped the first-order term `y·K'` of the Whittaker
  equation; that field now carries the modified Bessel equation, and the defect is preserved as
  `FirstOrderFreeRadialData`, which `firstOrderFreeRadialData_false` shows is empty.
  `sqrt_weight_sign_flip` certifies that the restored term moves the deciding constant from
  `+r² ≥ 0` to `−(1/4 + r²) < 0`.
* **But sound.**  The cancellation field is nevertheless *attainable*: an explicit synthetic family
  satisfies it, and the corpus's reduction then delivers full carrier equidistribution
  (`witnessFamily_equidistributes`).

So the machinery is well-formed, discriminating, and capable of firing.  What is missing is not the
reduction but its arithmetic input: per-rank cancellation for a genuine Maass form needs
`L(Sym^r)` beyond `r = 4`, which is unavailable — and `majorant_lower_bound` shows the ranks that
*are* available cannot substitute, since no nonnegative majorant of degree `2n − 2` beats
`(4/n)·sin²(π/2n)`, a bound attained by the Gauss measure.
-/

open Filter Topology

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.SatoTateCarrier3D CriticalLinePhasor.MaassSatoTate

/-- **The ledger.**  Too weak, too strong, but sound. -/
theorem maass_satoTate_ledger :
    (¬ ArithmeticSymmetricPowerPrimeCancellation
        (maassSatoTateFamily divisorMaassEigenData divisorMaassTowerCeiling))
      ∧ IsEmpty FirstOrderFreeRadialData
      ∧ ArithmeticSymmetricPowerPrimeCancellation witnessFamily :=
  ⟨divisorMaass_no_primeCancellation, ⟨firstOrderFreeRadialData_false⟩,
    witnessFamily_cancellation⟩

/-- The positive half, spelled out: the reduction's conclusion is attainable. -/
theorem satoTate_conclusion_attainable :
    ∃ F : ArithmeticSatakePrimeFamily,
      Tendsto (empiricalPrimeCarrierMeasure F.angle) atTop (nhds carrierProbability) :=
  ⟨witnessFamily, witnessFamily_equidistributes⟩

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.maass_satoTate_ledger
#print axioms CriticalLinePhasor.ThreeDConverse.satoTate_conclusion_attainable
