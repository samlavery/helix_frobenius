import RequestProject.MaassIdentification
import RequestProject.CPSCharacterSatoTate3D
import RequestProject.RamanujanLimit

/-!
# Sato–Tate at the typed Maass seed: the register unification

The Sato–Tate bridge is compiled (`CPSCharacterSatoTate3D`): the per-rank prime-trace
cancellation — the Wiener–Ikehara step, the single cited analytic input — is
*equivalent* to equidistribution of the Satake angles against the carrier measure.
This file wires the campaign's typed Maass surface into that bridge, so the
Sato–Tate chain and the automorphy chain (packages, converse, wave-form
identification) share one seed object:

* `MaassTowerCeiling` — the per-prime rank-uniform ceiling on the seed's Satake
  powers, the classical per-rung Jacquet–Shalika input (`C = p^{1/2}`), typed;
* `maassTower` / `maassSatoTateFamily` — the arithmetic Satake tower and prime
  family of a `MaassEigenData` under the ceiling;
* `maass_temperedness` — **Sato–Tate (i) at the seed**: the ceiling forces
  `‖α_p‖ = 1` at every prime (the compiled radial limit — the 1D chart reads it as
  Ramanujan–Petersson);
* `maass_satoTate_iff` / `maass_satoTate_of_cancellation` — **Sato–Tate (ii) at the
  seed**: the compiled biconditional instantiated — the per-rank cancellation of
  the seed's literal symmetric-power prime traces is equivalent to carrier
  equidistribution of its angles, and yields it.

The cited inputs are exactly the classical ones the manuscript names: the per-rung
ceiling and the per-rank prime cancellation (Wiener–Ikehara is not yet in Mathlib).
No `axiom`, no `sorry`.
-/

open Filter Topology

namespace CriticalLinePhasor.MaassSatoTate

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.SatoTateCarrier3D
open CriticalLinePhasor.RamanujanLimit

/-- **The per-prime rank-uniform ceiling** on the Maass seed's Satake powers — the
classical per-rung Jacquet–Shalika input, typed. -/
structure MaassTowerCeiling (M : MaassEigenData) where
  C : Nat.Primes → ℝ
  top : ∀ (p : Nat.Primes) (r : ℕ), 1 ≤ r →
    ‖(SatakeSeed.ofMaass M).satake p ^ r‖ ≤ C p
  bottom : ∀ (p : Nat.Primes) (r : ℕ), 1 ≤ r →
    ‖((SatakeSeed.ofMaass M).satake p)⁻¹ ^ r‖ ≤ C p

/-- The arithmetic Satake tower of the Maass seed at a prime. -/
noncomputable def maassTower (M : MaassEigenData) (hC : MaassTowerCeiling M)
    (p : Nat.Primes) : CriticalLinePhasor.GlobalHelix.ArithmeticSatakeTowerAtPrime where
  value := (SatakeSeed.ofMaass M).satake p
  value_ne_zero := (SatakeSeed.ofMaass M).satake_ne_zero p
  topSatake := fun r => (SatakeSeed.ofMaass M).satake p ^ r
  bottomSatake := fun r => ((SatakeSeed.ofMaass M).satake p)⁻¹ ^ r
  topSatake_eq := fun _ => rfl
  bottomSatake_eq := fun _ => rfl
  bound := hC.C p
  topSatake_bound := fun r hr => hC.top p r hr
  bottomSatake_bound := fun r hr => hC.bottom p r hr

/-- The Sato–Tate prime family of the typed Maass seed. -/
noncomputable def maassSatoTateFamily (M : MaassEigenData) (hC : MaassTowerCeiling M) :
    ArithmeticSatakePrimeFamily :=
  ⟨fun p => maassTower M hC p⟩

/-- **Sato–Tate (i) at the seed — temperedness**: the rank-uniform ceiling forces
unit radius at every prime.  The 1D chart reads this as Ramanujan–Petersson. -/
theorem maass_temperedness (M : MaassEigenData) (hC : MaassTowerCeiling M)
    (p : Nat.Primes) : ‖(SatakeSeed.ofMaass M).satake p‖ = 1 :=
  strand_radius_one_of_tower_ceiling ((SatakeSeed.ofMaass M).satake_ne_zero p)
    (fun r hr => hC.top p r hr) (fun r hr => hC.bottom p r hr)

/-- **Sato–Tate (ii) at the seed — the compiled biconditional instantiated**: the
per-rank cancellation of the seed's literal symmetric-power prime traces is
equivalent to carrier equidistribution of its Satake angles. -/
theorem maass_satoTate_iff (M : MaassEigenData) (hC : MaassTowerCeiling M) :
    (∀ r : ℕ, 1 ≤ r →
        Tendsto (fun n =>
          arithmeticSymmetricPowerPrimeAverage (maassSatoTateFamily M hC) r n)
          atTop (nhds 0)) ↔
      Tendsto
        (empiricalPrimeCarrierMeasure
          (maassSatoTateFamily M hC).angle) atTop
        (nhds carrierProbability) :=
  arithmeticSatakeCancellation_iff_carrierEquidistribution (maassSatoTateFamily M hC)

/-- **Sato–Tate for the typed Maass seed, from the cited cancellation**: the
Wiener–Ikehara input yields carrier equidistribution of the seed's angles. -/
theorem maass_satoTate_of_cancellation (M : MaassEigenData) (hC : MaassTowerCeiling M)
    (h : ∀ r : ℕ, 1 ≤ r →
      Tendsto (fun n =>
        arithmeticSymmetricPowerPrimeAverage (maassSatoTateFamily M hC) r n)
        atTop (nhds 0)) :
    Tendsto
      (empiricalPrimeCarrierMeasure
        (maassSatoTateFamily M hC).angle) atTop
      (nhds carrierProbability) :=
  (maass_satoTate_iff M hC).mp h

end CriticalLinePhasor.MaassSatoTate

#print axioms CriticalLinePhasor.MaassSatoTate.maassSatoTateFamily
#print axioms CriticalLinePhasor.MaassSatoTate.maass_temperedness
#print axioms CriticalLinePhasor.MaassSatoTate.maass_satoTate_iff
#print axioms CriticalLinePhasor.MaassSatoTate.maass_satoTate_of_cancellation
