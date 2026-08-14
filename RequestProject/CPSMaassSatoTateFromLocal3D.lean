import RequestProject.CPSLocalAnalyticRoute3D
import RequestProject.CPSMaassTauberianTransfer3D

/-!
# Sato--Tate from the local analytic input

The closing composition.  `CPSLocalAnalyticRoute3D` produces the `o(N)` summatory estimate for the
generalized von Mangoldt coefficients of a rung from purely local analytic data; the compiled
Tauberian transfer turns that into the unweighted prime estimate; and the compiled character
bridge turns the family of prime estimates into carrier equidistribution.

The result below is therefore the exact residual of the programme, as one statement:

> **temperedness (the tower ceiling) + per-rank local holomorphy, Dirichlet identification and
> nonvanishing near `Re s ≥ 1` ⟹ Sato--Tate.**

`h_feq`, the functional equation, entirety on `ℂ`, and automorphy of `Sym^r` appear nowhere.

**Not proven here, and not proven anywhere in this repository:** the local analytic input itself.
For a Maass form, holomorphy and nonvanishing of `L(s, Sym^r)` on a neighbourhood of `Re s ≥ 1`
at every rank is not known — this is the open problem, and the theorem below is a reduction to it,
not a proof of it.
-/

set_option maxHeartbeats 1000000

open Filter Topology Asymptotics

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate

/-- The per-rank local analytic input: holomorphy on a neighbourhood of the closed readout
half-plane, agreement with the bank Dirichlet series to the right of it, and nonvanishing.  This
is the whole of what the consumer chain asks of the analytic side. -/
structure LocalAnalyticInput3D
    (M : GenuineMaassCuspForm3D) {D : (r : ℕ) → ArithmeticCPSCompletionData r 1}
    (L : ∀ r : ℕ, 1 ≤ r → ConventionalCompletedRankinSelbergSource3D r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D (D r)) where
  cand : ℕ → ℂ → ℂ
  domain : ℕ → Set ℂ
  domain_open : ∀ r, IsOpen (domain r)
  domain_mem : ∀ r, {s : ℂ | 1 ≤ s.re} ⊆ domain r
  cand_diff : ∀ r, DifferentiableOn ℂ (cand r) (domain r)
  cand_eq : ∀ (r : ℕ) (hr : 1 ≤ r),
    Set.EqOn (cand r) (LSeries (⇑(L r hr).arithmeticCoefficient)) {s : ℂ | 1 < s.re}
  cand_ne : ∀ (r : ℕ) (s : ℂ), 1 ≤ s.re → cand r s ≠ 0

/-- The `o(N)` estimate for every rung, from the local input. -/
theorem LocalAnalyticInput3D.cumsum_isLittleO
    {M : GenuineMaassCuspForm3D} (hC : MaassTowerCeiling M.eigenData)
    {D : (r : ℕ) → ArithmeticCPSCompletionData r 1}
    {L : ∀ r : ℕ, 1 ≤ r → ConventionalCompletedRankinSelbergSource3D r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D (D r)}
    (A : LocalAnalyticInput3D M L) (r : ℕ) (hr : 1 ≤ r) :
    (fun N : ℕ ↦ cumsum (fun n => ((L r hr).logarithmicCoefficient n).re) N) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) :=
  cumsum_isLittleO_of_localHolomorphy hC (L r hr) (A.cand r) (A.domain r) (A.domain_open r)
    (A.domain_mem r) (A.cand_diff r) (A.cand_eq r hr) (A.cand_ne r)

/-- **Sato--Tate from the local analytic input.**  Every hypothesis other than `A` is discharged
from the tower: the ceiling gives temperedness and hence unit roots and real power sums, and the
compiled chain supplies the Euler identification, the edge argument and the Tauberian transfer.
The functional equation is never used.

The `sources` field of the tower is used only for coefficient bookkeeping; `A` carries the whole
analytic content. -/
theorem maassSatoTate_of_localAnalyticInput
    {M : GenuineMaassCuspForm3D}
    {X P : ℕ → Type*} {U : (r : ℕ) → P r → Type*}
    {Vlocal : ℕ → Nat.Primes → Type*} {Ares Wres Vres : ℕ → ℕ → Type*}
    [∀ r, TopologicalSpace (X r)] [∀ r, AddCommGroup (X r)] [∀ r, Module ℂ (X r)]
    [∀ r, MulAction (AdelicGL (r + 1)) (X r)]
    [∀ r, ContinuousSMul (AdelicGL (r + 1)) (X r)]
    [∀ r q, MeasurableSpace (U r q)] [∀ r q, Group (U r q)]
    [∀ r q, MeasurableMul (U r q)] [∀ r q, MeasurableInv (U r q)]
    [∀ r p, AddCommGroup (Vlocal r p)] [∀ r p, Module ℂ (Vlocal r p)]
    [∀ r m, Ring (Ares r m)] [∀ r m, Algebra ℂ (Ares r m)]
    [∀ r m, AddCommGroup (Wres r m)] [∀ r m, Module ℂ (Wres r m)]
    [∀ r m, Module (Ares r m) (Wres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Wres r m)]
    [∀ r m, AddCommGroup (Vres r m)] [∀ r m, Module ℂ (Vres r m)]
    [∀ r m, Module (Ares r m) (Vres r m)]
    [∀ r m, IsScalarTower ℂ (Ares r m) (Vres r m)]
    (T : GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D M X P U Vlocal
      Ares Wres Vres)
    (A : LocalAnalyticInput3D M T.sources.standardSource) :
    ∀ r : ℕ, 1 ≤ r →
      (fun n : ℕ ↦ maassCPSLocalPrimeSummatory M r n) =o[atTop]
        (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))) := by
  intro r hr
  exact T.maassCPSLocalPrimeSummatory_isLittleO_of_cumsum r hr
    (A.cumsum_isLittleO T.toCeiling r hr)

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.LocalAnalyticInput3D.cumsum_isLittleO
#print axioms CriticalLinePhasor.ThreeDConverse.maassSatoTate_of_localAnalyticInput
