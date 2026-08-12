import RequestProject.CPSMaassSatakeRealizedTower3D
import RequestProject.CPSLocalEulerLogDerivative3D
import RequestProject.CPSUncompletedContinuation3D

/-!
# A source-retaining genuine adelic Maass CPS tower

The representation-bound Maass tower previously consumed its reflected-theta sources during the
CPS construction and then discarded them.  This file retains those exact completed
Rankin--Selberg sources beside the resulting genuine adelic tower.  It also records the standard
`GL(1)` twist at every rank, including rank one, so the automorphic-prime step can read the
standard symmetric-power logarithmic derivative without reconstructing analytic metadata.
-/

open scoped RestrictedProduct

namespace CriticalLinePhasor.GlobalHelix

/-- The canonical degree-one trivial Satake pair. -/
noncomputable def trivialPolynomialSatakePair3D : PolynomialSatakeDualPair (Fin 1) where
  primal := fun _ _ => 1
  dual := fun _ _ => 1
  primalExponent := 0
  dualExponent := 0
  primal_ne_zero := fun _ _ => one_ne_zero
  dual_eq_inv := fun _ _ => by simp
  primal_bound := fun _ _ => by simp
  dual_bound := fun _ _ => by simp

@[simp] theorem trivialPolynomialSatakePair3D_primal (p : Nat.Primes) (i : Fin 1) :
    trivialPolynomialSatakePair3D.primal p i = 1 := rfl

@[simp] theorem trivialPolynomialSatakePair3D_dual (p : Nat.Primes) (i : Fin 1) :
    trivialPolynomialSatakePair3D.dual p i = 1 := rfl

/-- Tensoring a symmetric-power packet with the canonical trivial degree-one packet changes no
local root. -/
theorem arithmeticCPSTensorRoot_trivialPolynomialSatakePair3D
    (r : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (p : Nat.Primes) (i : CPSTensorIndex r 1) :
    arithmeticCPSTensorRoot r 1 pi trivialPolynomialSatakePair3D p i =
      CriticalLinePhasor.ThreeDConverse.arithmeticSymmetricPowerRoot r pi p i.1 := by
  simp [arithmeticCPSTensorRoot,
    CriticalLinePhasor.ThreeDConverse.arithmeticSymmetricPowerRoot]

/-- The tensor-indexed power sum for the trivial degree-one twist is the ordinary
symmetric-power power sum. -/
theorem sum_arithmeticCPSTensorRoot_trivialPolynomialSatakePair3D
    (r j : ℕ) (pi : PolynomialSatakeDualPair (Fin 2)) (p : Nat.Primes) :
    (∑ i : CPSTensorIndex r 1,
        arithmeticCPSTensorRoot r 1 pi trivialPolynomialSatakePair3D p i ^ j) =
      ∑ i : Fin (r + 1),
        CriticalLinePhasor.ThreeDConverse.arithmeticSymmetricPowerRoot r pi p i ^ j := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [arithmeticCPSTensorRoot_trivialPolynomialSatakePair3D]

/-- The completed Rankin--Selberg source family retained by the Maass tower.  `standardSource`
is the trivial `GL(1)` twist at every positive symmetric-power rank; `twistedSource` is the full
CPS converse family. -/
structure MaassCompletedRankinSelbergSourceFamily3D
    (M : CriticalLinePhasor.ThreeDConverse.GenuineMaassCuspForm3D) where
  standardCompletion : (r : ℕ) → ArithmeticCPSCompletionData r 1
  standardSource : ∀ r : ℕ, 1 ≤ r →
    ConventionalCompletedRankinSelbergSource3D r 1
      (CriticalLinePhasor.ThreeDConverse.maassCPSBase M)
      trivialPolynomialSatakePair3D (standardCompletion r)
  twistedSource : ∀ (r m : ℕ), 1 ≤ m → m < r →
    (tau : PolynomialSatakeDualPair (Fin m)) →
    (D : ArithmeticCPSCompletionData r m) →
      ConventionalCompletedRankinSelbergSource3D r m
        (CriticalLinePhasor.ThreeDConverse.maassCPSBase M) tau D

end CriticalLinePhasor.GlobalHelix

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate

/-- The representation-bound genuine adelic tower together with the exact completed
Rankin--Selberg sources used to construct all of its lifts. -/
structure GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D
    (M : GenuineMaassCuspForm3D)
    (X P : ℕ → Type*) (U : (r : ℕ) → P r → Type*)
    (Vlocal : ℕ → Nat.Primes → Type*)
    (Ares Wres Vres : ℕ → ℕ → Type*)
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
    [∀ r m, IsScalarTower ℂ (Ares r m) (Vres r m)] where
  sources : MaassCompletedRankinSelbergSourceFamily3D M
  tower : GenuineAdelicSatakeRealizedCPSMaassTower3D M X P U Vlocal Ares Wres Vres

/-- Construct the source-retaining tower.  The reflected-theta source passed into the CPS
constructor is definitionally the source stored in the returned object. -/
noncomputable def GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.ofCompletedSources
    (M : GenuineMaassCuspForm3D)
    {X P : ℕ → Type*} {U : (r : ℕ) → P r → Type*}
    {Vlocal : ℕ → Nat.Primes → Type*}
    {Ares Wres Vres : ℕ → ℕ → Type*}
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
    (sources : MaassCompletedRankinSelbergSourceFamily3D M)
    (representation : ∀ r,
      SatakeRealizedRestrictedSymmetricPowerRepresentation3D r (maassCPSBase M)
        (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
        (fun p ↦ PadicGL (r + 1) p)
        (fun p ↦ Subgroup (PadicGL (r + 1) p))
        (fun p ↦ padicIntegralSubgroup (r + 1) p) (Vlocal r) (X r))
    (bank : ∀ r, GenuineAdelicCPSBankBridge3D (r + 1) (X r) (P r) (U r))
    (residual : ∀ (r m : ℕ), 1 ≤ m → m < r →
      (tau : PolynomialSatakeDualPair (Fin m)) →
        EquivariantCPSResidual3D (Ares r m) (Wres r m) (Vres r m))
    (local_bound : ∀ (r : ℕ) (p : Nat.Primes) (j : Fin (r + 1)),
      ‖arithmeticSymmetricPowerRoot r (maassCPSBase M) p j‖ ≤ Real.sqrt p.1) :
    GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D M X P U Vlocal
      Ares Wres Vres where
  sources := sources
  tower := GenuineAdelicSatakeRealizedCPSMaassTower3D.ofReflectedThetaSources M
    representation bank
    (fun r m hm hmr tau D ↦ (sources.twistedSource r m hm hmr tau D).source)
    residual local_bound

/-- The source-retaining tower has the same rank-uniform ceiling as its representation-bound
genuine adelic tower. -/
noncomputable def GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.toCeiling
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
      Ares Wres Vres) : MaassTowerCeiling M.eigenData :=
  T.tower.toCeiling

/-- The entire uncompleted standard symmetric-power continuation retained at rank `r`. -/
noncomputable def GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardContinuation
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
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r) : ℂ → ℂ :=
  (T.sources.standardSource r hr).uncompletedContinuation

/-- The retained standard continuation is entire at every symmetric-power rank. -/
theorem GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardContinuation_entire
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
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r) :
    Differentiable ℂ (T.standardContinuation r hr) :=
  (T.sources.standardSource r hr).uncompletedContinuation_entire

/-- On every common initial point, the tower's standard continuation is the literal Euler readout
whose logarithmic coefficients were identified with symmetric-power Satake power sums below. -/
theorem GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardContinuation_initialIdentification
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
      Ares Wres Vres) (r : ℕ) (hr : 1 ≤ r)
    (point : CPSCompletionPoint
      (arithmeticCPSPolynomialTwist r 1 (maassCPSBase M) trivialPolynomialSatakePair3D)
      ((T.sources.standardCompletion r).clock one_pos)) :
    T.standardContinuation r hr point.s =
      (T.sources.standardSource r hr).uncompletedEuler point.s :=
  (T.sources.standardSource r hr).uncompletedContinuation_initialIdentification one_pos point

/-- Every positive prime-power logarithmic coefficient of the retained standard source is the
literal symmetric-power Satake power sum, in its one-dimensional tensor indexing. -/
theorem GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standard_logarithmicCoefficient
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
    (r : ℕ) (hr : 1 ≤ r) {p j : ℕ} (hp : p.Prime) (hj : 0 < j) :
    (T.sources.standardSource r hr).logarithmicCoefficient (p ^ j) =
      Complex.log (p : ℂ) *
        ∑ i : CPSTensorIndex r 1,
          arithmeticCPSTensorRoot r 1 (maassCPSBase M) trivialPolynomialSatakePair3D
            (show Nat.Primes from ⟨p, hp⟩) i ^ j := by
  exact logarithmicCoefficient_prime_pow_eq_satakePowerSum
    (T.sources.standardSource r hr) hp hj

/-- The retained standard source reads the ordinary rank-`r` symmetric-power power sum, with no
residual `Fin 1` tensor coordinate. -/
theorem GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standard_logarithmicCoefficient_eq_sum
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
    (r : ℕ) (hr : 1 ≤ r) {p j : ℕ} (hp : p.Prime) (hj : 0 < j) :
    (T.sources.standardSource r hr).logarithmicCoefficient (p ^ j) =
      Complex.log (p : ℂ) *
        ∑ i : Fin (r + 1),
          arithmeticSymmetricPowerRoot r (maassCPSBase M)
            (show Nat.Primes from ⟨p, hp⟩) i ^ j := by
  rw [T.standard_logarithmicCoefficient r hr hp hj,
    sum_arithmeticCPSTensorRoot_trivialPolynomialSatakePair3D]

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.GlobalHelix.trivialPolynomialSatakePair3D
#print axioms CriticalLinePhasor.GlobalHelix.arithmeticCPSTensorRoot_trivialPolynomialSatakePair3D
#print axioms CriticalLinePhasor.GlobalHelix.sum_arithmeticCPSTensorRoot_trivialPolynomialSatakePair3D
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.ofCompletedSources
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.toCeiling
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardContinuation_entire
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standardContinuation_initialIdentification
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standard_logarithmicCoefficient
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCompletedSatakeRealizedCPSMaassTower3D.standard_logarithmicCoefficient_eq_sum
