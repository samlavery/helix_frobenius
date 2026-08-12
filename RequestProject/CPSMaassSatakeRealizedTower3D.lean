import RequestProject.CPSMaassSatoTate3D
import RequestProject.CPSUnramifiedSatakeRealization3D

/-!
# The representation-bound genuine adelic Maass symmetric-power tower

Unlike the legacy scalar tower, the global and local representation spaces in this file vary with
the symmetric-power rank.  Every returned CPS lift retains a spherical-Hecke realization of its
literal arithmetic Satake roots.
-/

open scoped RestrictedProduct

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate

/-- The all-rank genuine adelic CPS tower on rank-dependent representation spaces, with every
local Satake packet realized by the actual finite-place representation. -/
structure GenuineAdelicSatakeRealizedCPSMaassTower3D
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
  lift : ∀ r,
    SatakeRealizedArithmeticSymmetricPowerCuspidalLift3D r (maassCPSBase M) (X r)
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ) (P r)
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
      (U r) (Vlocal r) (Ares r) (Wres r) (Vres r)
  local_bound : ∀ (r : ℕ) (p : Nat.Primes) (j : Fin (r + 1)),
    ‖arithmeticSymmetricPowerRoot r (maassCPSBase M) p j‖ ≤ Real.sqrt p.1

/-- Completed reflected-theta sources, genuine adelic banks, and representation-bound local
Satake realizations assemble the genuine all-rank tower without a scalar carrier substitution. -/
noncomputable def GenuineAdelicSatakeRealizedCPSMaassTower3D.ofReflectedThetaSources
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
    (representation : ∀ r,
      SatakeRealizedRestrictedSymmetricPowerRepresentation3D r (maassCPSBase M)
        (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
        (fun p ↦ PadicGL (r + 1) p)
        (fun p ↦ Subgroup (PadicGL (r + 1) p))
        (fun p ↦ padicIntegralSubgroup (r + 1) p) (Vlocal r) (X r))
    (bank : ∀ r, GenuineAdelicCPSBankBridge3D (r + 1) (X r) (P r) (U r))
    (source : ∀ (r m : ℕ), 1 ≤ m → m < r →
      (tau : PolynomialSatakeDualPair (Fin m)) →
      (D : ArithmeticCPSCompletionData r m) →
        ArithmeticCPSReflectedThetaSource r m (maassCPSBase M) tau D)
    (residual : ∀ (r m : ℕ), 1 ≤ m → m < r →
      (tau : PolynomialSatakeDualPair (Fin m)) →
        EquivariantCPSResidual3D (Ares r m) (Wres r m) (Vres r m))
    (local_bound : ∀ (r : ℕ) (p : Nat.Primes) (j : Fin (r + 1)),
      ‖arithmeticSymmetricPowerRoot r (maassCPSBase M) p j‖ ≤ Real.sqrt p.1) :
    GenuineAdelicSatakeRealizedCPSMaassTower3D M X P U Vlocal Ares Wres Vres where
  lift := fun r ↦
    SatakeRealizedArithmeticSymmetricPowerCuspidalLift3D.ofReflectedThetaSources
      (representation r) (bank r).bridge (source r) (residual r)
  local_bound := local_bound

/-- The arithmetic root bound is transported to the local Satake roots of the exact realized
finite-place representation. -/
theorem GenuineAdelicSatakeRealizedCPSMaassTower3D.lift_local_bound
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
    (T : GenuineAdelicSatakeRealizedCPSMaassTower3D M X P U Vlocal Ares Wres Vres)
    (r : ℕ) (p : Nat.Primes) (j : Fin (r + 1)) :
    ‖(T.lift r).lift.candidate.representation.localSatakeRoot p j‖ ≤ Real.sqrt p.1 := by
  rw [(T.lift r).lift.candidate.representation.local_compatible p j]
  exact T.local_bound r p j

/-- The extreme roots of the representation-bound all-rank tower construct the Maass tower
ceiling used by the prime theorem and Sato--Tate endpoint. -/
noncomputable def GenuineAdelicSatakeRealizedCPSMaassTower3D.toCeiling
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
    (T : GenuineAdelicSatakeRealizedCPSMaassTower3D M X P U Vlocal Ares Wres Vres) :
    MaassTowerCeiling M.eigenData where
  C := fun p ↦ Real.sqrt p.1
  top := by
    intro p r _
    rw [← arithmeticSymmetricPowerRoot_maass_zero M r p]
    exact T.local_bound r p 0
  bottom := by
    intro p r _
    rw [← arithmeticSymmetricPowerRoot_maass_last M r p]
    exact T.local_bound r p (Fin.last r)

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicSatakeRealizedCPSMaassTower3D.ofReflectedThetaSources
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicSatakeRealizedCPSMaassTower3D.lift_local_bound
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicSatakeRealizedCPSMaassTower3D.toCeiling
