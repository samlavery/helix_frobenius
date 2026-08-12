import RequestProject.CPSProfileFunctoriality3D
import RequestProject.GenuineMaassCuspForm3D
import RequestProject.MaassSatoTateClosure

/-!
# From the all-symmetric-power CPS tower to Maass Sato--Tate

This file joins the object-valued CPS lift of every `Sym^r` rung to the typed Maass
Sato--Tate endpoint.

* `maassCPSBase` is the canonical rank-two polynomial Satake pair attached to a
  genuine nonzero cuspidal Hecke--Maass wave.
* `CPSMaassSymmetricPowerTower3D` stores the CPS cuspidal lift at every rank together
  with the standard local bound on every Satake root of the unitary automorphic lift.
* `CPSMaassSymmetricPowerTower3D.toCeiling` reads the extreme roots `j = 0, r` and
  constructs the Maass tower ceiling; hence temperedness is derived from the CPS tower.
* `CPSAutomorphicPrimeTheorem3D` is the typed Jacquet--Shalika/Wiener--Ikehara output:
  cancellation of every nontrivial symmetric-power prime trace.
* `cpsMaassSatoTate3D` composes the two automorphic consequences with the compiled
  character-density bridge and returns temperedness and native carrier equidistribution.

No angle bank or unit-radius hypothesis is supplied.
-/

open Filter Topology Asymptotics
open scoped RestrictedProduct

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate CriticalLinePhasor.SatoTateCarrier3D
open CriticalLinePhasor.RungCapstone

/-! ## The canonical Maass base and its extreme symmetric-power roots -/

/-- The canonical rank-two polynomial Satake pair of a genuine Maass cusp form. -/
noncomputable def maassCPSBase (M : GenuineMaassCuspForm3D) :
    PolynomialSatakeDualPair (Fin 2) :=
  symrSatakePairOf (SatakeSeed.ofMaass M.eigenData) 1

@[simp] theorem maassCPSBase_primal_zero (M : GenuineMaassCuspForm3D)
    (p : Nat.Primes) :
    (maassCPSBase M).primal p 0 = (SatakeSeed.ofMaass M.eigenData).satake p := by
  simp [maassCPSBase, symrSatakePairOf, symClockWeight]

@[simp] theorem maassCPSBase_primal_one (M : GenuineMaassCuspForm3D)
    (p : Nat.Primes) :
    (maassCPSBase M).primal p 1 = ((SatakeSeed.ofMaass M.eigenData).satake p)⁻¹ := by
  simp [maassCPSBase, symrSatakePairOf, symClockWeight]

/-- The top root of the CPS `Sym^r` local packet is the literal power `alpha_p^r`. -/
theorem arithmeticSymmetricPowerRoot_maass_zero (M : GenuineMaassCuspForm3D) (r : ℕ)
    (p : Nat.Primes) :
    arithmeticSymmetricPowerRoot r (maassCPSBase M) p 0 =
      (SatakeSeed.ofMaass M.eigenData).satake p ^ r := by
  simp [arithmeticSymmetricPowerRoot]

/-- The bottom root is the literal reciprocal power `alpha_p⁻¹^r`. -/
theorem arithmeticSymmetricPowerRoot_maass_last (M : GenuineMaassCuspForm3D) (r : ℕ)
    (p : Nat.Primes) :
    arithmeticSymmetricPowerRoot r (maassCPSBase M) p (Fin.last r) =
      ((SatakeSeed.ofMaass M.eigenData).satake p)⁻¹ ^ r := by
  simp [arithmeticSymmetricPowerRoot]

/-- The literal Satake trace used by the Sato--Tate average is exactly the sum of the
local roots supplied to the CPS converse construction. -/
theorem symmetricPowerSatakeTrace_maass_eq_sum_arithmeticRoots
    (M : GenuineMaassCuspForm3D) (r : ℕ) (p : Nat.Primes) :
    symmetricPowerSatakeTrace ((SatakeSeed.ofMaass M.eigenData).satake p) r =
      ∑ j : Fin (r + 1), arithmeticSymmetricPowerRoot r (maassCPSBase M) p j := by
  rw [symmetricPowerSatakeTrace_eq_sum_roots]
  apply Finset.sum_congr rfl
  intro j _
  simp [symmetricPowerSatakeRoot, arithmeticSymmetricPowerRoot]

/-- The prime average written directly in the local-root coordinates of the CPS
`Sym^r` candidate. -/
noncomputable def maassCPSLocalPrimeAverage
    (M : GenuineMaassCuspForm3D) (r n : ℕ) : ℝ :=
  (1 / ((n + 1 : ℕ) : ℝ)) *
    ∑ i : Fin (n + 1),
      (∑ j : Fin (r + 1),
        arithmeticSymmetricPowerRoot r (maassCPSBase M) (nthPrime i) j).re

/-- Exact reduction of the Sato--Tate cancellation average to the CPS candidate's
unramified local-root trace. -/
theorem arithmeticSymmetricPowerPrimeAverage_maass_eq_cpsLocal
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData)
    (r n : ℕ) :
    arithmeticSymmetricPowerPrimeAverage
        (maassSatoTateFamily M.eigenData hC) r n =
      maassCPSLocalPrimeAverage M r n := by
  unfold arithmeticSymmetricPowerPrimeAverage maassSatoTateFamily maassTower
    maassCPSLocalPrimeAverage
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [symmetricPowerSatakeTrace_maass_eq_sum_arithmeticRoots]

/-- Every local root entering the CPS prime trace has unit norm once the all-rank
ceiling has closed the two extreme Satake strands. -/
theorem norm_arithmeticSymmetricPowerRoot_maass
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData)
    (r : ℕ) (p : Nat.Primes) (j : Fin (r + 1)) :
    ‖arithmeticSymmetricPowerRoot r (maassCPSBase M) p j‖ = 1 := by
  have ha := maass_temperedness M.eigenData hC p
  simp [arithmeticSymmetricPowerRoot, ha]

/-- The real local `Sym^r` trace is uniformly bounded by its degree `r+1`. -/
theorem abs_sum_arithmeticSymmetricPowerRoot_maass_re_le
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData)
    (r : ℕ) (p : Nat.Primes) :
    |(∑ j : Fin (r + 1),
      arithmeticSymmetricPowerRoot r (maassCPSBase M) p j).re| ≤ r + 1 := by
  calc
    |(∑ j : Fin (r + 1),
        arithmeticSymmetricPowerRoot r (maassCPSBase M) p j).re| ≤
        ‖∑ j : Fin (r + 1), arithmeticSymmetricPowerRoot r (maassCPSBase M) p j‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑ j : Fin (r + 1),
        ‖arithmeticSymmetricPowerRoot r (maassCPSBase M) p j‖ := norm_sum_le _ _
    _ = r + 1 := by
      simp [norm_arithmeticSymmetricPowerRoot_maass M hC]

/-- Every finite CPS local prime average is uniformly bounded by the degree `r+1`. -/
theorem abs_maassCPSLocalPrimeAverage_le
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData) (r n : ℕ) :
    |maassCPSLocalPrimeAverage M r n| ≤ r + 1 := by
  unfold maassCPSLocalPrimeAverage
  have hden : (0 : ℝ) ≤ 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
  rw [abs_mul, abs_of_nonneg hden]
  calc
    (1 / ((n + 1 : ℕ) : ℝ)) *
        |∑ i : Fin (n + 1),
          (∑ j : Fin (r + 1), arithmeticSymmetricPowerRoot r (maassCPSBase M)
            (nthPrime i) j).re| ≤
        (1 / ((n + 1 : ℕ) : ℝ)) *
          ∑ i : Fin (n + 1),
            |(∑ j : Fin (r + 1), arithmeticSymmetricPowerRoot r (maassCPSBase M)
              (nthPrime i) j).re| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 / ((n + 1 : ℕ) : ℝ)) *
          ∑ _i : Fin (n + 1), (r + 1 : ℝ) := by
      gcongr with i
      exact abs_sum_arithmeticSymmetricPowerRoot_maass_re_le M hC r (nthPrime i)
    _ = r + 1 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-! ## The all-rank CPS automorphy tower -/

/-- The object-valued CPS cuspidal lift at every symmetric-power rank, together with
the standard `p^(1/2)` bound on every local root of each unitary automorphic lift. -/
structure CPSMaassSymmetricPowerTower3D
    (M : GenuineMaassCuspForm3D)
    (X Garch P : Type*) (G : Nat.Primes → Type*) (S : Nat.Primes → Type*)
    [Group Garch] [TopologicalSpace Garch]
    [∀ p, Group (G p)] [∀ p, TopologicalSpace (G p)]
    [∀ p, SetLike (S p) (G p)] [∀ p, SubgroupClass (S p) (G p)]
    (compact : ∀ p, S p)
    [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [MulAction (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    [ContinuousSMul (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    (U : P → Type*)
    [∀ q, MeasurableSpace (U q)] [∀ q, Group (U q)]
    [∀ q, MeasurableMul (U q)] [∀ q, MeasurableInv (U q)]
    (Vlocal : Nat.Primes → Type*)
    [∀ p, AddCommGroup (Vlocal p)] [∀ p, Module ℂ (Vlocal p)]
    (Ares Wres Vres : ℕ → Type*)
    [∀ m, Ring (Ares m)] [∀ m, Algebra ℂ (Ares m)]
    [∀ m, AddCommGroup (Wres m)] [∀ m, Module ℂ (Wres m)]
    [∀ m, Module (Ares m) (Wres m)] [∀ m, IsScalarTower ℂ (Ares m) (Wres m)]
    [∀ m, AddCommGroup (Vres m)] [∀ m, Module ℂ (Vres m)]
    [∀ m, Module (Ares m) (Vres m)] [∀ m, IsScalarTower ℂ (Ares m) (Vres m)] where
  lift : ∀ r : ℕ,
    ArithmeticSymmetricPowerCuspidalLift3D r (maassCPSBase M)
      X Garch P G S compact U Vlocal Ares Wres Vres
  local_bound : ∀ (r : ℕ) (p : Nat.Primes) (j : Fin (r + 1)),
    ‖(lift r).candidate.representation.localSatakeRoot p j‖ ≤ Real.sqrt p.1

/-- The extreme local roots of the all-rank CPS tower construct the uniform Maass
tower ceiling with constant `sqrt p`. -/
noncomputable def CPSMaassSymmetricPowerTower3D.toCeiling
    {M : GenuineMaassCuspForm3D}
    {X Garch P : Type*} {G : Nat.Primes → Type*} {S : Nat.Primes → Type*}
    [Group Garch] [TopologicalSpace Garch]
    [∀ p, Group (G p)] [∀ p, TopologicalSpace (G p)]
    [∀ p, SetLike (S p) (G p)] [∀ p, SubgroupClass (S p) (G p)]
    {compact : ∀ p, S p}
    [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [MulAction (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    [ContinuousSMul (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    {U : P → Type*}
    [∀ q, MeasurableSpace (U q)] [∀ q, Group (U q)]
    [∀ q, MeasurableMul (U q)] [∀ q, MeasurableInv (U q)]
    {Vlocal : Nat.Primes → Type*}
    [∀ p, AddCommGroup (Vlocal p)] [∀ p, Module ℂ (Vlocal p)]
    {Ares Wres Vres : ℕ → Type*}
    [∀ m, Ring (Ares m)] [∀ m, Algebra ℂ (Ares m)]
    [∀ m, AddCommGroup (Wres m)] [∀ m, Module ℂ (Wres m)]
    [∀ m, Module (Ares m) (Wres m)] [∀ m, IsScalarTower ℂ (Ares m) (Wres m)]
    [∀ m, AddCommGroup (Vres m)] [∀ m, Module ℂ (Vres m)]
    [∀ m, Module (Ares m) (Vres m)] [∀ m, IsScalarTower ℂ (Ares m) (Vres m)]
    (T : CPSMaassSymmetricPowerTower3D M X Garch P G S compact U Vlocal
      Ares Wres Vres) : MaassTowerCeiling M.eigenData where
  C := fun p ↦ Real.sqrt p.1
  top := by
    intro p r _
    rw [← arithmeticSymmetricPowerRoot_maass_zero M r p,
      ← (T.lift r).candidate.representation.local_compatible p 0]
    exact T.local_bound r p 0
  bottom := by
    intro p r _
    rw [← arithmeticSymmetricPowerRoot_maass_last M r p,
      ← (T.lift r).candidate.representation.local_compatible p (Fin.last r)]
    exact T.local_bound r p (Fin.last r)

/-- Assemble the tower directly from the warp-to-CPS automorphic object at every rung. -/
noncomputable def CPSMaassSymmetricPowerTower3D.ofRungAutomorphicLifts
    {M : GenuineMaassCuspForm3D}
    {X Garch P : Type*} {G : Nat.Primes → Type*} {S : Nat.Primes → Type*}
    [Group Garch] [TopologicalSpace Garch]
    [∀ p, Group (G p)] [∀ p, TopologicalSpace (G p)]
    [∀ p, SetLike (S p) (G p)] [∀ p, SubgroupClass (S p) (G p)]
    {compact : ∀ p, S p}
    [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [MulAction (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    [ContinuousSMul (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    {U : P → Type*}
    [∀ q, MeasurableSpace (U q)] [∀ q, Group (U q)]
    [∀ q, MeasurableMul (U q)] [∀ q, MeasurableInv (U q)]
    {Vlocal : Nat.Primes → Type*}
    [∀ p, AddCommGroup (Vlocal p)] [∀ p, Module ℂ (Vlocal p)]
    {Ares Wres Vres : ℕ → Type*}
    [∀ m, Ring (Ares m)] [∀ m, Algebra ℂ (Ares m)]
    [∀ m, AddCommGroup (Wres m)] [∀ m, Module ℂ (Wres m)]
    [∀ m, Module (Ares m) (Wres m)] [∀ m, IsScalarTower ℂ (Ares m) (Wres m)]
    [∀ m, AddCommGroup (Vres m)] [∀ m, Module ℂ (Vres m)]
    [∀ m, Module (Ares m) (Vres m)] [∀ m, IsScalarTower ℂ (Ares m) (Vres m)]
    {n : ℕ → ℕ} (W : ∀ r, RungWarpData (n r))
    (rung : ∀ r,
      CPSRungAutomorphicLift3D (n r) r (maassCPSBase M) (W r)
        X Garch P G S compact U Vlocal Ares Wres Vres)
    (local_bound : ∀ (r : ℕ) (p : Nat.Primes) (j : Fin (r + 1)),
      ‖(rung r).lift.candidate.representation.localSatakeRoot p j‖ ≤ Real.sqrt p.1) :
    CPSMaassSymmetricPowerTower3D M X Garch P G S compact U Vlocal
      Ares Wres Vres where
  lift := fun r ↦ (rung r).lift
  local_bound := local_bound

/-! ## The rank-dependent genuine adelic tower -/

/-- The all-rank tower on the literal groups `GL (r+1, 𝔸_ℚ)`.  Unlike
`CPSMaassSymmetricPowerTower3D`, whose group parameters are fixed outside `r`, this carrier makes
the archimedean and finite adelic groups depend on the symmetric-power rank. -/
structure GenuineAdelicCPSMaassSymmetricPowerTower3D (M : GenuineMaassCuspForm3D) where
  lift : ∀ r : ℕ,
    letI := scalarAdelicAction
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
    letI : ContinuousSMul (AdelicGL (r + 1)) ℂ := ⟨continuous_snd⟩
    ArithmeticSymmetricPowerCuspidalLift3D r (maassCPSBase M) ℂ
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ) PUnit
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
      (fun _ ↦ ZeroChannel) (fun _ ↦ ℂ) (fun _ ↦ ℂ)
      (fun _ ↦ Fin 0 → ℂ) (fun _ ↦ ℂ)
  local_bound : ∀ (r : ℕ) (p : Nat.Primes) (j : Fin (r + 1)),
    ‖arithmeticSymmetricPowerRoot r (maassCPSBase M) p j‖ ≤ Real.sqrt p.1

/-- Completed Rankin--Selberg reflected-theta sources at every rank and twist assemble the
rank-dependent genuine adelic tower.  The local bound is stated on the arithmetic roots and is
transported to the exact local Satake roots by the representation compatibility theorem. -/
noncomputable def GenuineAdelicCPSMaassSymmetricPowerTower3D.ofReflectedThetaSources
    (M : GenuineMaassCuspForm3D)
    (source : ∀ (r m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
      (D : GlobalHelix.ArithmeticCPSCompletionData r m) →
        GlobalHelix.ArithmeticCPSReflectedThetaSource r m (maassCPSBase M) tau D)
    (local_bound : ∀ (r : ℕ) (p : Nat.Primes) (j : Fin (r + 1)),
      ‖arithmeticSymmetricPowerRoot r (maassCPSBase M) p j‖ ≤ Real.sqrt p.1) :
    GenuineAdelicCPSMaassSymmetricPowerTower3D M where
  lift := fun r ↦
    scalarGenuineAdelicSymmetricPowerLift3D_ofReflectedThetaSources (source r)
  local_bound := local_bound

/-- The arithmetic root bound is exactly the local Satake-root bound on the rank-`r` adelic
representation constructed by the tower. -/
theorem GenuineAdelicCPSMaassSymmetricPowerTower3D.lift_local_bound
    {M : GenuineMaassCuspForm3D} (T : GenuineAdelicCPSMaassSymmetricPowerTower3D M)
    (r : ℕ) (p : Nat.Primes) (j : Fin (r + 1)) :
    letI := scalarAdelicAction
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
      (fun q ↦ PadicGL (r + 1) q)
      (fun q ↦ Subgroup (PadicGL (r + 1) q))
      (fun q ↦ padicIntegralSubgroup (r + 1) q)
    letI : ContinuousSMul (AdelicGL (r + 1)) ℂ := ⟨continuous_snd⟩
    ‖(T.lift r).candidate.representation.localSatakeRoot p j‖ ≤ Real.sqrt p.1 := by
  letI := scalarAdelicAction
    (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
    (fun q ↦ PadicGL (r + 1) q)
    (fun q ↦ Subgroup (PadicGL (r + 1) q))
    (fun q ↦ padicIntegralSubgroup (r + 1) q)
  letI : ContinuousSMul (AdelicGL (r + 1)) ℂ := ⟨continuous_snd⟩
  rw [(T.lift r).candidate.representation.local_compatible p j]
  exact T.local_bound r p j

/-- The extreme roots of the genuine rank-dependent adelic tower construct the Maass tower
ceiling used by the prime theorem and Sato--Tate endpoint. -/
noncomputable def GenuineAdelicCPSMaassSymmetricPowerTower3D.toCeiling
    {M : GenuineMaassCuspForm3D} (T : GenuineAdelicCPSMaassSymmetricPowerTower3D M) :
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

/-- The genuine adelic all-rank tower retaining the arithmetic warp object and polar-carrier
extinction at every rank. -/
structure GenuineAdelicCPSMaassWarpTower3D
    (M : GenuineMaassCuspForm3D) (n : ℕ → ℕ) (W : ∀ r, RungWarpData (n r)) where
  rung : ∀ r : ℕ,
    letI := scalarAdelicAction
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
    letI : ContinuousSMul (AdelicGL (r + 1)) ℂ := ⟨continuous_snd⟩
    CPSRungAutomorphicLift3D (n r) r (maassCPSBase M) (W r) ℂ
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ) PUnit
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
      (fun _ ↦ ZeroChannel) (fun _ ↦ ℂ) (fun _ ↦ ℂ)
      (fun _ ↦ Fin 0 → ℂ) (fun _ ↦ ℂ)
  local_bound : ∀ (r : ℕ) (p : Nat.Primes) (j : Fin (r + 1)),
    ‖arithmeticSymmetricPowerRoot r (maassCPSBase M) p j‖ ≤ Real.sqrt p.1

/-- Completed Rankin--Selberg sources and arithmetic warp data assemble the full warp-preserving
genuine adelic tower. -/
noncomputable def GenuineAdelicCPSMaassWarpTower3D.ofReflectedThetaSources
    (M : GenuineMaassCuspForm3D) {n : ℕ → ℕ} (W : ∀ r, RungWarpData (n r))
    (source : ∀ (r m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
      (D : GlobalHelix.ArithmeticCPSCompletionData r m) →
        GlobalHelix.ArithmeticCPSReflectedThetaSource r m (maassCPSBase M) tau D)
    (local_bound : ∀ (r : ℕ) (p : Nat.Primes) (j : Fin (r + 1)),
      ‖arithmeticSymmetricPowerRoot r (maassCPSBase M) p j‖ ≤ Real.sqrt p.1) :
    GenuineAdelicCPSMaassWarpTower3D M n W where
  rung := fun r ↦
    scalarGenuineAdelicCPSRungAutomorphicLift3D_ofReflectedThetaSources (W r) (source r)
  local_bound := local_bound

/-- Forgetting the polar-carrier component of every rung gives the genuine adelic CPS tower used
by the automorphic-prime and Sato--Tate endpoints. -/
noncomputable def GenuineAdelicCPSMaassWarpTower3D.toSymmetricPowerTower
    {M : GenuineMaassCuspForm3D} {n : ℕ → ℕ} {W : ∀ r, RungWarpData (n r)}
    (T : GenuineAdelicCPSMaassWarpTower3D M n W) :
    GenuineAdelicCPSMaassSymmetricPowerTower3D M where
  lift := fun r ↦ by
    letI := scalarAdelicAction
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
    letI : ContinuousSMul (AdelicGL (r + 1)) ℂ := ⟨continuous_snd⟩
    exact (T.rung r).lift
  local_bound := T.local_bound

/-! ## The automorphic prime theorem and the Sato--Tate endpoint -/

/-- The unnormalized first-prime summatory function of the literal CPS `Sym^r` trace. -/
noncomputable def maassCPSLocalPrimeSummatory
    (M : GenuineMaassCuspForm3D) (r n : ℕ) : ℝ :=
  ∑ i : Fin (n + 1),
    (∑ j : Fin (r + 1),
      arithmeticSymmetricPowerRoot r (maassCPSBase M) (nthPrime i) j).re

/-- The standard summatory little-`o` conclusion delivered by the cited automorphic
Wiener--Ikehara argument, stated on the exact CPS local-root trace. -/
structure CPSWienerIkeharaOutput3D
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData) : Prop where
  summatory_littleO : ∀ r : ℕ, 1 ≤ r →
    (fun n : ℕ ↦ maassCPSLocalPrimeSummatory M r n) =o[atTop]
      (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)))

/-- The cited Wiener--Ikehara summatory conclusion implies the literal symmetric-power
prime cancellation consumed by the Sato--Tate endpoint. -/
theorem CPSWienerIkeharaOutput3D.toPrimeCancellation
    {M : GenuineMaassCuspForm3D} {hC : MaassTowerCeiling M.eigenData}
    (W : CPSWienerIkeharaOutput3D M hC) :
    ArithmeticSymmetricPowerPrimeCancellation (maassSatoTateFamily M.eigenData hC) where
  tendsto_zero := by
    intro r hr
    have h := (W.summatory_littleO r hr).tendsto_div_nhds_zero
    simpa only [arithmeticSymmetricPowerPrimeAverage_maass_eq_cpsLocal,
      maassCPSLocalPrimeAverage, maassCPSLocalPrimeSummatory, div_eq_mul_inv,
      mul_comm, one_mul, mul_one] using h

/-- The prime theorem attached to the all-symmetric-power automorphic tower: every
nontrivial literal symmetric-power prime-trace average tends to zero. -/
structure CPSAutomorphicPrimeTheorem3D
    {M : GenuineMaassCuspForm3D}
    {X Garch P : Type*} {G : Nat.Primes → Type*} {S : Nat.Primes → Type*}
    [Group Garch] [TopologicalSpace Garch]
    [∀ p, Group (G p)] [∀ p, TopologicalSpace (G p)]
    [∀ p, SetLike (S p) (G p)] [∀ p, SubgroupClass (S p) (G p)]
    {compact : ∀ p, S p}
    [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [MulAction (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    [ContinuousSMul (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    {U : P → Type*}
    [∀ q, MeasurableSpace (U q)] [∀ q, Group (U q)]
    [∀ q, MeasurableMul (U q)] [∀ q, MeasurableInv (U q)]
    {Vlocal : Nat.Primes → Type*}
    [∀ p, AddCommGroup (Vlocal p)] [∀ p, Module ℂ (Vlocal p)]
    {Ares Wres Vres : ℕ → Type*}
    [∀ m, Ring (Ares m)] [∀ m, Algebra ℂ (Ares m)]
    [∀ m, AddCommGroup (Wres m)] [∀ m, Module ℂ (Wres m)]
    [∀ m, Module (Ares m) (Wres m)] [∀ m, IsScalarTower ℂ (Ares m) (Wres m)]
    [∀ m, AddCommGroup (Vres m)] [∀ m, Module ℂ (Vres m)]
    [∀ m, Module (Ares m) (Vres m)] [∀ m, IsScalarTower ℂ (Ares m) (Vres m)]
    (T : CPSMaassSymmetricPowerTower3D M X Garch P G S compact U Vlocal
      Ares Wres Vres) where
  cancellation : ArithmeticSymmetricPowerPrimeCancellation
    (maassSatoTateFamily M.eigenData T.toCeiling)

/-- The automorphic prime theorem for the rank-dependent genuine adelic tower. -/
structure GenuineAdelicCPSAutomorphicPrimeTheorem3D
    {M : GenuineMaassCuspForm3D} (T : GenuineAdelicCPSMaassSymmetricPowerTower3D M) where
  cancellation : ArithmeticSymmetricPowerPrimeCancellation
    (maassSatoTateFamily M.eigenData T.toCeiling)

/-- The Wiener--Ikehara summatory output constructs the automorphic prime theorem on the genuine
adelic tower. -/
theorem GenuineAdelicCPSAutomorphicPrimeTheorem3D.ofWienerIkehara
    {M : GenuineMaassCuspForm3D} {T : GenuineAdelicCPSMaassSymmetricPowerTower3D M}
    (W : CPSWienerIkeharaOutput3D M T.toCeiling) :
    GenuineAdelicCPSAutomorphicPrimeTheorem3D T where
  cancellation := W.toPrimeCancellation

/-- **Maass Sato--Tate from the full CPS symmetric-power tower.**  The local bounds
on the CPS lifts force unit radius, and the automorphic prime theorem supplies the
character averages consumed by the native three-dimensional density theorem. -/
theorem cpsMaassSatoTate3D
    {M : GenuineMaassCuspForm3D}
    {X Garch P : Type*} {G : Nat.Primes → Type*} {S : Nat.Primes → Type*}
    [Group Garch] [TopologicalSpace Garch]
    [∀ p, Group (G p)] [∀ p, TopologicalSpace (G p)]
    [∀ p, SetLike (S p) (G p)] [∀ p, SubgroupClass (S p) (G p)]
    {compact : ∀ p, S p}
    [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [MulAction (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    [ContinuousSMul (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    {U : P → Type*}
    [∀ q, MeasurableSpace (U q)] [∀ q, Group (U q)]
    [∀ q, MeasurableMul (U q)] [∀ q, MeasurableInv (U q)]
    {Vlocal : Nat.Primes → Type*}
    [∀ p, AddCommGroup (Vlocal p)] [∀ p, Module ℂ (Vlocal p)]
    {Ares Wres Vres : ℕ → Type*}
    [∀ m, Ring (Ares m)] [∀ m, Algebra ℂ (Ares m)]
    [∀ m, AddCommGroup (Wres m)] [∀ m, Module ℂ (Wres m)]
    [∀ m, Module (Ares m) (Wres m)] [∀ m, IsScalarTower ℂ (Ares m) (Wres m)]
    [∀ m, AddCommGroup (Vres m)] [∀ m, Module ℂ (Vres m)]
    [∀ m, Module (Ares m) (Vres m)] [∀ m, IsScalarTower ℂ (Ares m) (Vres m)]
    (T : CPSMaassSymmetricPowerTower3D M X Garch P G S compact U Vlocal
      Ares Wres Vres)
    (PNT : CPSAutomorphicPrimeTheorem3D T) :
    (∀ p : Nat.Primes, ‖(SatakeSeed.ofMaass M.eigenData).satake p‖ = 1) ∧
      Tendsto
        (empiricalPrimeCarrierMeasure
          (maassSatoTateFamily M.eigenData T.toCeiling).angle)
        atTop (nhds carrierProbability) :=
  ⟨fun p ↦ maass_temperedness M.eigenData T.toCeiling p,
    empiricalPrimeCarrierMeasure_tendsto_of_arithmeticSatakeCancellation
      (maassSatoTateFamily M.eigenData T.toCeiling) PNT.cancellation⟩

/-- Maass Sato--Tate from the rank-dependent genuine adelic CPS tower and its automorphic prime
theorem. -/
theorem genuineAdelicCPSMaassSatoTate3D
    {M : GenuineMaassCuspForm3D} (T : GenuineAdelicCPSMaassSymmetricPowerTower3D M)
    (PNT : GenuineAdelicCPSAutomorphicPrimeTheorem3D T) :
    (∀ p : Nat.Primes, ‖(SatakeSeed.ofMaass M.eigenData).satake p‖ = 1) ∧
      Tendsto
        (empiricalPrimeCarrierMeasure (maassSatoTateFamily M.eigenData T.toCeiling).angle)
        atTop (nhds carrierProbability) :=
  ⟨fun p ↦ maass_temperedness M.eigenData T.toCeiling p,
    empiricalPrimeCarrierMeasure_tendsto_of_arithmeticSatakeCancellation
      (maassSatoTateFamily M.eigenData T.toCeiling) PNT.cancellation⟩

/-- The direct closing composition from the genuine adelic tower and Wiener--Ikehara output to
Maass Sato--Tate. -/
theorem genuineAdelicCPSMaassSatoTate3D_ofWienerIkehara
    {M : GenuineMaassCuspForm3D} (T : GenuineAdelicCPSMaassSymmetricPowerTower3D M)
    (W : CPSWienerIkeharaOutput3D M T.toCeiling) :
    (∀ p : Nat.Primes, ‖(SatakeSeed.ofMaass M.eigenData).satake p‖ = 1) ∧
      Tendsto
        (empiricalPrimeCarrierMeasure (maassSatoTateFamily M.eigenData T.toCeiling).angle)
        atTop (nhds carrierProbability) :=
  genuineAdelicCPSMaassSatoTate3D T
    (GenuineAdelicCPSAutomorphicPrimeTheorem3D.ofWienerIkehara W)

/-- The complete closing composition for the warp-preserving tower. -/
theorem genuineAdelicCPSMaassWarpSatoTate3D_ofWienerIkehara
    {M : GenuineMaassCuspForm3D} {n : ℕ → ℕ} {W : ∀ r, RungWarpData (n r)}
    (T : GenuineAdelicCPSMaassWarpTower3D M n W)
    (WI : CPSWienerIkeharaOutput3D M T.toSymmetricPowerTower.toCeiling) :
    (∀ p : Nat.Primes, ‖(SatakeSeed.ofMaass M.eigenData).satake p‖ = 1) ∧
      Tendsto
        (empiricalPrimeCarrierMeasure
          (maassSatoTateFamily M.eigenData T.toSymmetricPowerTower.toCeiling).angle)
        atTop (nhds carrierProbability) :=
  genuineAdelicCPSMaassSatoTate3D_ofWienerIkehara T.toSymmetricPowerTower WI

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.CPSMaassSymmetricPowerTower3D.toCeiling
#print axioms CriticalLinePhasor.ThreeDConverse.CPSMaassSymmetricPowerTower3D.ofRungAutomorphicLifts
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCPSMaassSymmetricPowerTower3D.ofReflectedThetaSources
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCPSMaassSymmetricPowerTower3D.lift_local_bound
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCPSMaassSymmetricPowerTower3D.toCeiling
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCPSMaassWarpTower3D.ofReflectedThetaSources
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCPSMaassWarpTower3D.toSymmetricPowerTower
#print axioms CriticalLinePhasor.ThreeDConverse.symmetricPowerSatakeTrace_maass_eq_sum_arithmeticRoots
#print axioms CriticalLinePhasor.ThreeDConverse.arithmeticSymmetricPowerPrimeAverage_maass_eq_cpsLocal
#print axioms CriticalLinePhasor.ThreeDConverse.norm_arithmeticSymmetricPowerRoot_maass
#print axioms CriticalLinePhasor.ThreeDConverse.abs_sum_arithmeticSymmetricPowerRoot_maass_re_le
#print axioms CriticalLinePhasor.ThreeDConverse.abs_maassCPSLocalPrimeAverage_le
#print axioms CriticalLinePhasor.ThreeDConverse.CPSWienerIkeharaOutput3D.toPrimeCancellation
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineAdelicCPSAutomorphicPrimeTheorem3D.ofWienerIkehara
#print axioms CriticalLinePhasor.ThreeDConverse.cpsMaassSatoTate3D
#print axioms CriticalLinePhasor.ThreeDConverse.genuineAdelicCPSMaassSatoTate3D
#print axioms CriticalLinePhasor.ThreeDConverse.genuineAdelicCPSMaassSatoTate3D_ofWienerIkehara
#print axioms CriticalLinePhasor.ThreeDConverse.genuineAdelicCPSMaassWarpSatoTate3D_ofWienerIkehara
