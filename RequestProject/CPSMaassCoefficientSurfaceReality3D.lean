import RequestProject.CPSMaassCompletedRankinSelbergTower3D
import RequestProject.RSPositivity

/-!
# The real standard coefficient surface of the Maass CPS tower

This file identifies the retained standard `GL(1)` twist with the ordinary symmetric-power Euler
surface, proves its coefficients are real from the unit Satake circle and clock reversal, and forms
the coefficientwise Rankin--Selberg square used by the positivity/Tauberian layer.
-/

open Complex

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.ExchangeInstrument CriticalLinePhasor.RSPositivity
open CriticalLinePhasor.MaassSatoTate

/-- Complex conjugation commutes with every complete-homogeneous local Euler coefficient. -/
theorem star_radialLocalEulerCoeff
    {ι : Type*} [Fintype ι] (w : ι → ℂ) (n : ℕ) :
    (starRingEnd ℂ) (radialLocalEulerCoeff w n) =
      radialLocalEulerCoeff (fun i => (starRingEnd ℂ) (w i)) n := by
  classical
  unfold radialLocalEulerCoeff
  simp_rw [map_sum, map_prod, map_pow]

/-- Complex conjugation commutes with the multiplicative all-prime Euler coefficient bank. -/
theorem star_radialGlobalSatakeCoeff
    {ι : Type*} [Fintype ι] (w : Nat.Primes → ι → ℂ) (n : ℕ) :
    (starRingEnd ℂ) (radialGlobalSatakeCoeff w n) =
      radialGlobalSatakeCoeff (fun p i => (starRingEnd ℂ) (w p i)) n := by
  classical
  unfold radialGlobalSatakeCoeff
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p _
  exact star_radialLocalEulerCoeff
    (w (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes)) _

/-- For a unitary polynomial Satake pair, conjugating the primal Euler bank gives its literal
contragredient bank. -/
theorem PolynomialSatakeDualPair.star_primalCoeff_eq_dualCoeff_of_unit
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (hunit : ∀ p i, ‖W.primal p i‖ = 1) (n : ℕ) :
    (starRingEnd ℂ) (cpsPolynomialPrimalCoeff W n) =
      cpsPolynomialDualCoeff W n := by
  unfold cpsPolynomialPrimalCoeff cpsPolynomialDualCoeff
  rw [star_radialGlobalSatakeCoeff]
  congr 1
  funext p i
  rw [W.dual_eq_inv]
  exact (Complex.inv_eq_conj (hunit p i)).symm

/-- The exact standard coefficient surface attached to the rank-`r` Maass symmetric power. -/
noncomputable def maassStandardCoefficientSurface
    (M : GenuineMaassCuspForm3D) (r : ℕ) :
    CriticalLinePhasor.RamifiedMechanism.CoefficientSurface :=
  symrSurface (SatakeSeed.ofMaass M.eigenData) r

/-- Every coefficient of the standard Maass symmetric-power Euler surface is real. -/
theorem maassStandardCoefficientSurface_real
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData)
    (r n : ℕ) :
    (starRingEnd ℂ) ((maassStandardCoefficientSurface M r).a n) =
      (maassStandardCoefficientSurface M r).a n := by
  rw [show (maassStandardCoefficientSurface M r).a n =
      cpsPolynomialPrimalCoeff
        (symrSatakePairOf (SatakeSeed.ofMaass M.eigenData) r) n from rfl]
  rw [PolynomialSatakeDualPair.star_primalCoeff_eq_dualCoeff_of_unit]
  · exact symrPairOf_dual_eq_primal (SatakeSeed.ofMaass M.eigenData) r n
  · intro p i
    have ha := maass_temperedness M.eigenData hC p
    simp [symrSatakePairOf, symClockWeight, ha]

/-- Tensoring with the canonical `GL(1)` packet does not change any global Euler coefficient: the
retained standard CPS source is exactly the ordinary symmetric-power surface. -/
theorem standardTwist_primalCoeff_eq_maassStandardCoefficientSurface
    (M : GenuineMaassCuspForm3D) (r n : ℕ) :
    cpsPolynomialPrimalCoeff
        (arithmeticCPSPolynomialTwist r 1 (maassCPSBase M)
          trivialPolynomialSatakePair3D) n =
      (maassStandardCoefficientSurface M r).a n := by
  unfold cpsPolynomialPrimalCoeff maassStandardCoefficientSurface symrSurface
  let e : (Fin (r + 1) × Fin 1) ≃ Fin (r + 1) := Equiv.prodUnique _ _
  rw [show (arithmeticCPSPolynomialTwist r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D).primal =
      fun p => (symrSatakePairOf (SatakeSeed.ofMaass M.eigenData) r).primal p ∘ e by
    funext p i
    simp only [arithmeticCPSPolynomialTwist, arithmeticCPSTensorRoot,
      trivialPolynomialSatakePair3D_primal, mul_one, Function.comp_apply,
      symrSatakePairOf, symClockWeight, maassCPSBase_primal_zero,
      maassCPSBase_primal_one, e, Equiv.prodUnique_apply]
    rw [← zpow_natCast, ← zpow_natCast, inv_zpow',
      ← zpow_add₀ ((SatakeSeed.ofMaass M.eigenData).satake_ne_zero p)]
    congr 1
    have hi : (i.1 : ℕ) ≤ r := Nat.lt_succ_iff.mp i.1.2
    push_cast [Nat.cast_sub hi]
    ring]
  exact CriticalLinePhasor.GenuineGL2Carrier.radialGlobalSatakeCoeff_comp_equiv
    e (symrSatakePairOf (SatakeSeed.ofMaass M.eigenData) r).primal n

/-- The uncompleted Euler function of every conventional retained standard source is literally the
Dirichlet readout of the standard Maass coefficient surface. -/
theorem ConventionalCompletedRankinSelbergSource3D.standard_uncompletedEuler_eq_surface
    {M : GenuineMaassCuspForm3D} {r : ℕ} {D : ArithmeticCPSCompletionData r 1}
    (L : ConventionalCompletedRankinSelbergSource3D r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D D) (s : ℂ) :
    L.uncompletedEuler s =
      CriticalLinePhasor.CarrierTheta.dirichlet
        (maassStandardCoefficientSurface M r).a s := by
  unfold ConventionalCompletedRankinSelbergSource3D.uncompletedEuler
  rw [show cpsPolynomialPrimalCoeff
      (arithmeticCPSPolynomialTwist r 1 (maassCPSBase M)
        trivialPolynomialSatakePair3D) =
      (maassStandardCoefficientSurface M r).a from by
    funext n
    exact standardTwist_primalCoeff_eq_maassStandardCoefficientSurface M r n]

/-- The coefficientwise Rankin--Selberg square of the standard symmetric-power surface. -/
noncomputable def maassStandardRSSquareSurface
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData) (r : ℕ) :
    CriticalLinePhasor.RamifiedMechanism.CoefficientSurface :=
  RSSquareSurface (maassStandardCoefficientSurface M r)
    (maassStandardCoefficientSurface_real M hC r)

/-- The standard coefficientwise Rankin--Selberg square has nonnegative Dirichlet readout on every
real line. -/
theorem maassStandardRSSquare_dirichlet_nonneg
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData)
    (r : ℕ) (σ : ℝ) :
    0 ≤ (CriticalLinePhasor.CarrierTheta.dirichlet
      (maassStandardRSSquareSurface M hC r).a ((σ : ℝ) : ℂ)).re := by
  exact rsSquare_dirichlet_nonneg (maassStandardCoefficientSurface M r)
    (maassStandardCoefficientSurface_real M hC r) σ

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.star_radialLocalEulerCoeff
#print axioms CriticalLinePhasor.ThreeDConverse.star_radialGlobalSatakeCoeff
#print axioms CriticalLinePhasor.ThreeDConverse.PolynomialSatakeDualPair.star_primalCoeff_eq_dualCoeff_of_unit
#print axioms CriticalLinePhasor.ThreeDConverse.maassStandardCoefficientSurface_real
#print axioms CriticalLinePhasor.ThreeDConverse.standardTwist_primalCoeff_eq_maassStandardCoefficientSurface
#print axioms CriticalLinePhasor.ThreeDConverse.ConventionalCompletedRankinSelbergSource3D.standard_uncompletedEuler_eq_surface
#print axioms CriticalLinePhasor.ThreeDConverse.maassStandardRSSquare_dirichlet_nonneg
