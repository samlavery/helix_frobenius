import RequestProject.CPSMaassCompletedRankinSelbergTower3D
import RequestProject.CPSBankEulerProduct3D
import RequestProject.CPSContinuationDescent3D
import RequestProject.CPSSymmetricPowerRootReality3D

/-!
# The identification seam, closed

Composing the Euler product with the continuation descent identifies the tower's **entire**
continuation with the bank Euler readout on the whole readout half-plane, and hence shows it does
not vanish there.  For the retained standard Maass rung the tensor index `Fin (r+1) × Fin 1`
collapses to `Fin (r+1)`, so the readout is the symmetric-power one that the edge argument names.

This closes the `hCeq` hypothesis of `maass_edge_nonvanishing` from the tower ceiling alone.  Two
inputs of that theorem remain open and are stated, not assumed: the companion identification
`hDeq` with its simple-pole bound (the diagonal Rankin--Selberg side), and the point `y = 0`.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix
namespace ConventionalCompletedRankinSelbergSource3D

open CriticalLinePhasor.ThreeDConverse

variable {r m : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
  {tau : PolynomialSatakeDualPair (Fin m)}
  {D : ArithmeticCPSCompletionData r m}

/-- **The identification seam.**  The entire continuation is the bank Euler readout on the whole
readout half-plane. -/
theorem uncompletedContinuation_eqOn_bankEulerReadout
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) (hm : 0 < m)
    (htemp : ∀ (p : Nat.Primes) (i : CPSTensorIndex r m),
      ‖(arithmeticCPSPolynomialTwist r m pi tau).primal p i‖ = 1) :
    Set.EqOn L.uncompletedContinuation
      (bankEulerReadout (arithmeticCPSPolynomialTwist r m pi tau).primal)
      {s : ℂ | 1 < s.re} := by
  intro s hs
  rw [uncompletedContinuation_eqOn_LSeries L hm htemp hs]
  exact LSeries_bankArithmetic_eq_bankEulerReadout
    (arithmeticCPSPolynomialTwist r m pi tau).primal htemp hs

/-- The entire continuation does not vanish on the readout half-plane. -/
theorem uncompletedContinuation_ne_zero_of_one_lt_re
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) (hm : 0 < m)
    (htemp : ∀ (p : Nat.Primes) (i : CPSTensorIndex r m),
      ‖(arithmeticCPSPolynomialTwist r m pi tau).primal p i‖ = 1)
    {s : ℂ} (hs : 1 < s.re) :
    L.uncompletedContinuation s ≠ 0 := by
  rw [uncompletedContinuation_eqOn_bankEulerReadout L hm htemp (Set.mem_setOf.mpr hs)]
  exact Complex.exp_ne_zero _

end ConventionalCompletedRankinSelbergSource3D
end CriticalLinePhasor.GlobalHelix

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate

/-- The bank Euler readout only sees the channel multiset, not its enumeration. -/
theorem bankEulerReadout_congr_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : Nat.Primes → κ → ℂ) (s : ℂ) :
    bankEulerReadout (fun p i => w p (e i)) s = bankEulerReadout w s := by
  unfold bankEulerReadout bankEulerLog
  congr 1
  exact tsum_congr fun p => Fintype.sum_equiv e _ _ fun i => rfl

/-- Tensoring with the trivial `GL(1)` packet leaves the Euler readout unchanged: the standard
rung reads the symmetric-power bank. -/
theorem standardTwist_bankEulerReadout
    (M : GenuineMaassCuspForm3D) (r : ℕ) (s : ℂ) :
    bankEulerReadout
        (arithmeticCPSPolynomialTwist r 1 (maassCPSBase M)
          trivialPolynomialSatakePair3D).primal s =
      bankEulerReadout (arithmeticSymmetricPowerRoot r (maassCPSBase M)) s := by
  have hbank :
      (fun (p : Nat.Primes) (i : Fin (r + 1)) =>
        (arithmeticCPSPolynomialTwist r 1 (maassCPSBase M)
          trivialPolynomialSatakePair3D).primal p
            (((Equiv.prodUnique (Fin (r + 1)) (Fin 1)).symm) i)) =
        arithmeticSymmetricPowerRoot r (maassCPSBase M) := by
    funext p i
    simpa [arithmeticCPSPolynomialTwist] using
      arithmeticCPSTensorRoot_trivialPolynomialSatakePair3D r (maassCPSBase M) p
        (((Equiv.prodUnique (Fin (r + 1)) (Fin 1)).symm) i)
  rw [← bankEulerReadout_congr_equiv
    ((Equiv.prodUnique (Fin (r + 1)) (Fin 1)).symm)
    (arithmeticCPSPolynomialTwist r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D).primal s, hbank]

/-- **The standard Maass rung's continuation is the symmetric-power Euler readout on the readout
half-plane**, from the tower ceiling alone. -/
theorem standard_uncompletedContinuation_eqOn_symmetricPowerReadout
    {M : GenuineMaassCuspForm3D} (hC : MaassTowerCeiling M.eigenData) {r : ℕ}
    {D : ArithmeticCPSCompletionData r 1}
    (L : ConventionalCompletedRankinSelbergSource3D r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D D) :
    Set.EqOn L.uncompletedContinuation
      (bankEulerReadout (arithmeticSymmetricPowerRoot r (maassCPSBase M)))
      {s : ℂ | 1 < s.re} := by
  have htemp : ∀ (p : Nat.Primes) (i : CPSTensorIndex r 1),
      ‖(arithmeticCPSPolynomialTwist r 1 (maassCPSBase M)
        trivialPolynomialSatakePair3D).primal p i‖ = 1 := by
    intro p i
    have h := (maass_symmetricPowerRoot_unit_and_real M hC r).1 p i.1
    rw [show (arithmeticCPSPolynomialTwist r 1 (maassCPSBase M)
        trivialPolynomialSatakePair3D).primal p i =
        arithmeticSymmetricPowerRoot r (maassCPSBase M) p i.1 from
      arithmeticCPSTensorRoot_trivialPolynomialSatakePair3D r (maassCPSBase M) p i]
    exact h
  intro s hs
  rw [ConventionalCompletedRankinSelbergSource3D.uncompletedContinuation_eqOn_bankEulerReadout
    L one_pos htemp hs]
  exact standardTwist_bankEulerReadout M r s

/-- **Edge nonvanishing for the standard Maass rung, with only the companion left open.**  The
candidate identification is now discharged from the tower ceiling; what remains supplied are the
diagonal Rankin--Selberg companion and its simple-pole bound. -/
theorem standard_edge_nonvanishing_of_companion
    {M : GenuineMaassCuspForm3D} (hC : MaassTowerCeiling M.eigenData) {r : ℕ}
    {D : ArithmeticCPSCompletionData r 1}
    (L : ConventionalCompletedRankinSelbergSource3D r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D D)
    {Dcomp : ℂ → ℂ}
    (hDeq : Set.EqOn Dcomp
      (bankEulerReadout (pairBank (arithmeticSymmetricPowerRoot r (maassCPSBase M))))
      {s : ℂ | 1 < s.re})
    {y K K₂ : ℝ}
    (hDpole : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      ‖Dcomp (sigma : ℂ)‖ * (sigma - 1) ≤ K)
    (hDtwist : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      ‖Dcomp ((sigma : ℂ) + 2 * y * I)‖ ≤ K₂) :
    L.uncompletedContinuation (1 + y * I) ≠ 0 :=
  maass_edge_nonvanishing M hC r L.uncompletedContinuation_entire
    (standard_uncompletedContinuation_eqOn_symmetricPowerReadout hC L) hDeq hDpole hDtwist

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.uncompletedContinuation_eqOn_bankEulerReadout
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.uncompletedContinuation_ne_zero_of_one_lt_re
#print axioms CriticalLinePhasor.ThreeDConverse.standard_uncompletedContinuation_eqOn_symmetricPowerReadout
#print axioms CriticalLinePhasor.ThreeDConverse.standard_edge_nonvanishing_of_companion
