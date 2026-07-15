import RequestProject.HodgeDial
import Mathlib.Data.Nat.Pairing

/-!
# Retention for finite extension data beyond the semisimple carrier state

The semisimple model stores one amplitude at each distinct clock.  General finite extension data
stores an arbitrary finite jet stack at every clock: layer zero is the value coordinate and the
positive layers are extension coordinates.  The normalized jet tower pairs a layer with a moment
depth.  Each layer is separated by the same Vandermonde theorem, so simultaneous silence of all
value and jet channels forces the entire extension datum to vanish.
-/

open scoped BigOperators

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- A finite clock bank with pairwise distinct frequencies. -/
structure DistinctClockBank (m : ℕ) where
  frequency : Fin m → ℂ
  injective : Function.Injective frequency

/-- General finite extension data of order `order`: layer zero is the semisimple value coordinate
and layers `1, ..., order` are the retained jet/extension coordinates. -/
abbrev GeneralExtensionData (order m : ℕ) := Fin (order + 1) → Fin m → ℂ

/-- The normalized extension-jet tower.  A natural level is decoded as `(layer, momentDepth)`;
levels whose layer is outside the finite extension stack return zero. -/
noncomputable def generalExtensionTower {order m : ℕ} (bank : DistinctClockBank m)
    (q : ℕ) (data : GeneralExtensionData order m) : ℂ :=
  if h : (Nat.unpair q).1 < order + 1 then
    ∑ i, data ⟨(Nat.unpair q).1, h⟩ i * bank.frequency i ^ (Nat.unpair q).2
  else
    0

/-- At the paired index `(layer, d)`, the general tower is exactly the `d`th moment of that
extension layer. -/
theorem generalExtensionTower_pair {order m : ℕ} (bank : DistinctClockBank m)
    (layer : Fin (order + 1)) (d : ℕ) (data : GeneralExtensionData order m) :
    generalExtensionTower bank (Nat.pair layer d) data =
      ∑ i, data layer i * bank.frequency i ^ d := by
  simp [generalExtensionTower, Nat.unpair_pair, layer.isLt]

/-- The complete value-and-jet tower separates arbitrary finite extension data. -/
theorem generalExtensionTower_detects {order m : ℕ} (bank : DistinctClockBank m)
    (data : GeneralExtensionData order m)
    (hsilent : ∀ q : ℕ, generalExtensionTower bank q data = 0) :
    data = 0 := by
  funext layer
  apply momentTower_detects bank.frequency (data layer) bank.injective
  intro d
  simpa only [generalExtensionTower_pair] using hsilent (Nat.pair layer d)

/-- The radical of the full extension-jet tower is trivial for every finite extension order. -/
theorem generalExtensionTower_radical_trivial {order m : ℕ} (bank : DistinctClockBank m) :
    ∀ data : GeneralExtensionData order m,
      data ∈ radical (generalExtensionTower bank) → data = 0 := by
  intro data hdata
  exact generalExtensionTower_detects bank data hdata

/-- Retention for general finite extension data: every nonzero value/jet stack fires at some
paired layer-and-moment level. -/
theorem generalExtensionTower_exhaustive {order m : ℕ} (bank : DistinctClockBank m) :
    Exhaustive (Z := GeneralExtensionData order m)
      (generalExtensionTower (order := order) bank) :=
  exhaustive_of_radical_trivial (generalExtensionTower_radical_trivial bank)

/-- The Hodge dial on the complete finite extension state, with no semisimplification of its
positive jet layers. -/
noncomputable def generalExtensionDial {order m : ℕ} (bank : DistinctClockBank m)
    (Algebraic : GeneralExtensionData order m → Prop) :
    HodgeDial (GeneralExtensionData order m) where
  DC _ := True
  Rational _ := True
  Algebraic := Algebraic
  T := generalExtensionTower (order := order) bank

/-- The complete finite extension dial satisfies `Retention` at every extension order. -/
theorem generalExtension_retention {order m : ℕ} (bank : DistinctClockBank m)
    (Algebraic : GeneralExtensionData order m → Prop) :
    Retention (generalExtensionDial bank Algebraic) :=
  retention_of_exhaustive (generalExtensionTower_exhaustive bank)

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.generalExtensionTower_pair
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.generalExtensionTower_detects
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.generalExtensionTower_exhaustive
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.generalExtension_retention
