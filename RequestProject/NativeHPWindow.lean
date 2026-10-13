import RequestProject.DilationEigenfunctional
import RequestProject.DVPLadder1016o2

/-!
# The native Hilbert–Pólya correspondence, complete up to height 508 (ledger 1221)

The area-measure dilation group (`AreaDilation`, unitary exactly at weight `½`) acts on the power
function `x^{−s}` by `e^{t(½ − s)}` (`dil_power`). A zero is realized as a unitary eigen-direction of the
native operator exactly when that scalar is unimodular for all `t` (`dil_power_unimodular_iff`), i.e. when
`Re ρ` is the area-measure exponent.

* `realized_iff`: a nontrivial zero is a unitary eigen-direction iff `Re ρ = ½`, where the ½ is the
  unique isometric weight of the area measure (`dilW_isometry_iff`), not an inserted constant.
* `zeros_below_508_realized`: every nontrivial zero with `|Im ρ| ≤ 508` is realized, from the compiled
  verified window `DVP.online_below_1016o2`. Up to that height the native correspondence covers the
  whole zero set. Above it, "every zero is realized" is RH.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.NativeHP

open CriticalLinePhasor.AreaDilation

/-- A zero is realized when the area-measure dilations act on its power function unimodularly. -/
def Realized (ρ : ℂ) : Prop := ∀ t : ℝ, ‖Complex.exp ((t : ℂ) * (1 / 2 - ρ))‖ = 1

theorem realized_iff (ρ : ℂ) : Realized ρ ↔ ρ.re = 1 / 2 := dil_power_unimodular_iff ρ

/-- **Every zero up to height 508 is realized by the native operator.** -/
theorem zeros_below_508_realized :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 1016 / 2 → Realized ρ := fun ρ hρ hwin =>
  (realized_iff ρ).mpr (CriticalLinePhasor.DVP.online_below_1016o2 ρ hρ hwin)

end CriticalLinePhasor.NativeHP

end

#print axioms CriticalLinePhasor.NativeHP.realized_iff
#print axioms CriticalLinePhasor.NativeHP.zeros_below_508_realized
