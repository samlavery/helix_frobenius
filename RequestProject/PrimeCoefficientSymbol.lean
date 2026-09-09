import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Nat.Choose.Basic

namespace CriticalLinePhasor.SeatingLedger

/-- The polynomial multiplying one integer's arithmetic phase in degree k+1. -/
noncomputable def primeCoeffSymbol (d : ℂ) (k : ℕ) (ℓ : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℂ) * d ^ (k - i) * (-1) ^ i *
    ((-1) ^ (k + 1 - i) / ((k + 1 - i).factorial : ℂ) * (ℓ : ℂ) ^ (k + 1 - i))

end CriticalLinePhasor.SeatingLedger
