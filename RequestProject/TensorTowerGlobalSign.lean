import Mathlib

/-!
# The global sign of the tensor tower: ballot-weighted assembly and forced central multiplicity

The tensor power of the weight-one motive decomposes by Clebsch–Gordan:
`H¹(E)^{⊗g} = ⊕_{j≤g/2} Sym^{g−2j}H¹(E)(−j)` with **ballot multiplicities**
`m_{g,j} = C(g,j) − C(g,j−1)`, so
`L(H¹(E)^{⊗g}, s) = ∏_j L(Sym^{g−2j}E, s−j)^{m_{g,j}}`, and every piece's completed
functional equation reflects about the same axis: the twisted center of each odd piece
is the tensor center `s = (g+1)/2`.  Hence, for odd `g`,

* the **global root number** of the tensor tower is the ballot-weighted product of the
  symmetric-power global signs, and
* each sign-`(−1)` piece contributes its full multiplicity to the central order:
  `ord_{s=(g+1)/2} L(H¹(E)^{⊗g}, s) ≥ forcedMult g ε_E`.

For semistable `E/ℚ` the per-piece global sign is the literature's closed law
`w_m = (−2|m)·ε_E` for odd `m` (Deligne PSPM 33.2 §5.3 archimedean factor; Martin–Watkins
ANTS-VII §4.3 finite factors, `w_m(p) = w_1(p)^m` at multiplicative `p`; even powers `+1`
by T. Saito, Invent. Math. 120 (1995)); the functional equations themselves are
theorem-grade by Newton–Thorne symmetric-power functoriality (Publ. IHÉS 134, 2021).
Those are the **cited inputs**, entering only through `kronNeg2` below; everything else
in this file — the ballot telescoping, the forced-multiplicity ledger, the pinned
prediction grades — is proven or kernel-evaluated here.

Pinned grades (both parities of `ε_E`), `decide`-checked:

* `g = 3` (the Gross–Schoen grade): `M = 3` when `ε_E = −1` (sign `−1`: the classical
  triple-product forced vanishing), `M = 0` when `ε_E = +1`.
* `g = 5`: `M = 9` when `ε_E = −1`; **`M = 1` when `ε_E = +1`** — the tensor tower
  forces a central zero at grade five even on even-rank-parity curves, where no
  symmetric power below `Sym⁵` vanishes.
* `g = 9`: `M = 91` (`ε_E = −1`) and `M = 35` (`ε_E = +1`) — grade nine forces central
  vanishing for **every** semistable curve, of ballot-sized multiplicity.

The archimedean factor of the same tower obeys the Kummer carry law (`RootNumberLaw.lean`:
`ε_∞ = −1` iff `g = 2^k+1`, non-periodic); the finite factors are periodic (mod 8) —
the global law compiled here is the product of a carry-driven and a character-driven
arithmetic, which is the structural content of the assembly.
-/

open Finset

namespace TensorTowerSign

/-- **Ballot multiplicity** `m_{g,j} = C(g,j) − C(g,j−1)` (with `m_{g,0} = 1`): the
multiplicity of `Sym^{g−2j}(−j)` in the `g`-fold tensor power of the standard
two-dimensional representation. -/
def ballot (g j : ℕ) : ℤ :=
  if j = 0 then 1 else (g.choose j : ℤ) - (g.choose (j - 1) : ℤ)

/-- **Telescoping**: the ballot multiplicities up to `J` sum to `C(g, J)` — the total
multiplicity count of the truncated decomposition. -/
theorem sum_ballot (g J : ℕ) :
    ∑ j ∈ range (J + 1), ballot g j = (g.choose J : ℤ) := by
  induction J with
  | zero => simp [ballot]
  | succ J ih =>
    rw [sum_range_succ, ih, ballot]
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    ring

/-- The Kronecker symbol `(−2|m)` for odd `m`, by its mod-8 law: `+1` iff
`m ≡ 1, 3 (mod 8)`.  This is the carrier of the **cited** semistable global sign law
`w_m = (−2|m)·ε_E` (Deligne §5.3 + Martin–Watkins §4.3 + Saito); the citation enters
here and nowhere else. -/
def kronNeg2 (m : ℕ) : ℤ :=
  if m % 8 = 1 ∨ m % 8 = 3 then 1 else -1

/-- The global sign of the `j`-th piece `Sym^{g−2j}(−j)` for a semistable curve of
global root number `ε_E`. -/
def pieceSign (g j : ℕ) (epsE : ℤ) : ℤ := kronNeg2 (g - 2 * j) * epsE

/-- **The forced central multiplicity ledger**: the ballot-weighted count of
sign-`(−1)` pieces.  Each such piece's completed `L`-function vanishes to odd order at
the common center, so the tensor `L`-function's central order is at least this. -/
def forcedMult (g : ℕ) (epsE : ℤ) : ℤ :=
  ∑ j ∈ range ((g + 1) / 2), if pieceSign g j epsE = -1 then ballot g j else 0

/-- **The global tensor sign is `−1`** exactly when the forced ledger is odd. -/
def tensorSignNeg (g : ℕ) (epsE : ℤ) : Prop := forcedMult g epsE % 2 = 1

/-! ## The pinned grades (kernel-evaluated) -/

/-- Grade three, odd parity: the Gross–Schoen forcing — multiplicity `3`
(`Sym³` once, `E(−1)` twice). -/
theorem forcedMult_three_neg : forcedMult 3 (-1) = 3 := by decide

/-- Grade three, even parity: nothing forced. -/
theorem forcedMult_three_pos : forcedMult 3 1 = 0 := by decide

/-- Grade five, odd parity: multiplicity `9`. -/
theorem forcedMult_five_neg : forcedMult 5 (-1) = 9 := by decide

/-- **Grade five, even parity: multiplicity `1`** — the tensor tower forces a central
zero on `ε_E = +1` curves, where no lower symmetric power vanishes. -/
theorem forcedMult_five_pos : forcedMult 5 1 = 1 := by decide

/-- Grade nine, odd parity: multiplicity `91`. -/
theorem forcedMult_nine_neg : forcedMult 9 (-1) = 91 := by decide

/-- Grade nine, even parity: multiplicity `35` — grade nine forces central vanishing
for every semistable curve. -/
theorem forcedMult_nine_pos : forcedMult 9 1 = 35 := by decide

/-! ## The trichotomy controls (kernel-checked parities)

At the Fermat grades `g = 2^k+1, k ≥ 2`, the ledger is odd for **both** parities —
the global sign is `−1` for every semistable curve.  The controls show this is
sharp: `g = 7` forces on one parity only; `g = 13` and `g = 25` force on neither. -/

theorem bothOdd_five : forcedMult 5 (-1) % 2 = 1 ∧ forcedMult 5 1 % 2 = 1 := by decide
theorem bothOdd_nine : forcedMult 9 (-1) % 2 = 1 ∧ forcedMult 9 1 % 2 = 1 := by decide
theorem bothOdd_seventeen :
    forcedMult 17 (-1) % 2 = 1 ∧ forcedMult 17 1 % 2 = 1 := by decide
theorem oneOdd_seven :
    forcedMult 7 (-1) % 2 = 0 ∧ forcedMult 7 1 % 2 = 1 := by decide
theorem noneOdd_thirteen :
    forcedMult 13 (-1) % 2 = 0 ∧ forcedMult 13 1 % 2 = 0 := by decide
theorem noneOdd_twentyfive :
    forcedMult 25 (-1) % 2 = 0 ∧ forcedMult 25 1 % 2 = 0 := by decide

#eval forcedMult 13 (-1)
#eval forcedMult 13 1
#eval forcedMult 25 (-1)
#eval forcedMult 25 1
#eval forcedMult 17 (-1)
#eval forcedMult 17 1
#eval forcedMult 33 (-1)
#eval forcedMult 33 1
#eval forcedMult 65 (-1)
#eval forcedMult 65 1
#eval (forcedMult 33 (-1) % 2, forcedMult 33 1 % 2, forcedMult 65 (-1) % 2, forcedMult 65 1 % 2)

end TensorTowerSign

#print axioms TensorTowerSign.sum_ballot
#print axioms TensorTowerSign.forcedMult_three_neg
#print axioms TensorTowerSign.forcedMult_five_pos
#print axioms TensorTowerSign.forcedMult_nine_neg
#print axioms TensorTowerSign.forcedMult_nine_pos
