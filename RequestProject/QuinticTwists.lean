import RequestProject.CapVehicle

/-!
# The quintic twist scoreboard: `m = 2` and `m = 3` for `Sym⁵` — one degree from the converse

The `GL(6)` converse theorem for `Sym⁵f` consumes twisted niceness at degrees
`1 ≤ m ≤ 4`.  This file compiles the two vehicle identities that settle `m = 2` and
`m = 3`:

* **`m = 2`** (`quinticG_bank`): `(std_g ⊗ Sym²_f) ⊗ Sym³_f
  = (std_g⊗Sym⁵_f) ⊕ (std_g⊗Sym³_f) ⊕ (std_g⊗std_f)` — the Kim–Shahidi vehicle
  `g ⊠ Sym²f` (automorphic `GL(6)`) paired against `Sym³f` (automorphic `GL(4)`),
  so JPSS controls the left side and division by the two known factors controls
  `L(g × Sym⁵f)` on `Re s ≥ 1` for **every** `GL(2)` cusp form `g`;
* **`m = 3`** (`quinticTau_bank`): `(std_f ⊗ τ₃) ⊗ Sym⁴_f = (Sym⁵_f ⊕ Sym³_f) ⊗ τ₃`
  — the **swapped-role** Kim–Shahidi vehicle `f ⊠ τ₃` (automorphic `GL(6)` for any
  `GL(3)` cusp form `τ₃`) paired against `Sym⁴f` (automorphic `GL(5)`, Kim), so JPSS
  controls the left side, `L(Sym³f × τ₃)` is itself a `GL(4)×GL(3)` automorphic pair
  (holomorphic and nonvanishing on `Re s ≥ 1`), and division controls
  `L(Sym⁵f × τ₃)` on `Re s ≥ 1` for **every** `GL(3)` cusp form `τ₃`.

The compiled layer is **universal**: `quinticTau_bank` quantifies over an arbitrary
Satake family `T : Nat.Primes → Fin 3 → ℂ` — pure channel algebra, no automorphy
consumed.  The analytic consequences are classical *given the cited inputs*
(Kim–Shahidi `GL(2)×GL(3)` functoriality in both roles, Kim `Sym⁴`, JPSS,
Shahidi nonvanishing) and are registered, not compiled.

Scoreboard after this file, `GL(6)` converse for `Sym⁵`: `m = 1` classical (twisted
tower), `m = 2` and `m = 3` via the two vehicles here, `m = 4` blocked — every
factorization of `τ₄ ⊗ Sym⁵_f` through known automorphic pairs requires
`⊠(GL(2)×GL(4))` or `⊠(GL(3)×GL(3))`, checked over all rank splits.  **The `Sym⁵`
converse lacks exactly one twist degree, and that degree is exactly one new
functorial product.**  Whether the `m = 2, 3` statements are already in print
(Kim–Shahidi's applications papers) is a named pin-cite obligation before paper
use.  No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups ArithmeticFunction.zeta LSeries.notation

namespace CriticalLinePhasor.QuinticTwists

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.Sym2Rankin CriticalLinePhasor.SymrBank
open CriticalLinePhasor.TransportClosure CriticalLinePhasor.TensorTowerBanks

variable {k k' : ℤ} {f : CuspForm 𝒮ℒ k} {g : CuspForm 𝒮ℒ k'}

/-! ## `m = 2`: `(std_g ⊗ Sym²_f) ⊗ Sym³_f` -/

/-- The `std_g ⊗ Sym⁵_f` twisted-rung weight system: twelve products. -/
noncomputable def gSym5Weight (β α : ℂ) : Fin 12 → ℂ :=
  ![β ^ (1 : ℤ) * α ^ (5 : ℤ), β ^ (1 : ℤ) * α ^ (3 : ℤ), β ^ (1 : ℤ) * α ^ (1 : ℤ),
    β ^ (1 : ℤ) * α ^ (-1 : ℤ), β ^ (1 : ℤ) * α ^ (-3 : ℤ), β ^ (1 : ℤ) * α ^ (-5 : ℤ),
    β ^ (-1 : ℤ) * α ^ (5 : ℤ), β ^ (-1 : ℤ) * α ^ (3 : ℤ), β ^ (-1 : ℤ) * α ^ (1 : ℤ),
    β ^ (-1 : ℤ) * α ^ (-1 : ℤ), β ^ (-1 : ℤ) * α ^ (-3 : ℤ), β ^ (-1 : ℤ) * α ^ (-5 : ℤ)]

/-- The `std_g ⊗ Sym³_f` twisted-rung weight system: eight products. -/
noncomputable def gSym3Weight (β α : ℂ) : Fin 8 → ℂ :=
  ![β ^ (1 : ℤ) * α ^ (3 : ℤ), β ^ (1 : ℤ) * α ^ (1 : ℤ), β ^ (1 : ℤ) * α ^ (-1 : ℤ),
    β ^ (1 : ℤ) * α ^ (-3 : ℤ),
    β ^ (-1 : ℤ) * α ^ (3 : ℤ), β ^ (-1 : ℤ) * α ^ (1 : ℤ), β ^ (-1 : ℤ) * α ^ (-1 : ℤ),
    β ^ (-1 : ℤ) * α ^ (-3 : ℤ)]

/-- The `std_g ⊗ std_f` twisted-rung weight system: four products. -/
noncomputable def gStdWeight (β α : ℂ) : Fin 4 → ℂ :=
  ![β ^ (1 : ℤ) * α ^ (1 : ℤ), β ^ (1 : ℤ) * α ^ (-1 : ℤ),
    β ^ (-1 : ℤ) * α ^ (1 : ℤ), β ^ (-1 : ℤ) * α ^ (-1 : ℤ)]

/-- The `m = 2` vehicle weight system `std_g ⊗ (Sym²_f ⊗ Sym³_f)`: twenty-four
products, the `β`-row then the `β⁻¹`-row over the twelve `Sym²⊗Sym³` products. -/
noncomputable def quinticGWeight (β α : ℂ) : Fin 24 → ℂ :=
  ![β ^ (1 : ℤ) * α ^ (5 : ℤ), β ^ (1 : ℤ) * α ^ (3 : ℤ), β ^ (1 : ℤ) * α ^ (1 : ℤ),
    β ^ (1 : ℤ) * α ^ (-1 : ℤ),
    β ^ (1 : ℤ) * α ^ (3 : ℤ), β ^ (1 : ℤ) * α ^ (1 : ℤ), β ^ (1 : ℤ) * α ^ (-1 : ℤ),
    β ^ (1 : ℤ) * α ^ (-3 : ℤ),
    β ^ (1 : ℤ) * α ^ (1 : ℤ), β ^ (1 : ℤ) * α ^ (-1 : ℤ), β ^ (1 : ℤ) * α ^ (-3 : ℤ),
    β ^ (1 : ℤ) * α ^ (-5 : ℤ),
    β ^ (-1 : ℤ) * α ^ (5 : ℤ), β ^ (-1 : ℤ) * α ^ (3 : ℤ), β ^ (-1 : ℤ) * α ^ (1 : ℤ),
    β ^ (-1 : ℤ) * α ^ (-1 : ℤ),
    β ^ (-1 : ℤ) * α ^ (3 : ℤ), β ^ (-1 : ℤ) * α ^ (1 : ℤ), β ^ (-1 : ℤ) * α ^ (-1 : ℤ),
    β ^ (-1 : ℤ) * α ^ (-3 : ℤ),
    β ^ (-1 : ℤ) * α ^ (1 : ℤ), β ^ (-1 : ℤ) * α ^ (-1 : ℤ), β ^ (-1 : ℤ) * α ^ (-3 : ℤ),
    β ^ (-1 : ℤ) * α ^ (-5 : ℤ)]

/-- The relabeling `Fin 24 ≃ Fin 12 ⊕ (Fin 8 ⊕ Fin 4)`. -/
def quinticGSplit : Fin 24 ≃ Fin 12 ⊕ (Fin 8 ⊕ Fin 4) where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3,
             Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), Sum.inr (Sum.inl 2),
             Sum.inr (Sum.inl 3),
             Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1), Sum.inl 4, Sum.inl 5,
             Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9,
             Sum.inr (Sum.inl 4), Sum.inr (Sum.inl 5), Sum.inr (Sum.inl 6),
             Sum.inr (Sum.inl 7),
             Sum.inr (Sum.inr 2), Sum.inr (Sum.inr 3), Sum.inl 10, Sum.inl 11]
  invFun := Sum.elim ![0, 1, 2, 3, 10, 11, 12, 13, 14, 15, 22, 23]
    (Sum.elim ![4, 5, 6, 7, 16, 17, 18, 19] ![8, 9, 20, 21])
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    rcases i with i | i
    · fin_cases i <;> rfl
    · rcases i with i | i
      · fin_cases i <;> rfl
      · fin_cases i <;> rfl

/-- **`std_g ⊗ (Sym²_f ⊗ Sym³_f) = (std_g⊗Sym⁵_f) ⊕ (std_g⊗Sym³_f) ⊕ (std_g⊗std_f)`**
at the weight level. -/
theorem quinticGWeight_decomposition (β α : ℂ) :
    quinticGWeight β α
      = (Sum.elim (gSym5Weight β α)
          (Sum.elim (gSym3Weight β α) (gStdWeight β α))) ∘ quinticGSplit := by
  funext i
  fin_cases i <;> rfl

/-- **The `m = 2` quintic vehicle bank law**:
`L((g⊠Sym²f) × Sym³f) = L(g×Sym⁵f)·L(g×Sym³f)·L(g×f)` at every `n`. -/
theorem quinticG_bank (G : HeckeEigenData g) (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => quinticGWeight (G.satake p.2) (H.satake p.2)))
      = coefficientArithmetic (radialGlobalSatakeCoeff
          (fun p => gSym5Weight (G.satake p.2) (H.satake p.2)))
        * (coefficientArithmetic (radialGlobalSatakeCoeff
            (fun p => gSym3Weight (G.satake p.2) (H.satake p.2)))
          * coefficientArithmetic (radialGlobalSatakeCoeff
              (fun p => gStdWeight (G.satake p.2) (H.satake p.2)))) := by
  have hdec : (fun p : Nat.Primes => quinticGWeight (G.satake p.2) (H.satake p.2))
      = fun p : Nat.Primes =>
          (Sum.elim (gSym5Weight (G.satake p.2) (H.satake p.2))
            (Sum.elim (gSym3Weight (G.satake p.2) (H.satake p.2))
              (gStdWeight (G.satake p.2) (H.satake p.2)))) ∘ quinticGSplit := by
    funext p
    exact quinticGWeight_decomposition (G.satake p.2) (H.satake p.2)
  rw [hdec, radialGlobalSatakeCoeff_equiv quinticGSplit, bankArithmetic_sumElim,
    bankArithmetic_sumElim]

/-! ## `m = 3`: `(std_f ⊗ τ₃) ⊗ Sym⁴_f`, universal over abstract `GL(3)` Satake -/

/-- The `Sym⁵_f ⊗ τ₃` weight system over an abstract Satake triple `t`: eighteen
products, `f`-clock-major order. -/
noncomputable def sym5TauWeight (α : ℂ) (t : Fin 3 → ℂ) : Fin 18 → ℂ :=
  ![α ^ (5 : ℤ) * t 0, α ^ (5 : ℤ) * t 1, α ^ (5 : ℤ) * t 2,
    α ^ (3 : ℤ) * t 0, α ^ (3 : ℤ) * t 1, α ^ (3 : ℤ) * t 2,
    α ^ (1 : ℤ) * t 0, α ^ (1 : ℤ) * t 1, α ^ (1 : ℤ) * t 2,
    α ^ (-1 : ℤ) * t 0, α ^ (-1 : ℤ) * t 1, α ^ (-1 : ℤ) * t 2,
    α ^ (-3 : ℤ) * t 0, α ^ (-3 : ℤ) * t 1, α ^ (-3 : ℤ) * t 2,
    α ^ (-5 : ℤ) * t 0, α ^ (-5 : ℤ) * t 1, α ^ (-5 : ℤ) * t 2]

/-- The `Sym³_f ⊗ τ₃` weight system over an abstract Satake triple `t`: twelve
products. -/
noncomputable def sym3TauWeight (α : ℂ) (t : Fin 3 → ℂ) : Fin 12 → ℂ :=
  ![α ^ (3 : ℤ) * t 0, α ^ (3 : ℤ) * t 1, α ^ (3 : ℤ) * t 2,
    α ^ (1 : ℤ) * t 0, α ^ (1 : ℤ) * t 1, α ^ (1 : ℤ) * t 2,
    α ^ (-1 : ℤ) * t 0, α ^ (-1 : ℤ) * t 1, α ^ (-1 : ℤ) * t 2,
    α ^ (-3 : ℤ) * t 0, α ^ (-3 : ℤ) * t 1, α ^ (-3 : ℤ) * t 2]

/-- The `m = 3` vehicle weight system `(std_f ⊗ τ₃) ⊗ Sym⁴_f`: thirty products,
`(std⊗Sym⁴)_f`-major order over the abstract triple. -/
noncomputable def quinticTauWeight (α : ℂ) (t : Fin 3 → ℂ) : Fin 30 → ℂ :=
  ![α ^ (5 : ℤ) * t 0, α ^ (5 : ℤ) * t 1, α ^ (5 : ℤ) * t 2,
    α ^ (3 : ℤ) * t 0, α ^ (3 : ℤ) * t 1, α ^ (3 : ℤ) * t 2,
    α ^ (1 : ℤ) * t 0, α ^ (1 : ℤ) * t 1, α ^ (1 : ℤ) * t 2,
    α ^ (-1 : ℤ) * t 0, α ^ (-1 : ℤ) * t 1, α ^ (-1 : ℤ) * t 2,
    α ^ (-3 : ℤ) * t 0, α ^ (-3 : ℤ) * t 1, α ^ (-3 : ℤ) * t 2,
    α ^ (3 : ℤ) * t 0, α ^ (3 : ℤ) * t 1, α ^ (3 : ℤ) * t 2,
    α ^ (1 : ℤ) * t 0, α ^ (1 : ℤ) * t 1, α ^ (1 : ℤ) * t 2,
    α ^ (-1 : ℤ) * t 0, α ^ (-1 : ℤ) * t 1, α ^ (-1 : ℤ) * t 2,
    α ^ (-3 : ℤ) * t 0, α ^ (-3 : ℤ) * t 1, α ^ (-3 : ℤ) * t 2,
    α ^ (-5 : ℤ) * t 0, α ^ (-5 : ℤ) * t 1, α ^ (-5 : ℤ) * t 2]

/-- The relabeling `Fin 30 ≃ Fin 18 ⊕ Fin 12`. -/
def quinticTauSplit : Fin 30 ≃ Fin 18 ⊕ Fin 12 where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2,
             Sum.inl 3, Sum.inl 4, Sum.inl 5,
             Sum.inl 6, Sum.inl 7, Sum.inl 8,
             Sum.inl 9, Sum.inl 10, Sum.inl 11,
             Sum.inl 12, Sum.inl 13, Sum.inl 14,
             Sum.inr 0, Sum.inr 1, Sum.inr 2,
             Sum.inr 3, Sum.inr 4, Sum.inr 5,
             Sum.inr 6, Sum.inr 7, Sum.inr 8,
             Sum.inr 9, Sum.inr 10, Sum.inr 11,
             Sum.inl 15, Sum.inl 16, Sum.inl 17]
  invFun := Sum.elim
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 27, 28, 29]
    ![15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    rcases i with i | i
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl

/-- **`(std_f ⊗ τ₃) ⊗ Sym⁴_f = (Sym⁵_f ⊗ τ₃) ⊕ (Sym³_f ⊗ τ₃)` at the weight level**,
for an arbitrary Satake triple. -/
theorem quinticTauWeight_decomposition (α : ℂ) (t : Fin 3 → ℂ) :
    quinticTauWeight α t
      = (Sum.elim (sym5TauWeight α t) (sym3TauWeight α t)) ∘ quinticTauSplit := by
  funext i
  fin_cases i <;> rfl

/-- **The `m = 3` quintic vehicle bank law**, universal over an arbitrary `GL(3)`
Satake family `T`: `L((f⊠τ₃) × Sym⁴f) = L(Sym⁵f × τ₃) · L(Sym³f × τ₃)` at every
`n` — pure channel algebra, no automorphy consumed. -/
theorem quinticTau_bank (H : HeckeEigenData f) (T : Nat.Primes → Fin 3 → ℂ) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => quinticTauWeight (H.satake p.2) (T p)))
      = coefficientArithmetic (radialGlobalSatakeCoeff
          (fun p => sym5TauWeight (H.satake p.2) (T p)))
        * coefficientArithmetic (radialGlobalSatakeCoeff
            (fun p => sym3TauWeight (H.satake p.2) (T p))) := by
  have hdec : (fun p : Nat.Primes => quinticTauWeight (H.satake p.2) (T p))
      = fun p : Nat.Primes =>
          (Sum.elim (sym5TauWeight (H.satake p.2) (T p))
            (sym3TauWeight (H.satake p.2) (T p))) ∘ quinticTauSplit := by
    funext p
    exact quinticTauWeight_decomposition (H.satake p.2) (T p)
  rw [hdec, radialGlobalSatakeCoeff_equiv quinticTauSplit, bankArithmetic_sumElim]

end CriticalLinePhasor.QuinticTwists

#print axioms CriticalLinePhasor.QuinticTwists.quinticGWeight_decomposition
#print axioms CriticalLinePhasor.QuinticTwists.quinticG_bank
#print axioms CriticalLinePhasor.QuinticTwists.quinticTauWeight_decomposition
#print axioms CriticalLinePhasor.QuinticTwists.quinticTau_bank
