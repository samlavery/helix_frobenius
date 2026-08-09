import RequestProject.TensorTowerBanks

/-!
# The cap vehicle: `(g ⊠ Sym²f) × Sym⁴f` carries `Sym⁶` — the twisted rung beyond the pair list

The tensor tower caps at `r = 8` because `Sym⁴ ⊗ Sym⁴` is the largest Rankin–Selberg
pair of *known automorphic* objects.  This file compiles the **vehicle identity** that
carries analytic control past the naive pair list: the Kim–Shahidi product
`g ⊠ Sym²f` is a genuine automorphic representation of `GL(6)` (cuspidal for generic
`(g, f)`), so its Rankin–Selberg pairing against `Sym⁴f` is in Jacquet–
Piatetski-Shapiro–Shalika range, and it decomposes as

  `(std_g ⊗ Sym²_f) ⊗ Sym⁴_f = (std_g ⊗ Sym⁶_f) ⊕ (std_g ⊗ Sym⁴_f) ⊕ (std_g ⊗ Sym²_f)`

— the two-seed weight identity compiled here (`vehicleWeight_decomposition`,
`vehicle_bank`): the thirty pairwise products split as the three `g`-twisted rungs,
and the vehicle bank is the `⋆`-product of the three twisted-rung banks, at every `n`.

* `gSym6Weight` / `gSym4Weight` / `gSym2Weight` — the two-seed twisted-rung weight
  systems `std_g ⊗ Sym^k_f` (`k = 6, 4, 2`);
* `vehicleWeight` — the thirty products `std_g ⊗ (Sym²_f ⊗ Sym⁴_f)`;
* `vehicleSplit : Fin 30 ≃ Fin 14 ⊕ (Fin 10 ⊕ Fin 6)` + `vehicleWeight_decomposition`;
* `vehicle_bank` — the bank factorization
  `bank(vehicle) = bank(g×Sym⁶) ⋆ bank(g×Sym⁴) ⋆ bank(g×Sym²)`.

Register.  The analytic consequence is classical *given the cited inputs* and is
registered, not compiled: `g ⊠ Sym²f` automorphic on `GL(6)` (Kim–Shahidi, cuspidal
by their criterion for generic pairs), Rankin–Selberg niceness of automorphic pairs
(JPSS), nonvanishing on `Re s = 1` (Shahidi).  Feeding the vehicle identity with
them: `L(g × Sym⁶f)` is holomorphic and nonvanishing on `Re s ≥ 1` for **every**
`GL(2)` cusp form `g` — twist degree `m = 2` of the `GL(7)` converse scoreboard for
`Sym⁶`, beyond the naive pair list (`Sym⁶f` itself is not known automorphic).
Scoreboard: `m = 1` classical (twisted tower), `m = 2` via this vehicle,
`m = 3, 4, 5` each blocked by exactly one unknown functorial product
(`GL(3)×GL(3)` or `GL(2)×GL(4)`) — **the cap's minimal remaining target is one new
functorial product**; pin-cite verification of the `m ≤ 2` classical record is a
named obligation before any paper use.  No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups ArithmeticFunction.zeta LSeries.notation

namespace CriticalLinePhasor.CapVehicle

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.Sym2Rankin CriticalLinePhasor.SymrBank
open CriticalLinePhasor.TransportClosure CriticalLinePhasor.TensorTowerBanks

variable {k k' : ℤ} {f : CuspForm 𝒮ℒ k} {g : CuspForm 𝒮ℒ k'}

/-- The `std_g ⊗ Sym⁶_f` twisted-rung weight system: fourteen products. -/
noncomputable def gSym6Weight (β α : ℂ) : Fin 14 → ℂ :=
  ![β ^ (1 : ℤ) * α ^ (6 : ℤ), β ^ (1 : ℤ) * α ^ (4 : ℤ), β ^ (1 : ℤ) * α ^ (2 : ℤ),
    β ^ (1 : ℤ) * α ^ (0 : ℤ), β ^ (1 : ℤ) * α ^ (-2 : ℤ), β ^ (1 : ℤ) * α ^ (-4 : ℤ),
    β ^ (1 : ℤ) * α ^ (-6 : ℤ),
    β ^ (-1 : ℤ) * α ^ (6 : ℤ), β ^ (-1 : ℤ) * α ^ (4 : ℤ), β ^ (-1 : ℤ) * α ^ (2 : ℤ),
    β ^ (-1 : ℤ) * α ^ (0 : ℤ), β ^ (-1 : ℤ) * α ^ (-2 : ℤ), β ^ (-1 : ℤ) * α ^ (-4 : ℤ),
    β ^ (-1 : ℤ) * α ^ (-6 : ℤ)]

/-- The `std_g ⊗ Sym⁴_f` twisted-rung weight system: ten products. -/
noncomputable def gSym4Weight (β α : ℂ) : Fin 10 → ℂ :=
  ![β ^ (1 : ℤ) * α ^ (4 : ℤ), β ^ (1 : ℤ) * α ^ (2 : ℤ), β ^ (1 : ℤ) * α ^ (0 : ℤ),
    β ^ (1 : ℤ) * α ^ (-2 : ℤ), β ^ (1 : ℤ) * α ^ (-4 : ℤ),
    β ^ (-1 : ℤ) * α ^ (4 : ℤ), β ^ (-1 : ℤ) * α ^ (2 : ℤ), β ^ (-1 : ℤ) * α ^ (0 : ℤ),
    β ^ (-1 : ℤ) * α ^ (-2 : ℤ), β ^ (-1 : ℤ) * α ^ (-4 : ℤ)]

/-- The `std_g ⊗ Sym²_f` twisted-rung weight system: six products. -/
noncomputable def gSym2Weight (β α : ℂ) : Fin 6 → ℂ :=
  ![β ^ (1 : ℤ) * α ^ (2 : ℤ), β ^ (1 : ℤ) * α ^ (0 : ℤ), β ^ (1 : ℤ) * α ^ (-2 : ℤ),
    β ^ (-1 : ℤ) * α ^ (2 : ℤ), β ^ (-1 : ℤ) * α ^ (0 : ℤ), β ^ (-1 : ℤ) * α ^ (-2 : ℤ)]

/-- The vehicle weight system `std_g ⊗ (Sym²_f ⊗ Sym⁴_f)`: thirty products, the
`β`-row then the `β⁻¹`-row over the fifteen `Sym²⊗Sym⁴` products. -/
noncomputable def vehicleWeight (β α : ℂ) : Fin 30 → ℂ :=
  ![β ^ (1 : ℤ) * α ^ (6 : ℤ), β ^ (1 : ℤ) * α ^ (4 : ℤ), β ^ (1 : ℤ) * α ^ (2 : ℤ),
    β ^ (1 : ℤ) * α ^ (0 : ℤ), β ^ (1 : ℤ) * α ^ (-2 : ℤ),
    β ^ (1 : ℤ) * α ^ (4 : ℤ), β ^ (1 : ℤ) * α ^ (2 : ℤ), β ^ (1 : ℤ) * α ^ (0 : ℤ),
    β ^ (1 : ℤ) * α ^ (-2 : ℤ), β ^ (1 : ℤ) * α ^ (-4 : ℤ),
    β ^ (1 : ℤ) * α ^ (2 : ℤ), β ^ (1 : ℤ) * α ^ (0 : ℤ), β ^ (1 : ℤ) * α ^ (-2 : ℤ),
    β ^ (1 : ℤ) * α ^ (-4 : ℤ), β ^ (1 : ℤ) * α ^ (-6 : ℤ),
    β ^ (-1 : ℤ) * α ^ (6 : ℤ), β ^ (-1 : ℤ) * α ^ (4 : ℤ), β ^ (-1 : ℤ) * α ^ (2 : ℤ),
    β ^ (-1 : ℤ) * α ^ (0 : ℤ), β ^ (-1 : ℤ) * α ^ (-2 : ℤ),
    β ^ (-1 : ℤ) * α ^ (4 : ℤ), β ^ (-1 : ℤ) * α ^ (2 : ℤ), β ^ (-1 : ℤ) * α ^ (0 : ℤ),
    β ^ (-1 : ℤ) * α ^ (-2 : ℤ), β ^ (-1 : ℤ) * α ^ (-4 : ℤ),
    β ^ (-1 : ℤ) * α ^ (2 : ℤ), β ^ (-1 : ℤ) * α ^ (0 : ℤ), β ^ (-1 : ℤ) * α ^ (-2 : ℤ),
    β ^ (-1 : ℤ) * α ^ (-4 : ℤ), β ^ (-1 : ℤ) * α ^ (-6 : ℤ)]

/-- The relabeling `Fin 30 ≃ Fin 14 ⊕ (Fin 10 ⊕ Fin 6)` splitting the vehicle into
the three twisted rungs. -/
def vehicleSplit : Fin 30 ≃ Fin 14 ⊕ (Fin 10 ⊕ Fin 6) where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4,
             Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), Sum.inr (Sum.inl 2),
             Sum.inr (Sum.inl 3), Sum.inl 5,
             Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 2),
             Sum.inr (Sum.inl 4), Sum.inl 6,
             Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11,
             Sum.inr (Sum.inl 5), Sum.inr (Sum.inl 6), Sum.inr (Sum.inl 7),
             Sum.inr (Sum.inl 8), Sum.inl 12,
             Sum.inr (Sum.inr 3), Sum.inr (Sum.inr 4), Sum.inr (Sum.inr 5),
             Sum.inr (Sum.inl 9), Sum.inl 13]
  invFun := Sum.elim ![0, 1, 2, 3, 4, 9, 14, 15, 16, 17, 18, 19, 24, 29]
    (Sum.elim ![5, 6, 7, 8, 13, 20, 21, 22, 23, 28] ![10, 11, 12, 25, 26, 27])
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

/-- **The vehicle decomposition**:
`std_g ⊗ (Sym²_f ⊗ Sym⁴_f) = (std_g⊗Sym⁶_f) ⊕ (std_g⊗Sym⁴_f) ⊕ (std_g⊗Sym²_f)` at
the weight level. -/
theorem vehicleWeight_decomposition (β α : ℂ) :
    vehicleWeight β α
      = (Sum.elim (gSym6Weight β α)
          (Sum.elim (gSym4Weight β α) (gSym2Weight β α))) ∘ vehicleSplit := by
  funext i
  fin_cases i <;> rfl

/-- **THE VEHICLE BANK LAW**: the `(g ⊠ Sym²f) × Sym⁴f` coefficient bank is the
`⋆`-product of the three twisted-rung banks —
`L((g⊠Sym²f) × Sym⁴f) = L(g×Sym⁶f)·L(g×Sym⁴f)·L(g×Sym²f)` at every `n`.  With the
cited automorphy of `g ⊠ Sym²f` (Kim–Shahidi) this is the channel through which
Jacquet–Piatetski-Shapiro–Shalika control reaches the `g`-twisted rung 6. -/
theorem vehicle_bank (G : HeckeEigenData g) (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => vehicleWeight (G.satake p.2) (H.satake p.2)))
      = coefficientArithmetic (radialGlobalSatakeCoeff
          (fun p => gSym6Weight (G.satake p.2) (H.satake p.2)))
        * (coefficientArithmetic (radialGlobalSatakeCoeff
            (fun p => gSym4Weight (G.satake p.2) (H.satake p.2)))
          * coefficientArithmetic (radialGlobalSatakeCoeff
              (fun p => gSym2Weight (G.satake p.2) (H.satake p.2)))) := by
  have hdec : (fun p : Nat.Primes => vehicleWeight (G.satake p.2) (H.satake p.2))
      = fun p : Nat.Primes =>
          (Sum.elim (gSym6Weight (G.satake p.2) (H.satake p.2))
            (Sum.elim (gSym4Weight (G.satake p.2) (H.satake p.2))
              (gSym2Weight (G.satake p.2) (H.satake p.2)))) ∘ vehicleSplit := by
    funext p
    exact vehicleWeight_decomposition (G.satake p.2) (H.satake p.2)
  rw [hdec, radialGlobalSatakeCoeff_equiv vehicleSplit, bankArithmetic_sumElim,
    bankArithmetic_sumElim]

end CriticalLinePhasor.CapVehicle

#print axioms CriticalLinePhasor.CapVehicle.vehicleWeight_decomposition
#print axioms CriticalLinePhasor.CapVehicle.vehicle_bank
