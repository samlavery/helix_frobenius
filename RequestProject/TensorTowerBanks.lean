import RequestProject.TransportClosure

/-!
# The tensor-tower bank identities: the r = 3 opener and the r = 5 lever

The pinning campaign's transfer layer.  The registration of a `Sym^r` bank on the
carrier is the campaign's open analytic step at `r ≥ 3`; this file compiles the
**exact coefficient-level transfer identities** that convert each `Sym^r` obligation
into a *convolution* obligation, where the seed's modularity can act (at `r = 2` the
registration consumed modularity twice — the double-rail load `|f|²` against the
carrier's lattice theta; the classical shadow of the `r = 3` convolution step is the
`GL(2)×GL(3)` Rankin–Selberg / Garrett layer, the house form the tri-rail load):

* `bank_symClock` — the extracted rank-uniform identification: the all-place bank of
  the `Sym^r` clock family is `symrBank H r`, every rank (factored out of the
  `plethysm_bank` assembly for reuse);
* `stdSym2Weight` + `stdSym2Weight_products` + `stdSym2Weight_decomposition` —
  **`std ⊗ Sym² = Sym³ ⊕ std`** at the weight level: the six pairwise products of the
  `std` and `Sym²` clocks are the `Sym³` clock together with the `std` clock
  (`stdSym2Split : Fin 6 ≃ Fin 4 ⊕ Fin 2`);
* `tensorCube_bank` — **the r = 3 opener**: the `std ⊗ Sym²` bank equals
  `symrBank H 3 ⋆ symrBank H 1` — `L(f × Sym²f) = L(Sym³f)·L(f)` as an identity of
  coefficient banks, at every `n`;
* `stdSym4Weight` + honesty + decomposition — **`std ⊗ Sym⁴ = Sym⁵ ⊕ Sym³`**
  (`stdSym4Split : Fin 10 ≃ Fin 6 ⊕ Fin 4`);
* `tensorQuintic_bank` — **the r = 5 lever**: the `std ⊗ Sym⁴` bank equals
  `symrBank H 5 ⋆ symrBank H 3` — `L(f × Sym⁴f) = L(Sym⁵f)·L(Sym³f)` as banks, the
  exact identity through which the analytic properties of the automorphic pair
  `(f, Sym⁴f)` reach `Sym⁵`.

Harmonic register.  The identities are exact channel regroupings — the pairwise
product multiset *is* the target multiset, no estimate anywhere; the local shadow is
`tensorStepLocalPoly_eq_sym_mul_lower` (already compiled), and the trace shadow is
`clebsch_gordan_trace` (`RSLocalCauchy`).  The analytic difficulty is untouched here
and lives in the convolution package for the pair — the registration step.

Register, scope.  Remaining named steps of the campaign: the `Sym² ⊗ Sym⁴`,
`Sym³ ⊗ Sym⁴`, `Sym⁴ ⊗ Sym⁴` instances (same pattern, completing the `r ≤ 8`
coefficient tower); the convolution analytic package for `(f, Sym²f)` (the tri-rail
registration — the campaign's heart); the division interface producing the `Sym^r`
one-line data from the pair package and lower rungs.  No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups ArithmeticFunction.zeta LSeries.notation

namespace CriticalLinePhasor.TensorTowerBanks

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.Sym2Rankin CriticalLinePhasor.SymrBank
open CriticalLinePhasor.TransportClosure

variable {k : ℤ} {f : CuspForm 𝒮ℒ k}

/-! ## The extracted rank-uniform bank identification -/

/-- The all-place bank of the `Sym^r` clock family is `symrBank H r`, at every rank —
extracted from the `plethysm_bank` assembly for reuse across the tower. -/
theorem bank_symClock (H : HeckeEigenData f) (r : ℕ) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p : Nat.Primes => fun i : Fin (r + 1) =>
        symClockWeight r (H.satake p.2) (i : ℕ)))
      = symrBank H r := by
  ext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [coefficientArithmetic]
  · show (if m = 0 then 0 else _) = _
    rw [if_neg hm.ne']
    rw [show radialGlobalSatakeCoeff
        (fun p : Nat.Primes => fun i : Fin (r + 1) =>
          symClockWeight r (H.satake p.2) (i : ℕ)) (m - 1)
        = symrBank H r (m - 1 + 1) from
      CriticalLinePhasor.Sym2Join.radialGlobal_eq_symrBank H r (m - 1),
      Nat.sub_add_cancel hm]

/-! ## `std ⊗ Sym² = Sym³ ⊕ std`: the r = 3 opener -/

/-- The `std ⊗ Sym²` weight system: the six pairwise products of the `std` clock
`(α, α⁻¹)` and the `Sym²` clock `(α², 1, α⁻²)`, in the order
`(0,0),(0,1),(0,2),(1,0),(1,1),(1,2)`. -/
noncomputable def stdSym2Weight (α : ℂ) : Fin 6 → ℂ :=
  ![α ^ (3 : ℤ), α ^ (1 : ℤ), α ^ (-1 : ℤ), α ^ (1 : ℤ), α ^ (-1 : ℤ), α ^ (-3 : ℤ)]

/-- The six entries are the pairwise products `u_i · w_j` of the `std` and `Sym²`
clocks. -/
theorem stdSym2Weight_products (α : ℂ) (hα : α ≠ 0) :
    stdSym2Weight α 0 = symClockWeight 1 α 0 * symClockWeight 2 α 0 ∧
    stdSym2Weight α 1 = symClockWeight 1 α 0 * symClockWeight 2 α 1 ∧
    stdSym2Weight α 2 = symClockWeight 1 α 0 * symClockWeight 2 α 2 ∧
    stdSym2Weight α 3 = symClockWeight 1 α 1 * symClockWeight 2 α 0 ∧
    stdSym2Weight α 4 = symClockWeight 1 α 1 * symClockWeight 2 α 1 ∧
    stdSym2Weight α 5 = symClockWeight 1 α 1 * symClockWeight 2 α 2 := by
  have h10 : symClockWeight 1 α 0 = α ^ (1 : ℤ) := by unfold symClockWeight; norm_num
  have h11 : symClockWeight 1 α 1 = α ^ (-1 : ℤ) := by unfold symClockWeight; norm_num
  have h20 : symClockWeight 2 α 0 = α ^ (2 : ℤ) := by unfold symClockWeight; norm_num
  have h21 : symClockWeight 2 α 1 = 1 := by unfold symClockWeight; norm_num
  have h22 : symClockWeight 2 α 2 = α ^ (-2 : ℤ) := by unfold symClockWeight; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [stdSym2Weight, h10, h11, h20, h21, h22] <;>
    field_simp

/-- The relabeling `Fin 6 ≃ Fin 4 ⊕ Fin 2` splitting the products into the `Sym³`
clock and the `std` clock. -/
def stdSym2Split : Fin 6 ≃ Fin 4 ⊕ Fin 2 where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1, Sum.inl 3]
  invFun := Sum.elim ![0, 1, 2, 5] ![3, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    rcases i with i | i
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl

/-- **`std ⊗ Sym² = Sym³ ⊕ std` at the weight level**: the six pairwise products are
the `Sym³` clock together with the `std` clock. -/
theorem stdSym2Weight_decomposition (α : ℂ) :
    stdSym2Weight α
      = (Sum.elim (fun i : Fin 4 => symClockWeight 3 α (i : ℕ))
          (fun i : Fin 2 => symClockWeight 1 α (i : ℕ))) ∘ stdSym2Split := by
  funext i
  fin_cases i <;>
    simp only [stdSym2Weight, stdSym2Split, Function.comp_apply, Equiv.coe_fn_mk] <;>
    norm_num [symClockWeight]

/-- **THE r = 3 OPENER**: the `std ⊗ Sym²` bank is `symrBank 3 ⋆ symrBank 1` —
`L(f × Sym²f) = L(Sym³f) · L(f)` as an identity of coefficient banks at every `n`.
The `Sym³` registration obligation is exactly the `(f, Sym²f)` convolution
obligation. -/
theorem tensorCube_bank (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => stdSym2Weight (H.satake p.2)))
      = symrBank H 3 * symrBank H 1 := by
  have hdec : (fun p : Nat.Primes => stdSym2Weight (H.satake p.2))
      = fun p : Nat.Primes =>
          (Sum.elim (fun i : Fin 4 => symClockWeight 3 (H.satake p.2) (i : ℕ))
            (fun i : Fin 2 => symClockWeight 1 (H.satake p.2) (i : ℕ))) ∘ stdSym2Split := by
    funext p
    exact stdSym2Weight_decomposition (H.satake p.2)
  rw [hdec, radialGlobalSatakeCoeff_equiv stdSym2Split, bankArithmetic_sumElim,
    bank_symClock H 3, bank_symClock H 1]

/-! ## `std ⊗ Sym⁴ = Sym⁵ ⊕ Sym³`: the r = 5 lever -/

/-- The `std ⊗ Sym⁴` weight system: the ten pairwise products of the `std` clock
`(α, α⁻¹)` and the `Sym⁴` clock `(α⁴, α², 1, α⁻², α⁻⁴)`, rows in order. -/
noncomputable def stdSym4Weight (α : ℂ) : Fin 10 → ℂ :=
  ![α ^ (5 : ℤ), α ^ (3 : ℤ), α ^ (1 : ℤ), α ^ (-1 : ℤ), α ^ (-3 : ℤ),
    α ^ (3 : ℤ), α ^ (1 : ℤ), α ^ (-1 : ℤ), α ^ (-3 : ℤ), α ^ (-5 : ℤ)]

/-- The ten entries are the pairwise products of the `std` and `Sym⁴` clocks. -/
theorem stdSym4Weight_products (α : ℂ) (hα : α ≠ 0) :
    stdSym4Weight α 0 = symClockWeight 1 α 0 * symClockWeight 4 α 0 ∧
    stdSym4Weight α 1 = symClockWeight 1 α 0 * symClockWeight 4 α 1 ∧
    stdSym4Weight α 2 = symClockWeight 1 α 0 * symClockWeight 4 α 2 ∧
    stdSym4Weight α 3 = symClockWeight 1 α 0 * symClockWeight 4 α 3 ∧
    stdSym4Weight α 4 = symClockWeight 1 α 0 * symClockWeight 4 α 4 ∧
    stdSym4Weight α 5 = symClockWeight 1 α 1 * symClockWeight 4 α 0 ∧
    stdSym4Weight α 6 = symClockWeight 1 α 1 * symClockWeight 4 α 1 ∧
    stdSym4Weight α 7 = symClockWeight 1 α 1 * symClockWeight 4 α 2 ∧
    stdSym4Weight α 8 = symClockWeight 1 α 1 * symClockWeight 4 α 3 ∧
    stdSym4Weight α 9 = symClockWeight 1 α 1 * symClockWeight 4 α 4 := by
  have h10 : symClockWeight 1 α 0 = α ^ (1 : ℤ) := by unfold symClockWeight; norm_num
  have h11 : symClockWeight 1 α 1 = α ^ (-1 : ℤ) := by unfold symClockWeight; norm_num
  have h40 : symClockWeight 4 α 0 = α ^ (4 : ℤ) := by unfold symClockWeight; norm_num
  have h41 : symClockWeight 4 α 1 = α ^ (2 : ℤ) := by unfold symClockWeight; norm_num
  have h42 : symClockWeight 4 α 2 = 1 := by unfold symClockWeight; norm_num
  have h43 : symClockWeight 4 α 3 = α ^ (-2 : ℤ) := by unfold symClockWeight; norm_num
  have h44 : symClockWeight 4 α 4 = α ^ (-4 : ℤ) := by unfold symClockWeight; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [stdSym4Weight, h10, h11, h40, h41, h42, h43, h44] <;>
    field_simp

/-- The relabeling `Fin 10 ≃ Fin 6 ⊕ Fin 4` splitting the products into the `Sym⁵`
clock and the `Sym³` clock. -/
def stdSym4Split : Fin 10 ≃ Fin 6 ⊕ Fin 4 where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4,
             Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl 5]
  invFun := Sum.elim ![0, 1, 2, 3, 4, 9] ![5, 6, 7, 8]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    rcases i with i | i
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl

/-- **`std ⊗ Sym⁴ = Sym⁵ ⊕ Sym³` at the weight level**. -/
theorem stdSym4Weight_decomposition (α : ℂ) :
    stdSym4Weight α
      = (Sum.elim (fun i : Fin 6 => symClockWeight 5 α (i : ℕ))
          (fun i : Fin 4 => symClockWeight 3 α (i : ℕ))) ∘ stdSym4Split := by
  funext i
  fin_cases i <;>
    simp only [stdSym4Weight, stdSym4Split, Function.comp_apply, Equiv.coe_fn_mk] <;>
    norm_num [symClockWeight]

/-- **THE r = 5 LEVER**: the `std ⊗ Sym⁴` bank is `symrBank 5 ⋆ symrBank 3` —
`L(f × Sym⁴f) = L(Sym⁵f) · L(Sym³f)` as an identity of coefficient banks at every
`n`: the exact channel through which the analytic properties of the automorphic pair
`(f, Sym⁴f)` reach `Sym⁵`. -/
theorem tensorQuintic_bank (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => stdSym4Weight (H.satake p.2)))
      = symrBank H 5 * symrBank H 3 := by
  have hdec : (fun p : Nat.Primes => stdSym4Weight (H.satake p.2))
      = fun p : Nat.Primes =>
          (Sum.elim (fun i : Fin 6 => symClockWeight 5 (H.satake p.2) (i : ℕ))
            (fun i : Fin 4 => symClockWeight 3 (H.satake p.2) (i : ℕ))) ∘ stdSym4Split := by
    funext p
    exact stdSym4Weight_decomposition (H.satake p.2)
  rw [hdec, radialGlobalSatakeCoeff_equiv stdSym4Split, bankArithmetic_sumElim,
    bank_symClock H 5, bank_symClock H 3]

/-! ## `Sym² ⊗ Sym⁴ = Sym⁶ ⊕ Sym⁴ ⊕ Sym²`: the r = 6 rung -/

/-- The `Sym² ⊗ Sym⁴` weight system: fifteen pairwise products, rows in order. -/
noncomputable def sym2Sym4Weight (α : ℂ) : Fin 15 → ℂ :=
  ![α ^ (6 : ℤ), α ^ (4 : ℤ), α ^ (2 : ℤ), 1, α ^ (-2 : ℤ),
    α ^ (4 : ℤ), α ^ (2 : ℤ), 1, α ^ (-2 : ℤ), α ^ (-4 : ℤ),
    α ^ (2 : ℤ), 1, α ^ (-2 : ℤ), α ^ (-4 : ℤ), α ^ (-6 : ℤ)]

/-- The relabeling `Fin 15 ≃ Fin 7 ⊕ (Fin 5 ⊕ Fin 3)` splitting the products into the
`Sym⁶`, `Sym⁴`, `Sym²` clocks. -/
def sym2Sym4Split : Fin 15 ≃ Fin 7 ⊕ (Fin 5 ⊕ Fin 3) where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4,
             Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), Sum.inr (Sum.inl 2),
             Sum.inr (Sum.inl 3), Sum.inl 5,
             Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 2),
             Sum.inr (Sum.inl 4), Sum.inl 6]
  invFun := Sum.elim ![0, 1, 2, 3, 4, 9, 14] (Sum.elim ![5, 6, 7, 8, 13] ![10, 11, 12])
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

/-- **`Sym² ⊗ Sym⁴ = Sym⁶ ⊕ Sym⁴ ⊕ Sym²` at the weight level**. -/
theorem sym2Sym4Weight_decomposition (α : ℂ) :
    sym2Sym4Weight α
      = (Sum.elim (fun i : Fin 7 => symClockWeight 6 α (i : ℕ))
          (Sum.elim (fun i : Fin 5 => symClockWeight 4 α (i : ℕ))
            (fun i : Fin 3 => symClockWeight 2 α (i : ℕ)))) ∘ sym2Sym4Split := by
  funext i
  fin_cases i <;>
    simp only [sym2Sym4Weight, sym2Sym4Split, Function.comp_apply, Equiv.coe_fn_mk] <;>
    norm_num [symClockWeight]

/-- **The r = 6 rung**: `L(Sym²f × Sym⁴f) = L(Sym⁶f)·L(Sym⁴f)·L(Sym²f)` as banks. -/
theorem tensorSym2Sym4_bank (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => sym2Sym4Weight (H.satake p.2)))
      = symrBank H 6 * (symrBank H 4 * symrBank H 2) := by
  have hdec : (fun p : Nat.Primes => sym2Sym4Weight (H.satake p.2))
      = fun p : Nat.Primes =>
          (Sum.elim (fun i : Fin 7 => symClockWeight 6 (H.satake p.2) (i : ℕ))
            (Sum.elim (fun i : Fin 5 => symClockWeight 4 (H.satake p.2) (i : ℕ))
              (fun i : Fin 3 => symClockWeight 2 (H.satake p.2) (i : ℕ)))) ∘ sym2Sym4Split := by
    funext p
    exact sym2Sym4Weight_decomposition (H.satake p.2)
  rw [hdec, radialGlobalSatakeCoeff_equiv sym2Sym4Split, bankArithmetic_sumElim,
    bank_symClock H 6, bankArithmetic_sumElim, bank_symClock H 4, bank_symClock H 2]

/-! ## `Sym³ ⊗ Sym⁴ = Sym⁷ ⊕ Sym⁵ ⊕ Sym³ ⊕ std`: the r = 7 rung -/

/-- The `Sym³ ⊗ Sym⁴` weight system: twenty pairwise products, rows in order. -/
noncomputable def sym3Sym4Weight (α : ℂ) : Fin 20 → ℂ :=
  ![α ^ (7 : ℤ), α ^ (5 : ℤ), α ^ (3 : ℤ), α ^ (1 : ℤ), α ^ (-1 : ℤ),
    α ^ (5 : ℤ), α ^ (3 : ℤ), α ^ (1 : ℤ), α ^ (-1 : ℤ), α ^ (-3 : ℤ),
    α ^ (3 : ℤ), α ^ (1 : ℤ), α ^ (-1 : ℤ), α ^ (-3 : ℤ), α ^ (-5 : ℤ),
    α ^ (1 : ℤ), α ^ (-1 : ℤ), α ^ (-3 : ℤ), α ^ (-5 : ℤ), α ^ (-7 : ℤ)]

/-- The relabeling `Fin 20 ≃ Fin 8 ⊕ (Fin 6 ⊕ (Fin 4 ⊕ Fin 2))`. -/
def sym3Sym4Split : Fin 20 ≃ Fin 8 ⊕ (Fin 6 ⊕ (Fin 4 ⊕ Fin 2)) where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4,
             Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), Sum.inr (Sum.inl 2),
             Sum.inr (Sum.inl 3), Sum.inl 5,
             Sum.inr (Sum.inr (Sum.inl 0)), Sum.inr (Sum.inr (Sum.inl 1)),
             Sum.inr (Sum.inr (Sum.inl 2)), Sum.inr (Sum.inl 4), Sum.inl 6,
             Sum.inr (Sum.inr (Sum.inr 0)), Sum.inr (Sum.inr (Sum.inr 1)),
             Sum.inr (Sum.inr (Sum.inl 3)), Sum.inr (Sum.inl 5), Sum.inl 7]
  invFun := Sum.elim ![0, 1, 2, 3, 4, 9, 14, 19]
    (Sum.elim ![5, 6, 7, 8, 13, 18] (Sum.elim ![10, 11, 12, 17] ![15, 16]))
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    rcases i with i | i
    · fin_cases i <;> rfl
    · rcases i with i | i
      · fin_cases i <;> rfl
      · rcases i with i | i
        · fin_cases i <;> rfl
        · fin_cases i <;> rfl

/-- **`Sym³ ⊗ Sym⁴ = Sym⁷ ⊕ Sym⁵ ⊕ Sym³ ⊕ std` at the weight level**. -/
theorem sym3Sym4Weight_decomposition (α : ℂ) :
    sym3Sym4Weight α
      = (Sum.elim (fun i : Fin 8 => symClockWeight 7 α (i : ℕ))
          (Sum.elim (fun i : Fin 6 => symClockWeight 5 α (i : ℕ))
            (Sum.elim (fun i : Fin 4 => symClockWeight 3 α (i : ℕ))
              (fun i : Fin 2 => symClockWeight 1 α (i : ℕ))))) ∘ sym3Sym4Split := by
  funext i
  fin_cases i <;>
    simp only [sym3Sym4Weight, sym3Sym4Split, Function.comp_apply, Equiv.coe_fn_mk] <;>
    norm_num [symClockWeight]

/-- **The r = 7 rung**: `L(Sym³f × Sym⁴f) = L(Sym⁷f)·L(Sym⁵f)·L(Sym³f)·L(f)` as
banks. -/
theorem tensorSym3Sym4_bank (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => sym3Sym4Weight (H.satake p.2)))
      = symrBank H 7 * (symrBank H 5 * (symrBank H 3 * symrBank H 1)) := by
  have hdec : (fun p : Nat.Primes => sym3Sym4Weight (H.satake p.2))
      = fun p : Nat.Primes =>
          (Sum.elim (fun i : Fin 8 => symClockWeight 7 (H.satake p.2) (i : ℕ))
            (Sum.elim (fun i : Fin 6 => symClockWeight 5 (H.satake p.2) (i : ℕ))
              (Sum.elim (fun i : Fin 4 => symClockWeight 3 (H.satake p.2) (i : ℕ))
                (fun i : Fin 2 => symClockWeight 1 (H.satake p.2) (i : ℕ))))) ∘ sym3Sym4Split := by
    funext p
    exact sym3Sym4Weight_decomposition (H.satake p.2)
  rw [hdec, radialGlobalSatakeCoeff_equiv sym3Sym4Split, bankArithmetic_sumElim,
    bank_symClock H 7, bankArithmetic_sumElim, bank_symClock H 5,
    bankArithmetic_sumElim, bank_symClock H 3, bank_symClock H 1]

/-! ## `Sym⁴ ⊗ Sym⁴ = Sym⁸ ⊕ Sym⁶ ⊕ Sym⁴ ⊕ Sym² ⊕ 1`: the r = 8 rung -/

/-- The `Sym⁴ ⊗ Sym⁴` weight system: twenty-five pairwise products, rows in order. -/
noncomputable def sym4Sym4Weight (α : ℂ) : Fin 25 → ℂ :=
  ![α ^ (8 : ℤ), α ^ (6 : ℤ), α ^ (4 : ℤ), α ^ (2 : ℤ), 1,
    α ^ (6 : ℤ), α ^ (4 : ℤ), α ^ (2 : ℤ), 1, α ^ (-2 : ℤ),
    α ^ (4 : ℤ), α ^ (2 : ℤ), 1, α ^ (-2 : ℤ), α ^ (-4 : ℤ),
    α ^ (2 : ℤ), 1, α ^ (-2 : ℤ), α ^ (-4 : ℤ), α ^ (-6 : ℤ),
    1, α ^ (-2 : ℤ), α ^ (-4 : ℤ), α ^ (-6 : ℤ), α ^ (-8 : ℤ)]

/-- The relabeling `Fin 25 ≃ Fin 9 ⊕ (Fin 7 ⊕ (Fin 5 ⊕ (Fin 3 ⊕ Fin 1)))`. -/
def sym4Sym4Split : Fin 25 ≃ Fin 9 ⊕ (Fin 7 ⊕ (Fin 5 ⊕ (Fin 3 ⊕ Fin 1))) where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4,
             Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), Sum.inr (Sum.inl 2),
             Sum.inr (Sum.inl 3), Sum.inl 5,
             Sum.inr (Sum.inr (Sum.inl 0)), Sum.inr (Sum.inr (Sum.inl 1)),
             Sum.inr (Sum.inr (Sum.inl 2)), Sum.inr (Sum.inl 4), Sum.inl 6,
             Sum.inr (Sum.inr (Sum.inr (Sum.inl 0))), Sum.inr (Sum.inr (Sum.inr (Sum.inl 1))),
             Sum.inr (Sum.inr (Sum.inl 3)), Sum.inr (Sum.inl 5), Sum.inl 7,
             Sum.inr (Sum.inr (Sum.inr (Sum.inr 0))), Sum.inr (Sum.inr (Sum.inr (Sum.inl 2))),
             Sum.inr (Sum.inr (Sum.inl 4)), Sum.inr (Sum.inl 6), Sum.inl 8]
  invFun := Sum.elim ![0, 1, 2, 3, 4, 9, 14, 19, 24]
    (Sum.elim ![5, 6, 7, 8, 13, 18, 23]
      (Sum.elim ![10, 11, 12, 17, 22] (Sum.elim ![15, 16, 21] ![20])))
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    rcases i with i | i
    · fin_cases i <;> rfl
    · rcases i with i | i
      · fin_cases i <;> rfl
      · rcases i with i | i
        · fin_cases i <;> rfl
        · rcases i with i | i
          · fin_cases i <;> rfl
          · fin_cases i
            rfl

/-- **`Sym⁴ ⊗ Sym⁴ = Sym⁸ ⊕ Sym⁶ ⊕ Sym⁴ ⊕ Sym² ⊕ 1` at the weight level**. -/
theorem sym4Sym4Weight_decomposition (α : ℂ) :
    sym4Sym4Weight α
      = (Sum.elim (fun i : Fin 9 => symClockWeight 8 α (i : ℕ))
          (Sum.elim (fun i : Fin 7 => symClockWeight 6 α (i : ℕ))
            (Sum.elim (fun i : Fin 5 => symClockWeight 4 α (i : ℕ))
              (Sum.elim (fun i : Fin 3 => symClockWeight 2 α (i : ℕ))
                (fun _ : Fin 1 => (1 : ℂ)))))) ∘ sym4Sym4Split := by
  funext i
  fin_cases i <;>
    simp only [sym4Sym4Weight, sym4Sym4Split, Function.comp_apply, Equiv.coe_fn_mk] <;>
    norm_num [symClockWeight]

/-- **The r = 8 rung (the classical tower's cap)**:
`L(Sym⁴f × Sym⁴f) = L(Sym⁸f)·L(Sym⁶f)·L(Sym⁴f)·L(Sym²f)·ζ` as banks. -/
theorem tensorSym4Sym4_bank (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => sym4Sym4Weight (H.satake p.2)))
      = symrBank H 8 * (symrBank H 6 * (symrBank H 4 * (symrBank H 2 *
          ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)))) := by
  have hdec : (fun p : Nat.Primes => sym4Sym4Weight (H.satake p.2))
      = fun p : Nat.Primes =>
          (Sum.elim (fun i : Fin 9 => symClockWeight 8 (H.satake p.2) (i : ℕ))
            (Sum.elim (fun i : Fin 7 => symClockWeight 6 (H.satake p.2) (i : ℕ))
              (Sum.elim (fun i : Fin 5 => symClockWeight 4 (H.satake p.2) (i : ℕ))
                (Sum.elim (fun i : Fin 3 => symClockWeight 2 (H.satake p.2) (i : ℕ))
                  (fun _ : Fin 1 => (1 : ℂ)))))) ∘ sym4Sym4Split := by
    funext p
    exact sym4Sym4Weight_decomposition (H.satake p.2)
  rw [hdec, radialGlobalSatakeCoeff_equiv sym4Sym4Split, bankArithmetic_sumElim,
    bank_symClock H 8, bankArithmetic_sumElim, bank_symClock H 6,
    bankArithmetic_sumElim, bank_symClock H 4, bankArithmetic_sumElim,
    bank_symClock H 2, bankArithmetic_unit_eq_zeta]

/-! ## The identities in L-function form -/

/-- **The r = 3 opener as L-functions**: on the common summability region,
`L(f × Sym²f, s) = L(Sym³f, s) · L(f, s)`. -/
theorem tensorCube_LSeries (H : HeckeEigenData f) (s : ℂ)
    (h3 : LSeriesSummable (⇑(symrBank H 3)) s)
    (h1 : LSeriesSummable (⇑(symrBank H 1)) s) :
    LSeries (⇑(coefficientArithmetic (radialGlobalSatakeCoeff
        (fun p => stdSym2Weight (H.satake p.2))))) s
      = LSeries (⇑(symrBank H 3)) s * LSeries (⇑(symrBank H 1)) s := by
  rw [tensorCube_bank H]
  exact ArithmeticFunction.LSeries_mul' h3 h1

/-- **The r = 5 lever as L-functions**: on the common summability region,
`L(f × Sym⁴f, s) = L(Sym⁵f, s) · L(Sym³f, s)` — the exact identity through which
the analytic control of the automorphic pair `(f, Sym⁴f)` reaches `Sym⁵`. -/
theorem tensorQuintic_LSeries (H : HeckeEigenData f) (s : ℂ)
    (h5 : LSeriesSummable (⇑(symrBank H 5)) s)
    (h3 : LSeriesSummable (⇑(symrBank H 3)) s) :
    LSeries (⇑(coefficientArithmetic (radialGlobalSatakeCoeff
        (fun p => stdSym4Weight (H.satake p.2))))) s
      = LSeries (⇑(symrBank H 5)) s * LSeries (⇑(symrBank H 3)) s := by
  rw [tensorQuintic_bank H]
  exact ArithmeticFunction.LSeries_mul' h5 h3

end CriticalLinePhasor.TensorTowerBanks

#print axioms CriticalLinePhasor.TensorTowerBanks.bank_symClock
#print axioms CriticalLinePhasor.TensorTowerBanks.stdSym2Weight_products
#print axioms CriticalLinePhasor.TensorTowerBanks.stdSym2Weight_decomposition
#print axioms CriticalLinePhasor.TensorTowerBanks.tensorCube_bank
#print axioms CriticalLinePhasor.TensorTowerBanks.stdSym4Weight_products
#print axioms CriticalLinePhasor.TensorTowerBanks.stdSym4Weight_decomposition
#print axioms CriticalLinePhasor.TensorTowerBanks.tensorQuintic_bank
#print axioms CriticalLinePhasor.TensorTowerBanks.tensorSym2Sym4_bank
#print axioms CriticalLinePhasor.TensorTowerBanks.tensorSym3Sym4_bank
#print axioms CriticalLinePhasor.TensorTowerBanks.tensorSym4Sym4_bank
#print axioms CriticalLinePhasor.TensorTowerBanks.tensorCube_LSeries
#print axioms CriticalLinePhasor.TensorTowerBanks.tensorQuintic_LSeries
