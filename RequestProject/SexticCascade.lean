import RequestProject.QuinticTwists

/-!
# The sextic cascade and the quintic square: the conditional tower's algebra layer

Two unconditional channel identities extending the tower past the classical cap,
compiled now so that the analytic cascade is pure citation the day its named
hypothesis lands:

* `sexticTau_bank` — **the cascade step**:
  `(std_f ⊗ τ₃) ⊗ Sym⁵_f = (Sym⁶_f ⊗ τ₃) ⊕ (Sym⁴_f ⊗ τ₃)`, universal over abstract
  `GL(3)` Satake families.  Register: *if* `Sym⁵f` is automorphic (the named
  hypothesis — equivalently one new functorial product, or converse-grade `m ≤ 4`
  entirety), then `(f⊠τ₃) × Sym⁵f` is a JPSS pair and division by the controlled
  `L(Sym⁴f × τ₃)` gives Serre-grade `L(Sym⁶f × τ₃)` for every `GL(3)` cusp form —
  the `m = 3` family one rung up, and the tower's moment reach extends toward
  twelve;
* `quinticSquare_bank` — **the conditional pair**:
  `Sym⁵ ⊗ Sym⁵ = Sym¹⁰ ⊕ Sym⁸ ⊕ Sym⁶ ⊕ Sym⁴ ⊕ Sym² ⊕ 1` — under the same named
  hypothesis, `L(Sym⁵f × Sym⁵f)` is JPSS-controlled and this identity distributes
  that control across the even rungs to `r = 10`.

Grade register.  The compiled content is exact channel algebra, hypothesis-free.
Every analytic consequence above is **conditional on `Sym⁵` automorphy and stated
at Serre grade** (holomorphy and nonvanishing on `Re s ≥ 1`); division chains
never supply converse-grade entirety.  No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups ArithmeticFunction.zeta LSeries.notation

namespace CriticalLinePhasor.SexticCascade

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.Sym2Rankin CriticalLinePhasor.SymrBank
open CriticalLinePhasor.TransportClosure CriticalLinePhasor.TensorTowerBanks

variable {k : ℤ} {f : CuspForm 𝒮ℒ k}

/-! ## The sextic cascade vehicle -/

/-- The `Sym⁶_f ⊗ τ₃` weight system over an abstract Satake triple: twenty-one
products. -/
noncomputable def sym6TauWeight (α : ℂ) (t : Fin 3 → ℂ) : Fin 21 → ℂ :=
  ![α ^ (6 : ℤ) * t 0, α ^ (6 : ℤ) * t 1, α ^ (6 : ℤ) * t 2,
    α ^ (4 : ℤ) * t 0, α ^ (4 : ℤ) * t 1, α ^ (4 : ℤ) * t 2,
    α ^ (2 : ℤ) * t 0, α ^ (2 : ℤ) * t 1, α ^ (2 : ℤ) * t 2,
    α ^ (0 : ℤ) * t 0, α ^ (0 : ℤ) * t 1, α ^ (0 : ℤ) * t 2,
    α ^ (-2 : ℤ) * t 0, α ^ (-2 : ℤ) * t 1, α ^ (-2 : ℤ) * t 2,
    α ^ (-4 : ℤ) * t 0, α ^ (-4 : ℤ) * t 1, α ^ (-4 : ℤ) * t 2,
    α ^ (-6 : ℤ) * t 0, α ^ (-6 : ℤ) * t 1, α ^ (-6 : ℤ) * t 2]

/-- The `Sym⁴_f ⊗ τ₃` weight system over an abstract Satake triple: fifteen
products. -/
noncomputable def sym4TauWeight (α : ℂ) (t : Fin 3 → ℂ) : Fin 15 → ℂ :=
  ![α ^ (4 : ℤ) * t 0, α ^ (4 : ℤ) * t 1, α ^ (4 : ℤ) * t 2,
    α ^ (2 : ℤ) * t 0, α ^ (2 : ℤ) * t 1, α ^ (2 : ℤ) * t 2,
    α ^ (0 : ℤ) * t 0, α ^ (0 : ℤ) * t 1, α ^ (0 : ℤ) * t 2,
    α ^ (-2 : ℤ) * t 0, α ^ (-2 : ℤ) * t 1, α ^ (-2 : ℤ) * t 2,
    α ^ (-4 : ℤ) * t 0, α ^ (-4 : ℤ) * t 1, α ^ (-4 : ℤ) * t 2]

/-- The sextic cascade weight system `(std_f ⊗ τ₃) ⊗ Sym⁵_f`: thirty-six products,
`(std⊗Sym⁵)_f`-major order. -/
noncomputable def sexticTauWeight (α : ℂ) (t : Fin 3 → ℂ) : Fin 36 → ℂ :=
  ![α ^ (6 : ℤ) * t 0, α ^ (6 : ℤ) * t 1, α ^ (6 : ℤ) * t 2,
    α ^ (4 : ℤ) * t 0, α ^ (4 : ℤ) * t 1, α ^ (4 : ℤ) * t 2,
    α ^ (2 : ℤ) * t 0, α ^ (2 : ℤ) * t 1, α ^ (2 : ℤ) * t 2,
    α ^ (0 : ℤ) * t 0, α ^ (0 : ℤ) * t 1, α ^ (0 : ℤ) * t 2,
    α ^ (-2 : ℤ) * t 0, α ^ (-2 : ℤ) * t 1, α ^ (-2 : ℤ) * t 2,
    α ^ (-4 : ℤ) * t 0, α ^ (-4 : ℤ) * t 1, α ^ (-4 : ℤ) * t 2,
    α ^ (4 : ℤ) * t 0, α ^ (4 : ℤ) * t 1, α ^ (4 : ℤ) * t 2,
    α ^ (2 : ℤ) * t 0, α ^ (2 : ℤ) * t 1, α ^ (2 : ℤ) * t 2,
    α ^ (0 : ℤ) * t 0, α ^ (0 : ℤ) * t 1, α ^ (0 : ℤ) * t 2,
    α ^ (-2 : ℤ) * t 0, α ^ (-2 : ℤ) * t 1, α ^ (-2 : ℤ) * t 2,
    α ^ (-4 : ℤ) * t 0, α ^ (-4 : ℤ) * t 1, α ^ (-4 : ℤ) * t 2,
    α ^ (-6 : ℤ) * t 0, α ^ (-6 : ℤ) * t 1, α ^ (-6 : ℤ) * t 2]

/-- The relabeling `Fin 36 ≃ Fin 21 ⊕ Fin 15`. -/
def sexticTauSplit : Fin 36 ≃ Fin 21 ⊕ Fin 15 where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2,
             Sum.inl 3, Sum.inl 4, Sum.inl 5,
             Sum.inl 6, Sum.inl 7, Sum.inl 8,
             Sum.inl 9, Sum.inl 10, Sum.inl 11,
             Sum.inl 12, Sum.inl 13, Sum.inl 14,
             Sum.inl 15, Sum.inl 16, Sum.inl 17,
             Sum.inr 0, Sum.inr 1, Sum.inr 2,
             Sum.inr 3, Sum.inr 4, Sum.inr 5,
             Sum.inr 6, Sum.inr 7, Sum.inr 8,
             Sum.inr 9, Sum.inr 10, Sum.inr 11,
             Sum.inr 12, Sum.inr 13, Sum.inr 14,
             Sum.inl 18, Sum.inl 19, Sum.inl 20]
  invFun := Sum.elim
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 33, 34, 35]
    ![18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    rcases i with i | i
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl

/-- **`(std_f ⊗ τ₃) ⊗ Sym⁵_f = (Sym⁶_f ⊗ τ₃) ⊕ (Sym⁴_f ⊗ τ₃)` at the weight
level**, for an arbitrary Satake triple. -/
theorem sexticTauWeight_decomposition (α : ℂ) (t : Fin 3 → ℂ) :
    sexticTauWeight α t
      = (Sum.elim (sym6TauWeight α t) (sym4TauWeight α t)) ∘ sexticTauSplit := by
  funext i
  fin_cases i <;> rfl

/-- **The sextic cascade bank law**, universal over an arbitrary `GL(3)` Satake
family: `L((f⊠τ₃) × Sym⁵f) = L(Sym⁶f × τ₃) · L(Sym⁴f × τ₃)` at every `n` — pure
channel algebra; the analytic reading is conditional on `Sym⁵` automorphy and
Serre-grade. -/
theorem sexticTau_bank (H : HeckeEigenData f) (T : Nat.Primes → Fin 3 → ℂ) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => sexticTauWeight (H.satake p.2) (T p)))
      = coefficientArithmetic (radialGlobalSatakeCoeff
          (fun p => sym6TauWeight (H.satake p.2) (T p)))
        * coefficientArithmetic (radialGlobalSatakeCoeff
            (fun p => sym4TauWeight (H.satake p.2) (T p))) := by
  have hdec : (fun p : Nat.Primes => sexticTauWeight (H.satake p.2) (T p))
      = fun p : Nat.Primes =>
          (Sum.elim (sym6TauWeight (H.satake p.2) (T p))
            (sym4TauWeight (H.satake p.2) (T p))) ∘ sexticTauSplit := by
    funext p
    exact sexticTauWeight_decomposition (H.satake p.2) (T p)
  rw [hdec, radialGlobalSatakeCoeff_equiv sexticTauSplit, bankArithmetic_sumElim]

/-! ## The quintic square -/

/-- The quintic-square weight system `Sym⁵ ⊗ Sym⁵`: thirty-six products, row-major
over the two `Sym⁵` clocks. -/
noncomputable def quinticSquareWeight (α : ℂ) : Fin 36 → ℂ :=
  ![α ^ (10 : ℤ), α ^ (8 : ℤ), α ^ (6 : ℤ), α ^ (4 : ℤ), α ^ (2 : ℤ), α ^ (0 : ℤ),
    α ^ (8 : ℤ), α ^ (6 : ℤ), α ^ (4 : ℤ), α ^ (2 : ℤ), α ^ (0 : ℤ), α ^ (-2 : ℤ),
    α ^ (6 : ℤ), α ^ (4 : ℤ), α ^ (2 : ℤ), α ^ (0 : ℤ), α ^ (-2 : ℤ), α ^ (-4 : ℤ),
    α ^ (4 : ℤ), α ^ (2 : ℤ), α ^ (0 : ℤ), α ^ (-2 : ℤ), α ^ (-4 : ℤ), α ^ (-6 : ℤ),
    α ^ (2 : ℤ), α ^ (0 : ℤ), α ^ (-2 : ℤ), α ^ (-4 : ℤ), α ^ (-6 : ℤ), α ^ (-8 : ℤ),
    α ^ (0 : ℤ), α ^ (-2 : ℤ), α ^ (-4 : ℤ), α ^ (-6 : ℤ), α ^ (-8 : ℤ), α ^ (-10 : ℤ)]

/-- The `Sym^{2k}` clocks written with explicit `zpow` middles, for the six even
rungs of the quintic square. -/
noncomputable def sym10Q (α : ℂ) : Fin 11 → ℂ :=
  ![α ^ (10 : ℤ), α ^ (8 : ℤ), α ^ (6 : ℤ), α ^ (4 : ℤ), α ^ (2 : ℤ), α ^ (0 : ℤ),
    α ^ (-2 : ℤ), α ^ (-4 : ℤ), α ^ (-6 : ℤ), α ^ (-8 : ℤ), α ^ (-10 : ℤ)]

noncomputable def sym8Q (α : ℂ) : Fin 9 → ℂ :=
  ![α ^ (8 : ℤ), α ^ (6 : ℤ), α ^ (4 : ℤ), α ^ (2 : ℤ), α ^ (0 : ℤ),
    α ^ (-2 : ℤ), α ^ (-4 : ℤ), α ^ (-6 : ℤ), α ^ (-8 : ℤ)]

noncomputable def sym6Q (α : ℂ) : Fin 7 → ℂ :=
  ![α ^ (6 : ℤ), α ^ (4 : ℤ), α ^ (2 : ℤ), α ^ (0 : ℤ),
    α ^ (-2 : ℤ), α ^ (-4 : ℤ), α ^ (-6 : ℤ)]

noncomputable def sym4Q (α : ℂ) : Fin 5 → ℂ :=
  ![α ^ (4 : ℤ), α ^ (2 : ℤ), α ^ (0 : ℤ), α ^ (-2 : ℤ), α ^ (-4 : ℤ)]

noncomputable def sym2Q (α : ℂ) : Fin 3 → ℂ :=
  ![α ^ (2 : ℤ), α ^ (0 : ℤ), α ^ (-2 : ℤ)]

noncomputable def sym0Q (α : ℂ) : Fin 1 → ℂ :=
  ![α ^ (0 : ℤ)]

/-- The relabeling
`Fin 36 ≃ Fin 11 ⊕ (Fin 9 ⊕ (Fin 7 ⊕ (Fin 5 ⊕ (Fin 3 ⊕ Fin 1))))`. -/
def quinticSquareSplit :
    Fin 36 ≃ Fin 11 ⊕ (Fin 9 ⊕ (Fin 7 ⊕ (Fin 5 ⊕ (Fin 3 ⊕ Fin 1)))) where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5,
             Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), Sum.inr (Sum.inl 2),
             Sum.inr (Sum.inl 3), Sum.inr (Sum.inl 4), Sum.inl 6,
             Sum.inr (Sum.inr (Sum.inl 0)), Sum.inr (Sum.inr (Sum.inl 1)),
             Sum.inr (Sum.inr (Sum.inl 2)), Sum.inr (Sum.inr (Sum.inl 3)),
             Sum.inr (Sum.inl 5), Sum.inl 7,
             Sum.inr (Sum.inr (Sum.inr (Sum.inl 0))),
             Sum.inr (Sum.inr (Sum.inr (Sum.inl 1))),
             Sum.inr (Sum.inr (Sum.inr (Sum.inl 2))),
             Sum.inr (Sum.inr (Sum.inl 4)), Sum.inr (Sum.inl 6), Sum.inl 8,
             Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl 0)))),
             Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl 1)))),
             Sum.inr (Sum.inr (Sum.inr (Sum.inl 3))), Sum.inr (Sum.inr (Sum.inl 5)),
             Sum.inr (Sum.inl 7), Sum.inl 9,
             Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr 0)))),
             Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl 2)))),
             Sum.inr (Sum.inr (Sum.inr (Sum.inl 4))), Sum.inr (Sum.inr (Sum.inl 6)),
             Sum.inr (Sum.inl 8), Sum.inl 10]
  invFun := Sum.elim ![0, 1, 2, 3, 4, 5, 11, 17, 23, 29, 35]
    (Sum.elim ![6, 7, 8, 9, 10, 16, 22, 28, 34]
      (Sum.elim ![12, 13, 14, 15, 21, 27, 33]
        (Sum.elim ![18, 19, 20, 26, 32] (Sum.elim ![24, 25, 31] ![30]))))
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
          · rcases i with i | i
            · fin_cases i <;> rfl
            · fin_cases i
              rfl

/-- **`Sym⁵ ⊗ Sym⁵ = Sym¹⁰ ⊕ Sym⁸ ⊕ Sym⁶ ⊕ Sym⁴ ⊕ Sym² ⊕ 1` at the weight
level**. -/
theorem quinticSquareWeight_decomposition (α : ℂ) :
    quinticSquareWeight α
      = (Sum.elim (sym10Q α)
          (Sum.elim (sym8Q α)
            (Sum.elim (sym6Q α)
              (Sum.elim (sym4Q α) (Sum.elim (sym2Q α) (sym0Q α))))))
          ∘ quinticSquareSplit := by
  funext i
  fin_cases i <;> rfl

/-- **The quintic-square bank law**:
`L(Sym⁵f × Sym⁵f) = L(Sym¹⁰f)·L(Sym⁸f)·L(Sym⁶f)·L(Sym⁴f)·L(Sym²f)·ζ`-shaped
factorization of coefficient banks at every `n` — the conditional pair's algebra,
hypothesis-free at this layer. -/
theorem quinticSquare_bank (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => quinticSquareWeight (H.satake p.2)))
      = coefficientArithmetic (radialGlobalSatakeCoeff
          (fun p => sym10Q (H.satake p.2)))
        * (coefficientArithmetic (radialGlobalSatakeCoeff
            (fun p => sym8Q (H.satake p.2)))
          * (coefficientArithmetic (radialGlobalSatakeCoeff
              (fun p => sym6Q (H.satake p.2)))
            * (coefficientArithmetic (radialGlobalSatakeCoeff
                (fun p => sym4Q (H.satake p.2)))
              * (coefficientArithmetic (radialGlobalSatakeCoeff
                  (fun p => sym2Q (H.satake p.2)))
                * coefficientArithmetic (radialGlobalSatakeCoeff
                    (fun p => sym0Q (H.satake p.2))))))) := by
  have hdec : (fun p : Nat.Primes => quinticSquareWeight (H.satake p.2))
      = fun p : Nat.Primes =>
          (Sum.elim (sym10Q (H.satake p.2))
            (Sum.elim (sym8Q (H.satake p.2))
              (Sum.elim (sym6Q (H.satake p.2))
                (Sum.elim (sym4Q (H.satake p.2))
                  (Sum.elim (sym2Q (H.satake p.2)) (sym0Q (H.satake p.2)))))))
            ∘ quinticSquareSplit := by
    funext p
    exact quinticSquareWeight_decomposition (H.satake p.2)
  rw [hdec, radialGlobalSatakeCoeff_equiv quinticSquareSplit,
    bankArithmetic_sumElim, bankArithmetic_sumElim, bankArithmetic_sumElim,
    bankArithmetic_sumElim, bankArithmetic_sumElim]

end CriticalLinePhasor.SexticCascade

#print axioms CriticalLinePhasor.SexticCascade.sexticTauWeight_decomposition
#print axioms CriticalLinePhasor.SexticCascade.sexticTau_bank
#print axioms CriticalLinePhasor.SexticCascade.quinticSquareWeight_decomposition
#print axioms CriticalLinePhasor.SexticCascade.quinticSquare_bank
