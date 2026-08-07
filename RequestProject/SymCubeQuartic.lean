import RequestProject.BaseChangeInduction

/-!
# The symmetric cube and quartic: tensor decompositions, Euler determinations, transport

Rungs 4–5 of the benchmark ladder, at the layer the closure calculus reaches exactly.
The two tensor laws, as finite weight-multiset identities over the compiled engine:

* `tensor23Weight` / `split23` / `tensor23_decomposition` / `tensor23_products` —
  **`std ⊗ Sym² = Sym³ ⊕ std`**: the six pairwise products of the standard and `Sym²`
  clocks are the `Sym³` clock together with the standard clock;
* `tensor33Weight` / `split33` / `tensor33_decomposition` / `tensor33_products` —
  **`Sym² ⊗ Sym² = Sym⁴ ⊕ Sym² ⊕ 1`**: the nine products split as `Sym⁴`, `Sym²`, and one
  trivial channel.

Assembled globally through the closure law and the rank-uniform clock-bank
identification:

* `bankArithmetic_symClock` — the generic identification at every rank;
* `tensor23_bank` — the tensor bank is `Sym³-bank ⋆ seed-bank`;
* `tensor33_bank` — the tensor-square bank is `Sym⁴-bank ⋆ Sym²-bank ⋆ ζ`.

The analytic reach, with no temperedness input:

* `satake_single_bound` / `symClock_norm_bound` / `symrSatakePair` — the `Sym^r` clock
  as a polynomial Satake pair at **every** rank, bounds from Hecke's estimate alone;
* `symrBank_LSeriesSummable` — every `Sym^r` bank is L-series-summable beyond its
  polynomial threshold `symrBound`;
* `sym3_euler_determination` / `sym4_euler_determination` — **the Euler determinations**:
  on the common half-plane, `L(std⊗Sym², s) = L(Sym³,s)·L(std,s)` and
  `L(Sym²⊗Sym², s) = L(Sym⁴,s)·L(Sym²,s)·ζ(s)` — the symmetric cube and quartic
  L-series are the cofactors of compiled objects in compiled tensor banks;
* `FE_transport` — division-free reflection transport: a self-dual factorization carries
  the functional equation to the cofactor in cross-multiplied form, so each rung's
  analytic wall is exactly one self-dual reflection for one explicitly presented tensor
  bank — the same typed slot the r = 2 rung's lattice route discharged.

No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups ArithmeticFunction.zeta LSeries.notation

namespace CriticalLinePhasor.SymCubeQuartic

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.TransportClosure
open CriticalLinePhasor.BaseChangeInduction CriticalLinePhasor.Sym2Wire
open CriticalLinePhasor.Sym2Rankin CriticalLinePhasor.SymrBank
open CriticalLinePhasor.CarrierTheta

variable {k : ℤ} {f : CuspForm 𝒮ℒ k}


/-- The `std ⊗ Sym²` weight system: the six pairwise products. -/
noncomputable def tensor23Weight (α : ℂ) : Fin 6 → ℂ :=
  ![α ^ (3 : ℤ), α ^ (1 : ℤ), α ^ (-1 : ℤ), α ^ (1 : ℤ), α ^ (-1 : ℤ), α ^ (-3 : ℤ)]

/-- The relabeling `Fin 6 ≃ Fin 4 ⊕ Fin 2` splitting `Sym³` from `std`. -/
def split23 : Fin 6 ≃ Fin 4 ⊕ Fin 2 where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1, Sum.inl 3]
  invFun := Sum.elim ![0, 1, 2, 5] ![3, 4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by
    intro i
    rcases i with i | i
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl

/-- **`std ⊗ Sym² = Sym³ ⊕ std` at the weight level**: the six products are the `Sym³`
clock together with the standard clock. -/
theorem tensor23_decomposition (α : ℂ) :
    tensor23Weight α
      = (Sum.elim (fun i : Fin 4 => symClockWeight 3 α (i : ℕ))
          (fun i : Fin 2 => symClockWeight 1 α (i : ℕ))) ∘ split23 := by
  funext i
  fin_cases i <;>
    simp only [tensor23Weight, split23, Function.comp_apply, Equiv.coe_fn_mk] <;>
    norm_num [symClockWeight]

/-- The six entries are the pairwise products of the `std` clock `(α, α⁻¹)` with the
`Sym²` clock `(α², 1, α⁻²)`. -/
theorem tensor23_products (α : ℂ) (hα : α ≠ 0) :
    tensor23Weight α 0 = symClockWeight 1 α 0 * symClockWeight 2 α 0 ∧
    tensor23Weight α 1 = symClockWeight 1 α 0 * symClockWeight 2 α 1 ∧
    tensor23Weight α 2 = symClockWeight 1 α 0 * symClockWeight 2 α 2 ∧
    tensor23Weight α 3 = symClockWeight 1 α 1 * symClockWeight 2 α 0 ∧
    tensor23Weight α 4 = symClockWeight 1 α 1 * symClockWeight 2 α 1 ∧
    tensor23Weight α 5 = symClockWeight 1 α 1 * symClockWeight 2 α 2 := by
  have h0 : symClockWeight 1 α 0 = α ^ (1 : ℤ) := by unfold symClockWeight; norm_num
  have h1 : symClockWeight 1 α 1 = α ^ (-1 : ℤ) := by unfold symClockWeight; norm_num
  have g0 : symClockWeight 2 α 0 = α ^ (2 : ℤ) := by unfold symClockWeight; norm_num
  have g1 : symClockWeight 2 α 1 = 1 := by unfold symClockWeight; norm_num
  have g2 : symClockWeight 2 α 2 = α ^ (-2 : ℤ) := by unfold symClockWeight; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    set_option linter.unusedSimpArgs false in
    simp [tensor23Weight, h0, h1, g0, g1, g2, ← zpow_add₀ hα] <;>
    field_simp


/-- The `Sym² ⊗ Sym²` weight system: the nine pairwise products. -/
noncomputable def tensor33Weight (α : ℂ) : Fin 9 → ℂ :=
  ![α ^ (4 : ℤ), α ^ (2 : ℤ), 1, α ^ (2 : ℤ), 1, α ^ (-2 : ℤ), 1, α ^ (-2 : ℤ), α ^ (-4 : ℤ)]

/-- The relabeling `Fin 9 ≃ (Fin 5 ⊕ Fin 3) ⊕ Fin 1`. -/
def split33 : Fin 9 ≃ (Fin 5 ⊕ Fin 3) ⊕ Fin 1 where
  toFun := ![Sum.inl (Sum.inl 0), Sum.inl (Sum.inl 1), Sum.inl (Sum.inl 2),
    Sum.inl (Sum.inr 0), Sum.inl (Sum.inr 1), Sum.inl (Sum.inl 3),
    Sum.inr 0, Sum.inl (Sum.inr 2), Sum.inl (Sum.inl 4)]
  invFun := Sum.elim (Sum.elim ![0, 1, 2, 5, 8] ![3, 4, 7]) ![6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by
    intro i
    rcases i with (i | i) | i
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
    · fin_cases i
      rfl

/-- **`Sym² ⊗ Sym² = Sym⁴ ⊕ Sym² ⊕ 1` at the weight level**. -/
theorem tensor33_decomposition (α : ℂ) :
    tensor33Weight α
      = (Sum.elim (Sum.elim (fun i : Fin 5 => symClockWeight 4 α (i : ℕ))
          (fun i : Fin 3 => symClockWeight 2 α (i : ℕ)))
          (fun _ : Fin 1 => (1 : ℂ))) ∘ split33 := by
  funext i
  fin_cases i <;>
    simp only [tensor33Weight, split33, Function.comp_apply, Equiv.coe_fn_mk] <;>
    norm_num [symClockWeight]

/-- The nine entries are the pairwise products of two `Sym²` clocks. -/
theorem tensor33_products (α : ℂ) (hα : α ≠ 0) :
    ∀ i : Fin 3, ∀ j : Fin 3,
      tensor33Weight α ⟨3 * (i : ℕ) + (j : ℕ), by omega⟩
        = symClockWeight 2 α (i : ℕ) * symClockWeight 2 α (j : ℕ) := by
  have g0 : symClockWeight 2 α 0 = α ^ (2 : ℤ) := by unfold symClockWeight; norm_num
  have g1 : symClockWeight 2 α 1 = 1 := by unfold symClockWeight; norm_num
  have g2 : symClockWeight 2 α 2 = α ^ (-2 : ℤ) := by unfold symClockWeight; norm_num
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [tensor33Weight, g0, g1, g2, ← zpow_add₀ hα] <;>
    field_simp



/-- The generic clock-bank identification at every rank. -/
theorem bankArithmetic_symClock (H : HeckeEigenData f) (r : ℕ) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => fun i : Fin (r + 1) => symClockWeight r (H.satake p.2) (i : ℕ)))
      = symrBank H r := by
  ext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [coefficientArithmetic]
  · show (if m = 0 then 0 else _) = _
    rw [if_neg hm.ne']
    rw [show radialGlobalSatakeCoeff
        (fun p => fun i : Fin (r + 1) => symClockWeight r (H.satake p.2) (i : ℕ)) (m - 1)
        = symrBank H r (m - 1 + 1) from
      CriticalLinePhasor.Sym2Join.radialGlobal_eq_symrBank H r (m - 1),
      Nat.sub_add_cancel hm]

/-- **`std ⊗ Sym² = Sym³ ⊕ std` at the bank level**: the tensor bank is the convolution
of the `Sym³` bank with the seed bank. -/
theorem tensor23_bank (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => tensor23Weight (H.satake p.2)))
      = symrBank H 3 * symrBank H 1 := by
  have hdec : (fun p : Nat.Primes => tensor23Weight (H.satake p.2))
      = fun p : Nat.Primes =>
          (Sum.elim (fun i : Fin 4 => symClockWeight 3 (H.satake p.2) (i : ℕ))
            (fun i : Fin 2 => symClockWeight 1 (H.satake p.2) (i : ℕ))) ∘ split23 := by
    funext p
    exact tensor23_decomposition (H.satake p.2)
  rw [hdec, radialGlobalSatakeCoeff_equiv split23, bankArithmetic_sumElim,
    bankArithmetic_symClock H 3, bankArithmetic_symClock H 1]

/-- **`Sym² ⊗ Sym² = Sym⁴ ⊕ Sym² ⊕ 1` at the bank level**: the tensor-square bank is
`ζ ⋆ Sym²-bank ⋆ Sym⁴-bank`. -/
theorem tensor33_bank (H : HeckeEigenData f) :
    coefficientArithmetic (radialGlobalSatakeCoeff
      (fun p => tensor33Weight (H.satake p.2)))
      = (symrBank H 4 * symrBank H 2) *
          ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
  have hdec : (fun p : Nat.Primes => tensor33Weight (H.satake p.2))
      = fun p : Nat.Primes =>
          (Sum.elim (Sum.elim (fun i : Fin 5 => symClockWeight 4 (H.satake p.2) (i : ℕ))
            (fun i : Fin 3 => symClockWeight 2 (H.satake p.2) (i : ℕ)))
            (fun _ : Fin 1 => (1 : ℂ))) ∘ split33 := by
    funext p
    exact tensor33_decomposition (H.satake p.2)
  rw [hdec, radialGlobalSatakeCoeff_equiv split33, bankArithmetic_sumElim,
    bankArithmetic_sumElim, bankArithmetic_symClock H 4, bankArithmetic_symClock H 2,
    bankArithmetic_unit_eq_zeta]



/-- The Satake norm bound in single-power form: `‖α_p‖ ≤ p^{E+1}` and same for the
inverse — from the compiled square bound. -/
theorem satake_single_bound (H : HeckeEigenData f) :
    ∃ E : ℕ, ∀ (p : Nat.Primes),
      ‖H.satake p.2‖ ≤ (p.1 : ℝ) ^ E ∧ ‖(H.satake p.2)⁻¹‖ ≤ (p.1 : ℝ) ^ E := by
  obtain ⟨E, hE⟩ := satake_uniform_bound H
  refine ⟨E + 1, fun p => ?_⟩
  have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
  obtain ⟨h1, h2⟩ := hE p
  have hstep : ∀ y : ℝ, 0 ≤ y → y ^ 2 ≤ (p.1 : ℝ) ^ E → y ≤ (p.1 : ℝ) ^ (E + 1) := by
    intro y hy hsq
    rcases le_total y 1 with h | h
    · exact le_trans h (one_le_pow₀ hp1)
    · calc y ≤ y ^ 2 := by nlinarith
        _ ≤ (p.1 : ℝ) ^ E := hsq
        _ ≤ (p.1 : ℝ) ^ (E + 1) := pow_le_pow_right₀ hp1 (Nat.le_succ E)
  exact ⟨hstep _ (norm_nonneg _) h1, hstep _ (norm_nonneg _) h2⟩

/-- The clock-weight norm bound at every channel: `‖α^{r−2i}‖ ≤ p^{E·r}`. -/
theorem symClock_norm_bound (H : HeckeEigenData f) (E : ℕ)
    (hE : ∀ (p : Nat.Primes),
      ‖H.satake p.2‖ ≤ (p.1 : ℝ) ^ E ∧ ‖(H.satake p.2)⁻¹‖ ≤ (p.1 : ℝ) ^ E)
    (r : ℕ) (p : Nat.Primes) (i : Fin (r + 1)) :
    ‖symClockWeight r (H.satake p.2) (i : ℕ)‖ ≤ (p.1 : ℝ) ^ (E * r) := by
  have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
  obtain ⟨h1, h2⟩ := hE p
  unfold symClockWeight
  set m : ℤ := (r : ℤ) - 2 * ((i : ℕ) : ℤ) with hmdef
  have hm : m.natAbs ≤ r := by
    have := i.2
    omega
  have hcalc : ∀ y : ℝ, 0 ≤ y → y ≤ (p.1 : ℝ) ^ E →
      y ^ m.natAbs ≤ (p.1 : ℝ) ^ (E * r) := by
    intro y hy hyE
    calc y ^ m.natAbs ≤ ((p.1 : ℝ) ^ E) ^ m.natAbs :=
          pow_le_pow_left₀ hy hyE _
      _ = (p.1 : ℝ) ^ (E * m.natAbs) := by rw [← pow_mul]
      _ ≤ (p.1 : ℝ) ^ (E * r) :=
          pow_le_pow_right₀ hp1 (Nat.mul_le_mul_left E hm)
  rcases Int.lt_or_le m 0 with hm0 | hm0
  · have hzp : (H.satake p.2) ^ m = ((H.satake p.2)⁻¹) ^ m.natAbs := by
      conv_lhs => rw [show m = -(m.natAbs : ℤ) from by omega]
      rw [zpow_neg, ← inv_zpow, zpow_natCast]
    rw [hzp, norm_pow]
    exact hcalc _ (norm_nonneg _) h2
  · have hzp : (H.satake p.2) ^ m = (H.satake p.2) ^ m.natAbs := by
      conv_lhs => rw [← Int.natAbs_of_nonneg hm0]
      rw [zpow_natCast]
    rw [hzp, norm_pow]
    exact hcalc _ (norm_nonneg _) h1

/-- The general clock pair: `Sym^r` weights with polynomial bounds at every rank. -/
noncomputable def symrSatakePair (H : HeckeEigenData f) (r : ℕ) :
    PolynomialSatakeDualPair (Fin (r + 1)) where
  primal := fun p i => symClockWeight r (H.satake p.2) (i : ℕ)
  dual := fun p i => (symClockWeight r (H.satake p.2) (i : ℕ))⁻¹
  primalExponent := ((satake_single_bound H).choose) * r
  dualExponent := ((satake_single_bound H).choose) * r
  primal_ne_zero := fun p _ => zpow_ne_zero _ (H.satake_ne_zero p.2)
  dual_eq_inv := fun _ _ => rfl
  primal_bound := fun p i =>
    symClock_norm_bound H _ (satake_single_bound H).choose_spec r p i
  dual_bound := by
    intro p i
    have hinv : (symClockWeight r (H.satake p.2) (i : ℕ))⁻¹
        = symClockWeight r ((H.satake p.2)⁻¹) (i : ℕ) := by
      unfold symClockWeight
      rw [← inv_zpow]
    rw [hinv]
    have hE := (satake_single_bound H).choose_spec
    have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.one_lt.le
    obtain ⟨h1, h2⟩ := hE p
    unfold symClockWeight
    set m : ℤ := (r : ℤ) - 2 * ((i : ℕ) : ℤ) with hmdef
    have hm : m.natAbs ≤ r := by
      have := i.2
      omega
    have hcalc : ∀ y : ℝ, 0 ≤ y → y ≤ (p.1 : ℝ) ^ (satake_single_bound H).choose →
        y ^ m.natAbs ≤ (p.1 : ℝ) ^ ((satake_single_bound H).choose * r) := by
      intro y hy hyE
      calc y ^ m.natAbs ≤ ((p.1 : ℝ) ^ (satake_single_bound H).choose) ^ m.natAbs :=
            pow_le_pow_left₀ hy hyE _
        _ = (p.1 : ℝ) ^ ((satake_single_bound H).choose * m.natAbs) := by rw [← pow_mul]
        _ ≤ (p.1 : ℝ) ^ ((satake_single_bound H).choose * r) :=
            pow_le_pow_right₀ hp1 (Nat.mul_le_mul_left _ hm)
    rcases Int.lt_or_le m 0 with hm0 | hm0
    · have hzp : ((H.satake p.2)⁻¹) ^ m = (H.satake p.2) ^ m.natAbs := by
        conv_lhs => rw [show m = -(m.natAbs : ℤ) from by omega]
        rw [zpow_neg, ← inv_zpow, zpow_natCast, inv_inv]
      rw [hzp, norm_pow]
      exact hcalc _ (norm_nonneg _) h1
    · have hzp : ((H.satake p.2)⁻¹) ^ m = ((H.satake p.2)⁻¹) ^ m.natAbs := by
        conv_lhs => rw [← Int.natAbs_of_nonneg hm0]
        rw [zpow_natCast]
      rw [hzp, norm_pow]
      exact hcalc _ (norm_nonneg _) h2




/-- The summability threshold of the rank-`r` bank. -/
noncomputable def symrBound (H : HeckeEigenData f) (r : ℕ) : ℕ :=
  (r + 1) + (satake_single_bound H).choose * r

/-- **The `Sym^r` bank is L-series-summable** beyond its polynomial threshold, at every
rank — no temperedness input. -/
theorem symrBank_LSeriesSummable (H : HeckeEigenData f) (r : ℕ) {s : ℂ}
    (hs : ((symrBound H r : ℕ) : ℝ) + 1 < s.re) :
    LSeriesSummable (⇑(symrBank H r)) s := by
  refine LSeriesSummable_of_le_const_mul_rpow hs ⟨1, fun n hn => ?_⟩
  have hb := cpsPolynomialPrimalArithmetic_norm_le (symrSatakePair H r) n
  have hid : (coefficientArithmetic (cpsPolynomialPrimalCoeff (symrSatakePair H r))) n
      = symrBank H r n := by
    rw [show cpsPolynomialPrimalCoeff (symrSatakePair H r)
        = radialGlobalSatakeCoeff (fun p => fun i : Fin (r + 1) =>
            symClockWeight r (H.satake p.2) (i : ℕ)) from rfl,
      bankArithmetic_symClock H r]
  rw [hid] at hb
  calc ‖symrBank H r n‖ ≤ (1 : ℝ) * (n : ℝ) ^ ((Fintype.card (Fin (r + 1))
        + (symrSatakePair H r).primalExponent : ℕ)) := hb
    _ ≤ 1 * (n : ℝ) ^ ((((symrBound H r : ℕ) : ℝ) + 1) - 1) := by
      rw [one_mul, one_mul]
      have hcard : (Fintype.card (Fin (r + 1)) + (symrSatakePair H r).primalExponent : ℕ)
          = symrBound H r := by
        simp [symrBound, symrSatakePair]
      rw [hcard, add_sub_cancel_right, ← Real.rpow_natCast ((n : ℝ)) (symrBound H r)]
  
/-- **Rung 4, Euler determination**: the `std⊗Sym²` tensor bank's L-series factors as
`L(Sym³)·L(std)` on the common half-plane — `Sym³` is the cofactor of the seed in the
compiled tensor object. -/
theorem sym3_euler_determination (H : HeckeEigenData f) {s : ℂ}
    (hs3 : ((symrBound H 3 : ℕ) : ℝ) + 1 < s.re)
    (hs1 : ((symrBound H 1 : ℕ) : ℝ) + 1 < s.re) :
    LSeries (⇑(coefficientArithmetic (radialGlobalSatakeCoeff
        (fun p => tensor23Weight (H.satake p.2))))) s
      = LSeries (⇑(symrBank H 3)) s * LSeries (⇑(symrBank H 1)) s := by
  rw [tensor23_bank H]
  exact ArithmeticFunction.LSeries_mul' (symrBank_LSeriesSummable H 3 hs3)
    (symrBank_LSeriesSummable H 1 hs1)

/-- **Rung 5, Euler determination**: the `Sym²⊗Sym²` tensor bank's L-series factors as
`ζ(s)·L(Sym²)·L(Sym⁴)` — `Sym⁴` is the cofactor of `ζ·Sym²` in the compiled
tensor-square. -/
theorem sym4_euler_determination (H : HeckeEigenData f) {s : ℂ}
    (hs4 : ((symrBound H 4 : ℕ) : ℝ) + 1 < s.re)
    (hs2 : ((symrBound H 2 : ℕ) : ℝ) + 1 < s.re) (hs1 : 1 < s.re) :
    LSeries (⇑(coefficientArithmetic (radialGlobalSatakeCoeff
        (fun p => tensor33Weight (H.satake p.2))))) s
      = (LSeries (⇑(symrBank H 4)) s * LSeries (⇑(symrBank H 2)) s) * riemannZeta s := by
  rw [tensor33_bank H]
  have hζ : LSeriesSummable (⇑((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) s := by
    have hcoe : (⇑((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗ζ := by
      funext n; simp
    rw [hcoe]
    exact LSeriesSummable_zeta_iff.mpr hs1
  have hζval : LSeries (⇑((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) s
      = riemannZeta s := by
    have hcoe : (⇑((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗ζ := by
      funext n; simp
    rw [hcoe]
    exact LSeries_zeta_eq_riemannZeta hs1
  rw [ArithmeticFunction.LSeries_mul'
    (ArithmeticFunction.LSeriesSummable_mul (symrBank_LSeriesSummable H 4 hs4)
      (symrBank_LSeriesSummable H 2 hs2)) hζ,
    ArithmeticFunction.LSeries_mul' (symrBank_LSeriesSummable H 4 hs4)
      (symrBank_LSeriesSummable H 2 hs2), hζval]

/-- **Division-free functional-equation transport**: a self-dual completed factorization
transports the reflection to the cofactor in cross-multiplied form. -/
theorem FE_transport {T Z Q : ℂ → ℂ} (hfac : ∀ s, T s = Z s * Q s)
    (hT : ∀ s : ℂ, T (1 - s) = T s) (s : ℂ) :
    Z (1 - s) * Q (1 - s) = Z s * Q s := by
  rw [← hfac, ← hfac]
  exact hT s

end CriticalLinePhasor.SymCubeQuartic

#print axioms CriticalLinePhasor.SymCubeQuartic.tensor23_decomposition
#print axioms CriticalLinePhasor.SymCubeQuartic.tensor23_products
#print axioms CriticalLinePhasor.SymCubeQuartic.tensor33_decomposition
#print axioms CriticalLinePhasor.SymCubeQuartic.tensor33_products
#print axioms CriticalLinePhasor.SymCubeQuartic.bankArithmetic_symClock
#print axioms CriticalLinePhasor.SymCubeQuartic.tensor23_bank
#print axioms CriticalLinePhasor.SymCubeQuartic.tensor33_bank
#print axioms CriticalLinePhasor.SymCubeQuartic.satake_single_bound
#print axioms CriticalLinePhasor.SymCubeQuartic.symClock_norm_bound
#print axioms CriticalLinePhasor.SymCubeQuartic.symrSatakePair
#print axioms CriticalLinePhasor.SymCubeQuartic.symrBank_LSeriesSummable
#print axioms CriticalLinePhasor.SymCubeQuartic.sym3_euler_determination
#print axioms CriticalLinePhasor.SymCubeQuartic.sym4_euler_determination
#print axioms CriticalLinePhasor.SymCubeQuartic.FE_transport
