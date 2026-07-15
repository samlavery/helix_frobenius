import RequestProject.FiniteWeightFiber

/-!
# Clebsch--Gordan splitting of the symmetric-power clock bank

The primary datum is the finite clock bank.  The tensor of the two clocks of `Sym^1` with the
`r` clocks of `Sym^(r-1)` consists of the upper string `r, r-2, ..., -r+2` and the lower string
`r-2, r-4, ..., -r`.  Their overlap is exactly `Sym^(r-2)`, while their two endpoints complete
`Sym^r`.  This file proves the resulting local-polynomial factorization directly as a finite-product
identity.
-/

open Complex Finset
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

/-- The `k`th symmetric-power clock weight `α^(r-2k)`. -/
noncomputable def symClockWeight (r : ℕ) (α : ℂ) (k : ℕ) : ℂ :=
  α ^ ((r : ℤ) - 2 * (k : ℤ))

/-- The local numerator read from the complete `Sym^r` clock string. -/
noncomputable def symClockLocalPoly (r : ℕ) (α X : ℂ) : ℂ :=
  ∏ k ∈ Finset.range (r + 1), (1 - symClockWeight r α k * X)

/-- The tensor-step bank: the upper `Sym^1` lane and lower `Sym^1` lane applied to
`Sym^(r-1)`, written in their resulting `Sym^r` clock coordinates. -/
noncomputable def tensorStepLocalPoly (r : ℕ) (α X : ℂ) : ℂ :=
  (∏ k ∈ Finset.range r, (1 - symClockWeight r α k * X)) *
    ∏ k ∈ Finset.range r, (1 - symClockWeight r α (k + 1) * X)

private theorem shiftedInterior_eq_lowerSym
    {r : ℕ} (hr : 2 ≤ r) (α X : ℂ) :
    (∏ k ∈ Finset.range (r - 1), (1 - symClockWeight r α (k + 1) * X)) =
      symClockLocalPoly (r - 2) α X := by
  unfold symClockLocalPoly
  have hlen : r - 2 + 1 = r - 1 := by omega
  rw [hlen]
  apply Finset.prod_congr rfl
  intro k hk
  unfold symClockWeight
  congr 3
  omega

private theorem upperString_append_endpoint
    {r : ℕ} (hr : 1 ≤ r) (α X : ℂ) :
    symClockLocalPoly r α X =
      (∏ k ∈ Finset.range r, (1 - symClockWeight r α k * X)) *
        (1 - symClockWeight r α r * X) := by
  unfold symClockLocalPoly
  simpa [Nat.add_comm] using
    (Finset.prod_range_succ (fun k => 1 - symClockWeight r α k * X) r)

private theorem shiftedString_append_endpoint
    {r : ℕ} (hr : 1 ≤ r) (α X : ℂ) :
    (∏ k ∈ Finset.range r, (1 - symClockWeight r α (k + 1) * X)) =
      (∏ k ∈ Finset.range (r - 1), (1 - symClockWeight r α (k + 1) * X)) *
        (1 - symClockWeight r α r * X) := by
  have hrange : r - 1 + 1 = r := by omega
  calc
    (∏ k ∈ Finset.range r, (1 - symClockWeight r α (k + 1) * X)) =
        ∏ k ∈ Finset.range (r - 1 + 1),
          (1 - symClockWeight r α (k + 1) * X) := by rw [hrange]
    _ = (∏ k ∈ Finset.range (r - 1),
          (1 - symClockWeight r α (k + 1) * X)) *
          (1 - symClockWeight r α ((r - 1) + 1) * X) := by
        rw [Finset.prod_range_succ]
    _ = (∏ k ∈ Finset.range (r - 1),
          (1 - symClockWeight r α (k + 1) * X)) *
          (1 - symClockWeight r α r * X) := by rw [hrange]

/-- Exact finite-bank Clebsch--Gordan factorization:
`Sym^1 ⊗ Sym^(r-1) = Sym^r ⊕ Sym^(r-2)` at the local numerator. -/
theorem tensorStepLocalPoly_eq_sym_mul_lower
    {r : ℕ} (hr : 2 ≤ r) (α X : ℂ) :
    tensorStepLocalPoly r α X =
      symClockLocalPoly r α X * symClockLocalPoly (r - 2) α X := by
  rw [tensorStepLocalPoly,
    shiftedString_append_endpoint (show 1 ≤ r by omega),
    shiftedInterior_eq_lowerSym hr,
    upperString_append_endpoint (show 1 ≤ r by omega)]
  ring

/-- The explicit clock weight agrees with the weight stored in `symFiber`. -/
theorem symClockWeight_eq_symFiber_weight
    (r : ℕ) (α : ℂ) (hα : ‖α‖ = 1) (k : Fin (r + 1)) :
    symClockWeight r α k = (FiniteWeightFiber.symFiber r α hα).weight k := by
  rfl

/-- Consequently the explicit local polynomial is the `FiniteWeightFiber` local polynomial. -/
theorem symClockLocalPoly_eq_symFiber_localPoly
    (r : ℕ) (α : ℂ) (hα : ‖α‖ = 1) (X : ℂ) :
    symClockLocalPoly r α X = (FiniteWeightFiber.symFiber r α hα).localPoly X := by
  unfold symClockLocalPoly FiniteWeightFiber.localPoly
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro k hk
  have hk' : k < r + 1 := Finset.mem_range.mp hk
  simp only [hk', dif_pos]
  rw [symClockWeight_eq_symFiber_weight r α hα ⟨k, hk'⟩]

/-- The upper tensor lane has the first `r` weights of `Sym^r`. -/
theorem tensorSym_upper_weight
    {r : ℕ} (hr : 1 ≤ r) (α : ℂ) (hα : ‖α‖ = 1)
    (k : Fin ((r - 1) + 1)) :
    (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.symFiber 1 α hα)
        (FiniteWeightFiber.symFiber (r - 1) α hα)).weight (0, k) =
      symClockWeight r α k := by
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hα
    exact zero_ne_one hα
  change α ^ (1 : ℤ) * α ^ (((r - 1 : ℕ) : ℤ) - 2 * (k.val : ℤ)) =
    α ^ ((r : ℤ) - 2 * (k.val : ℤ))
  rw [← zpow_add₀ hα0]
  congr 1
  omega

/-- The lower tensor lane has the last `r` weights of `Sym^r`. -/
theorem tensorSym_lower_weight
    {r : ℕ} (hr : 1 ≤ r) (α : ℂ) (hα : ‖α‖ = 1)
    (k : Fin ((r - 1) + 1)) :
    (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.symFiber 1 α hα)
        (FiniteWeightFiber.symFiber (r - 1) α hα)).weight (1, k) =
      symClockWeight r α (k + 1) := by
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hα
    exact zero_ne_one hα
  change α ^ (-1 : ℤ) * α ^ (((r - 1 : ℕ) : ℤ) - 2 * (k.val : ℤ)) =
    α ^ ((r : ℤ) - 2 * ((k.val + 1 : ℕ) : ℤ))
  rw [← zpow_add₀ hα0]
  congr 1
  omega

/-- The explicit tensor-step numerator is exactly the local polynomial of the actual tensor fiber. -/
theorem tensorStepLocalPoly_eq_tensorFiber_localPoly
    {r : ℕ} (hr : 1 ≤ r) (α : ℂ) (hα : ‖α‖ = 1) (X : ℂ) :
    tensorStepLocalPoly r α X =
      (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.symFiber 1 α hα)
        (FiniteWeightFiber.symFiber (r - 1) α hα)).localPoly X := by
  have hrange : r - 1 + 1 = r := by omega
  unfold tensorStepLocalPoly FiniteWeightFiber.localPoly
  rw [Fintype.prod_prod_type, Fin.prod_univ_two]
  congr 1
  · rw [Finset.prod_fin_eq_prod_range]
    simp only [hrange]
    apply Finset.prod_congr rfl
    intro k hk
    have hk' : k < r := Finset.mem_range.mp hk
    simp only [hrange, hk', dif_pos]
    rw [tensorSym_upper_weight hr α hα ⟨k, by omega⟩]
  · rw [Finset.prod_fin_eq_prod_range]
    simp only [hrange]
    apply Finset.prod_congr rfl
    intro k hk
    have hk' : k < r := Finset.mem_range.mp hk
    simp only [hrange, hk', dif_pos]
    rw [tensorSym_lower_weight hr α hα ⟨k, by omega⟩]

/-- Clebsch--Gordan factorization stated entirely in the repository's `FiniteWeightFiber` API. -/
theorem tensorSym_localPoly_eq_sym_mul_lower
    {r : ℕ} (hr : 2 ≤ r) (α : ℂ) (hα : ‖α‖ = 1) (X : ℂ) :
    (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.symFiber 1 α hα)
        (FiniteWeightFiber.symFiber (r - 1) α hα)).localPoly X =
      (FiniteWeightFiber.symFiber r α hα).localPoly X *
        (FiniteWeightFiber.symFiber (r - 2) α hα).localPoly X := by
  rw [← tensorStepLocalPoly_eq_tensorFiber_localPoly (show 1 ≤ r by omega) α hα X,
    tensorStepLocalPoly_eq_sym_mul_lower hr,
    symClockLocalPoly_eq_symFiber_localPoly r α hα X,
    symClockLocalPoly_eq_symFiber_localPoly (r - 2) α hα X]

/-- The local polynomial of a tensor fiber is the product, over right-hand clocks, of the left
fiber polynomial at the correspondingly scaled variable. -/
theorem tensorFiber_localPoly_eq_prod_right
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W₁ : FiniteWeightFiber ι) (W₂ : FiniteWeightFiber κ) (X : ℂ) :
    (FiniteWeightFiber.tensorFiber W₁ W₂).localPoly X =
      ∏ j, W₁.localPoly (W₂.weight j * X) := by
  unfold FiniteWeightFiber.localPoly FiniteWeightFiber.tensorFiber
  rw [Fintype.prod_prod_type]
  calc
    (∏ i, ∏ j, (1 - (W₁.weight i * W₂.weight j) * X)) =
        ∏ j, ∏ i, (1 - (W₁.weight i * W₂.weight j) * X) := by
      rw [Finset.prod_comm]
    _ = ∏ j, ∏ i, (1 - W₁.weight i * (W₂.weight j * X)) := by
      apply Finset.prod_congr rfl
      intro j _
      apply Finset.prod_congr rfl
      intro i _
      ring

/-- The Clebsch--Gordan split survives tensoring with every finite duality-stable twist fiber. -/
theorem tensorSymTwist_localPoly_eq_mul
    {κ : Type*} [Fintype κ] {r : ℕ} (hr : 2 ≤ r)
    (α : ℂ) (hα : ‖α‖ = 1) (Wτ : FiniteWeightFiber κ) (X : ℂ) :
    (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber 1 α hα)
          (FiniteWeightFiber.symFiber (r - 1) α hα)) Wτ).localPoly X =
      (FiniteWeightFiber.tensorFiber (FiniteWeightFiber.symFiber r α hα) Wτ).localPoly X *
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber (r - 2) α hα) Wτ).localPoly X := by
  rw [tensorFiber_localPoly_eq_prod_right,
    tensorFiber_localPoly_eq_prod_right,
    tensorFiber_localPoly_eq_prod_right]
  calc
    (∏ j, (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.symFiber 1 α hα)
        (FiniteWeightFiber.symFiber (r - 1) α hα)).localPoly (Wτ.weight j * X)) =
        ∏ j, ((FiniteWeightFiber.symFiber r α hα).localPoly (Wτ.weight j * X) *
          (FiniteWeightFiber.symFiber (r - 2) α hα).localPoly (Wτ.weight j * X)) := by
      apply Finset.prod_congr rfl
      intro j _
      exact tensorSym_localPoly_eq_sym_mul_lower hr α hα (Wτ.weight j * X)
    _ = (∏ j, (FiniteWeightFiber.symFiber r α hα).localPoly (Wτ.weight j * X)) *
        ∏ j, (FiniteWeightFiber.symFiber (r - 2) α hα).localPoly (Wτ.weight j * X) := by
      rw [Finset.prod_mul_distrib]

/-- The same twisted Clebsch--Gordan identity for local Euler factors. -/
theorem tensorSymTwist_localFactor_eq_mul
    {κ : Type*} [Fintype κ] {r : ℕ} (hr : 2 ≤ r)
    (α : ℂ) (hα : ‖α‖ = 1) (Wτ : FiniteWeightFiber κ) (q : ℝ) (s : ℂ) :
    (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber 1 α hα)
          (FiniteWeightFiber.symFiber (r - 1) α hα)) Wτ).localFactor q s =
      (FiniteWeightFiber.tensorFiber (FiniteWeightFiber.symFiber r α hα) Wτ).localFactor q s *
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber (r - 2) α hα) Wτ).localFactor q s := by
  unfold FiniteWeightFiber.localFactor
  rw [tensorSymTwist_localPoly_eq_mul hr α hα Wτ, mul_inv]

/-- Exact Clebsch--Gordan factorization of every finite global Euler approximant, with independently
varying local Satake clocks and twist fibers at the places in `S`. -/
theorem finiteTensorSymTwistEulerProduct_eq_mul
    {V κ : Type*} [Fintype κ] [DecidableEq V]
    (S : Finset V) {r : ℕ} (hr : 2 ≤ r)
    (α : V → ℂ) (hα : ∀ v, ‖α v‖ = 1)
    (Wτ : V → FiniteWeightFiber κ) (q : V → ℝ) (s : ℂ) :
    (∏ v ∈ S,
      (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber 1 (α v) (hα v))
          (FiniteWeightFiber.symFiber (r - 1) (α v) (hα v))) (Wτ v)).localFactor (q v) s) =
      (∏ v ∈ S,
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber r (α v) (hα v)) (Wτ v)).localFactor (q v) s) *
      ∏ v ∈ S,
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber (r - 2) (α v) (hα v)) (Wτ v)).localFactor (q v) s := by
  simp_rw [tensorSymTwist_localFactor_eq_mul hr]
  rw [Finset.prod_mul_distrib]

/-- The same finite-place identity as a quotient when the lower symmetric-power approximant is
nonzero.  This is the exact initial-half-plane induction formula used to isolate the top block. -/
theorem finiteSymTwistEulerProduct_eq_div_tensorStep
    {V κ : Type*} [Fintype κ] [DecidableEq V]
    (S : Finset V) {r : ℕ} (hr : 2 ≤ r)
    (α : V → ℂ) (hα : ∀ v, ‖α v‖ = 1)
    (Wτ : V → FiniteWeightFiber κ) (q : V → ℝ) (s : ℂ)
    (hlower : (∏ v ∈ S,
      (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.symFiber (r - 2) (α v) (hα v)) (Wτ v)).localFactor (q v) s) ≠ 0) :
    (∏ v ∈ S,
      (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.symFiber r (α v) (hα v)) (Wτ v)).localFactor (q v) s) =
      (∏ v ∈ S,
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.tensorFiber
            (FiniteWeightFiber.symFiber 1 (α v) (hα v))
            (FiniteWeightFiber.symFiber (r - 1) (α v) (hα v))) (Wτ v)).localFactor (q v) s) /
      ∏ v ∈ S,
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber (r - 2) (α v) (hα v)) (Wτ v)).localFactor (q v) s := by
  have hfac := finiteTensorSymTwistEulerProduct_eq_mul S hr α hα Wτ q s
  apply (eq_div_iff hlower).2
  exact hfac.symm

/-- A unit-clock local numerator is nonzero in the absolute half-plane `q > 1`, `Re(s) > 0`. -/
theorem localPoly_cpow_ne_zero
    {ι : Type*} [Fintype ι] (W : FiniteWeightFiber ι)
    {q : ℝ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    W.localPoly ((q : ℂ) ^ (-s)) ≠ 0 := by
  unfold FiniteWeightFiber.localPoly
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply sub_ne_zero.mpr
  intro heq
  have hnormPow : ‖(q : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < q)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by simp; linarith)
  have hnorm : ‖W.weight i * (q : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, W.unit i, one_mul]
    exact hnormPow
  rw [← heq, norm_one] at hnorm
  exact lt_irrefl 1 hnorm

/-- Hence every local Euler factor is nonzero in that half-plane. -/
theorem localFactor_ne_zero
    {ι : Type*} [Fintype ι] (W : FiniteWeightFiber ι)
    {q : ℝ} (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    W.localFactor q s ≠ 0 := by
  unfold FiniteWeightFiber.localFactor
  exact inv_ne_zero (localPoly_cpow_ne_zero W hq hs)

/-- Every finite Euler approximant of unit-clock fibers is nonzero in the same half-plane. -/
theorem finiteEulerProduct_ne_zero
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι)
    (q : V → ℝ) (hq : ∀ v ∈ S, 1 < q v) {s : ℂ} (hs : 0 < s.re) :
    (∏ v ∈ S, (W v).localFactor (q v) s) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  exact localFactor_ne_zero (W v) (hq v hv) hs

/-- Quotient isolation of the top symmetric-power twist with nonvanishing discharged from the
unit clock ledger and the absolute-half-plane inequalities. -/
theorem finiteSymTwistEulerProduct_eq_div_tensorStep_of_halfPlane
    {V κ : Type*} [Fintype κ] [DecidableEq V]
    (S : Finset V) {r : ℕ} (hr : 2 ≤ r)
    (α : V → ℂ) (hα : ∀ v, ‖α v‖ = 1)
    (Wτ : V → FiniteWeightFiber κ) (q : V → ℝ)
    (hq : ∀ v ∈ S, 1 < q v) {s : ℂ} (hs : 0 < s.re) :
    (∏ v ∈ S,
      (FiniteWeightFiber.tensorFiber
        (FiniteWeightFiber.symFiber r (α v) (hα v)) (Wτ v)).localFactor (q v) s) =
      (∏ v ∈ S,
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.tensorFiber
            (FiniteWeightFiber.symFiber 1 (α v) (hα v))
            (FiniteWeightFiber.symFiber (r - 1) (α v) (hα v))) (Wτ v)).localFactor (q v) s) /
      ∏ v ∈ S,
        (FiniteWeightFiber.tensorFiber
          (FiniteWeightFiber.symFiber (r - 2) (α v) (hα v)) (Wτ v)).localFactor (q v) s := by
  apply finiteSymTwistEulerProduct_eq_div_tensorStep S hr α hα Wτ q s
  exact finiteEulerProduct_ne_zero S
    (fun v => FiniteWeightFiber.tensorFiber
      (FiniteWeightFiber.symFiber (r - 2) (α v) (hα v)) (Wτ v)) q hq hs

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.tensorStepLocalPoly_eq_sym_mul_lower
#print axioms CriticalLinePhasor.GlobalHelix.symClockWeight_eq_symFiber_weight
#print axioms CriticalLinePhasor.GlobalHelix.symClockLocalPoly_eq_symFiber_localPoly
#print axioms CriticalLinePhasor.GlobalHelix.tensorSym_upper_weight
#print axioms CriticalLinePhasor.GlobalHelix.tensorSym_lower_weight
#print axioms CriticalLinePhasor.GlobalHelix.tensorStepLocalPoly_eq_tensorFiber_localPoly
#print axioms CriticalLinePhasor.GlobalHelix.tensorSym_localPoly_eq_sym_mul_lower
#print axioms CriticalLinePhasor.GlobalHelix.tensorFiber_localPoly_eq_prod_right
#print axioms CriticalLinePhasor.GlobalHelix.tensorSymTwist_localPoly_eq_mul
#print axioms CriticalLinePhasor.GlobalHelix.tensorSymTwist_localFactor_eq_mul
#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorSymTwistEulerProduct_eq_mul
#print axioms CriticalLinePhasor.GlobalHelix.finiteSymTwistEulerProduct_eq_div_tensorStep
#print axioms CriticalLinePhasor.GlobalHelix.localPoly_cpow_ne_zero
#print axioms CriticalLinePhasor.GlobalHelix.localFactor_ne_zero
#print axioms CriticalLinePhasor.GlobalHelix.finiteEulerProduct_ne_zero
#print axioms CriticalLinePhasor.GlobalHelix.finiteSymTwistEulerProduct_eq_div_tensorStep_of_halfPlane
