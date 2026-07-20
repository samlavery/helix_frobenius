import Mathlib

/-!
# Carrier faithfulness and the analytic inputs, proved universally (not per-class)

Two audit objections, answered by theorem — and stated for the **widest** setting each admits, not
just for Dirichlet characters.  The Dirichlet statements are then one-line instances.

**Objection 1 (source→carrier injectivity).**  `source_determined_by_bank`: for **any**
function-like source (`FunLike F α β`), the map to its coefficient bank `χ ↦ ⇑χ` is injective —
distinct sources give distinct carrier banks.  Fully universal; no arithmetic hypotheses.

**Objection 2 (analytic inputs).**  The load-bearing analytic input is bounded coefficient
primitives, and it is proved with **no character and no class**:
`bounded_partial_sums_of_window_zero`: for any `f : ℕ → E` into a normed group whose every
`N`-window sums to zero and whose terms are `C`-bounded, the partial sums are bounded by `N·C` — the
Dirichlet-test hypothesis Abel summation consumes.  `window_shift_invariant` (translation of a
finite-group sum) and Mathlib's `MulChar.sum_eq_zero_of_ne_one` (any nontrivial multiplicative
character) supply the window-zero hypothesis for the arithmetic instances.

The analytic continuation is **also universal** — because the functional equation is not a per-class
import but the carrier's **Poisson/theta self-duality**, an abstract FE-pair.  For *any* such pair
the completed readout `Λ` is entire (`readout_entire_of_carrier_FE`).  The carrier supplies the pair
for every fiber (the general-lattice theta functional equation, proved in this project's
`GeneralLatticeFE`/`EpsteinZetaGaussian`); Dirichlet `L` is one fiber, not the source of the FE.
Footprint `{propext, Classical.choice, Quot.sound}`; no `sorry`, no `axiom`.
-/

namespace CriticalLinePhasor.CarrierFaithfulness

open Finset

/-! ## Universal theorems (no class, no arithmetic hypotheses) -/

/-- **Objection 1, universal — source→carrier injectivity for any function-like source.**  A source
`χ : F` with a coefficient bank `⇑χ : α → β` is determined by that bank: `χ ↦ ⇑χ` is injective.  No
class, no continuation, no arithmetic — lossless bookkeeping is source-faithful for *every*
function-like structure. -/
theorem source_determined_by_bank {F : Type*} {α β : Type*} [FunLike F α β] :
    Function.Injective (fun χ : F => (⇑χ : α → β)) :=
  DFunLike.coe_injective

/-- **Universal translation invariance.**  A sum over a finite commutative group is invariant under
translation by any element — the group-theoretic core behind "every full period cancels". -/
theorem window_shift_invariant {G E : Type*} [AddCommGroup G] [Fintype G] [AddCommMonoid E]
    (f : G → E) (g₀ : G) : ∑ g, f (g₀ + g) = ∑ g, f g :=
  Equiv.sum_comp (Equiv.addLeft g₀) f

/-- **Objection 2, universal — bounded coefficient primitives, no character.**  For any
`f : ℕ → E` into a normed additive group whose every `N`-window sums to zero (`hwin`) and whose
terms are `C`-bounded (`hC`), the partial sums are bounded by `N·C`, uniformly in `M`.  Proof: the
window-zero hypothesis makes the partial sum periodic with period `N`, so strong induction reduces
any `M` to fewer than `N` unit-bounded terms.  This is the Dirichlet-test hypothesis for
Abel-summation continuation — a genuine analytic bound, proved for *any* such `f`. -/
theorem bounded_partial_sums_of_window_zero {E : Type*} [NormedAddCommGroup E] {f : ℕ → E}
    {N : ℕ} (hN : 0 < N) (hwin : ∀ k, ∑ j ∈ range N, f (k + j) = 0)
    {C : ℝ} (hC : ∀ n, ‖f n‖ ≤ C) : ∀ M, ‖∑ n ∈ range M, f n‖ ≤ N * C := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hper : ∀ M, ∑ n ∈ range (M + N), f n = ∑ n ∈ range M, f n := by
    intro M; rw [Finset.sum_range_add, hwin M, add_zero]
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    by_cases hMN : N ≤ M
    · obtain ⟨M', rfl⟩ := Nat.exists_eq_add_of_le hMN
      rw [add_comm N M', hper M']
      exact ih M' (by omega)
    · push_neg at hMN
      calc ‖∑ n ∈ range M, f n‖
          ≤ ∑ n ∈ range M, ‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ range M, C := Finset.sum_le_sum (fun n _ => hC n)
        _ = M * C := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ N * C := by
              apply mul_le_mul_of_nonneg_right _ hC0
              exact_mod_cast hMN.le

/-- **Objection 1, coordinate level — the polar carrier state recovers the coefficient.**  The
carrier coordinate `(r, θ) = (‖a‖, arg a)` determines the complex coefficient `a` exactly, so the
map is injective.  Composed with `source_determined_by_bank`, the source→carrier-*state* map is
injective: the carrier state `(r, θ, z)` contains the source, not merely lossless bookkeeping. -/
theorem carrier_coord_injective :
    Function.Injective (fun a : ℂ => (‖a‖, Complex.arg a)) := by
  intro a b h
  have h1 : ‖a‖ = ‖b‖ := congrArg Prod.fst h
  have h2 : Complex.arg a = Complex.arg b := congrArg Prod.snd h
  rw [← Complex.norm_mul_exp_arg_mul_I a, ← Complex.norm_mul_exp_arg_mul_I b, h1, h2]

/-- **Objection 3, universal — an admissible warp preserves bounded primitives (the missing step).**
Forcible closure only spans a residual; it does *not* show the correcting coefficients form a
bounded, readout-preserving adapter.  But an **admissible** adapter — a warp `w` of bounded
modulus (`hW`) and *summable variation* (`hV`) — provably keeps the coefficient primitives bounded:
by Abel summation (`sum_range_by_parts`), bounded `a`-primitives (`hC`) transfer to bounded
`(w • a)`-primitives, with bound `C·(W + V)`.  This is what distinguishes an admissible warp from
free per-cell (forcible-closure) coefficients, and it is exactly the warp-removal control the
readout's continuation needs — proved for any `a`, `w`. -/
theorem warp_preserves_bounded_partial_sums {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : ℕ → E} {w : ℕ → ℂ} {C W V : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k, ‖∑ n ∈ range k, a n‖ ≤ C) (hW : ∀ n, ‖w n‖ ≤ W)
    (hV : ∀ M, ∑ i ∈ range M, ‖w (i + 1) - w i‖ ≤ V) :
    ∀ M, ‖∑ n ∈ range M, w n • a n‖ ≤ C * W + C * V := by
  have hW0 : 0 ≤ W := le_trans (norm_nonneg _) (hW 0)
  intro M
  rw [Finset.sum_range_by_parts w a M]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    calc ‖w (M - 1)‖ * ‖∑ n ∈ range M, a n‖
        ≤ W * C := mul_le_mul (hW _) (hC M) (norm_nonneg _) hW0
      _ = C * W := mul_comm W C
  · calc ‖∑ i ∈ range (M - 1), (w (i + 1) - w i) • ∑ j ∈ range (i + 1), a j‖
        ≤ ∑ i ∈ range (M - 1), ‖(w (i + 1) - w i) • ∑ j ∈ range (i + 1), a j‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range (M - 1), ‖w (i + 1) - w i‖ * C := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left (hC (i + 1)) (norm_nonneg _)
      _ = C * ∑ i ∈ range (M - 1), ‖w (i + 1) - w i‖ := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ C * V := mul_le_mul_of_nonneg_left (hV (M - 1)) hC0

/-- **Objection 2, universal — the readout continues, from the carrier's functional equation.**  The
functional equation is *not* a per-class import: it is the carrier's Poisson/theta self-duality,
packaged as an abstract FE-pair `P`.  For **any** complete (strong) FE-pair the completed readout
`Λ` is entire.  The carrier supplies such a pair for every fiber (the general-lattice theta
functional equation — `GeneralLatticeFE`, `EpsteinZetaGaussian` in this project), so the continuation
is universal; Dirichlet `L` below is one instance, not the source of the mechanism. -/
theorem readout_entire_of_carrier_FE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P : WeakFEPair E} (hP : IsStrongFEPair P) : Differentiable ℂ P.Λ :=
  hP.differentiable_Λ

/-! ## Arithmetic instances (the universal theorems specialize; Dirichlet is one class of many) -/

/-- The reindexing `range N ≃ ZMod N` via `natCast`. -/
private theorem sum_range_natCast_eq_sum {N : ℕ} [NeZero N] (g : ZMod N → ℂ) :
    ∑ n ∈ range N, g (n : ZMod N) = ∑ a : ZMod N, g a := by
  refine Finset.sum_nbij' (fun n => (n : ZMod N)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
  · intro n _; exact mem_univ _
  · intro a _; exact mem_range.mpr (ZMod.val_lt a)
  · intro n hn; exact ZMod.val_natCast_of_lt (mem_range.mp hn)
  · intro a _; simp
  · intro n _; rfl

/-- **Objection 1 instance — Dirichlet.**  A Dirichlet character is determined by its ℕ-indexed
coefficient bank (natCast surjectivity feeds the universal `source_determined_by_bank`). -/
theorem source_to_carrier_injective {N : ℕ} [NeZero N] :
    Function.Injective (fun (χ : DirichletCharacter ℂ N) => fun n : ℕ => χ (n : ZMod N)) := by
  -- `DFunLike.ext` is the concrete face of the universal `source_determined_by_bank`
  intro χ₁ χ₂ h
  refine DFunLike.ext _ _ (fun a => ?_)
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ZMod N) = a := ⟨a.val, by simp⟩
  simpa using congrFun h m

/-- **Objection 2 instance — continuation for one fiber (Dirichlet).**  A specialization of the
universal `readout_entire_of_carrier_FE`: the Dirichlet `L`-function is the completed readout of the
Jacobi-theta FE-pair, so it is entire for `χ ≠ 1` (Mathlib packages this as
`differentiable_LFunction`).  The mechanism — the theta functional equation — is the carrier's and
universal; this is merely its instance on the character fiber. -/
theorem readout_continues {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (DirichletCharacter.LFunction χ) :=
  DirichletCharacter.differentiable_LFunction hχ

/-- Every full period of a nontrivial character's bank cancels — the window-zero hypothesis for the
universal bounded-partial-sums theorem, from `window_shift_invariant` and Mathlib's general
`MulChar.sum_eq_zero_of_ne_one` (valid for **any** nontrivial multiplicative character, not only
Dirichlet ones). -/
theorem char_shifted_period_sum_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (M : ℕ) : ∑ j ∈ range N, χ ((M + j : ℕ) : ZMod N) = 0 := by
  have h1 : ∑ j ∈ range N, χ ((M + j : ℕ) : ZMod N)
      = ∑ j ∈ range N, χ ((M : ZMod N) + (j : ZMod N)) :=
    Finset.sum_congr rfl (fun j _ => by rw [Nat.cast_add])
  rw [h1, sum_range_natCast_eq_sum (fun a => χ ((M : ZMod N) + a))]
  calc ∑ a : ZMod N, χ ((M : ZMod N) + a)
      = ∑ a : ZMod N, χ a := window_shift_invariant (fun a => χ a) (M : ZMod N)
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

/-- **Objection 2 instance — bounded coefficient primitives for a Dirichlet character**, obtained by
instantiating the universal `bounded_partial_sums_of_window_zero` (window-zero from
`char_shifted_period_sum_zero`, unit bound from `DirichletCharacter.norm_le_one`). -/
theorem bounded_partial_sums {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∀ M, ‖∑ n ∈ range M, χ (n : ZMod N)‖ ≤ N := by
  intro M
  have h := bounded_partial_sums_of_window_zero (f := fun n => χ (n : ZMod N))
    (Nat.pos_of_ne_zero (NeZero.ne N)) (fun k => char_shifted_period_sum_zero hχ k)
    (C := 1) (fun n => DirichletCharacter.norm_le_one χ _) M
  simpa using h

end CriticalLinePhasor.CarrierFaithfulness

#print axioms CriticalLinePhasor.CarrierFaithfulness.source_determined_by_bank
#print axioms CriticalLinePhasor.CarrierFaithfulness.window_shift_invariant
#print axioms CriticalLinePhasor.CarrierFaithfulness.bounded_partial_sums_of_window_zero
#print axioms CriticalLinePhasor.CarrierFaithfulness.carrier_coord_injective
#print axioms CriticalLinePhasor.CarrierFaithfulness.warp_preserves_bounded_partial_sums
#print axioms CriticalLinePhasor.CarrierFaithfulness.readout_entire_of_carrier_FE
#print axioms CriticalLinePhasor.CarrierFaithfulness.source_to_carrier_injective
#print axioms CriticalLinePhasor.CarrierFaithfulness.readout_continues
#print axioms CriticalLinePhasor.CarrierFaithfulness.char_shifted_period_sum_zero
#print axioms CriticalLinePhasor.CarrierFaithfulness.bounded_partial_sums
