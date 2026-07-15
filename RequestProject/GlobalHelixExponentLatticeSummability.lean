import RequestProject.GlobalHelixLocalEulerBounds
import RequestProject.GlobalHelixBilateralEulerHeight
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fintype.Option

/-!
# Absolute summability on finite-place exponent lattices

The local tensor-Euler coefficient has polynomial growth in its exponent, while a negative power
of every residue height supplies a geometric factor.  Finite-type induction splits a function on
`Option α` into its head and tail coordinates, giving the required finite-product Tonelli lemma.
-/

open Real Complex
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

universe u

/-- A finite product of nonnegative summable one-coordinate sequences is summable on the full
function lattice. -/
theorem summable_pi_prod_of_summable
    {α : Type u} [Fintype α] (f : α → ℕ → ℝ)
    (hf : ∀ i, Summable (f i)) (hfn : ∀ i n, 0 ≤ f i n) :
    Summable (fun k : α → ℕ => ∏ i, f i (k i)) := by
  classical
  let P : ∀ (α : Type u) [Fintype α], Prop := fun α _ =>
    ∀ (f : α → ℕ → ℝ), (∀ i, Summable (f i)) → (∀ i n, 0 ≤ f i n) →
      Summable (fun k : α → ℕ => ∏ i, f i (k i))
  have hP : P α := by
    apply Fintype.induction_empty_option (P := P)
    · intro β γ instγ e ih
      letI : Fintype β := Fintype.ofEquiv γ e.symm
      intro g hg hgn
      let gβ : β → ℕ → ℝ := fun i => g (e i)
      have hsβ := ih gβ (fun i => hg (e i)) (fun i n => hgn (e i) n)
      let ep : (γ → ℕ) ≃ (β → ℕ) := Equiv.piCongrLeft (fun _ => ℕ) e.symm
      rw [← ep.summable_iff] at hsβ
      convert hsβ using 1
      funext k
      simp only [Function.comp_apply, ep, gβ]
      have hk (i : β) :
          (Equiv.piCongrLeft (fun _ : β => ℕ) e.symm) k i = k (e i) := by
        simpa using
          (Equiv.piCongrLeft_apply_apply (P := fun _ : β => ℕ) e.symm k (e i))
      simp_rw [hk]
      change (∏ i : γ, g i (k i)) = ∏ i : β, g (e i) (k (e i))
      symm
      exact Fintype.prod_equiv e _ _ (fun _ => rfl)
    · intro g hg hgn
      exact Summable.of_finite
    · intro β instβ ih g hg hgn
      let e : (Option β → ℕ) ≃ ℕ × (β → ℕ) := Equiv.piOptionEquivProd
      have hnone : Summable (g none) := hg none
      have hsome : Summable (fun k : β → ℕ => ∏ i, g (some i) (k i)) :=
        ih (fun i => g (some i)) (fun i => hg (some i)) (fun i n => hgn (some i) n)
      have hp : Summable (fun p : ℕ × (β → ℕ) =>
          g none p.1 * ∏ i, g (some i) (p.2 i)) :=
        hnone.mul_of_nonneg hsome (hgn none)
          (fun k => Finset.prod_nonneg fun i _ => hgn (some i) _)
      rw [← e.summable_iff] at hp
      convert hp using 1
      funext k
      simp [e, Fintype.prod_option]
  exact hP f hf hfn

/-- A shifted polynomial times a strict geometric progression is summable. -/
theorem summable_add_one_pow_mul_geometric
    (d : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ d * r ^ n) := by
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_of_nonneg hr0.le]
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ d * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one d hrnorm
  have hs' : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ d * r ^ (n + 1)) := by
    apply (hs.comp_injective Nat.succ_injective).congr
    intro n
    simp [Nat.cast_succ]
  have hscaled := hs'.mul_left r⁻¹
  apply hscaled.congr
  intro n
  rw [pow_succ]
  field_simp [hr0.ne']

/-- The product polynomial/geometric majorant is summable on a finite-place exponent lattice. -/
theorem summable_tensorEuler_power_majorant
    {V : Type*} (S : Finset V) (q : V → ℝ) (hq : ∀ v ∈ S, 1 < q v)
    (d M : ℕ) (hM : 0 < M) :
    Summable (fun k : (v : S) → ℕ =>
      ∏ v : S, (((k v + 1 : ℕ) : ℝ) ^ d) * (((q v)⁻¹) ^ M) ^ (k v)) := by
  refine summable_pi_prod_of_summable
    (f := fun (v : S) n => (((n + 1 : ℕ) : ℝ) ^ d) * (((q v)⁻¹) ^ M) ^ n) ?_ ?_
  · intro v
    apply summable_add_one_pow_mul_geometric d
    · exact pow_pos (inv_pos.mpr (lt_trans zero_lt_one (hq v v.property))) M
    · have hqv := hq v v.property
      have hi : (q v)⁻¹ < 1 :=
        (inv_lt_one₀ (lt_trans zero_lt_one hqv)).2 hqv
      exact pow_lt_one₀ (inv_pos.mpr (lt_trans zero_lt_one hqv)).le hi hM.ne'
  · intro v n
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (pow_nonneg (pow_nonneg
        (inv_nonneg.mpr (lt_trans zero_lt_one (hq v v.property)).le) _) _)

/-- A negative integral power of the multiplicative height factors coordinatewise. -/
theorem naturalEulerHeight_rpow_neg_nat
    {V : Type*} (S : Finset V) (q : V → ℝ) (hq : ∀ v ∈ S, 0 < q v)
    (k : (v : S) → ℕ) (M : ℕ) :
    (∏ v : S, q v ^ k v) ^ (-(M : ℝ)) =
      ∏ v : S, (((q v)⁻¹) ^ M) ^ k v := by
  have hH : 0 < ∏ v : S, q v ^ k v :=
    Finset.prod_pos fun v _ => pow_pos (hq v v.property) _
  rw [Real.rpow_neg hH.le, Real.rpow_natCast]
  rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  calc
    ((q v ^ k v) ^ M)⁻¹ = ((q v ^ k v)⁻¹) ^ M := by
      rw [inv_pow]
    _ = (((q v)⁻¹) ^ k v) ^ M := by
      congr 1
      exact (inv_pow (q v) (k v)).symm
    _ = ((q v)⁻¹) ^ (k v * M) := by rw [pow_mul]
    _ = ((q v)⁻¹) ^ (M * k v) := by rw [Nat.mul_comm]
    _ = (((q v)⁻¹) ^ M) ^ k v := by rw [pow_mul]

/-- Absolute summability of the tensor-Euler coefficient bank after any positive integral
negative power of its multiplicative height. -/
theorem summable_naturalTensorEulerCoeff_mul_height_rpow
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι)
    (q : V → ℝ) (hq : ∀ v ∈ S, 1 < q v) (M : ℕ) (hM : 0 < M) :
    Summable (fun k : (v : S) → ℕ =>
      ‖∏ v : S, localEulerCoeff (W v) (k v)‖ *
        (∏ v : S, q v ^ k v) ^ (-(M : ℝ))) := by
  have hs := summable_tensorEuler_power_majorant S q hq (Fintype.card ι) M hM
  refine Summable.of_nonneg_of_le
    (f := fun k : (v : S) → ℕ =>
      ∏ v : S, (((k v + 1 : ℕ) : ℝ) ^ Fintype.card ι) *
        (((q v)⁻¹) ^ M) ^ (k v)) ?_ ?_ hs
  · intro k
    have hH : 0 ≤ ∏ v : S, q v ^ k v :=
      (Finset.prod_pos (s := Finset.univ) fun (v : S) _ =>
        pow_pos (lt_trans zero_lt_one (hq v v.property)) _).le
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hH _)
  · intro k
    rw [naturalEulerHeight_rpow_neg_nat S q
      (fun v hv => lt_trans zero_lt_one (hq v hv)) k M]
    rw [norm_prod]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro v hv
      exact mul_nonneg (norm_nonneg _)
        (pow_nonneg (pow_nonneg (inv_nonneg.mpr
          (lt_trans zero_lt_one (hq v v.property)).le) _) _)
    · intro v hv
      have hcoeff : ‖localEulerCoeff (W v) (k v)‖ ≤
          (((k v + 1 : ℕ) : ℝ) ^ Fintype.card ι) := by
        simpa [Nat.cast_pow] using
          (norm_localEulerCoeff_le_add_one_pow (W v) (k v))
      exact mul_le_mul_of_nonneg_right hcoeff
        (pow_nonneg (pow_nonneg (inv_nonneg.mpr
          (lt_trans zero_lt_one (hq v v.property)).le) _) _)

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.summable_pi_prod_of_summable
#print axioms CriticalLinePhasor.GlobalHelix.summable_tensorEuler_power_majorant
#print axioms CriticalLinePhasor.GlobalHelix.naturalEulerHeight_rpow_neg_nat
#print axioms CriticalLinePhasor.GlobalHelix.summable_naturalTensorEulerCoeff_mul_height_rpow
