import RequestProject.CPSTemperedBankAbscissa3D
import RequestProject.BaseChangeInduction
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The local Euler series sums to the reciprocal Satake polynomial

The analytic half of the Euler-product identification.  Formally, the complete-homogeneous
generating series of a finite weight family is the reciprocal of the Satake polynomial; that is
already compiled as a power-series identity (`localEulerPowerSeries_mul_reciprocal`).  What the
Euler product needs is the *convergent* statement at a point of the readout half-plane:

  `∑' e, h_e(w) · z ^ e = ∏ i, (1 - w i · z)⁻¹`   for `‖w i‖ ≤ 1` and `‖z‖ < 1`,

together with absolute convergence.  Both come from one induction on the number of channels,
using the repository's own channel recursion `radialLocalEulerCoeff_snoc`
(`h_j(w) = ∑_{a ≤ j} h_a(w restricted) · w_last ^ (j - a)`) against Mathlib's Cauchy product for
absolutely convergent series.  Adding a channel multiplies by one geometric series — the statement
is literally that the channel recursion *is* the Cauchy product.

Scope: this file proves the local identity only.  The global Euler product over primes and its
identification with the bank Dirichlet series are not proven here.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix

/-- **The local Euler sum.**  For a family of weights of modulus at most one and `‖z‖ < 1`, the
complete-homogeneous generating series converges absolutely to the reciprocal of the Satake
polynomial.  Induction on the number of channels: the channel recursion is the Cauchy product with
one more geometric series. -/
theorem localEuler_summable_and_tsum :
    ∀ (d : ℕ) (w : Fin d → ℂ), (∀ i, ‖w i‖ ≤ 1) → ∀ {z : ℂ}, ‖z‖ < 1 →
      Summable (fun e : ℕ => ‖radialLocalEulerCoeff w e * z ^ e‖) ∧
        (∑' e : ℕ, radialLocalEulerCoeff w e * z ^ e) = ∏ i, (1 - w i * z)⁻¹ := by
  intro d
  induction d with
  | zero =>
      intro w _ z _
      have hw0 : w = fun _ : Fin 0 => (0 : ℂ) := Subsingleton.elim _ _
      have hzero : ∀ e : ℕ, radialLocalEulerCoeff w e = if e = 0 then 1 else 0 := by
        intro e
        rw [hw0]
        exact CriticalLinePhasor.BaseChangeInduction.radialLocalEulerCoeff_isEmpty e
      have hfun : (fun e : ℕ => radialLocalEulerCoeff w e * z ^ e) =
          fun e : ℕ => if e = 0 then (1 : ℂ) else 0 := by
        funext e
        rw [hzero e]
        by_cases he : e = 0 <;> simp [he]
      refine ⟨?_, ?_⟩
      · refine summable_of_ne_finset_zero (s := {0}) fun e he => ?_
        simp only [Finset.mem_singleton] at he
        rw [hzero e, if_neg he, zero_mul, norm_zero]
      · rw [hfun, tsum_ite_eq]
        simp
  | succ d ih =>
      intro w hw z hz
      have hu : ∀ i : Fin d, ‖w i.castSucc‖ ≤ 1 := fun i => hw _
      obtain ⟨hsu, htu⟩ := ih (fun i : Fin d => w i.castSucc) hu hz
      have hαz : ‖w (Fin.last d) * z‖ < 1 := by
        rw [norm_mul]
        calc ‖w (Fin.last d)‖ * ‖z‖ ≤ 1 * ‖z‖ := by
              gcongr
              exact hw _
          _ = ‖z‖ := one_mul _
          _ < 1 := hz
      have hg : Summable (fun e : ℕ => ‖(w (Fin.last d) * z) ^ e‖) := by
        simp only [norm_pow]
        exact summable_geometric_of_lt_one (norm_nonneg _) hαz
      have hgsum : (∑' e : ℕ, (w (Fin.last d) * z) ^ e) =
          (1 - w (Fin.last d) * z)⁻¹ := tsum_geometric_of_norm_lt_one hαz
      -- the channel recursion IS the Cauchy product
      have hterm : ∀ n : ℕ,
          (∑ k ∈ Finset.range (n + 1),
            (radialLocalEulerCoeff (fun i : Fin d => w i.castSucc) k * z ^ k) *
              (w (Fin.last d) * z) ^ (n - k)) =
            radialLocalEulerCoeff w n * z ^ n := by
        intro n
        rw [CriticalLinePhasor.BaseChangeInduction.radialLocalEulerCoeff_snoc d w n,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun a ha => ?_
        have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have hzz : z ^ a * z ^ (n - a) = z ^ n := by
          rw [← pow_add, Nat.add_sub_cancel' han]
        calc
          (radialLocalEulerCoeff (fun i : Fin d => w i.castSucc) a * z ^ a) *
              (w (Fin.last d) * z) ^ (n - a) =
              (radialLocalEulerCoeff (fun i : Fin d => w i.castSucc) a *
                w (Fin.last d) ^ (n - a)) * (z ^ a * z ^ (n - a)) := by
            rw [mul_pow]; ring
          _ = radialLocalEulerCoeff (fun i : Fin d => w i.castSucc) a *
                w (Fin.last d) ^ (n - a) * z ^ n := by rw [hzz]
      refine ⟨?_, ?_⟩
      · have hsum := summable_norm_sum_mul_range_of_summable_norm hsu hg
        refine hsum.congr fun n => ?_
        rw [hterm n]
      · rw [Fin.prod_univ_castSucc, ← htu, ← hgsum,
          tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hsu hg]
        exact (tsum_congr hterm).symm

/-- The local Euler series of a unit-modulus weight family converges absolutely. -/
theorem localEuler_summable {d : ℕ} (w : Fin d → ℂ) (hw : ∀ i, ‖w i‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun e : ℕ => ‖radialLocalEulerCoeff w e * z ^ e‖) :=
  (localEuler_summable_and_tsum d w hw hz).1

/-- The local Euler series of a unit-modulus weight family sums to the reciprocal Satake
polynomial. -/
theorem localEuler_tsum {d : ℕ} (w : Fin d → ℂ) (hw : ∀ i, ‖w i‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' e : ℕ, radialLocalEulerCoeff w e * z ^ e) = ∏ i, (1 - w i * z)⁻¹ :=
  (localEuler_summable_and_tsum d w hw hz).2

/-- Reindexed form: the local Euler sum for an arbitrary finite channel set, read through any
enumeration.  The coefficient is enumeration-independent by `radialLocalEulerCoeff_equiv`. -/
theorem localEuler_tsum_fintype {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (hw : ∀ i, ‖w i‖ ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' e : ℕ, radialLocalEulerCoeff w e * z ^ e) = ∏ i, (1 - w i * z)⁻¹ := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hcoeff : ∀ n : ℕ,
      radialLocalEulerCoeff (w ∘ e) n = radialLocalEulerCoeff w n :=
    fun n => CriticalLinePhasor.TransportClosure.radialLocalEulerCoeff_equiv e w n
  have hwe : ∀ i, ‖(w ∘ e) i‖ ≤ 1 := fun i => hw _
  have h := localEuler_tsum (w ∘ e) hwe hz
  rw [show (fun n : ℕ => radialLocalEulerCoeff (w ∘ e) n * z ^ n) =
      fun n : ℕ => radialLocalEulerCoeff w n * z ^ n by
    funext n; rw [hcoeff n]] at h
  rw [h]
  exact Fintype.prod_equiv e _ _ fun i => rfl

/-- Absolute convergence in the reindexed form. -/
theorem localEuler_summable_fintype {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (hw : ∀ i, ‖w i‖ ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun e : ℕ => ‖radialLocalEulerCoeff w e * z ^ e‖) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hcoeff : ∀ n : ℕ,
      radialLocalEulerCoeff (w ∘ e) n = radialLocalEulerCoeff w n :=
    fun n => CriticalLinePhasor.TransportClosure.radialLocalEulerCoeff_equiv e w n
  have hwe : ∀ i, ‖(w ∘ e) i‖ ≤ 1 := fun i => hw _
  refine (localEuler_summable (w ∘ e) hwe hz).congr fun n => ?_
  rw [hcoeff n]

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.localEuler_summable_and_tsum
#print axioms CriticalLinePhasor.GlobalHelix.localEuler_tsum_fintype
#print axioms CriticalLinePhasor.GlobalHelix.localEuler_summable_fintype
