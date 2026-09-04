import Mathlib
import RequestProject.FinitePartSymmetry
import RequestProject.SeatPrimeAnchorHermitian

/-!
# The seat form as a finite functional of the jets of `ξ′/ξ` (ledger 594)

The compiled door `rh_iff_hermForm_nonneg` has hypothesis `Re Q_w(R) ≥ 0` with
`Q_w(R) = hermForm w R = Σ'_ρ m_ρ · conj(R(x̄_ρ)) · R(x′_ρ)`, nodes `x_ρ = 1/(s−ρ)`, `x′_ρ = 1/(ρ−c)`,
`s = ½ + i w`, `c = 1 − s̄`. The nodes satisfy ONE relation, `x + x′ = d·x·x′` with `d = s − c` real,
which reduces every monomial `x^j x′^k` to pure powers by a Pascal-type recursion (`pf`,
`pf_identity`). The first-order coefficients agree (`pf_first_symm`), so the two conditionally
convergent first-order pieces pair into the absolutely convergent
`Σ' m_ρ (x_ρ + x′_ρ) = FP(s) − FP(c) = 2·Re FP(s)` (593), while every higher pure power is a compiled jet
(`hadamard_jet`, 592).

Part 1 (this section): the algebra of the reduction.
-/

open Complex Finset Filter Topology
open CriticalLinePhasor.SeatPrimeAnchorHermitian

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. Partial fractions in two node variables with `X + Y = d X Y` -/

/-- Coefficient pair `(a, b)` of `X^j Y^k = Σ_i a i X^i + Σ_l b l Y^l` under `X + Y = d X Y`:
pure powers are the base cases, and `X^{j+1} Y^{k+1} = (X^{j+1} Y^k + X^j Y^{k+1})/d`. -/
def pf (d : ℂ) : ℕ → ℕ → (ℕ → ℂ) × (ℕ → ℂ)
  | j, 0 => (fun i => if i = j then 1 else 0, fun _ => 0)
  | 0, k + 1 => (fun _ => 0, fun l => if l = k + 1 then 1 else 0)
  | j + 1, k + 1 =>
      ((fun i => (1 / d) * ((pf d (j + 1) k).1 i + (pf d j (k + 1)).1 i)),
       (fun l => (1 / d) * ((pf d (j + 1) k).2 l + (pf d j (k + 1)).2 l)))
termination_by j k => j + k

theorem pf_zero_right (d : ℂ) (j : ℕ) :
    pf d j 0 = (fun i => if i = j then 1 else 0, fun _ => 0) := by
  cases j <;> rw [pf]

theorem pf_zero_left (d : ℂ) (k : ℕ) :
    pf d 0 (k + 1) = (fun _ => 0, fun l => if l = k + 1 then 1 else 0) := by
  rw [pf]

theorem pf_succ (d : ℂ) (j k : ℕ) :
    pf d (j + 1) (k + 1)
      = ((fun i => (1 / d) * ((pf d (j + 1) k).1 i + (pf d j (k + 1)).1 i)),
         (fun l => (1 / d) * ((pf d (j + 1) k).2 l + (pf d j (k + 1)).2 l))) := by
  rw [pf]

/-- **The reduction identity**, with both sums over `range (N+1)` for any `N ≥ j + k`. -/
theorem pf_identity {d X Y : ℂ} (hd : d ≠ 0) (hXY : X + Y = d * X * Y) (N : ℕ) :
    ∀ n : ℕ, ∀ j k : ℕ, j + k = n → j + k ≤ N →
      X ^ j * Y ^ k = (∑ i ∈ range (N + 1), (pf d j k).1 i * X ^ i)
        + ∑ l ∈ range (N + 1), (pf d j k).2 l * Y ^ l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j k hn hN
    rcases k with _ | k
    · -- pure power X^j
      rw [pf_zero_right]
      have hj : j < N + 1 := by omega
      simp [ite_mul, Finset.sum_ite_eq', Finset.mem_range, hj]
    · rcases j with _ | j
      · -- pure power Y^{k+1}
        rw [pf_zero_left]
        have hk : k + 1 < N + 1 := by omega
        simp [ite_mul, Finset.sum_ite_eq', Finset.mem_range, hk]
      · -- the step
        have hstep : X ^ (j + 1) * Y ^ (k + 1)
            = (1 / d) * (X ^ (j + 1) * Y ^ k + X ^ j * Y ^ (k + 1)) := by
          have h1 : X ^ (j + 1) * Y ^ (k + 1) = X ^ j * Y ^ k * (X * Y) := by ring
          have hXYd : X * Y = (1 / d) * (X + Y) := by
            rw [hXY]
            field_simp
          rw [h1, hXYd]
          ring
        have ih1 := ih (j + 1 + k) (by omega) (j + 1) k rfl (by omega)
        have ih2 := ih (j + (k + 1)) (by omega) j (k + 1) rfl (by omega)
        rw [hstep, ih1, ih2, pf_succ]
        dsimp only
        have e1 : ∑ i ∈ range (N + 1), (1 / d * ((pf d (j + 1) k).1 i + (pf d j (k + 1)).1 i)) * X ^ i
            = ∑ i ∈ range (N + 1), (1 / d) * ((pf d (j + 1) k).1 i * X ^ i)
              + ∑ i ∈ range (N + 1), (1 / d) * ((pf d j (k + 1)).1 i * X ^ i) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        have e2 : ∑ l ∈ range (N + 1), (1 / d * ((pf d (j + 1) k).2 l + (pf d j (k + 1)).2 l)) * Y ^ l
            = ∑ l ∈ range (N + 1), (1 / d) * ((pf d (j + 1) k).2 l * Y ^ l)
              + ∑ l ∈ range (N + 1), (1 / d) * ((pf d j (k + 1)).2 l * Y ^ l) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          ring
        rw [e1, e2, mul_add, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
        ring

/-- The first-order coefficients agree for `j, k ≥ 1`. -/
theorem pf_first_symm (d : ℂ) :
    ∀ n : ℕ, ∀ j k : ℕ, j + k = n → 1 ≤ j → 1 ≤ k → (pf d j k).1 1 = (pf d j k).2 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j k hn hj hk
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [pf_succ]
    simp only
    rcases Nat.eq_zero_or_pos j' with hj0 | hj0 <;> rcases Nat.eq_zero_or_pos k' with hk0 | hk0
    · subst hj0; subst hk0
      rw [pf_zero_right, pf_zero_left]
      simp
    · subst hj0
      obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
      rw [pf_zero_left]
      have := ih (0 + 1 + (k'' + 1)) (by omega) 1 (k'' + 1) (by omega) le_rfl (by omega)
      simp only [zero_add] at this ⊢
      simp only [this]
      simp
    · subst hk0
      obtain ⟨j'', rfl⟩ : ∃ j'', j' = j'' + 1 := ⟨j' - 1, by omega⟩
      rw [pf_zero_right]
      have := ih (j'' + 1 + (0 + 1)) (by omega) (j'' + 1) 1 (by omega) (by omega) le_rfl
      simp only [zero_add] at this ⊢
      simp only [this]
      simp
    · have h1 := ih (j' + 1 + k') (by omega) (j' + 1) k' rfl (by omega) hk0
      have h2 := ih (j' + (k' + 1)) (by omega) j' (k' + 1) rfl hj0 (by omega)
      rw [h1, h2]

/-- The index-`0` coefficients vanish once `j + k ≥ 1`. -/
theorem pf_index_zero (d : ℂ) :
    ∀ n : ℕ, ∀ j k : ℕ, j + k = n → 1 ≤ j + k → (pf d j k).1 0 = 0 ∧ (pf d j k).2 0 = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j k hn hjk
    rcases k with _ | k
    · rw [pf_zero_right]
      refine ⟨?_, rfl⟩
      show (if 0 = j then (1 : ℂ) else 0) = 0
      rw [if_neg (by omega)]
    · rcases j with _ | j
      · rw [pf_zero_left]
        refine ⟨rfl, ?_⟩
        show (if 0 = k + 1 then (1 : ℂ) else 0) = 0
        rw [if_neg (by omega)]
      · rw [pf_succ]
        simp only
        have h1 := ih (j + 1 + k) (by omega) (j + 1) k rfl (by omega)
        have h2 := ih (j + (k + 1)) (by omega) j (k + 1) rfl (by omega)
        rw [h1.1, h2.1, h1.2, h2.2]
        simp

/-- Peel the indices `0` and `1` off a range sum. -/
theorem sum_range_peel_two {f : ℕ → ℂ} (n : ℕ) :
    ∑ i ∈ range (n + 2), f i = f 0 + f 1 + ∑ i ∈ range n, f (i + 2) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  ring

/-! ## 2. The zero sum of a monomial `x^j x′^k` -/

/-- The node relation `X + Y = (s − c)·X·Y` for `X = 1/(s−ρ)`, `Y = 1/(ρ−c)`. -/
theorem node_relation {s c ρ : ℂ} (hs : s - ρ ≠ 0) (hc : ρ - c ≠ 0) :
    (s - ρ)⁻¹ + (ρ - c)⁻¹ = (s - c) * (s - ρ)⁻¹ * (ρ - c)⁻¹ := by
  field_simp
  ring

/-- The paired first-order sum: `Σ' m_ρ (1/(s−ρ) + 1/(ρ−c)) = FP(s) − FP(c)`. -/
theorem tsum_pair_eq (s c : ℂ) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹ + (ρ.val - c)⁻¹)) ∧
    ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹ + (ρ.val - c)⁻¹)
      = xiFinitePart s - xiFinitePart c := by
  have h1 := summable_hadamard_term_any s
  have h2 := summable_hadamard_term_any c
  have hpt : ∀ ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹ + (ρ.val - c)⁻¹)
      = (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val s
        - (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val c := by
    intro ρ
    unfold hadamardTerm
    have : (ρ.val - c)⁻¹ = -(c - ρ.val)⁻¹ := by
      rw [← neg_sub, inv_neg]
    rw [this]
    simp only [one_div]
    ring
  refine ⟨(h1.sub h2).congr (fun ρ => (hpt ρ).symm), ?_⟩
  rw [tsum_congr hpt, h1.tsum_sub h2]
  unfold xiFinitePart
  ring

/-- The `Y`-moments are `(−1)^l` times the `zeroMoment`s at `c`. -/
theorem ymoment_eq (c : ℂ) (l : ℕ) :
    (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * ((ρ.val - c)⁻¹) ^ l)
      = fun ρ : Zero => (-1) ^ l * ((ZD.xiOrderNat ρ.val : ℂ) * ((c - ρ.val)⁻¹) ^ l) := by
  funext ρ
  have : (ρ.val - c)⁻¹ = -(c - ρ.val)⁻¹ := by rw [← neg_sub, inv_neg]
  rw [this, neg_pow]
  ring

/-- **The zero sum of one monomial**, `j, k ≥ 1`, `M ≥ j + k`, `M ≥ 2`: summable, and equal to
`a₁ (FP(s) − FP(c)) + Σ_{i} a_{i+2} zeroMoment (i+2) s + Σ_{l} b_{l+2} (−1)^{l+2} zeroMoment (l+2) c`. -/
theorem monomial_tsum {s c : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hc : c ∉ ZD.NontrivialZeros)
    (hd : s - c ≠ 0) {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) {M : ℕ} (hM : j + k ≤ M) (hM2 : 2 ≤ M) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹) ^ j * ((ρ.val - c)⁻¹) ^ k) ∧
    ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹) ^ j * ((ρ.val - c)⁻¹) ^ k
      = (pf (s - c) j k).1 1 * (xiFinitePart s - xiFinitePart c)
        + ∑ i ∈ range (M - 1), (pf (s - c) j k).1 (i + 2) * zeroMoment (i + 2) s
        + ∑ l ∈ range (M - 1), (pf (s - c) j k).2 (l + 2) * ((-1) ^ (l + 2) * zeroMoment (l + 2) c) := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
  have hM1 : M' + 2 - 1 = M' + 1 := by omega
  rw [hM1]
  have hz0 := pf_index_zero (s - c) (j + k) j k rfl (by omega)
  have hsym := pf_first_symm (s - c) (j + k) j k rfl hj hk
  -- pointwise decomposition
  have hpt : ∀ ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹) ^ j * ((ρ.val - c)⁻¹) ^ k
      = (pf (s - c) j k).1 1 * ((ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹ + (ρ.val - c)⁻¹))
        + ∑ i ∈ range (M' + 1), (pf (s - c) j k).1 (i + 2)
            * ((ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹) ^ (i + 2))
        + ∑ l ∈ range (M' + 1), (pf (s - c) j k).2 (l + 2)
            * ((ZD.xiOrderNat ρ.val : ℂ) * ((ρ.val - c)⁻¹) ^ (l + 2)) := by
    intro ρ
    have hsρ : s - ρ.val ≠ 0 := sub_ne_zero.mpr (fun h => hs (h ▸ ρ.2))
    have hρc : ρ.val - c ≠ 0 := sub_ne_zero.mpr (fun h => hc (h ▸ ρ.2))
    have hrel := node_relation hsρ hρc
    have hid := pf_identity hd hrel (M' + 2) (j + k) j k rfl hM
    rw [sum_range_peel_two, sum_range_peel_two] at hid
    rw [hz0.1, hz0.2, ← hsym] at hid
    have e1 : (ZD.xiOrderNat ρ.val : ℂ)
          * ∑ i ∈ range (M' + 1), (pf (s - c) j k).1 (i + 2) * ((s - ρ.val)⁻¹) ^ (i + 2)
        = ∑ i ∈ range (M' + 1), (pf (s - c) j k).1 (i + 2)
            * ((ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹) ^ (i + 2)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have e2 : (ZD.xiOrderNat ρ.val : ℂ)
          * ∑ l ∈ range (M' + 1), (pf (s - c) j k).2 (l + 2) * ((ρ.val - c)⁻¹) ^ (l + 2)
        = ∑ l ∈ range (M' + 1), (pf (s - c) j k).2 (l + 2)
            * ((ZD.xiOrderNat ρ.val : ℂ) * ((ρ.val - c)⁻¹) ^ (l + 2)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    linear_combination (ZD.xiOrderNat ρ.val : ℂ) * hid + e1 + e2
  -- summability of the pieces
  have hpair := tsum_pair_eq s c
  have hX : ∀ i : ℕ, Summable (fun ρ : Zero => (pf (s - c) j k).1 (i + 2)
      * ((ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹) ^ (i + 2))) :=
    fun i => (summable_zeroMoment (by omega) hs).mul_left _
  have hYm : ∀ l : ℕ, Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * ((ρ.val - c)⁻¹) ^ (l + 2)) := by
    intro l
    rw [ymoment_eq c (l + 2)]
    exact (summable_zeroMoment (by omega) hc).mul_left _
  have hY : ∀ l : ℕ, Summable (fun ρ : Zero => (pf (s - c) j k).2 (l + 2)
      * ((ZD.xiOrderNat ρ.val : ℂ) * ((ρ.val - c)⁻¹) ^ (l + 2))) :=
    fun l => (hYm l).mul_left _
  have hS1 := hpair.1.mul_left ((pf (s - c) j k).1 1)
  have hS2 : Summable (fun ρ : Zero => ∑ i ∈ range (M' + 1), (pf (s - c) j k).1 (i + 2)
      * ((ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹) ^ (i + 2))) :=
    summable_sum (fun i _ => hX i)
  have hS3 : Summable (fun ρ : Zero => ∑ l ∈ range (M' + 1), (pf (s - c) j k).2 (l + 2)
      * ((ZD.xiOrderNat ρ.val : ℂ) * ((ρ.val - c)⁻¹) ^ (l + 2))) :=
    summable_sum (fun l _ => hY l)
  refine ⟨((hS1.add hS2).add hS3).congr (fun ρ => (hpt ρ).symm), ?_⟩
  rw [tsum_congr hpt, (hS1.add hS2).tsum_add hS3, hS1.tsum_add hS2, tsum_mul_left, hpair.2,
    Summable.tsum_finsetSum (fun i _ => hX i), Summable.tsum_finsetSum (fun l _ => hY l)]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [tsum_mul_left]
    rfl
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [tsum_mul_left]
    congr 1
    rw [ymoment_eq c (l + 2), tsum_mul_left]
    rfl

/-! ## 3. The form as a finite functional of the zero moments -/

/-- The zero-side value of one monomial pair `(j, k)` after reduction: the coefficient functional. -/
def monomialValue (s c : ℂ) (M : ℕ) (j k : ℕ) : ℂ :=
  (pf (s - c) j k).1 1 * (xiFinitePart s - xiFinitePart c)
    + ∑ i ∈ range (M - 1), (pf (s - c) j k).1 (i + 2) * zeroMoment (i + 2) s
    + ∑ l ∈ range (M - 1), (pf (s - c) j k).2 (l + 2) * ((-1) ^ (l + 2) * zeroMoment (l + 2) c)

/-- `conj (R (conj X)) = Σ_j conj r_j X^j`. -/
theorem conj_eval_conj (R : Polynomial ℂ) (X : ℂ) :
    (starRingEnd ℂ) (R.eval ((starRingEnd ℂ) X))
      = ∑ j ∈ range (R.natDegree + 1), (starRingEnd ℂ) (R.coeff j) * X ^ j := by
  rw [Polynomial.eval_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, map_pow, Complex.conj_conj]

/-- The Hermitian term expanded into monomials of the two nodes. -/
theorem hermTerm_expand (w : ℂ) (R : Polynomial ℂ) (ρ : Zero) :
    hermTerm w R ρ
      = ∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
          ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
            * ((ZD.xiOrderNat ρ.val : ℂ) * (((1 / 2 : ℂ) + I * w - ρ.val)⁻¹) ^ j
                * ((ρ.val - ((1 / 2 : ℂ) + I * (starRingEnd ℂ) w))⁻¹) ^ k) := by
  unfold hermTerm
  rw [xnode_eq, xnode'_eq, conj_eval_conj, Polynomial.eval_eq_sum_range, Finset.sum_mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- **The seat form is a finite functional of the zero moments and the finite part.** For any `R`
with `R(0) = 0` and any anchor `w` with `s = ½ + i w` and `c = ½ + i w̄` off the zeros,
`hermForm w R = Σ_{j,k} conj(r_j) r_k · monomialValue s c (2N+2) j k`. No zero sum remains. -/
theorem hermForm_eq_monomialValues (w : ℂ) (R : Polynomial ℂ) (hR : R.coeff 0 = 0)
    (hs : (1 / 2 : ℂ) + I * w ∉ ZD.NontrivialZeros)
    (hc : (1 / 2 : ℂ) + I * (starRingEnd ℂ) w ∉ ZD.NontrivialZeros)
    (hd : (1 / 2 : ℂ) + I * w - ((1 / 2 : ℂ) + I * (starRingEnd ℂ) w) ≠ 0) :
    hermForm w R
      = ∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
          ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
            * monomialValue ((1 / 2 : ℂ) + I * w) ((1 / 2 : ℂ) + I * (starRingEnd ℂ) w)
                (2 * R.natDegree + 2) j k := by
  set s : ℂ := (1 / 2 : ℂ) + I * w with hsdef
  set c : ℂ := (1 / 2 : ℂ) + I * (starRingEnd ℂ) w with hcdef
  set N := R.natDegree with hN
  -- the family for each (j,k)
  set g : ℕ → ℕ → Zero → ℂ := fun j k ρ =>
    ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
      * ((ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹) ^ j * ((ρ.val - c)⁻¹) ^ k) with hg
  have hsumm : ∀ j ∈ range (N + 1), ∀ k ∈ range (N + 1), Summable (g j k) := by
    intro j hj k hk
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      have : g 0 k = fun _ => 0 := by
        funext ρ; simp [hg, hR]
      rw [this]; exact summable_zero
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have : g j 0 = fun _ => 0 := by
        funext ρ; simp [hg, hR]
      rw [this]; exact summable_zero
    have hjN := Finset.mem_range.mp hj
    have hkN := Finset.mem_range.mp hk
    exact (monomial_tsum hs hc hd hj0 hk0 (M := 2 * N + 2) (by omega) (by omega)).1.mul_left _
  have hval : ∀ j ∈ range (N + 1), ∀ k ∈ range (N + 1),
      ∑' ρ, g j k ρ = ((starRingEnd ℂ) (R.coeff j) * R.coeff k) * monomialValue s c (2 * N + 2) j k := by
    intro j hj k hk
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      simp [hg, hR]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      simp [hg, hR]
    have hjN := Finset.mem_range.mp hj
    have hkN := Finset.mem_range.mp hk
    have h := (monomial_tsum hs hc hd hj0 hk0 (M := 2 * N + 2) (by omega) (by omega)).2
    simp only [hg]
    rw [tsum_mul_left, h]
    rfl
  unfold hermForm
  have hexp : ∀ ρ : Zero, hermTerm w R ρ = ∑ j ∈ range (N + 1), ∑ k ∈ range (N + 1), g j k ρ :=
    fun ρ => hermTerm_expand w R ρ
  rw [tsum_congr hexp, Summable.tsum_finsetSum (fun j hj => summable_sum (fun k hk => hsumm j hj k hk))]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Summable.tsum_finsetSum (fun k hk => hsumm j hj k hk)]
  exact Finset.sum_congr rfl (fun k hk => hval j hj k hk)

/-! ## 4. Moments and finite part as jets of `ξ′/ξ` -/

/-- `c = ½ + i w̄` is the mirror `1 − s̄` of `s = ½ + i w`. -/
theorem mirror_anchor (w : ℂ) :
    (1 / 2 : ℂ) + I * (starRingEnd ℂ) w = 1 - (starRingEnd ℂ) ((1 / 2 : ℂ) + I * w) := by
  apply Complex.ext <;> simp
  ring

/-- `FP(s) − FP(1 − s̄) = 2 Re FP(s)`. -/
theorem fp_pair (s : ℂ) :
    xiFinitePart s - xiFinitePart (1 - (starRingEnd ℂ) s) = 2 * ((xiFinitePart s).re : ℂ) := by
  rw [xiFinitePart_one_sub, xiFinitePart_conj, sub_neg_eq_add, Complex.add_conj]
  push_cast
  ring

/-- The `(i+2)`-nd zero moment is the `(i+1)`-st jet of `ξ′/ξ`, normalised. -/
theorem zeroMoment_eq_jet {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (i : ℕ) :
    zeroMoment (i + 2) s
      = iteratedDeriv (i + 1) (logDeriv ZD.riemannXi) s / ((-1) ^ (i + 1) * ((i + 1).factorial : ℂ)) := by
  rw [hadamard_jet (k := i + 1) (by omega) hs]
  have h : ((-1 : ℂ) ^ (i + 1) * ((i + 1).factorial : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [mul_div_cancel_left₀ _ h]
  rfl

/-- The jet functional of one monomial pair `(j, k)`: first-order coefficient times `2 Re ξ′/ξ(s)`,
plus the higher `s`-jets, plus the higher `c`-jets. -/
def jetValue (s c : ℂ) (M : ℕ) (j k : ℕ) : ℂ :=
  (pf (s - c) j k).1 1 * (2 * ((logDeriv ZD.riemannXi s).re : ℂ))
    + ∑ i ∈ range (M - 1), (pf (s - c) j k).1 (i + 2)
        * (iteratedDeriv (i + 1) (logDeriv ZD.riemannXi) s / ((-1) ^ (i + 1) * ((i + 1).factorial : ℂ)))
    + ∑ l ∈ range (M - 1), (pf (s - c) j k).2 (l + 2)
        * ((-1) ^ (l + 2)
            * (iteratedDeriv (l + 1) (logDeriv ZD.riemannXi) c / ((-1) ^ (l + 1) * ((l + 1).factorial : ℂ))))

theorem monomialValue_eq_jetValue (w : ℂ) (M j k : ℕ)
    (hs : (1 / 2 : ℂ) + I * w ∉ ZD.NontrivialZeros)
    (hc : (1 / 2 : ℂ) + I * (starRingEnd ℂ) w ∉ ZD.NontrivialZeros) :
    monomialValue ((1 / 2 : ℂ) + I * w) ((1 / 2 : ℂ) + I * (starRingEnd ℂ) w) M j k
      = jetValue ((1 / 2 : ℂ) + I * w) ((1 / 2 : ℂ) + I * (starRingEnd ℂ) w) M j k := by
  unfold monomialValue jetValue
  congr 1
  · congr 1
    · congr 1
      rw [mirror_anchor, fp_pair, xiFinitePart_eq_logDeriv hs]
    · exact Finset.sum_congr rfl (fun i _ => by rw [zeroMoment_eq_jet hs i])
  · exact Finset.sum_congr rfl (fun l _ => by rw [zeroMoment_eq_jet hc l])

/-- **The seat form is a finite functional of the jets of `ξ′/ξ`** at `s = ½ + i w` and its mirror
`c = 1 − s̄`. No zero sum, no residue, no hypothesis on the zeros. -/
theorem hermForm_eq_jets (w : ℂ) (R : Polynomial ℂ) (hR : R.coeff 0 = 0)
    (hs : (1 / 2 : ℂ) + I * w ∉ ZD.NontrivialZeros)
    (hc : (1 / 2 : ℂ) + I * (starRingEnd ℂ) w ∉ ZD.NontrivialZeros)
    (hd : (1 / 2 : ℂ) + I * w - ((1 / 2 : ℂ) + I * (starRingEnd ℂ) w) ≠ 0) :
    hermForm w R
      = ∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
          ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
            * jetValue ((1 / 2 : ℂ) + I * w) ((1 / 2 : ℂ) + I * (starRingEnd ℂ) w)
                (2 * R.natDegree + 2) j k := by
  rw [hermForm_eq_monomialValues w R hR hs hc hd]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [monomialValue_eq_jetValue w _ j k hs hc]

/-! ## 5. At the door's anchors: the prime chart -/

theorem anchor_s (γ σ₀ : ℝ) :
    (1 / 2 : ℂ) + I * CriticalLinePhasor.SeatPrimeAnchor.anchor γ σ₀ = (σ₀ : ℂ) + (γ : ℂ) * I := by
  unfold CriticalLinePhasor.SeatPrimeAnchor.anchor
  apply Complex.ext <;> simp

theorem anchor_c (γ σ₀ : ℝ) :
    (1 / 2 : ℂ) + I * (starRingEnd ℂ) (CriticalLinePhasor.SeatPrimeAnchor.anchor γ σ₀)
      = ((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I := by
  unfold CriticalLinePhasor.SeatPrimeAnchor.anchor
  apply Complex.ext <;> simp
  ring

theorem anchor_s_not_zero {γ σ₀ : ℝ} (h : 1 < σ₀) :
    (σ₀ : ℂ) + (γ : ℂ) * I ∉ ZD.NontrivialZeros := by
  intro hmem
  have := hmem.2.1
  simp at this
  linarith

theorem anchor_c_not_zero {γ σ₀ : ℝ} (h : 1 < σ₀) :
    ((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I ∉ ZD.NontrivialZeros := by
  intro hmem
  have := hmem.1
  simp at this
  linarith

/-- **The seat form at the door's anchor, as jets.** For `1 < σ₀`, every `γ`, and every `R` with
`R(0) = 0`, `hermForm (anchor γ σ₀) R` is the finite jet functional at `s = σ₀ + iγ`, `c = 1 − σ₀ + iγ`. -/
theorem hermForm_anchor_eq_jets (γ σ₀ : ℝ) (h : 1 < σ₀) (R : Polynomial ℂ) (hR : R.coeff 0 = 0) :
    hermForm (CriticalLinePhasor.SeatPrimeAnchor.anchor γ σ₀) R
      = ∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
          ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
            * jetValue ((σ₀ : ℂ) + (γ : ℂ) * I) (((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I)
                (2 * R.natDegree + 2) j k := by
  have hs := anchor_s γ σ₀
  have hc := anchor_c γ σ₀
  have hd : (σ₀ : ℂ) + (γ : ℂ) * I - (((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  rw [hermForm_eq_jets _ R hR (hs ▸ anchor_s_not_zero h) (hc ▸ anchor_c_not_zero h)
    (by rw [hs, hc]; exact hd), hs, hc]

/-- **The door, read on the prime side.** RH ⟺ for all `γ`, all `1 < σ₀ < 3/2`, all `R` with
`R(0) = 0`: `Re Σ_{j,k} conj(r_j) r_k · jetValue(σ₀+iγ, 1−σ₀+iγ) j k ≥ 0`. The right-hand side
mentions only the jets of `ξ′/ξ` at points with `Re s > 1` and `Re s < 0`. -/
theorem rh_iff_jets_nonneg :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) ↔
    (∀ γ σ₀ : ℝ, 1 < σ₀ → σ₀ < 3 / 2 → ∀ R : Polynomial ℂ, R.coeff 0 = 0 →
      0 ≤ (∑ j ∈ range (R.natDegree + 1), ∑ k ∈ range (R.natDegree + 1),
          ((starRingEnd ℂ) (R.coeff j) * R.coeff k)
            * jetValue ((σ₀ : ℂ) + (γ : ℂ) * I) (((1 - σ₀ : ℝ) : ℂ) + (γ : ℂ) * I)
                (2 * R.natDegree + 2) j k).re) := by
  rw [rh_iff_hermForm_nonneg]
  constructor
  · intro H γ σ₀ h1 h2 R hR
    rw [← hermForm_anchor_eq_jets γ σ₀ h1 R hR]
    exact H γ σ₀ h1 h2 R hR
  · intro H γ σ₀ h1 h2 R hR
    rw [hermForm_anchor_eq_jets γ σ₀ h1 R hR]
    exact H γ σ₀ h1 h2 R hR

#print axioms hermForm_eq_monomialValues
#print axioms hermForm_eq_jets
#print axioms rh_iff_jets_nonneg

end CriticalLinePhasor.ContourArgument
