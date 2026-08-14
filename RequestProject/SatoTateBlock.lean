import RequestProject.SatoTateQuadrature
import RequestProject.RoundedWeights
import RequestProject.ChebyshevBound

/-!
# One Sato--Tate block, assembled

Everything the block needs is compiled, so this file puts it together: for each node count `n` and
each multiplicity budget `L`, the explicit finite **equal-weight** family that repeats the `i`-th
Gauss--Chebyshev node `⌊L·wᵢ⌋` times has

  **`|average of U_r| ≤ n·(r+1)/(L − n)`  for every `1 ≤ r` with `r + 2 < 2n`.**

Node count and budget are independent: `n` decides *how many ranks* are reached, `L` decides *how
small* the error is on them.  Both are free, which is exactly what a block sequence needs.

The inputs: `chebyshevU_nodeSum_eq_zero` (the weighted sum is exactly zero — this is what makes the
bound independent of `L`), `abs_chebyshevU_cos_le` (`B = r+1`), and `rounded_average_bound`.

**Scope.**  One block.  Concatenating blocks into a single sequence and inhabiting the corpus's
cancellation structure remain; nothing here concerns any arithmetic family.
-/

open Polynomial Polynomial.Chebyshev

namespace CriticalLinePhasor.ThreeDConverse

/-- The `i`-th Gauss--Chebyshev angle for node count `n`. -/
noncomputable def stAngle (n i : ℕ) : ℝ := (2 * (i : ℝ) + 1) / (2 * n) * Real.pi

/-- The `i`-th node. -/
noncomputable def stNode (n i : ℕ) : ℝ := Real.cos (stAngle n i)

/-- The unnormalised Sato--Tate mass at the node, `1 − x² = sin²θ`. -/
noncomputable def stMass (n i : ℕ) : ℝ := 1 - (stNode n i) ^ 2

lemma stAngle_pos {n i : ℕ} (hn : 0 < n) : 0 < stAngle n i := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have : 0 < (2 * (i : ℝ) + 1) / (2 * n) := by positivity
  exact mul_pos this Real.pi_pos

lemma stAngle_lt_pi {n i : ℕ} (hi : i < n) : stAngle n i < Real.pi := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le i) hi)
  have hir : (i : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hi
  have hlt : (2 * (i : ℝ) + 1) / (2 * n) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  calc stAngle n i = (2 * (i : ℝ) + 1) / (2 * n) * Real.pi := rfl
    _ < 1 * Real.pi := mul_lt_mul_of_pos_right hlt Real.pi_pos
    _ = Real.pi := one_mul _

lemma stMass_pos {n i : ℕ} (hi : i < n) : 0 < stMass n i := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i) hi
  have hs : 0 < Real.sin (stAngle n i) :=
    Real.sin_pos_of_pos_of_lt_pi (stAngle_pos hn) (stAngle_lt_pi hi)
  have hid : Real.sin (stAngle n i) ^ 2 = 1 - Real.cos (stAngle n i) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (stAngle n i); linarith
  rw [stMass, stNode, ← hid]
  positivity

lemma stTotal_pos {n : ℕ} (hn : 0 < n) : 0 < ∑ i ∈ Finset.range n, stMass n i :=
  Finset.sum_pos (fun i hi => stMass_pos (Finset.mem_range.mp hi))
    ⟨0, Finset.mem_range.mpr hn⟩

/-- The normalised Sato--Tate weight at the node. -/
noncomputable def stWeight (n i : ℕ) : ℝ := stMass n i / ∑ j ∈ Finset.range n, stMass n j

lemma stWeight_sum {n : ℕ} (hn : 0 < n) : ∑ i ∈ Finset.range n, stWeight n i = 1 := by
  simp only [stWeight, ← Finset.sum_div]
  exact div_self (stTotal_pos hn).ne'

/-- **The weights annihilate every rank the block reaches.**  Exactly zero, no error term. -/
theorem stWeight_chebyshev_sum_zero {n r : ℕ} (hn : 0 < n) (hr : 1 ≤ r)
    (hdeg : ((U ℝ (r : ℤ)) * (1 - X ^ 2)).degree < 2 * (n : WithBot ℕ)) :
    ∑ i ∈ Finset.range n, stWeight n i * (U ℝ (r : ℤ)).eval (stNode n i) = 0 := by
  have hnode := chebyshevU_nodeSum_eq_zero hn.ne' hr hdeg
  have hmass : ∑ i ∈ Finset.range n, stMass n i * (U ℝ (r : ℤ)).eval (stNode n i) = 0 := by
    rw [← hnode]
    exact Finset.sum_congr rfl fun i _ => by rw [stMass, stNode, stAngle]; ring
  simp only [stWeight, div_mul_eq_mul_div, ← Finset.sum_div, hmass, zero_div]

/-- **One block.**  The equal-weight family repeating node `i` exactly `⌊L·wᵢ⌋` times has
`U_r`-average at most `n(r+1)/(L−n)`, for every rank the block reaches. -/
theorem satoTate_block_bound {n r : ℕ} (hn : 0 < n) (hr : 1 ≤ r)
    (hdeg : ((U ℝ (r : ℤ)) * (1 - X ^ 2)).degree < 2 * (n : WithBot ℕ))
    {L : ℝ} (hL : (n : ℝ) < L) :
    |∑ i : Fin n, ((⌊L * stWeight n (i : ℕ)⌋ : ℤ) : ℝ) *
        (U ℝ (r : ℤ)).eval (stNode n (i : ℕ))|
        / (∑ i : Fin n, ((⌊L * stWeight n (i : ℕ)⌋ : ℤ) : ℝ))
      ≤ (n : ℝ) * ((r : ℝ) + 1) / (L - n) := by
  refine rounded_average_bound (fun i : Fin n => stWeight n (i : ℕ))
    (fun i : Fin n => (U ℝ (r : ℤ)).eval (stNode n (i : ℕ))) L ((r : ℝ) + 1) ?_ ?_ ?_ hL
    (by positivity)
  · rw [Fin.sum_univ_eq_sum_range (fun i => stWeight n i) n]
    exact stWeight_sum hn
  · rw [Fin.sum_univ_eq_sum_range
      (fun i => stWeight n i * (U ℝ (r : ℤ)).eval (stNode n i)) n]
    exact stWeight_chebyshev_sum_zero hn hr hdeg
  · exact fun i => abs_chebyshevU_cos_le r (stAngle n (i : ℕ))


/-! ## Odd ranks carry no rounding error at all

The Gauss--Chebyshev nodes are reflection-symmetric (`x_{n-1-i} = −x_i`) and so are the Sato--Tate
weights, hence so are the rounded multiplicities.  Since `U_r(−x) = (−1)^r U_r(x)`, the pairing
`i ↔ n−1−i` kills every **odd** rank *exactly* — before any error estimate.  So the
`n(r+1)/(L−n)` bound of `satoTate_block_bound` is only doing work on even ranks. -/

lemma stAngle_reflect {n i : ℕ} (hi : i < n) :
    stAngle n (n - 1 - i) = Real.pi - stAngle n i := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i) hi
  have hin : i ≤ n - 1 := Nat.le_sub_one_of_lt hi
  have hcast : ((n - 1 - i : ℕ) : ℝ) = (n : ℝ) - 1 - (i : ℝ) := by
    rw [Nat.cast_sub hin, Nat.cast_sub hn, Nat.cast_one]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [stAngle, stAngle, hcast]
  field_simp
  ring

lemma stNode_reflect {n i : ℕ} (hi : i < n) :
    stNode n (n - 1 - i) = -stNode n i := by
  rw [stNode, stNode, stAngle_reflect hi, Real.cos_pi_sub]

lemma stMass_reflect {n i : ℕ} (hi : i < n) :
    stMass n (n - 1 - i) = stMass n i := by
  rw [stMass, stMass, stNode_reflect hi, neg_pow, neg_one_pow_two, one_mul]

lemma stWeight_reflect {n i : ℕ} (hi : i < n) :
    stWeight n (n - 1 - i) = stWeight n i := by
  rw [stWeight, stWeight, stMass_reflect hi]

/-- **Odd ranks cancel exactly**, for every budget `L`, with no error term. -/
theorem satoTate_block_odd_exact {n r : ℕ} (hodd : Odd r) (L : ℝ) :
    ∑ i ∈ Finset.range n, ((⌊L * stWeight n i⌋ : ℤ) : ℝ) *
      (U ℝ (r : ℤ)).eval (stNode n i) = 0 := by
  set g : ℕ → ℝ := fun i => ((⌊L * stWeight n i⌋ : ℤ) : ℝ) *
    (U ℝ (r : ℤ)).eval (stNode n i) with hg
  have hrefl : ∀ i ∈ Finset.range n, g (n - 1 - i) = -g i := by
    intro i hi
    have hin := Finset.mem_range.mp hi
    have hU : (U ℝ (r : ℤ)).eval (stNode n (n - 1 - i))
        = -(U ℝ (r : ℤ)).eval (stNode n i) := by
      rw [stNode_reflect hin]
      rw [U_eval_neg ℝ r (stNode n i),
        Int.negOnePow_odd (r : ℤ) (by exact_mod_cast hodd)]
      push_cast
      ring
    rw [hg]
    simp only
    rw [stWeight_reflect hin, hU]
    ring
  have hsum : ∑ i ∈ Finset.range n, g i = -∑ i ∈ Finset.range n, g i := by
    conv_lhs => rw [← Finset.sum_range_reflect g n]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hrefl
  linarith [hsum]


/-! ## The total mass is exactly `n/2`

Applying the quadrature to the constant polynomial evaluates the normalising constant outright:
`∫_0^π sin²θ dθ = π/2` on one side, `(π/n)·∑ stMass` on the other.  So the weights are fully
explicit, `stWeight n i = 2·sin²θᵢ / n`, with no implicit normalisation left in the construction. -/

theorem stTotal_eq {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Finset.range n, stMass n i = (n : ℝ) / 2 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hdeg : ((1 : ℝ[X]) * (1 - X ^ 2)).degree < 2 * (n : WithBot ℕ) := by
    have h2 : ((1 : ℝ[X]) * (1 - X ^ 2)).degree ≤ 2 := by
      rw [one_mul]; compute_degree
    refine lt_of_le_of_lt h2 ?_
    have : (2 : ℕ) < 2 * n := by omega
    exact_mod_cast this
  have hq := satoTate_quadrature hn0.ne' hdeg
  have hlhs : (∫ θ in (0:ℝ)..Real.pi, (1 : ℝ[X]).eval (Real.cos θ) * Real.sin θ ^ 2)
      = Real.pi / 2 := by
    simp only [Polynomial.eval_one, one_mul]
    rw [integral_sin_sq]
    simp
  have hrhs : sumZeroes n ((1 : ℝ[X]) * (1 - X ^ 2))
      = (Real.pi / n) * ∑ i ∈ Finset.range n, stMass n i := by
    rw [sumZeroes]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [stMass, stNode, stAngle]
    simp
  rw [hlhs, hrhs] at hq
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
  field_simp at hq
  linarith

/-- The weights, explicitly: `stWeight n i = 2·sin²θᵢ / n`. -/
theorem stWeight_eq {n : ℕ} (hn : 2 ≤ n) (i : ℕ) :
    stWeight n i = 2 * stMass n i / n := by
  rw [stWeight, stTotal_eq hn]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp


/-! ## The existence interface

The form a concatenation argument consumes: for every rank ceiling `R` and every tolerance `ε`,
some block cancels *all* ranks up to `R` to within `ε`.  Node count `n = R + 2` fixes the ranks
reached; the budget `L` is then chosen against `ε`. -/

lemma degree_U_mul_one_sub_sq {r n : ℕ} (h : r + 2 < 2 * n) :
    ((U ℝ (r : ℤ)) * (1 - X ^ 2)).degree < 2 * (n : WithBot ℕ) := by
  have hU : (U ℝ (r : ℤ)).degree = (r : WithBot ℕ) := degree_U_natCast ℝ r
  have hq : ((1 : ℝ[X]) - X ^ 2).degree = (2 : WithBot ℕ) := by compute_degree!
  rw [degree_mul, hU, hq]
  have : (r : WithBot ℕ) + 2 = ((r + 2 : ℕ) : WithBot ℕ) := by push_cast; ring
  rw [this]
  have h2 : ((2 * n : ℕ) : WithBot ℕ) = 2 * (n : WithBot ℕ) := by push_cast; ring
  rw [← h2]
  exact_mod_cast h

/-- **Some block cancels every rank up to `R` to within `ε`.** -/
theorem exists_satoTate_block (R : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ L : ℝ, (n : ℝ) < L ∧
      ∀ r : ℕ, 1 ≤ r → r ≤ R →
        |∑ i : Fin n, ((⌊L * stWeight n (i : ℕ)⌋ : ℤ) : ℝ) *
            (U ℝ (r : ℤ)).eval (stNode n (i : ℕ))|
            / (∑ i : Fin n, ((⌊L * stWeight n (i : ℕ)⌋ : ℤ) : ℝ)) < ε := by
  refine ⟨R + 2, by omega, (R + 2 : ℝ) + (R + 2 : ℝ) * ((R : ℝ) + 1) / ε + 1, ?_, ?_⟩
  · have : 0 < (R + 2 : ℝ) * ((R : ℝ) + 1) / ε := by positivity
    push_cast
    linarith
  · intro r hr hrR
    have hn : 0 < R + 2 := by omega
    have hdeg : ((U ℝ (r : ℤ)) * (1 - X ^ 2)).degree < 2 * ((R + 2 : ℕ) : WithBot ℕ) :=
      degree_U_mul_one_sub_sq (by omega)
    have hLpos : ((R + 2 : ℕ) : ℝ)
        < (R + 2 : ℝ) + (R + 2 : ℝ) * ((R : ℝ) + 1) / ε + 1 := by
      have : 0 < (R + 2 : ℝ) * ((R : ℝ) + 1) / ε := by positivity
      push_cast
      linarith
    have hb := satoTate_block_bound hn hr hdeg hLpos
    refine lt_of_le_of_lt hb ?_
    have hden : (R + 2 : ℝ) + (R + 2 : ℝ) * ((R : ℝ) + 1) / ε + 1 - ((R + 2 : ℕ) : ℝ)
        = (R + 2 : ℝ) * ((R : ℝ) + 1) / ε + 1 := by push_cast; ring
    rw [hden]
    have hdpos : (0 : ℝ) < (R + 2 : ℝ) * ((R : ℝ) + 1) / ε + 1 := by positivity
    rw [div_lt_iff₀ hdpos]
    have hrR' : ((r : ℝ) + 1) ≤ ((R : ℝ) + 1) := by
      have : (r : ℝ) ≤ (R : ℝ) := Nat.cast_le.mpr hrR
      linarith
    have hnn : (0 : ℝ) < ((R + 2 : ℕ) : ℝ) := by push_cast; positivity
    have hkey : ((R + 2 : ℕ) : ℝ) * ((r : ℝ) + 1) ≤ (R + 2 : ℝ) * ((R : ℝ) + 1) := by
      push_cast
      nlinarith
    have hexp : ε * ((R + 2 : ℝ) * ((R : ℝ) + 1) / ε + 1)
        = (R + 2 : ℝ) * ((R : ℝ) + 1) + ε := by
      field_simp
    nlinarith [hexp, hkey, hε]

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.satoTate_block_bound
#print axioms CriticalLinePhasor.ThreeDConverse.satoTate_block_odd_exact
#print axioms CriticalLinePhasor.ThreeDConverse.stTotal_eq
#print axioms CriticalLinePhasor.ThreeDConverse.exists_satoTate_block
