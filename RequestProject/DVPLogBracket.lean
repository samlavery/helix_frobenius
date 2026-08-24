import RequestProject.DVPPilotStation

/-!
# The batch instruments for the `t = 58` segment certificate

Four general lemmas that turn the station sweep into kernel arithmetic:

* `log_bracket` — the packaged log certificate: `lo ≤ log p ≤ hi` from two
  order-9 `expTaylor` kernel checks (one invocation per `n = 2..100`, ~6
  lines each, instead of ~55 lines of hand plumbing).
* `rpow_neg_rat_bracket` — `q ≤ n^{−k/d} ≤ q′` from `q^d·n^k` comparisons:
  every σ-weight in the sweep is ALGEBRAIC (rational roots), so no
  transcendental certificate is spent on the weights at all.
* `abel_icc_lower` — the sharp Abel lower bound with antitone nonnegative
  weights: `∑ w·c ≥ (w_M − w_N)·Cmin + w_N·C_N`.  This is the DC move of
  the whole campaign: at fixed `t = 58` the cosines are STATION-FREE, the
  σ-dependence enters only through a monotone envelope, and one partial-sum
  floor replaces ~235 stations.
* `mul_lower_of_bracket` — the signed head-term bound.
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The packaged log certificate.**  `lo ≤ log p ≤ hi` from order-9
`expTaylor` kernel checks at the shifted arguments; `10/3265920` is the
exact order-9 tail factor `(9+1)/(9!·9)`. -/
theorem log_bracket {p : ℕ} {lo hi : ℚ} (m : ℕ) (hp : 1 ≤ p)
    (hlo1 : |lo - m| ≤ 1) (hhi1 : |hi - m| ≤ 1)
    (hup : (expTaylor (lo - m) 9 + |lo - m| ^ 9 * (10/3265920))
        * (2.7182818286 : ℚ) ^ m ≤ p)
    (hpos : 0 ≤ expTaylor (hi - m) 9 - |hi - m| ^ 9 * (10/3265920))
    (hdn : (p : ℚ) ≤ (expTaylor (hi - m) 9 - |hi - m| ^ 9 * (10/3265920))
        * (2.7182818283 : ℚ) ^ m) :
    ((lo : ℚ) : ℝ) ≤ Real.log p ∧ Real.log p ≤ ((hi : ℚ) : ℝ) := by
  have h9 : (0:ℕ) < 9 := by norm_num
  -- upper comparison: exp lo ≤ p
  have henc1 := exp_enclosure (x := lo - m) hlo1 h9
  have hbr1 : |((lo - m : ℚ) : ℝ)| ^ 9
      * (((9:ℕ).succ : ℝ) / (((9:ℕ).factorial : ℝ) * 9))
      ≤ ((|lo - m| ^ 9 * (10/3265920) : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]
    push_cast
    norm_num [Nat.factorial]
  have hτ1 := le_trans henc1 hbr1
  have hshift1 := exp_upper_shift (x := lo) m hτ1
  have h1 : Real.exp lo ≤ p := by
    refine le_trans hshift1 ?_
    exact_mod_cast hup
  -- lower comparison: p ≤ exp hi
  have henc2 := exp_enclosure (x := hi - m) hhi1 h9
  have hbr2 : |((hi - m : ℚ) : ℝ)| ^ 9
      * (((9:ℕ).succ : ℝ) / (((9:ℕ).factorial : ℝ) * 9))
      ≤ ((|hi - m| ^ 9 * (10/3265920) : ℚ) : ℝ) := by
    rw [← Rat.cast_abs]
    push_cast
    norm_num [Nat.factorial]
  have hτ2 := le_trans henc2 hbr2
  have hshift2 := exp_lower_shift (x := hi) m hτ2 hpos
  have h2 : (p : ℝ) ≤ Real.exp hi := by
    refine le_trans ?_ hshift2
    exact_mod_cast hdn
  exact log_enclosure_nat hp h1 h2

/-- **The algebraic weight bracket.**  `qlo ≤ n^{−k/d} ≤ qhi` from the pure
kernel comparisons `qlo^d·n^k ≤ 1 ≤ qhi^d·n^k`. -/
theorem rpow_neg_rat_bracket {n k d : ℕ} {qlo qhi : ℚ} (hn : 1 ≤ n)
    (hd : 0 < d) (hlo0 : 0 ≤ qlo) (hhi0 : 0 ≤ qhi)
    (hker_lo : qlo ^ d * (n : ℚ) ^ k ≤ 1)
    (hker_hi : 1 ≤ qhi ^ d * (n : ℚ) ^ k) :
    ((qlo : ℚ) : ℝ) ≤ (n : ℝ) ^ (-((k : ℝ) / (d : ℝ)))
      ∧ (n : ℝ) ^ (-((k : ℝ) / (d : ℝ))) ≤ ((qhi : ℚ) : ℝ) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  set x : ℝ := (n : ℝ) ^ (-((k : ℝ) / (d : ℝ))) with hxdef
  have hxpos : (0:ℝ) < x := Real.rpow_pos_of_pos hn0 _
  have hxpow : x ^ d * (n : ℝ) ^ k = 1 := by
    have h1 : x ^ d = (n : ℝ) ^ (-(k : ℝ)) := by
      rw [hxdef, ← Real.rpow_natCast ((n : ℝ) ^ (-((k : ℝ) / (d : ℝ)))) d,
        ← Real.rpow_mul hn0.le]
      congr 1
      rw [neg_mul, div_mul_cancel₀ _ hd0.ne']
    have h2 : (n : ℝ) ^ k = (n : ℝ) ^ ((k : ℕ) : ℝ) :=
      (Real.rpow_natCast _ k).symm
    rw [h1, h2, ← Real.rpow_add hn0]
    simp
  have hnk : (0:ℝ) < (n : ℝ) ^ k := pow_pos hn0 k
  have hlo0' : (0:ℝ) ≤ (qlo : ℝ) := by exact_mod_cast hlo0
  have hhi0' : (0:ℝ) ≤ (qhi : ℝ) := by exact_mod_cast hhi0
  have hker_lo' : (qlo : ℝ) ^ d * (n : ℝ) ^ k ≤ 1 := by exact_mod_cast hker_lo
  have hker_hi' : (1:ℝ) ≤ (qhi : ℝ) ^ d * (n : ℝ) ^ k := by
    exact_mod_cast hker_hi
  constructor
  · by_contra hc
    push_neg at hc
    have hpow : x ^ d < (qlo : ℝ) ^ d :=
      pow_lt_pow_left₀ hc hxpos.le (by omega)
    nlinarith [hxpow, hker_lo', hnk]
  · by_contra hc
    push_neg at hc
    have hpow : (qhi : ℝ) ^ d < x ^ d :=
      pow_lt_pow_left₀ hc hhi0' (by omega)
    nlinarith [hxpow, hker_hi', hnk]

/-- **The sharp Abel lower bound.**  Antitone nonnegative weights against a
partial-sum floor:
`∑_{k∈[M,N]} w_k·c_k ≥ (w_M − w_N)·Cmin + w_N·∑_{k∈[M,N]} c_k`. -/
theorem abel_icc_lower {c w : ℕ → ℝ} {M : ℕ} {Cmin : ℝ} :
    ∀ N, M ≤ N →
    (∀ k, M ≤ k → w (k+1) ≤ w k) →
    (∀ k, M ≤ k → 0 ≤ w k) →
    (∀ j, M ≤ j → j ≤ N → Cmin ≤ ∑ k ∈ Finset.Icc M j, c k) →
    (w M - w N) * Cmin + w N * (∑ k ∈ Finset.Icc M N, c k)
      ≤ ∑ k ∈ Finset.Icc M N, w k * c k := by
  intro N
  induction N with
  | zero =>
    intro hMN _ _ _
    interval_cases M
    simp [Finset.Icc_self]
  | succ N ih =>
    intro hMN hanti hnonneg hfloor
    rcases Nat.lt_or_ge M (N+1) with hlt | hge
    · -- M ≤ N: peel the top term
      have hMN' : M ≤ N := Nat.lt_succ_iff.mp hlt
      have hIH := ih hMN' hanti hnonneg
        (fun j hj1 hj2 => hfloor j hj1 (le_trans hj2 (Nat.le_succ N)))
      have htop : ∑ k ∈ Finset.Icc M (N+1), c k
          = (∑ k ∈ Finset.Icc M N, c k) + c (N+1) :=
        Finset.sum_Icc_succ_top (le_trans hMN' (Nat.le_succ N)) c
      have htopw : ∑ k ∈ Finset.Icc M (N+1), (fun k => w k * c k) k
          = (∑ k ∈ Finset.Icc M N, w k * c k) + w (N+1) * c (N+1) :=
        Finset.sum_Icc_succ_top (le_trans hMN' (Nat.le_succ N))
          (fun k => w k * c k)
      have hCN : Cmin ≤ ∑ k ∈ Finset.Icc M N, c k :=
        hfloor N hMN' (Nat.le_succ N)
      have hstep : (0:ℝ) ≤ (w N - w (N+1))
          * ((∑ k ∈ Finset.Icc M N, c k) - Cmin) :=
        mul_nonneg (by linarith [hanti N hMN']) (by linarith [hCN])
      rw [htop, htopw]
      nlinarith [hIH, hstep]
    · -- M = N+1: singleton
      have heq : M = N + 1 := le_antisymm hMN hge
      subst heq
      simp [Finset.Icc_self]

/-- **The signed head-term bound.**  For a weight in `[wlo, whi]` (both
nonnegative) and a factor `≥ clo`: `w·c ≥ wlo·clo` if `0 ≤ clo`, and
`w·c ≥ whi·clo` if `clo ≤ 0`.  Stated as the single usable disjunction. -/
theorem mul_lower_of_bracket {w cv wlo whi clo : ℝ}
    (hw1 : wlo ≤ w) (hw2 : w ≤ whi) (hwlo : 0 ≤ wlo)
    (hc : clo ≤ cv) :
    (0 ≤ clo → wlo * clo ≤ w * cv) ∧ (clo ≤ 0 → whi * clo ≤ w * cv) := by
  constructor
  · intro hclo
    have h1 : wlo * clo ≤ w * clo := mul_le_mul_of_nonneg_right hw1 hclo
    have h2 : w * clo ≤ w * cv :=
      mul_le_mul_of_nonneg_left hc (le_trans hwlo hw1)
    linarith
  · intro hclo
    have h1 : whi * clo ≤ w * clo := by nlinarith
    have h2 : w * clo ≤ w * cv :=
      mul_le_mul_of_nonneg_left hc (le_trans hwlo hw1)
    linarith

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.log_bracket
#print axioms CriticalLinePhasor.DVP.rpow_neg_rat_bracket
#print axioms CriticalLinePhasor.DVP.abel_icc_lower
#print axioms CriticalLinePhasor.DVP.mul_lower_of_bracket
end AxiomAudit
