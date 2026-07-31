import Mathlib

/-!
# The rank-ladder parity closure: exact ξ-channel cancellation at every odd rank

The carrier-native trace-formula ladder (`tmp/rank_ladder_closure.py` measures it
on the real master-formula dual terms): the elliptic dual term at rank `r` is

  `dual_ξ = w(ξ) · ∫_{-1}^{1} Φ(x) · U_r(x) · e^{-2πi x ξ c} dx`,

with `Φ` the (even) orbital profile, `U_r` the Chebyshev second-kind Satake
character of `Sym^r`, and `w` the (even) Kloosterman/prefactor weight.  This file
proves, uniformly in the rank:

* `chebU_neg` — the `(r+1)`-clock parity `U_r(-x) = (-1)^r U_r(x)`.
* `dualIntegral_neg` — the μ₂ parity clock on the dual variable:
  `I_r(-ξ) = (-1)^r I_r(ξ)`, with the odd/even specializations.
* `dualIntegral_zero_odd` — the DC term vanishes at every odd rank.
* `latticeSum_eq_zero_odd` — the signed ξ-lattice sum over any symmetric finite
  window (0 removed) vanishes EXACTLY at every odd rank, for every even weight.
* `tsum_eq_zero_odd` — the full-lattice version under summability.

No integrability hypotheses enter the parity identities: the substitution
`x ↦ -x` is an unconditional identity of interval integrals.  Even ranks carry
the complementary structure: the ξ-channel is symmetric (`dualIntegral_neg_even`)
and the DC term is the detecting channel — the productivity ledger.
-/

open Complex intervalIntegral

namespace CriticalLinePhasor.RankLadderParity

/-- `a = -a` forces `a = 0` in `ℂ` (no linear order needed). -/
private theorem self_eq_neg_eq_zero {a : ℂ} (h : a = -a) : a = 0 := by
  have h2 : (2 : ℂ) * a = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h' | h'
  · norm_num at h'
  · exact h'

/-- Second-kind Chebyshev `U_r` by the recurrence — the `(r+1)`-clock Satake
character of `Sym^r` on the elliptic band. -/
def chebU : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * x
  | (n + 2), x => 2 * x * chebU (n + 1) x - chebU n x

/-- The `(r+1)`-clock parity: `U_r(-x) = (-1)^r U_r(x)`. -/
theorem chebU_neg (r : ℕ) (x : ℝ) : chebU r (-x) = (-1) ^ r * chebU r x := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => simp [chebU]
    | 1 => show 2 * (-x) = (-1) ^ 1 * (2 * x); ring
    | (n + 2) =>
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      show 2 * (-x) * chebU (n + 1) (-x) - chebU n (-x) =
        (-1) ^ (n + 2) * (2 * x * chebU (n + 1) x - chebU n x)
      rw [h1, h0]
      ring

/-- The rank-`r` dual integrand at frequency `ξ` and scale `c`. -/
noncomputable def dualKernel (Φ : ℝ → ℝ) (r : ℕ) (c ξ : ℝ) (x : ℝ) : ℂ :=
  ((Φ x * chebU r x : ℝ) : ℂ) * Complex.exp (-2 * Real.pi * I * x * ξ * c)

/-- The rank-`r` dual integral. -/
noncomputable def dualIntegral (Φ : ℝ → ℝ) (r : ℕ) (c ξ : ℝ) : ℂ :=
  ∫ x in (-1 : ℝ)..1, dualKernel Φ r c ξ x

/-- The `-ξ` kernel at `x` is `(-1)^r` times the `ξ` kernel at `-x`. -/
theorem dualKernel_neg_eq (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    (r : ℕ) (c ξ x : ℝ) :
    dualKernel Φ r c (-ξ) x = ((-1 : ℂ) ^ r) * dualKernel Φ r c ξ (-x) := by
  unfold dualKernel
  rw [hΦ, chebU_neg]
  have h2 : ((-1 : ℂ)) ^ r * ((-1 : ℂ)) ^ r = 1 := by
    rw [← mul_pow]
    norm_num
  have hexp : Complex.exp (-2 * (Real.pi : ℂ) * I * (x : ℝ) * ((-ξ : ℝ) : ℂ) * (c : ℝ)) =
      Complex.exp (-2 * (Real.pi : ℂ) * I * ((-x : ℝ) : ℂ) * (ξ : ℝ) * (c : ℝ)) := by
    push_cast
    ring_nf
  rw [hexp]
  push_cast
  linear_combination (-(((Φ x : ℂ) * (chebU r x : ℂ)) *
    Complex.exp (-2 * (Real.pi : ℂ) * I * (-(x : ℂ)) * (ξ : ℂ) * (c : ℂ)))) * h2

/-- **The μ₂ parity clock on the dual variable**: `I_r(-ξ) = (-1)^r I_r(ξ)`.
Unconditional — the substitution `x ↦ -x` is an identity of interval
integrals, no integrability consumed. -/
theorem dualIntegral_neg (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    (r : ℕ) (c ξ : ℝ) :
    dualIntegral Φ r c (-ξ) = ((-1 : ℂ) ^ r) * dualIntegral Φ r c ξ := by
  unfold dualIntegral
  calc
    (∫ x in (-1 : ℝ)..1, dualKernel Φ r c (-ξ) x)
        = ∫ x in (-1 : ℝ)..1, ((-1 : ℂ) ^ r) * dualKernel Φ r c ξ (-x) := by
          apply intervalIntegral.integral_congr
          intro x _
          exact dualKernel_neg_eq Φ hΦ r c ξ x
    _ = ((-1 : ℂ) ^ r) * ∫ x in (-1 : ℝ)..1, dualKernel Φ r c ξ (-x) := by
          exact intervalIntegral.integral_const_mul _ _
    _ = ((-1 : ℂ) ^ r) * ∫ x in (-1 : ℝ)..1, dualKernel Φ r c ξ x := by
          congr 1
          simpa using intervalIntegral.integral_comp_neg
            (a := (-1 : ℝ)) (b := 1) (fun x => dualKernel Φ r c ξ x)

/-- Odd ranks: the dual channel is antisymmetric. -/
theorem dualIntegral_neg_odd (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    {r : ℕ} (hr : Odd r) (c ξ : ℝ) :
    dualIntegral Φ r c (-ξ) = - dualIntegral Φ r c ξ := by
  rw [dualIntegral_neg Φ hΦ r c ξ, hr.neg_one_pow]
  ring

/-- Even ranks: the dual channel is symmetric — the complementary structure
whose DC term is the detecting channel. -/
theorem dualIntegral_neg_even (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    {r : ℕ} (hr : Even r) (c ξ : ℝ) :
    dualIntegral Φ r c (-ξ) = dualIntegral Φ r c ξ := by
  rw [dualIntegral_neg Φ hΦ r c ξ, hr.neg_one_pow]
  ring

/-- **The DC term vanishes at every odd rank** — `U_r` odd kills the
zero-frequency channel. -/
theorem dualIntegral_zero_odd (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    {r : ℕ} (hr : Odd r) (c : ℝ) :
    dualIntegral Φ r c 0 = 0 := by
  have h := dualIntegral_neg_odd Φ hΦ hr c 0
  rw [neg_zero] at h
  exact self_eq_neg_eq_zero h

/-- **The exact lattice closure at every odd rank**: over any symmetric window
with `0` removed, the signed dual sum vanishes identically, for every even
Kloosterman/prefactor weight.  Identity-class closure of the ξ≠0 channel. -/
theorem latticeSum_eq_zero_odd (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    {r : ℕ} (hr : Odd r) (c : ℝ) (w : ℤ → ℂ) (hw : ∀ ξ : ℤ, w (-ξ) = w ξ)
    (N : ℕ) :
    (∑ ξ ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
      w ξ * dualIntegral Φ r c (ξ : ℝ)) = 0 := by
  set S := (Finset.Icc (-(N : ℤ)) N).erase 0 with hS
  have hsym : ∀ ξ : ℤ, ξ ∈ S ↔ -ξ ∈ S := by
    intro ξ
    simp only [hS, Finset.mem_erase, Finset.mem_Icc, neg_ne_zero]
    omega
  have hflip : (∑ ξ ∈ S, w ξ * dualIntegral Φ r c (ξ : ℝ)) =
      ∑ ξ ∈ S, w (-ξ) * dualIntegral Φ r c ((-ξ : ℤ) : ℝ) := by
    apply Finset.sum_nbij' (fun ξ => -ξ) (fun ξ => -ξ)
    · intro ξ hξ
      exact (hsym ξ).mp hξ
    · intro ξ hξ
      simpa using (hsym (-ξ)).mpr (by simpa using hξ)
    · intro ξ _
      simp
    · intro ξ _
      simp
    · intro ξ _
      simp
  have hodd : ∀ ξ : ℤ, w (-ξ) * dualIntegral Φ r c ((-ξ : ℤ) : ℝ) =
      -(w ξ * dualIntegral Φ r c (ξ : ℝ)) := by
    intro ξ
    rw [hw ξ]
    push_cast
    rw [dualIntegral_neg_odd Φ hΦ hr c (ξ : ℝ)]
    ring
  have h : (∑ ξ ∈ S, w ξ * dualIntegral Φ r c (ξ : ℝ)) =
      -(∑ ξ ∈ S, w ξ * dualIntegral Φ r c (ξ : ℝ)) := by
    calc
      (∑ ξ ∈ S, w ξ * dualIntegral Φ r c (ξ : ℝ))
          = ∑ ξ ∈ S, w (-ξ) * dualIntegral Φ r c ((-ξ : ℤ) : ℝ) := hflip
      _ = ∑ ξ ∈ S, -(w ξ * dualIntegral Φ r c (ξ : ℝ)) :=
            Finset.sum_congr rfl fun ξ _ => hodd ξ
      _ = -(∑ ξ ∈ S, w ξ * dualIntegral Φ r c (ξ : ℝ)) := by
            rw [Finset.sum_neg_distrib]
  exact self_eq_neg_eq_zero h

/-- **The full-lattice closure at every odd rank**: given summability, the
complete signed dual sum over `ℤ` vanishes — DC included, since the odd DC
term is itself zero. -/
theorem tsum_eq_zero_odd (Φ : ℝ → ℝ) (hΦ : ∀ x, Φ (-x) = Φ x)
    {r : ℕ} (hr : Odd r) (c : ℝ) (w : ℤ → ℂ) (hw : ∀ ξ : ℤ, w (-ξ) = w ξ)
    (hsum : Summable fun ξ : ℤ => w ξ * dualIntegral Φ r c (ξ : ℝ)) :
    (∑' ξ : ℤ, w ξ * dualIntegral Φ r c (ξ : ℝ)) = 0 := by
  set g : ℤ → ℂ := fun ξ => w ξ * dualIntegral Φ r c (ξ : ℝ) with hg
  have hgodd : ∀ ξ : ℤ, g (-ξ) = -g ξ := by
    intro ξ
    simp only [hg]
    rw [hw ξ]
    push_cast
    rw [dualIntegral_neg_odd Φ hΦ hr c (ξ : ℝ)]
    ring
  have hflip : (∑' ξ : ℤ, g ξ) = ∑' ξ : ℤ, g (-ξ) :=
    ((Equiv.neg ℤ).tsum_eq g).symm
  have h : (∑' ξ : ℤ, g ξ) = -(∑' ξ : ℤ, g ξ) := by
    calc
      (∑' ξ : ℤ, g ξ) = ∑' ξ : ℤ, g (-ξ) := hflip
      _ = ∑' ξ : ℤ, -g ξ := by
            apply tsum_congr
            intro ξ
            exact hgodd ξ
      _ = -(∑' ξ : ℤ, g ξ) := tsum_neg
  exact self_eq_neg_eq_zero h

end CriticalLinePhasor.RankLadderParity

#print axioms CriticalLinePhasor.RankLadderParity.chebU_neg
#print axioms CriticalLinePhasor.RankLadderParity.dualIntegral_neg
#print axioms CriticalLinePhasor.RankLadderParity.dualIntegral_zero_odd
#print axioms CriticalLinePhasor.RankLadderParity.latticeSum_eq_zero_odd
#print axioms CriticalLinePhasor.RankLadderParity.tsum_eq_zero_odd
