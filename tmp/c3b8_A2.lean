import c3b8_A1

/-!
# C3 batch 8, block A2 — lowering the majorant threshold from `A₁ ≥ 20` to `A₁ ≥ 6`

Batch 7 proved the sharp majorant chain under `A₁ ≥ 20` because that is what the *positivity*
comparison (`C3B7.modeBndS_tail_lt_head`) needed.  The *bound* half of the chain needs far
less: inspecting the batch-7 proofs, every step uses only

  * `2 ≤ A₁`      (for `C3B7.pow_four_exp_le` and `0 ≤ A₁ − 2`), and
  * `qFac A₁ ≤ 1/4` (for the geometric series and the `S² − q² ≤ 4q³` bracket).

This file restates those steps with exactly those two hypotheses — the correct refactor —
and then instantiates at `A₁ ≥ 6`, which by `Real.pi_gt_three` covers **every** `u ≥ 0`
(`modeA 0 0 u = 2πe^{2u} ≥ 2π > 6`).  Consequences:

* `radial_abs_le_sharp6` — the B1 packaging holds at `A ≥ 6`; the governing cubic
  `A³ + 2A² − 27A − 84` is `42 > 0` at `A = 6` (it is `−5.6 < 0` at `A = 5.5`, so `6` is
  essentially sharp for this packaging).
* `cellDensity_abs_le6` — the decay bound now holds on the **whole** half-line `u ≥ 0`,
  not just above `A₁ ≥ 20`.  This is what the `Ioi 0` integrability of the `sinh` pairing
  (block A3, target C) consumes.

Nothing here touches positivity: the certified positive range is still
`20(|x|+1)² ≤ modeA 0 0 u` (`C3B7.cellDensity_pos_uncond`).

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B8

open C3B6.Bessel
open C3B6.Theta
open C3B7

/-! ### 1. The radial packaging at `A ≥ 6` -/

/-- **B1's packaging, at the sharp threshold.**  `|radial A (kix 0 x A) (kix 1 x A)|
≤ 2(A+3)²e^{−A}` already for `A ≥ 6`. -/
theorem radial_abs_le_sharp6 (x : ℝ) {A : ℝ} (hA : 6 ≤ A) :
    |C3B5.A2.radial A (kix 0 x A) (kix 1 x A)| ≤ 2 * (A + 3) ^ 2 * Real.exp (-A) := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hE : (0 : ℝ) < Real.exp (-A) := Real.exp_pos _
  have hinv : Real.exp (1 / A) ≤ 1 + 2 / A := exp_inv_le (by linarith)
  have h0' : |kix 0 x A| ≤ Real.exp (-A) * (1 + 4 / A) := by
    have h := (kix_abs_le_coshMoment 0 x hA0).trans (coshMoment_sharp_le 0 hA0)
    simpa using h
  have h1' : |kix 1 x A| ≤ Real.exp (-A) * Real.exp (1 / A) * (1 + 4 / A) := by
    have h := (kix_abs_le_coshMoment 1 x hA0).trans (coshMoment_sharp_le 1 hA0)
    simpa using h
  have h1'' : |kix 1 x A| ≤ Real.exp (-A) * ((1 + 2 / A) * (1 + 4 / A)) := by
    refine h1'.trans ?_
    have hpos4 : (0 : ℝ) ≤ 1 + 4 / A := by positivity
    calc Real.exp (-A) * Real.exp (1 / A) * (1 + 4 / A)
        = Real.exp (-A) * (Real.exp (1 / A) * (1 + 4 / A)) := by ring
      _ ≤ Real.exp (-A) * ((1 + 2 / A) * (1 + 4 / A)) := by
          refine mul_le_mul_of_nonneg_left ?_ hE.le
          exact mul_le_mul_of_nonneg_right hinv hpos4
  have hstep : |C3B5.A2.radial A (kix 0 x A) (kix 1 x A)|
      ≤ (A ^ 2 + 9) * |kix 0 x A| + 6 * A * |kix 1 x A| := by
    unfold C3B5.A2.radial
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ A ^ 2 + 9),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 6 * A)]
  have hkey : (A ^ 2 + 9) * (1 + 4 / A) + 6 * A * ((1 + 2 / A) * (1 + 4 / A))
      ≤ 2 * (A + 3) ^ 2 := by
    have hne : A ≠ 0 := hA0.ne'
    have heq : (A ^ 2 + 9) * (1 + 4 / A) + 6 * A * ((1 + 2 / A) * (1 + 4 / A))
        = (A ^ 3 + 10 * A ^ 2 + 45 * A + 84) / A := by
      field_simp
      ring
    rw [heq, div_le_iff₀ hA0]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ A - 6) (sq_nonneg A),
      mul_nonneg (by linarith : (0:ℝ) ≤ A - 6) (by linarith : (0:ℝ) ≤ A), hA]
  have e0 : (A ^ 2 + 9) * |kix 0 x A| ≤ (A ^ 2 + 9) * (Real.exp (-A) * (1 + 4 / A)) :=
    mul_le_mul_of_nonneg_left h0' (by positivity)
  have e1 : 6 * A * |kix 1 x A|
      ≤ 6 * A * (Real.exp (-A) * ((1 + 2 / A) * (1 + 4 / A))) :=
    mul_le_mul_of_nonneg_left h1'' (by positivity)
  refine hstep.trans ?_
  calc (A ^ 2 + 9) * |kix 0 x A| + 6 * A * |kix 1 x A|
      ≤ (A ^ 2 + 9) * (Real.exp (-A) * (1 + 4 / A))
        + 6 * A * (Real.exp (-A) * ((1 + 2 / A) * (1 + 4 / A))) := by linarith
    _ = ((A ^ 2 + 9) * (1 + 4 / A) + 6 * A * ((1 + 2 / A) * (1 + 4 / A))) * Real.exp (-A) := by
        ring
    _ ≤ 2 * (A + 3) ^ 2 * Real.exp (-A) := mul_le_mul_of_nonneg_right hkey hE.le

theorem modeTerm_abs_le_sharp6 (x : ℝ) {u : ℝ} (hu : 6 ≤ modeA 0 0 u) (z : ℕ × ℕ) :
    |modeTerm x u z| ≤ modeBndS x u z := by
  obtain ⟨n, m⟩ := z
  have hAz : 6 ≤ modeA n m u := le_trans hu (modeA_ge_head n m u)
  have hrad := radial_abs_le_sharp6 (x := x) hAz
  have hcos : |Real.cos (x * modeLam n m)| ≤ 1 := Real.abs_cos_le_one _
  have hpi := Real.pi_pos
  have hw : (0 : ℝ) ≤ Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2
      * Real.exp (5 * u) := by positivity
  have hrabs : (0 : ℝ) ≤ |C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u))
      (kix 1 x (modeA n m u))| := abs_nonneg _
  unfold modeTerm modeBndS
  simp only []
  have hsplit : |Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u)
        * Real.cos (x * modeLam n m)
        * C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))|
      = (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u))
        * (|Real.cos (x * modeLam n m)|
          * |C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u))
              (kix 1 x (modeA n m u))|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw]
    ring
  rw [hsplit]
  have hstep : |Real.cos (x * modeLam n m)|
        * |C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))|
      ≤ 2 * (modeA n m u + 3) ^ 2 * Real.exp (-modeA n m u) := by
    calc |Real.cos (x * modeLam n m)|
          * |C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))|
        ≤ 1 * |C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u))
            (kix 1 x (modeA n m u))| := mul_le_mul_of_nonneg_right hcos hrabs
      _ = |C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u))| := by
          ring
      _ ≤ _ := hrad
  have hfin := mul_le_mul_of_nonneg_left hstep hw
  have hrw : Real.pi ^ 2 * Real.exp (5 * u) * (((n : ℝ) + 1) * ((m : ℝ) + 1)) ^ 2
      = Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u) := by ring
  rw [hrw]
  exact hfin

/-! ### 2. The tail chain, hypothesis-generic -/

theorem qFac_le_quarter6 {A₁ : ℝ} (hA : 6 ≤ A₁) : qFac A₁ ≤ 1 / 4 := by
  have h4 : (5 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hmono : Real.exp (-(A₁ - 2)) ≤ Real.exp (-4 : ℝ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hinv : Real.exp (-4 : ℝ) * Real.exp (4 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hq : Real.exp (-4 : ℝ) ≤ 1 / 4 := by
    nlinarith [hinv, h4, Real.exp_pos (-4 : ℝ), Real.exp_pos (4 : ℝ)]
  exact le_trans hmono hq

theorem summable_gq' {A₁ : ℝ} (hq : qFac A₁ ≤ 1 / 4) : Summable (gq A₁) := by
  have hq0 : 0 ≤ qFac A₁ := (qFac_pos A₁).le
  have hq1 : qFac A₁ < 1 := lt_of_le_of_lt hq (by norm_num)
  have hbase : Summable (fun n : ℕ => qFac A₁ ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hmul := hbase.mul_left (qFac A₁)
  refine hmul.congr fun n => ?_
  unfold gq
  rw [pow_succ]
  ring

theorem tsum_gq' {A₁ : ℝ} (hq : qFac A₁ ≤ 1 / 4) :
    ∑' n : ℕ, gq A₁ n = qFac A₁ * (1 - qFac A₁)⁻¹ := by
  have hq0 : 0 ≤ qFac A₁ := (qFac_pos A₁).le
  have hq1 : qFac A₁ < 1 := lt_of_le_of_lt hq (by norm_num)
  have hbase : ∑' n : ℕ, qFac A₁ ^ n = (1 - qFac A₁)⁻¹ :=
    tsum_geometric_of_lt_one hq0 hq1
  have hcongr : ∑' n : ℕ, gq A₁ n = ∑' n : ℕ, qFac A₁ * qFac A₁ ^ n := by
    refine tsum_congr fun n => ?_
    unfold gq
    rw [pow_succ]
    ring
  rw [hcongr, tsum_mul_left, hbase]

theorem summable_prod_gq' {A₁ : ℝ} (hq : qFac A₁ ≤ 1 / 4) :
    Summable (fun z : ℕ × ℕ => gq A₁ z.1 * gq A₁ z.2) :=
  (summable_gq' hq).mul_of_nonneg (summable_gq' hq) (gq_nonneg A₁) (gq_nonneg A₁)

theorem tsum_prod_gq' {A₁ : ℝ} (hq : qFac A₁ ≤ 1 / 4) :
    ∑' z : ℕ × ℕ, gq A₁ z.1 * gq A₁ z.2 = (∑' n : ℕ, gq A₁ n) ^ 2 := by
  have h := (summable_gq' hq).tsum_mul_tsum (summable_gq' hq) (summable_prod_gq' hq)
  rw [← h]
  ring

theorem tsum_gq_sq_sub' {A₁ : ℝ} (hq : qFac A₁ ≤ 1 / 4) :
    (∑' n : ℕ, gq A₁ n) ^ 2 - qFac A₁ ^ 2 ≤ 4 * qFac A₁ ^ 3 := by
  set q : ℝ := qFac A₁ with hqdef
  have hq0 : 0 < q := qFac_pos A₁
  have hq4 : q ≤ 1 / 4 := hq
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hsq : (0 : ℝ) < (1 - q) ^ 2 := by positivity
  rw [tsum_gq' hq, ← hqdef]
  have hval : (q * (1 - q)⁻¹) ^ 2 = q ^ 2 / (1 - q) ^ 2 := by
    rw [mul_pow, inv_pow, div_eq_mul_inv]
  rw [hval, sub_le_iff_le_add, div_le_iff₀ hsq]
  have hpoly : (0 : ℝ) ≤ 2 - 7 * q + 4 * q ^ 2 := by nlinarith [hq4, hq0, sq_nonneg q]
  have hq3 : (0 : ℝ) < q ^ 3 := by positivity
  nlinarith [mul_nonneg hq3.le hpoly]

/-- The factorised termwise bound, with the two genuine hypotheses. -/
theorem modeBndS_le_prod' (x : ℝ) {u : ℝ} (h2 : 2 ≤ modeA 0 0 u) {n m : ℕ}
    (hz : ¬(n = 0 ∧ m = 0)) :
    modeBndS x u (n, m)
      ≤ tailConst u (modeA 0 0 u) * (gq (modeA 0 0 u) n * gq (modeA 0 0 u) m) := by
  set A₁ : ℝ := modeA 0 0 u with hA1
  set a : ℝ := (n : ℝ) + 1 with hadef
  set b : ℝ := (m : ℝ) + 1 with hbdef
  have ha1 : (1 : ℝ) ≤ a := by rw [hadef]; exact one_le_cast_succ n
  have hb1 : (1 : ℝ) ≤ b := by rw [hbdef]; exact one_le_cast_succ m
  have hab1 : (1 : ℝ) ≤ a * b := by nlinarith
  have hA0 : (0 : ℝ) < A₁ := by linarith
  have hpi := Real.pi_pos
  have hAfac : modeA n m u = a * b * A₁ := by
    rw [hA1, hadef, hbdef]
    exact modeA_factor n m u
  have hab2 : (2 : ℝ) ≤ a * b := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have hm : m ≠ 0 := fun hm0 => hz ⟨hn, hm0⟩
      have hm1 : (1 : ℕ) ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have han : a = 1 := by rw [hadef, hn]; norm_num
      rw [han, one_mul, hbdef]
      linarith
    · have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have ha2 : (2 : ℝ) ≤ a := by rw [hadef]; linarith
      nlinarith
  have hsq : (modeA n m u + 3) ^ 2 ≤ (a * b) ^ 2 * (A₁ + 3) ^ 2 := by
    rw [hAfac]
    have h1 : a * b * A₁ + 3 ≤ a * b * (A₁ + 3) := by nlinarith [hab1, hA0]
    have h2' : (0 : ℝ) ≤ a * b * A₁ + 3 := by positivity
    nlinarith [h1, h2']
  have hstep := pow_four_exp_le (t := a * b) (A := A₁) hab2 h2
  have hhyp : a + b - 3 ≤ a * b - 2 := prod_sub_two_ge ha1 hb1
  have hA2 : (0 : ℝ) ≤ A₁ - 2 := by linarith
  have hshift : Real.exp (-((a * b - 2) * (A₁ - 2)))
      ≤ Real.exp (-((a + b - 3) * (A₁ - 2))) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hhyp, hA2]
  have hA' : modeBndS x u (n, m)
      = (Real.pi ^ 2 * Real.exp (5 * u) * (a * b) ^ 2 * 2)
        * ((modeA n m u + 3) ^ 2 * Real.exp (-(a * b * A₁))) := by
    unfold modeBndS
    simp only []
    rw [hAfac, ← hadef, ← hbdef]
    ring
  have hcoef : (0 : ℝ) ≤ Real.pi ^ 2 * Real.exp (5 * u) * (a * b) ^ 2 * 2 := by positivity
  have hB : (modeA n m u + 3) ^ 2 * Real.exp (-(a * b * A₁))
      ≤ ((a * b) ^ 2 * (A₁ + 3) ^ 2) * Real.exp (-(a * b * A₁)) :=
    mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
  have hstep2 : modeBndS x u (n, m)
      ≤ (2 * Real.pi ^ 2 * Real.exp (5 * u) * (A₁ + 3) ^ 2)
        * ((a * b) ^ 4 * Real.exp (-(a * b * A₁))) := by
    rw [hA']
    calc (Real.pi ^ 2 * Real.exp (5 * u) * (a * b) ^ 2 * 2)
          * ((modeA n m u + 3) ^ 2 * Real.exp (-(a * b * A₁)))
        ≤ (Real.pi ^ 2 * Real.exp (5 * u) * (a * b) ^ 2 * 2)
          * (((a * b) ^ 2 * (A₁ + 3) ^ 2) * Real.exp (-(a * b * A₁))) :=
          mul_le_mul_of_nonneg_left hB hcoef
      _ = (2 * Real.pi ^ 2 * Real.exp (5 * u) * (A₁ + 3) ^ 2)
          * ((a * b) ^ 4 * Real.exp (-(a * b * A₁))) := by ring
  have hstep3 : (a * b) ^ 4 * Real.exp (-(a * b * A₁))
      ≤ 16 * Real.exp (-(2 * A₁)) * Real.exp (-((a + b - 3) * (A₁ - 2))) := by
    refine le_trans hstep ?_
    have hnn : (0 : ℝ) ≤ 16 * Real.exp (-(2 * A₁)) := by positivity
    exact mul_le_mul_of_nonneg_left hshift hnn
  have hcoef2 : (0 : ℝ) ≤ 2 * Real.pi ^ 2 * Real.exp (5 * u) * (A₁ + 3) ^ 2 := by positivity
  have hg : gq A₁ n * gq A₁ m = Real.exp (-((a + b) * (A₁ - 2))) := by
    unfold gq qFac
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    rw [hadef, hbdef]
    ring
  have hE : Real.exp (3 * (A₁ - 2)) * Real.exp (-((a + b) * (A₁ - 2)))
      = Real.exp (-((a + b - 3) * (A₁ - 2))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hRHS : tailConst u A₁ * (gq A₁ n * gq A₁ m)
      = (2 * Real.pi ^ 2 * Real.exp (5 * u) * (A₁ + 3) ^ 2)
        * (16 * Real.exp (-(2 * A₁)) * Real.exp (-((a + b - 3) * (A₁ - 2)))) := by
    rw [hg]
    unfold tailConst
    rw [show Real.pi ^ 2 * Real.exp (5 * u) * (32 * (A₁ + 3) ^ 2 * Real.exp (-(2 * A₁)))
          * Real.exp (3 * (A₁ - 2)) * Real.exp (-((a + b) * (A₁ - 2)))
        = (2 * Real.pi ^ 2 * Real.exp (5 * u) * (A₁ + 3) ^ 2)
          * (16 * Real.exp (-(2 * A₁))
            * (Real.exp (3 * (A₁ - 2)) * Real.exp (-((a + b) * (A₁ - 2))))) by ring, hE]
  rw [hRHS]
  exact le_trans hstep2 (mul_le_mul_of_nonneg_left hstep3 hcoef2)

theorem modeBndS_le_prod_all' (x : ℝ) {u : ℝ} (h2 : 2 ≤ modeA 0 0 u) (z : ℕ × ℕ) :
    modeBndS x u z
      ≤ tailConst u (modeA 0 0 u) * (gq (modeA 0 0 u) z.1 * gq (modeA 0 0 u) z.2) := by
  obtain ⟨n, m⟩ := z
  by_cases hz : n = 0 ∧ m = 0
  · obtain ⟨hn, hm⟩ := hz
    subst hn; subst hm
    set A₁ : ℝ := modeA 0 0 u with hA1
    have hpi := Real.pi_pos
    have hA0 : (0 : ℝ) < A₁ := by linarith
    have hL : modeBndS x u ((0 : ℕ), (0 : ℕ))
        = Real.pi ^ 2 * Real.exp (5 * u) * (2 * (A₁ + 3) ^ 2 * Real.exp (-A₁)) := by
      unfold modeBndS
      simp only [Nat.cast_zero, zero_add, one_mul, one_pow]
      rw [hA1]
      ring
    have hq : gq A₁ 0 * gq A₁ 0 = Real.exp (-(2 * (A₁ - 2))) := by
      unfold gq qFac
      rw [pow_one, ← Real.exp_add]
      congr 1
      ring
    have hR : tailConst u A₁ * (gq A₁ 0 * gq A₁ 0)
        = Real.pi ^ 2 * Real.exp (5 * u)
          * (32 * (A₁ + 3) ^ 2 * (Real.exp (-A₁) * Real.exp (-2))) := by
      rw [hq]
      unfold tailConst
      rw [show Real.pi ^ 2 * Real.exp (5 * u) * (32 * (A₁ + 3) ^ 2 * Real.exp (-(2 * A₁)))
            * Real.exp (3 * (A₁ - 2)) * Real.exp (-(2 * (A₁ - 2)))
          = Real.pi ^ 2 * Real.exp (5 * u) * (32 * (A₁ + 3) ^ 2
            * (Real.exp (-(2 * A₁)) * Real.exp (3 * (A₁ - 2)) * Real.exp (-(2 * (A₁ - 2)))))
          by ring]
      congr 2
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hL, hR]
    have hcoef : (0 : ℝ) ≤ Real.pi ^ 2 * Real.exp (5 * u) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hcoef
    have he2 : Real.exp 2 ≤ 16 := exp_two_le_sixteen
    have hinv : Real.exp (-2 : ℝ) * Real.exp 2 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hge : (2 : ℝ) ≤ 32 * Real.exp (-2 : ℝ) := by
      nlinarith [hinv, he2, Real.exp_pos (-2 : ℝ), Real.exp_pos (2 : ℝ)]
    have hAe : (0 : ℝ) < (A₁ + 3) ^ 2 * Real.exp (-A₁) := by positivity
    nlinarith [hge, hAe]
  · exact modeBndS_le_prod' x h2 hz

theorem summable_modeBndS' (x : ℝ) {u : ℝ} (h2 : 2 ≤ modeA 0 0 u)
    (hq : qFac (modeA 0 0 u) ≤ 1 / 4) : Summable (modeBndS x u) :=
  ((summable_prod_gq' hq).mul_left _).of_nonneg_of_le
    (modeBndS_nonneg x u) (modeBndS_le_prod_all' x h2)

theorem modeBndS_tail_le' (x : ℝ) {u : ℝ} (h2 : 2 ≤ modeA 0 0 u)
    (hq : qFac (modeA 0 0 u) ≤ 1 / 4) :
    (∑' z : ℕ × ℕ, if z = (0, 0) then (0 : ℝ) else modeBndS x u z)
      ≤ Real.pi ^ 2 * Real.exp (5 * u)
        * (128 * (modeA 0 0 u + 3) ^ 2 * Real.exp (-(2 * modeA 0 0 u))) := by
  set A₁ : ℝ := modeA 0 0 u with hA1
  set P : ℕ × ℕ → ℝ := fun z => gq A₁ z.1 * gq A₁ z.2 with hP
  set G : ℕ × ℕ → ℝ := fun z => if z = (0, 0) then (0 : ℝ) else tailConst u A₁ * P z with hG
  have hPnn : ∀ z : ℕ × ℕ, 0 ≤ P z := fun z =>
    mul_nonneg (gq_nonneg A₁ z.1) (gq_nonneg A₁ z.2)
  have hTC : 0 ≤ tailConst u A₁ := tailConst_nonneg u A₁
  have hPsum : Summable P := summable_prod_gq' hq
  have hTPsum : Summable (fun z : ℕ × ℕ => tailConst u A₁ * P z) := hPsum.mul_left _
  have hFG : ∀ z : ℕ × ℕ,
      (if z = (0, 0) then (0 : ℝ) else modeBndS x u z) ≤ G z := by
    intro z
    obtain ⟨n, m⟩ := z
    by_cases h : (n, m) = ((0 : ℕ), (0 : ℕ))
    · simp only [hG, if_pos h, le_refl]
    · have hz : ¬(n = 0 ∧ m = 0) := by
        intro hnm
        exact h (by rw [hnm.1, hnm.2])
      simp only [hG, if_neg h]
      exact modeBndS_le_prod' x h2 hz
  have hGnn : ∀ z : ℕ × ℕ, 0 ≤ G z := by
    intro z
    by_cases h : z = (0, 0)
    · simp only [hG, if_pos h, le_refl]
    · simp only [hG, if_neg h]
      exact mul_nonneg hTC (hPnn z)
  have hGsum : Summable G := by
    refine hTPsum.of_nonneg_of_le hGnn (fun z => ?_)
    by_cases h : z = (0, 0)
    · simp only [hG, if_pos h]
      exact mul_nonneg hTC (hPnn z)
    · simp only [hG, if_neg h]
      exact le_rfl
  have hFnn : ∀ z : ℕ × ℕ, 0 ≤ (if z = (0, 0) then (0 : ℝ) else modeBndS x u z) := by
    intro z
    by_cases h : z = (0, 0)
    · simp only [if_pos h, le_refl]
    · simp only [if_neg h]
      exact modeBndS_nonneg x u z
  have hFsum : Summable (fun z : ℕ × ℕ => if z = (0, 0) then (0 : ℝ) else modeBndS x u z) :=
    hGsum.of_nonneg_of_le hFnn hFG
  have hle : (∑' z : ℕ × ℕ, if z = (0, 0) then (0 : ℝ) else modeBndS x u z) ≤ ∑' z, G z :=
    Summable.tsum_le_tsum hFG hFsum hGsum
  have hsplit := hTPsum.tsum_eq_add_tsum_ite ((0 : ℕ), (0 : ℕ))
  have hGval : ∑' z, G z
      = tailConst u A₁ * ((∑' n : ℕ, gq A₁ n) ^ 2 - qFac A₁ ^ 2) := by
    have hP00 : P ((0 : ℕ), (0 : ℕ)) = qFac A₁ ^ 2 := by
      simp only [hP, gq_zero]
      ring
    have hTP : ∑' z : ℕ × ℕ, tailConst u A₁ * P z
        = tailConst u A₁ * (∑' n : ℕ, gq A₁ n) ^ 2 := by
      rw [tsum_mul_left, hP, tsum_prod_gq' hq]
    have hGeq : ∑' z, G z = ∑' z : ℕ × ℕ,
        (if z = ((0:ℕ), (0:ℕ)) then (0 : ℝ) else tailConst u A₁ * P z) := rfl
    rw [hGeq]
    have hthis := hsplit
    rw [hTP, hP00] at hthis
    linarith [hthis]
  rw [hGval] at hle
  refine hle.trans ?_
  have hbr : (∑' n : ℕ, gq A₁ n) ^ 2 - qFac A₁ ^ 2 ≤ 4 * qFac A₁ ^ 3 := tsum_gq_sq_sub' hq
  have hTCmul : tailConst u A₁ * ((∑' n : ℕ, gq A₁ n) ^ 2 - qFac A₁ ^ 2)
      ≤ tailConst u A₁ * (4 * qFac A₁ ^ 3) := mul_le_mul_of_nonneg_left hbr hTC
  refine hTCmul.trans ?_
  have hcancel : tailConst u A₁ * (4 * qFac A₁ ^ 3)
      = Real.pi ^ 2 * Real.exp (5 * u)
        * (128 * (A₁ + 3) ^ 2 * Real.exp (-(2 * A₁)))
        * (Real.exp (3 * (A₁ - 2)) * qFac A₁ ^ 3) := by
    unfold tailConst
    ring
  rw [hcancel, exp_shift_qcube, mul_one]

/-! ### 3. The half-line bound -/

/-- `2π > 6`, so every height `u ≥ 0` clears the lowered threshold. -/
theorem modeA_head_ge_six {u : ℝ} (hu : 0 ≤ u) : 6 ≤ modeA 0 0 u := by
  rw [modeA_head]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hexp : (1 : ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  nlinarith [hpi, hexp]

/-- **THE HALF-LINE DECAY BOUND.**  Valid for every `u ≥ 0`, not only above `A₁ ≥ 20`. -/
theorem cellDensity_abs_le6 (x : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    |cellDensity x u|
      ≤ 16 * (modeBndS x u (0, 0)
        + Real.pi ^ 2 * Real.exp (5 * u)
          * (128 * (modeA 0 0 u + 3) ^ 2 * Real.exp (-(2 * modeA 0 0 u)))) := by
  have hA6 : 6 ≤ modeA 0 0 u := modeA_head_ge_six hu
  have h2 : (2 : ℝ) ≤ modeA 0 0 u := by linarith
  have hq : qFac (modeA 0 0 u) ≤ 1 / 4 := qFac_le_quarter6 hA6
  have hsum := summable_modeTerm x u
  have hsplit : ∑' z : ℕ × ℕ, modeTerm x u z
      = modeTerm x u (0, 0)
        + ∑' z : ℕ × ℕ, if z = (0, 0) then (0 : ℝ) else modeTerm x u z :=
    hsum.tsum_eq_add_tsum_ite (0, 0)
  have hbndS := summable_modeBndS' x h2 hq
  have hFabs : ∀ z : ℕ × ℕ,
      ‖(if z = (0, 0) then (0 : ℝ) else modeTerm x u z)‖
        ≤ (if z = (0, 0) then (0 : ℝ) else modeBndS x u z) := by
    intro z
    by_cases hz : z = (0, 0)
    · simp only [if_pos hz, norm_zero, le_refl]
    · simp only [if_neg hz, Real.norm_eq_abs]
      exact modeTerm_abs_le_sharp6 x hA6 z
  have hitebS : Summable (fun z : ℕ × ℕ => if z = (0, 0) then (0 : ℝ) else modeBndS x u z) := by
    refine hbndS.of_nonneg_of_le (fun z => ?_) (fun z => ?_)
    · by_cases hz : z = (0, 0)
      · simp only [if_pos hz, le_refl]
      · simp only [if_neg hz]
        exact modeBndS_nonneg x u z
    · by_cases hz : z = (0, 0)
      · simp only [if_pos hz]
        exact modeBndS_nonneg x u z
      · simp only [if_neg hz]
        exact le_rfl
  have hitef : Summable (fun z : ℕ × ℕ => if z = (0, 0) then (0 : ℝ) else modeTerm x u z) :=
    Summable.of_norm_bounded hitebS hFabs
  have hnorm : ‖∑' z : ℕ × ℕ, if z = (0, 0) then (0 : ℝ) else modeTerm x u z‖
      ≤ ∑' z : ℕ × ℕ, if z = (0, 0) then (0 : ℝ) else modeBndS x u z := by
    refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
    · exact hitebS.of_nonneg_of_le (fun z => norm_nonneg _) hFabs
    · exact Summable.tsum_le_tsum hFabs
        (hitebS.of_nonneg_of_le (fun z => norm_nonneg _) hFabs) hitebS
  rw [Real.norm_eq_abs] at hnorm
  have htail := modeBndS_tail_le' x h2 hq
  have hhead : |modeTerm x u (0, 0)| ≤ modeBndS x u (0, 0) :=
    modeTerm_abs_le_sharp6 x hA6 (0, 0)
  rw [cellDensity_eq_tsum, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (16:ℝ))]
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ (16:ℝ))
  refine (abs_add_le _ _).trans ?_
  linarith [hhead, hnorm, htail]

/-- The half-line bound in the shape the `sinh` pairing consumes:
`|C(u,x)| ≤ 33280π⁴e^{9u}e^{−A₁(u)}` for every `u ≥ 0`. -/
theorem cellDensity_abs_le_simple6 (x : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    |cellDensity x u| ≤ 33280 * Real.pi ^ 4 * Real.exp (9 * u) * Real.exp (-modeA 0 0 u) := by
  have hpi := Real.pi_pos
  have hA6 : 6 ≤ modeA 0 0 u := modeA_head_ge_six hu
  have hA0 : (0 : ℝ) < modeA 0 0 u := by linarith
  have h := cellDensity_abs_le6 x hu
  have hm : modeBndS x u (0, 0)
      = Real.pi ^ 2 * Real.exp (5 * u)
        * (2 * (modeA 0 0 u + 3) ^ 2 * Real.exp (-modeA 0 0 u)) := by
    unfold modeBndS
    norm_num
  rw [hm] at h
  have he2 : Real.exp (-(2 * modeA 0 0 u)) ≤ Real.exp (-modeA 0 0 u) :=
    Real.exp_le_exp.mpr (by linarith)
  have hbase : (0 : ℝ) ≤ Real.pi ^ 2 * Real.exp (5 * u) * (modeA 0 0 u + 3) ^ 2 := by
    positivity
  have hstep1 : |cellDensity x u|
      ≤ 2080 * Real.pi ^ 2 * Real.exp (5 * u) * (modeA 0 0 u + 3) ^ 2
        * Real.exp (-modeA 0 0 u) := by
    nlinarith [h, he2, hbase, Real.exp_pos (-modeA 0 0 u)]
  refine hstep1.trans ?_
  have hsq : (modeA 0 0 u + 3) ^ 2 ≤ 4 * modeA 0 0 u ^ 2 := by nlinarith [hA6]
  have hA2 : modeA 0 0 u ^ 2 = 4 * Real.pi ^ 2 * Real.exp (4 * u) := by
    have hsqe : Real.exp (2 * u) ^ 2 = Real.exp (4 * u) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [modeA_head]
    nlinarith [hsqe]
  have hE : (0 : ℝ) < Real.exp (-modeA 0 0 u) := Real.exp_pos _
  have hcoef : (0 : ℝ) ≤ 2080 * Real.pi ^ 2 * Real.exp (5 * u) := by positivity
  have hexp94 : Real.exp (5 * u) * Real.exp (4 * u) = Real.exp (9 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : (modeA 0 0 u + 3) ^ 2 * Real.exp (-modeA 0 0 u)
      ≤ (16 * Real.pi ^ 2 * Real.exp (4 * u)) * Real.exp (-modeA 0 0 u) := by
    refine mul_le_mul_of_nonneg_right ?_ hE.le
    calc (modeA 0 0 u + 3) ^ 2 ≤ 4 * modeA 0 0 u ^ 2 := hsq
      _ = 16 * Real.pi ^ 2 * Real.exp (4 * u) := by rw [hA2]; ring
  calc
    2080 * Real.pi ^ 2 * Real.exp (5 * u) * (modeA 0 0 u + 3) ^ 2
        * Real.exp (-modeA 0 0 u)
        = (2080 * Real.pi ^ 2 * Real.exp (5 * u))
          * ((modeA 0 0 u + 3) ^ 2 * Real.exp (-modeA 0 0 u)) := by ring
    _ ≤ (2080 * Real.pi ^ 2 * Real.exp (5 * u))
          * ((16 * Real.pi ^ 2 * Real.exp (4 * u))
            * Real.exp (-modeA 0 0 u)) :=
        mul_le_mul_of_nonneg_left hprod hcoef
    _ = 33280 * Real.pi ^ 4 * Real.exp (9 * u)
          * Real.exp (-modeA 0 0 u) := by rw [← hexp94]; ring

end C3B8

section AxiomAudit
#print axioms C3B8.radial_abs_le_sharp6
#print axioms C3B8.modeTerm_abs_le_sharp6
#print axioms C3B8.qFac_le_quarter6
#print axioms C3B8.summable_gq'
#print axioms C3B8.tsum_gq_sq_sub'
#print axioms C3B8.modeBndS_le_prod'
#print axioms C3B8.summable_modeBndS'
#print axioms C3B8.modeBndS_tail_le'
#print axioms C3B8.modeA_head_ge_six
#print axioms C3B8.cellDensity_abs_le6
#print axioms C3B8.cellDensity_abs_le_simple6
end AxiomAudit
