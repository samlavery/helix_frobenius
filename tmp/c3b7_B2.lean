import c3b7_B1

/-!
# C3 batch 7, block B2 — the sharp mode majorant and its hyperbola-factorised tail
(attack families 1, 2, 5)

`modeBndS` replaces `C3B6.Theta.modeBound`:

  `modeBndS x u (n,m) = π²e^{5u}·(ab)²·2(A_{nm}+3)²·e^{−A_{nm}}`,  `a = n+1`, `b = m+1`,

with `|modeTerm| ≤ modeBndS` supplied by `radial_abs_le_sharp` (B1).  The rate is
`e^{−A_{nm}}`, not the batch-6 `e^{−A_{nm}+A₁/2}`.

The tail is summed by the **hyperbola factorisation** (attack family 2).  With `t = ab`:

  `(A_z+3)² ≤ t²(A₁+3)²`                                  (`t ≥ 1`)
  `t⁴e^{−tA₁} ≤ 16 e^{−2A₁} e^{−(t−2)(A₁−2)}`              (`t ≥ 2`, from `1+y ≤ e^y`)
  `t − 2 = ab − 2 ≥ a + b − 3`                             (`(a−1)(b−1) ≥ 0`)

so every off-head mode is bounded by a **product** `q^a·q^b`, `q = e^{−(A₁−2)}`, and the
double tail collapses to `(Σ_a q^a)² − q²`.  With `q ≤ 1/4` (from `e^{18} ≥ 19 ≥ 4`) the
bracket is `≤ 4q³`, and `e^{3(A₁−2)}q³ = 1` cancels exactly, giving

  `Σ_{z≠(0,0)} modeBndS x u z ≤ π²e^{5u}·128(A₁+3)²e^{−2A₁}`   for `A₁ ≥ 20`
                                                            (`modeBndS_tail_le`)

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B7

open C3B6.Bessel
open C3B6.Theta

/-! ### 1. The sharp mode majorant -/

/-- The batch-7 mode majorant: `π²e^{5u}·(ab)²·2(A_{nm}+3)²e^{−A_{nm}}`. -/
def modeBndS (x u : ℝ) (z : ℕ × ℕ) : ℝ :=
  Real.pi ^ 2 * Real.exp (5 * u) * (((z.1 : ℝ) + 1) * ((z.2 : ℝ) + 1)) ^ 2
    * (2 * (modeA z.1 z.2 u + 3) ^ 2 * Real.exp (-modeA z.1 z.2 u))

theorem modeBndS_nonneg (x u : ℝ) (z : ℕ × ℕ) : 0 ≤ modeBndS x u z := by
  unfold modeBndS
  have := Real.pi_pos
  positivity

/-- **The termwise bound.**  Every mode of `cellDensity` is bounded by `modeBndS`. -/
theorem modeTerm_abs_le_sharp (x : ℝ) {u : ℝ} (hu : 8 ≤ modeA 0 0 u) (z : ℕ × ℕ) :
    |modeTerm x u z| ≤ modeBndS x u z := by
  obtain ⟨n, m⟩ := z
  have hAz : 8 ≤ modeA n m u := le_trans hu (modeA_ge_head n m u)
  have hrad := radial_abs_le_sharp (x := x) hAz
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

/-! ### 2. The geometric factor -/

/-- `q = e^{−(A₁−2)}`, the per-strand geometric ratio of the hyperbola factorisation. -/
def qFac (A₁ : ℝ) : ℝ := Real.exp (-(A₁ - 2))

theorem qFac_pos (A₁ : ℝ) : 0 < qFac A₁ := Real.exp_pos _

/-- `q ≤ 1/4` once `A₁ ≥ 20`, from `1 + y ≤ e^y` alone (`e^{18} ≥ 19 ≥ 4`). -/
theorem qFac_le_quarter {A₁ : ℝ} (hA : 20 ≤ A₁) : qFac A₁ ≤ 1 / 4 := by
  have h18 : (19 : ℝ) ≤ Real.exp 18 := by
    have := Real.add_one_le_exp (18 : ℝ)
    linarith
  have hmono : Real.exp (-(A₁ - 2)) ≤ Real.exp (-18 : ℝ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hinv : Real.exp (-18 : ℝ) * Real.exp (18 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hq : Real.exp (-18 : ℝ) ≤ 1 / 4 := by
    nlinarith [hinv, h18, Real.exp_pos (-18 : ℝ), Real.exp_pos (18 : ℝ)]
  exact le_trans hmono hq

/-- The one-strand family `q^{a}` with `a = n+1`. -/
def gq (A₁ : ℝ) (n : ℕ) : ℝ := qFac A₁ ^ (n + 1)

theorem gq_nonneg (A₁ : ℝ) (n : ℕ) : 0 ≤ gq A₁ n := by
  unfold gq
  exact pow_nonneg (qFac_pos A₁).le _

theorem gq_zero (A₁ : ℝ) : gq A₁ 0 = qFac A₁ := by
  unfold gq
  ring

theorem summable_gq {A₁ : ℝ} (hA : 20 ≤ A₁) : Summable (gq A₁) := by
  have hq0 : 0 ≤ qFac A₁ := (qFac_pos A₁).le
  have hq1 : qFac A₁ < 1 := lt_of_le_of_lt (qFac_le_quarter hA) (by norm_num)
  have hbase : Summable (fun n : ℕ => qFac A₁ ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hmul := hbase.mul_left (qFac A₁)
  refine hmul.congr fun n => ?_
  unfold gq
  rw [pow_succ]
  ring

theorem tsum_gq {A₁ : ℝ} (hA : 20 ≤ A₁) :
    ∑' n : ℕ, gq A₁ n = qFac A₁ * (1 - qFac A₁)⁻¹ := by
  have hq0 : 0 ≤ qFac A₁ := (qFac_pos A₁).le
  have hq1 : qFac A₁ < 1 := lt_of_le_of_lt (qFac_le_quarter hA) (by norm_num)
  have hbase : ∑' n : ℕ, qFac A₁ ^ n = (1 - qFac A₁)⁻¹ :=
    tsum_geometric_of_lt_one hq0 hq1
  have hcongr : ∑' n : ℕ, gq A₁ n = ∑' n : ℕ, qFac A₁ * qFac A₁ ^ n := by
    refine tsum_congr fun n => ?_
    unfold gq
    rw [pow_succ]
    ring
  rw [hcongr, tsum_mul_left, hbase]

/-! ### 3. The three elementary hyperbola steps -/

/-- `(1 + y)^4 ≤ e^{4y}` for `y ≥ 0`. -/
theorem one_add_pow_four_le {y : ℝ} (hy : 0 ≤ y) : (1 + y) ^ 4 ≤ Real.exp (4 * y) := by
  have h1 : 1 + y ≤ Real.exp y := by
    have := Real.add_one_le_exp y
    linarith
  have h2 : (0 : ℝ) ≤ 1 + y := by linarith
  calc (1 + y) ^ 4 ≤ Real.exp y ^ 4 := pow_le_pow_left₀ h2 h1 4
    _ = Real.exp (4 * y) := by
        rw [← Real.exp_nat_mul]
        norm_num

/-- **The `t⁴` step.**  `t⁴e^{−tA} ≤ 16 e^{−2A} e^{−(t−2)(A−2)}` for `t ≥ 2`, `A ≥ 2`. -/
theorem pow_four_exp_le {t A : ℝ} (ht : 2 ≤ t) (hA : 2 ≤ A) :
    t ^ 4 * Real.exp (-(t * A))
      ≤ 16 * Real.exp (-(2 * A)) * Real.exp (-((t - 2) * (A - 2))) := by
  have hs : (0 : ℝ) ≤ (t - 2) / 2 := by linarith
  have hkey : t ^ 4 ≤ 16 * Real.exp (2 * (t - 2)) := by
    have h := one_add_pow_four_le hs
    have hid : (1 : ℝ) + (t - 2) / 2 = t / 2 := by ring
    rw [hid] at h
    have h4 : (t / 2) ^ 4 = t ^ 4 / 16 := by ring
    rw [h4] at h
    have hexp : Real.exp (4 * ((t - 2) / 2)) = Real.exp (2 * (t - 2)) := by
      congr 1
      ring
    rw [hexp] at h
    linarith
  have hexpeq : Real.exp (2 * (t - 2)) * Real.exp (-(t * A))
      = Real.exp (-(2 * A)) * Real.exp (-((t - 2) * (A - 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc t ^ 4 * Real.exp (-(t * A))
      ≤ (16 * Real.exp (2 * (t - 2))) * Real.exp (-(t * A)) :=
        mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
    _ = 16 * (Real.exp (2 * (t - 2)) * Real.exp (-(t * A))) := by ring
    _ = 16 * (Real.exp (-(2 * A)) * Real.exp (-((t - 2) * (A - 2)))) := by rw [hexpeq]
    _ = 16 * Real.exp (-(2 * A)) * Real.exp (-((t - 2) * (A - 2))) := by ring

/-- **The hyperbola inequality.**  `a + b − 3 ≤ ab − 2` for `a, b ≥ 1`. -/
theorem prod_sub_two_ge {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : a + b - 3 ≤ a * b - 2 := by
  nlinarith [ha, hb]

/-! ### 4. The factorised termwise bound -/

/-- The constant in front of the factorised tail. -/
def tailConst (u A₁ : ℝ) : ℝ :=
  Real.pi ^ 2 * Real.exp (5 * u) * (32 * (A₁ + 3) ^ 2 * Real.exp (-(2 * A₁)))
    * Real.exp (3 * (A₁ - 2))

theorem tailConst_nonneg (u A₁ : ℝ) : 0 ≤ tailConst u A₁ := by
  unfold tailConst
  have := Real.pi_pos
  positivity

/-- **THE FACTORISED TERMWISE BOUND.**  Off the head, each mode majorant splits into a
product of two one-strand geometric factors. -/
theorem modeBndS_le_prod (x : ℝ) {u : ℝ} (hA : 20 ≤ modeA 0 0 u) {n m : ℕ}
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
    have h2 : (0 : ℝ) ≤ a * b * A₁ + 3 := by positivity
    nlinarith [h1, h2]
  have hstep := pow_four_exp_le (t := a * b) (A := A₁) hab2 (by linarith)
  have hhyp : a + b - 3 ≤ a * b - 2 := prod_sub_two_ge ha1 hb1
  have hA2 : (0 : ℝ) ≤ A₁ - 2 := by linarith
  have hshift : Real.exp (-((a * b - 2) * (A₁ - 2)))
      ≤ Real.exp (-((a + b - 3) * (A₁ - 2))) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hhyp, hA2]
  -- rewrite `modeBndS`
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
  -- the exponential bookkeeping
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

/-! ### 5. The summed tail -/

theorem summable_prod_gq {A₁ : ℝ} (hA : 20 ≤ A₁) :
    Summable (fun z : ℕ × ℕ => gq A₁ z.1 * gq A₁ z.2) :=
  (summable_gq hA).mul_of_nonneg (summable_gq hA) (gq_nonneg A₁) (gq_nonneg A₁)

theorem tsum_prod_gq {A₁ : ℝ} (hA : 20 ≤ A₁) :
    ∑' z : ℕ × ℕ, gq A₁ z.1 * gq A₁ z.2 = (∑' n : ℕ, gq A₁ n) ^ 2 := by
  have h := (summable_gq hA).tsum_mul_tsum (summable_gq hA) (summable_prod_gq hA)
  rw [← h]
  ring

/-- `S² − q² ≤ 4q³`, the whole content of the off-head bracket. -/
theorem tsum_gq_sq_sub {A₁ : ℝ} (hA : 20 ≤ A₁) :
    (∑' n : ℕ, gq A₁ n) ^ 2 - qFac A₁ ^ 2 ≤ 4 * qFac A₁ ^ 3 := by
  set q : ℝ := qFac A₁ with hqdef
  have hq0 : 0 < q := qFac_pos A₁
  have hq4 : q ≤ 1 / 4 := qFac_le_quarter hA
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hsq : (0 : ℝ) < (1 - q) ^ 2 := by positivity
  rw [tsum_gq hA, ← hqdef]
  have hval : (q * (1 - q)⁻¹) ^ 2 = q ^ 2 / (1 - q) ^ 2 := by
    rw [mul_pow, inv_pow, div_eq_mul_inv]
  rw [hval, sub_le_iff_le_add, div_le_iff₀ hsq]
  have hpoly : (0 : ℝ) ≤ 2 - 7 * q + 4 * q ^ 2 := by nlinarith [hq4, hq0, sq_nonneg q]
  have hq3 : (0 : ℝ) < q ^ 3 := by positivity
  nlinarith [mul_nonneg hq3.le hpoly]

/-- `e^{3(A₁−2)}·q³ = 1` — the exact cancellation of the shift. -/
theorem exp_shift_qcube (A₁ : ℝ) : Real.exp (3 * (A₁ - 2)) * qFac A₁ ^ 3 = 1 := by
  have h3 : qFac A₁ ^ 3 = Real.exp (-(3 * (A₁ - 2))) := by
    unfold qFac
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h3, ← Real.exp_add]
  norm_num

/-- **THE TAIL BOUND.**  `Σ_{z≠(0,0)} modeBndS x u z ≤ π²e^{5u}·128(A₁+3)²e^{−2A₁}`. -/
theorem modeBndS_tail_le (x : ℝ) {u : ℝ} (hA : 20 ≤ modeA 0 0 u) :
    (∑' z : ℕ × ℕ, if z = (0, 0) then (0 : ℝ) else modeBndS x u z)
      ≤ Real.pi ^ 2 * Real.exp (5 * u)
        * (128 * (modeA 0 0 u + 3) ^ 2 * Real.exp (-(2 * modeA 0 0 u))) := by
  set A₁ : ℝ := modeA 0 0 u with hA1
  set P : ℕ × ℕ → ℝ := fun z => gq A₁ z.1 * gq A₁ z.2 with hP
  set G : ℕ × ℕ → ℝ := fun z => if z = (0, 0) then (0 : ℝ) else tailConst u A₁ * P z with hG
  have hPnn : ∀ z : ℕ × ℕ, 0 ≤ P z := fun z =>
    mul_nonneg (gq_nonneg A₁ z.1) (gq_nonneg A₁ z.2)
  have hTC : 0 ≤ tailConst u A₁ := tailConst_nonneg u A₁
  have hPsum : Summable P := summable_prod_gq hA
  have hTPsum : Summable (fun z : ℕ × ℕ => tailConst u A₁ * P z) := hPsum.mul_left _
  -- termwise `F ≤ G`
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
      exact modeBndS_le_prod x hA hz
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
  -- evaluate `∑' G`
  have hsplit := hTPsum.tsum_eq_add_tsum_ite ((0 : ℕ), (0 : ℕ))
  have hGval : ∑' z, G z
      = tailConst u A₁ * ((∑' n : ℕ, gq A₁ n) ^ 2 - qFac A₁ ^ 2) := by
    have hP00 : P ((0 : ℕ), (0 : ℕ)) = qFac A₁ ^ 2 := by
      simp only [hP, gq_zero]
      ring
    have hTP : ∑' z : ℕ × ℕ, tailConst u A₁ * P z
        = tailConst u A₁ * (∑' n : ℕ, gq A₁ n) ^ 2 := by
      rw [tsum_mul_left, hP, tsum_prod_gq hA]
    have hGeq : ∑' z, G z = ∑' z : ℕ × ℕ,
        (if z = ((0:ℕ), (0:ℕ)) then (0 : ℝ) else tailConst u A₁ * P z) := rfl
    rw [hGeq]
    have := hsplit
    rw [hTP, hP00] at this
    linarith [this]
  rw [hGval] at hle
  refine hle.trans ?_
  -- final constant comparison
  have hbr : (∑' n : ℕ, gq A₁ n) ^ 2 - qFac A₁ ^ 2 ≤ 4 * qFac A₁ ^ 3 := tsum_gq_sq_sub hA
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

end C3B7

section AxiomAudit
#print axioms C3B7.modeTerm_abs_le_sharp
#print axioms C3B7.qFac_le_quarter
#print axioms C3B7.summable_gq
#print axioms C3B7.tsum_gq
#print axioms C3B7.pow_four_exp_le
#print axioms C3B7.prod_sub_two_ge
#print axioms C3B7.modeBndS_le_prod
#print axioms C3B7.tsum_gq_sq_sub
#print axioms C3B7.exp_shift_qcube
#print axioms C3B7.modeBndS_tail_le
end AxiomAudit
