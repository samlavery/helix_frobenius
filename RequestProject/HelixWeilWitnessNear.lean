import RequestProject.HelixWeilWitnessTail
import RequestProject.HelixLedgerPairing
import RequestProject.FoliatedGlobalPolarization

/-!
# The Weil witness, brick W2b (Case A): near-zero dominance under local maximality (ledger 1338)

For an off-axis zero `ρ₀ = β + iγ` of maximal deviation `d = |β − ½|` among the zeros within height distance `2`
of itself, the pair profile's zero side `Σ_ρ m_ρ D(ρ)²` (1336) has positive real part for large `λ`:

* `pairDiff_norm_le_M`: the sharp bound `‖D(z)‖ ≤ 2·exp(λ·Mexp ρ₀ z)`,
  `Mexp = max((Re z − β)², (Re z − (1−β))²) − (Im z − γ)²`.
* `Mexp_lt_of_near`: under local maximality every near zero other than the pair has `Mexp < 4d² = (2β−1)²`
  (same height forces smaller deviation; another height gives the gap).
* `nearSet_finite`: the near zeros form a finite set (`riemannXi_zeros_finite_in_closedBall`).
* `pairDiff_at_zero`, `pairDiff_at_mirror`: `D(ρ₀) = 1 − E`, `D(ρ₀*) = E − 1`, `E = exp(λ(2β−1)²)`.
* `gaussianZeroSide_pos_of_locallyMax`: `∃ λ ≥ 1, 0 < Re Σ'_ρ m_ρ D(ρ)²` — the pair's `2m₀(E−1)²` beats the
  finite near sum (each term `≤ 4m·exp(2λ(4d² − δ))`, `δ > 0`) and the far tail (`≤ 4e^{−6(λ−1)}T₀`, W2a).
* `gaussianWitness_of_locallyMax`: hence `Re Σ'_ρ m_ρ·laplaceTest(autocorr(pairProfile λ ρ₀)) ρ < 0`.

2026-10-14 (1341): the hypothesis is weakened to the **Gaussian peak** condition `GaussPeak` (every near zero
other than the pair has `Mexp < (2β−1)²`), which is all the dominance argument uses; local maximality is a
corollary (`gaussPeak_of_locallyMax`), and `HelixWeilWitnessAscent` shows a Gaussian peak exists whenever an
off-axis zero exists, so Case B is discharged. No `sorry`, no `axiom`, no window.
-/

open Complex
open scoped Real ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixWeilWitness

open CriticalLinePhasor.ContourArgument CriticalLinePhasor.HelixCarrierWeil

/-! ## The sharp exponent -/

/-- The exponent governing `‖D(z)‖`: the larger of the two abscissa gaps squared, minus the height gap squared. -/
def Mexp (ρ₀ z : ℂ) : ℝ :=
  max ((z.re - ρ₀.re) ^ 2) ((z.re - (1 - ρ₀.re)) ^ 2) - (z.im - ρ₀.im) ^ 2

theorem norm_exp_lam_sq_eq (lam : ℝ) (z ρ : ℂ) :
    ‖Complex.exp ((lam : ℂ) * (z - ρ) ^ 2)‖ = Real.exp (lam * ((z.re - ρ.re) ^ 2 - (z.im - ρ.im) ^ 2)) := by
  rw [Complex.norm_exp, re_lam_mul_sq]

/-- **The sharp bound** `‖D(z)‖ ≤ 2·exp(λ·Mexp)`. -/
theorem pairDiff_norm_le_M {lam : ℝ} (hlam : 0 ≤ lam) (ρ₀ z : ℂ) :
    ‖pairDiff lam ρ₀ z‖ ≤ 2 * Real.exp (lam * Mexp ρ₀ z) := by
  unfold pairDiff Mexp
  have hmre : (1 - conj ρ₀).re = 1 - ρ₀.re := by simp [Complex.conj_re]
  have hmim : (1 - conj ρ₀).im = ρ₀.im := by simp [Complex.conj_im]
  have h1 : ‖Complex.exp ((lam : ℂ) * (z - ρ₀) ^ 2)‖
      ≤ Real.exp (lam * (max ((z.re - ρ₀.re) ^ 2) ((z.re - (1 - ρ₀.re)) ^ 2) - (z.im - ρ₀.im) ^ 2)) := by
    rw [norm_exp_lam_sq_eq]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hlam
    linarith [le_max_left ((z.re - ρ₀.re) ^ 2) ((z.re - (1 - ρ₀.re)) ^ 2)]
  have h2 : ‖Complex.exp ((lam : ℂ) * (z - (1 - conj ρ₀)) ^ 2)‖
      ≤ Real.exp (lam * (max ((z.re - ρ₀.re) ^ 2) ((z.re - (1 - ρ₀.re)) ^ 2) - (z.im - ρ₀.im) ^ 2)) := by
    rw [norm_exp_lam_sq_eq, hmre, hmim]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hlam
    linarith [le_max_right ((z.re - ρ₀.re) ^ 2) ((z.re - (1 - ρ₀.re)) ^ 2)]
  calc ‖Complex.exp ((lam : ℂ) * (z - ρ₀) ^ 2) - Complex.exp ((lam : ℂ) * (z - (1 - conj ρ₀)) ^ 2)‖
      ≤ ‖Complex.exp ((lam : ℂ) * (z - ρ₀) ^ 2)‖ + ‖Complex.exp ((lam : ℂ) * (z - (1 - conj ρ₀)) ^ 2)‖ :=
        norm_sub_le _ _
    _ ≤ _ + _ := add_le_add h1 h2
    _ = 2 * Real.exp (lam * (max ((z.re - ρ₀.re) ^ 2) ((z.re - (1 - ρ₀.re)) ^ 2) - (z.im - ρ₀.im) ^ 2)) := by
        ring

/-! ## Local maximality gives the strict margin -/

/-- `(s' − s)² < 4s²` unless `s' = −s`, for `|s'| ≤ |s|`. -/
theorem sq_sub_lt_or {s s' : ℝ} (h : |s'| ≤ |s|) : (s' - s) ^ 2 < 4 * s ^ 2 ∨ s' = -s := by
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs] at h
    have h1 := (abs_le.mp h).1
    have h2 := (abs_le.mp h).2
    by_cases heq : s' = -s
    · right; exact heq
    · left
      have hlt : -s < s' := lt_of_le_of_ne h1 (fun h0 => heq h0.symm)
      nlinarith
  · rw [abs_of_neg hs] at h
    have h1 := (abs_le.mp h).1
    have h2 := (abs_le.mp h).2
    by_cases heq : s' = -s
    · right; exact heq
    · left
      have hlt : s' < -s := lt_of_le_of_ne h2 heq
      nlinarith

/-- `(s' + s)² < 4s²` unless `s' = s`, for `|s'| ≤ |s|`. -/
theorem sq_add_lt_or {s s' : ℝ} (h : |s'| ≤ |s|) : (s' + s) ^ 2 < 4 * s ^ 2 ∨ s' = s := by
  have h' : |s'| ≤ |-s| := by rwa [abs_neg]
  rcases sq_sub_lt_or h' with hlt | heq
  · left
    have : (s' - -s) ^ 2 = (s' + s) ^ 2 := by ring
    rw [this] at hlt
    have : 4 * (-s) ^ 2 = 4 * s ^ 2 := by ring
    linarith
  · right; linarith

/-- **The margin**: under local maximality, a near zero other than the pair has `Mexp < (2β − 1)²`. -/
theorem Mexp_lt_of_near {ρ₀ : ℂ} {d : ℝ} (hd : d = |ρ₀.re - 1 / 2|) {ρ : ℂ}
    (hdev : |ρ.re - 1 / 2| ≤ d) (hne1 : ρ ≠ ρ₀) (hne2 : ρ ≠ 1 - conj ρ₀) :
    Mexp ρ₀ ρ < (2 * ρ₀.re - 1) ^ 2 := by
  unfold Mexp
  set s : ℝ := ρ₀.re - 1 / 2 with hs
  set s' : ℝ := ρ.re - 1 / 2 with hs'
  have hdev' : |s'| ≤ |s| := by rw [hs, hs', ← hd]; exact hdev
  have e1 : (ρ.re - ρ₀.re) ^ 2 = (s' - s) ^ 2 := by rw [hs, hs']; ring
  have e2 : (ρ.re - (1 - ρ₀.re)) ^ 2 = (s' + s) ^ 2 := by rw [hs, hs']; ring
  have e3 : (2 * ρ₀.re - 1) ^ 2 = 4 * s ^ 2 := by rw [hs]; ring
  rw [e1, e2, e3]
  have hsq : 0 ≤ (ρ.im - ρ₀.im) ^ 2 := sq_nonneg _
  by_cases hu : ρ.im = ρ₀.im
  · -- same height: both abscissa gaps are strict, since `ρ` is neither `ρ₀` nor its mirror
    have hA : (s' - s) ^ 2 < 4 * s ^ 2 := by
      rcases sq_sub_lt_or hdev' with hlt | heq
      · exact hlt
      · exfalso; apply hne2
        apply Complex.ext
        · simp [Complex.conj_re]; rw [hs, hs'] at heq; linarith
        · simp [Complex.conj_im]; exact hu
    have hB : (s' + s) ^ 2 < 4 * s ^ 2 := by
      rcases sq_add_lt_or hdev' with hlt | heq
      · exact hlt
      · exfalso; apply hne1
        apply Complex.ext
        · rw [hs, hs'] at heq; linarith
        · exact hu
    have hmax : max ((s' - s) ^ 2) ((s' + s) ^ 2) < 4 * s ^ 2 := max_lt hA hB
    linarith
  · -- another height: the gap is strictly positive and the abscissa gaps are at most `4s²`
    have hu2 : 0 < (ρ.im - ρ₀.im) ^ 2 := by
      have : ρ.im - ρ₀.im ≠ 0 := sub_ne_zero.mpr hu
      positivity
    have hA : (s' - s) ^ 2 ≤ 4 * s ^ 2 := by
      rcases sq_sub_lt_or hdev' with hlt | heq
      · exact hlt.le
      · rw [heq]; nlinarith
    have hB : (s' + s) ^ 2 ≤ 4 * s ^ 2 := by
      rcases sq_add_lt_or hdev' with hlt | heq
      · exact hlt.le
      · rw [heq]; nlinarith
    have hmax : max ((s' - s) ^ 2) ((s' + s) ^ 2) ≤ 4 * s ^ 2 := max_le hA hB
    linarith

/-! ## The Gaussian peak condition (weaker than local maximality) -/

/-- **Gaussian peak**: every near zero other than `ρ₀` and its mirror has Gaussian exponent strictly below the
pair's `4d² = (2β − 1)²`. This is exactly what the dominance argument consumes; local maximality implies it
(`gaussPeak_of_locallyMax`), and a competitor with larger deviation is allowed when its height separation pays
for it. -/
def GaussPeak (ρ₀ : Zero) : Prop :=
  ∀ ρ : Zero, |ρ.val.im - ρ₀.val.im| < 2 → ρ.val ≠ ρ₀.val → ρ.val ≠ 1 - conj ρ₀.val →
    Mexp ρ₀.val ρ.val < (2 * ρ₀.val.re - 1) ^ 2

theorem gaussPeak_of_locallyMax (ρ₀ : Zero)
    (hmax : ∀ ρ : Zero, |ρ.val.im - ρ₀.val.im| < 2 → |ρ.val.re - 1 / 2| ≤ |ρ₀.val.re - 1 / 2|) :
    GaussPeak ρ₀ :=
  fun ρ hn h1 h2 => Mexp_lt_of_near rfl (hmax ρ hn) h1 h2

/-! ## The near set is finite -/

/-- The near zeros: height distance `< 2` from `γ`. -/
def nearSet (ρ₀ : ℂ) : Set Zero := {ρ : Zero | |ρ.val.im - ρ₀.im| < 2}

theorem nearSet_finite (ρ₀ : ℂ) : (nearSet ρ₀).Finite := by
  have hfin := ZD.ZeroCount.riemannXi_zeros_finite_in_closedBall (|ρ₀.im| + 3)
  have hsub : nearSet ρ₀ ⊆ Subtype.val ⁻¹' (Metric.closedBall (0 : ℂ) (|ρ₀.im| + 3) ∩ {z | ZD.riemannXi z = 0}) := by
    intro ρ hρ
    simp only [Set.mem_preimage, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right, Set.mem_ofPred_eq]
    constructor
    · have hre : |ρ.val.re| ≤ 1 := by
        have := ρ.2.1; have := ρ.2.2.1; rw [abs_le]; constructor <;> linarith
      have him : |ρ.val.im| ≤ |ρ₀.im| + 2 := by
        have hρ' : |ρ.val.im - ρ₀.im| < 2 := hρ
        calc |ρ.val.im| = |(ρ.val.im - ρ₀.im) + ρ₀.im| := by ring_nf
          _ ≤ |ρ.val.im - ρ₀.im| + |ρ₀.im| := abs_add_le _ _
          _ ≤ |ρ₀.im| + 2 := by linarith
      calc ‖ρ.val‖ ≤ |ρ.val.re| + |ρ.val.im| := Complex.norm_le_abs_re_add_abs_im ρ.val
        _ ≤ 1 + (|ρ₀.im| + 2) := add_le_add hre him
        _ = |ρ₀.im| + 3 := by ring
    · exact ZD.riemannXi_eq_zero_of_mem_NontrivialZeros _ ρ.2
  exact (hfin.preimage Subtype.val_injective.injOn).subset hsub

/-! ## The pair's own values -/

theorem pairDiff_at_zero (lam : ℝ) (ρ₀ : ℂ) :
    pairDiff lam ρ₀ ρ₀ = 1 - Complex.exp (lam * ((2 * ρ₀.re - 1 : ℝ) : ℂ) ^ 2) := by
  unfold pairDiff
  have hd : ρ₀ - (1 - conj ρ₀) = ((2 * ρ₀.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.conj_re]; ring
    · simp [Complex.conj_im]
  rw [sub_self, hd]
  simp

theorem pairDiff_at_mirror (lam : ℝ) (ρ₀ : ℂ) :
    pairDiff lam ρ₀ (1 - conj ρ₀) = Complex.exp (lam * ((2 * ρ₀.re - 1 : ℝ) : ℂ) ^ 2) - 1 := by
  unfold pairDiff
  have hd : (1 - conj ρ₀) - ρ₀ = -((2 * ρ₀.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.conj_re]; ring
    · simp [Complex.conj_im]
  rw [sub_self, hd, neg_sq]
  simp

/-- The mirror zero is a zero with the same multiplicity. -/
theorem mirror_mem (ρ : Zero) : (1 - conj ρ.val) ∈ ZD.NontrivialZeros := by
  rw [← ZD.riemannXi_eq_zero_iff, CriticalLinePhasor.ContourArgument.riemannXi_one_sub_conj,
    ZD.riemannXi_eq_zero_of_mem_NontrivialZeros _ ρ.2, map_zero]

theorem mirror_order (ρ : ℂ) : ZD.xiOrderNat (1 - conj ρ) = ZD.xiOrderNat ρ := by
  rw [CriticalLinePhasor.CaptureInterfaceAudit.xiOrderNat_one_sub,
    CriticalLinePhasor.FoliatedGlobalPolarization.xiOrderNat_conj]

/-! ## The zero side as a sum of complex terms -/

/-- The complex term `m_ρ·D(ρ)²` of the zero side at the pair profile. -/
def zTerm (lam : ℝ) (ρ₀ : ℂ) (ρ : Zero) : ℂ := (ZD.xiOrderNat ρ.val : ℂ) * pairDiff lam ρ₀ ρ.val ^ 2

theorem zTerm_norm_le {lam : ℝ} (hlam : 1 ≤ lam) {ρ₀ : ℂ} (hρ0 : 0 ≤ ρ₀.re) (hρ1 : ρ₀.re ≤ 1) (ρ : Zero) :
    ‖zTerm lam ρ₀ ρ‖ ≤ (4 * Real.exp (2 * lam)) * ((ZD.xiOrderNat ρ.val : ℝ) * farWeight ρ₀.im ρ) := by
  unfold zTerm
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  have hz0 : 0 ≤ ρ.val.re := ρ.2.1.le
  have hz1 : ρ.val.re ≤ 1 := ρ.2.2.1.le
  have hD := pairDiff_norm_le (by linarith) hρ0 hρ1 hz0 hz1 (lam := lam) (z := ρ.val)
  set u : ℝ := ρ.val.im - ρ₀.im with hu
  have hD2 : ‖pairDiff lam ρ₀ ρ.val‖ ^ 2 ≤ (2 * Real.exp (lam * (1 - u ^ 2))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hD 2
  have hexp : (2 * Real.exp (lam * (1 - u ^ 2))) ^ 2 ≤ 4 * Real.exp (2 * lam) * farWeight ρ₀.im ρ := by
    unfold farWeight
    rw [← hu]
    have hl : (2 * Real.exp (lam * (1 - u ^ 2))) ^ 2 = 4 * Real.exp (2 * (lam * (1 - u ^ 2))) := by
      rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
      have : lam * (1 - u ^ 2) + lam * (1 - u ^ 2) = 2 * (lam * (1 - u ^ 2)) := by ring
      rw [this]; norm_num
    have hr : 4 * Real.exp (2 * lam) * Real.exp (-2 * (u ^ 2 - 1))
        = 4 * Real.exp (2 * lam + -2 * (u ^ 2 - 1)) := by
      rw [mul_assoc, ← Real.exp_add]
    rw [hl, hr]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hlam) (sq_nonneg u)]
  have hm : (0 : ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
  calc (ZD.xiOrderNat ρ.val : ℝ) * ‖pairDiff lam ρ₀ ρ.val‖ ^ 2
      ≤ (ZD.xiOrderNat ρ.val : ℝ) * (4 * Real.exp (2 * lam) * farWeight ρ₀.im ρ) :=
        mul_le_mul_of_nonneg_left (hD2.trans hexp) hm
    _ = (4 * Real.exp (2 * lam)) * ((ZD.xiOrderNat ρ.val : ℝ) * farWeight ρ₀.im ρ) := by ring

theorem zTerm_summable {lam : ℝ} (hlam : 1 ≤ lam) {ρ₀ : ℂ} (hρ0 : 0 ≤ ρ₀.re) (hρ1 : ρ₀.re ≤ 1) :
    Summable (zTerm lam ρ₀) :=
  Summable.of_norm_bounded ((farWeight_summable ρ₀.im).mul_left _) (zTerm_norm_le hlam hρ0 hρ1)

/-- The real part of the zero side splits into the near part (finite) and the far part. -/
def nearRe (lam : ℝ) (ρ₀ : ℂ) (ρ : Zero) : ℝ :=
  if |ρ.val.im - ρ₀.im| < 2 then (zTerm lam ρ₀ ρ).re else 0

def farRe (lam : ℝ) (ρ₀ : ℂ) (ρ : Zero) : ℝ :=
  if |ρ.val.im - ρ₀.im| < 2 then 0 else (zTerm lam ρ₀ ρ).re

theorem re_zTerm_eq (lam : ℝ) (ρ₀ : ℂ) (ρ : Zero) :
    (zTerm lam ρ₀ ρ).re = nearRe lam ρ₀ ρ + farRe lam ρ₀ ρ := by
  unfold nearRe farRe
  split_ifs <;> simp

/-- The far real part is bounded below by `−farTerm`. -/
theorem farRe_ge (lam : ℝ) (ρ₀ : ℂ) (ρ : Zero) : -farTerm lam ρ₀ ρ ≤ farRe lam ρ₀ ρ := by
  unfold farRe farTerm
  by_cases h : |ρ.val.im - ρ₀.im| < 2
  · rw [if_pos h, if_neg (by linarith)]; simp
  · rw [if_neg h, if_pos (by linarith)]
    have hre : -‖zTerm lam ρ₀ ρ‖ ≤ (zTerm lam ρ₀ ρ).re := by
      have := Complex.abs_re_le_norm (zTerm lam ρ₀ ρ)
      have := neg_abs_le (zTerm lam ρ₀ ρ).re
      linarith
    have hn : ‖zTerm lam ρ₀ ρ‖ = (ZD.xiOrderNat ρ.val : ℝ) * ‖pairDiff lam ρ₀ ρ.val‖ ^ 2 := by
      unfold zTerm; rw [norm_mul, norm_pow, Complex.norm_natCast]
    rw [hn] at hre
    exact hre

theorem nearRe_eq_zero_of_not_mem (lam : ℝ) (ρ₀ : ℂ) {ρ : Zero} (h : ρ ∉ (nearSet_finite ρ₀).toFinset) :
    nearRe lam ρ₀ ρ = 0 := by
  unfold nearRe
  rw [if_neg]
  intro hlt
  apply h
  rw [Set.Finite.mem_toFinset]
  exact hlt

theorem nearRe_summable (lam : ℝ) (ρ₀ : ℂ) : Summable (nearRe lam ρ₀) :=
  summable_of_ne_finset_zero (fun ρ hρ => nearRe_eq_zero_of_not_mem lam ρ₀ hρ)

theorem tsum_nearRe (lam : ℝ) (ρ₀ : ℂ) :
    ∑' ρ : Zero, nearRe lam ρ₀ ρ = ∑ ρ ∈ (nearSet_finite ρ₀).toFinset, (zTerm lam ρ₀ ρ).re := by
  rw [tsum_eq_sum (fun ρ hρ => nearRe_eq_zero_of_not_mem lam ρ₀ hρ)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ
  have hρ' : |ρ.val.im - ρ₀.im| < 2 := hρ
  unfold nearRe
  rw [if_pos hρ']

/-! ## Assembly -/

/-- A uniform margin on a finite set of near zeros other than the pair, under the Gaussian peak condition. -/
theorem exists_margin (ρ₀ : Zero) (hpeak : GaussPeak ρ₀)
    (S' : Finset Zero) (hS' : ∀ ρ ∈ S', |ρ.val.im - ρ₀.val.im| < 2 ∧ ρ.val ≠ ρ₀.val ∧ ρ.val ≠ 1 - conj ρ₀.val) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ ∈ S', Mexp ρ₀.val ρ.val ≤ (2 * ρ₀.val.re - 1) ^ 2 - δ := by
  by_cases hne : S'.Nonempty
  · obtain ⟨ρm, hρm, hmin⟩ := Finset.exists_min_image S' (fun ρ => (2 * ρ₀.val.re - 1) ^ 2 - Mexp ρ₀.val ρ.val) hne
    obtain ⟨hn, h1, h2⟩ := hS' ρm hρm
    have hlt := hpeak ρm hn h1 h2
    refine ⟨(2 * ρ₀.val.re - 1) ^ 2 - Mexp ρ₀.val ρm.val, by linarith, fun ρ hρ => ?_⟩
    have := hmin ρ hρ
    linarith
  · refine ⟨1, one_pos, fun ρ hρ => ?_⟩
    exact absurd ⟨ρ, hρ⟩ hne

/-- `log A ≤ aλ` for `λ` at least `log A / a`. -/
theorem exp_ge_of_le {a A lam : ℝ} (ha : 0 < a) (hA : 0 < A) (h : Real.log A / a ≤ lam) :
    A ≤ Real.exp (a * lam) := by
  rw [← Real.log_le_iff_le_exp hA]
  rw [div_le_iff₀ ha] at h
  linarith

set_option maxHeartbeats 1600000 in
/-- **The zero side is positive for large λ, at a Gaussian peak.** -/
theorem gaussianZeroSide_pos_of_peak (ρ₀ : Zero) (hβ : ρ₀.val.re ≠ 1 / 2) (hpeak : GaussPeak ρ₀) :
    ∃ lam : ℝ, 1 ≤ lam ∧ 0 < (∑' ρ : Zero, zTerm lam ρ₀.val ρ).re := by
  -- data
  have hρ0 : 0 ≤ ρ₀.val.re := ρ₀.2.1.le
  have hρ1 : ρ₀.val.re ≤ 1 := ρ₀.2.2.1.le
  set c : ℝ := (2 * ρ₀.val.re - 1) ^ 2 with hcdef
  have hc : 0 < c := by
    have : 2 * ρ₀.val.re - 1 ≠ 0 := by intro h; apply hβ; linarith
    positivity
  -- the mirror as an element of `Zero`
  let ρm : Zero := ⟨1 - conj ρ₀.val, mirror_mem ρ₀⟩
  have hρm_ne : ρm ≠ ρ₀ := by
    intro h
    have := congrArg (fun ρ : Zero => ρ.val.re) h
    simp only [ρm, Complex.sub_re, Complex.one_re, Complex.conj_re] at this
    apply hβ; linarith
  -- the near finite set and the set of the other near zeros
  set S : Finset Zero := (nearSet_finite ρ₀.val).toFinset with hSdef
  have hρ₀S : ρ₀ ∈ S := by
    rw [hSdef, Set.Finite.mem_toFinset]; show |ρ₀.val.im - ρ₀.val.im| < 2; simp
  have hρmS : ρm ∈ S.erase ρ₀ := by
    rw [Finset.mem_erase]
    refine ⟨hρm_ne, ?_⟩
    rw [hSdef, Set.Finite.mem_toFinset]
    show |(1 - conj ρ₀.val).im - ρ₀.val.im| < 2
    simp [Complex.conj_im]
  set S' : Finset Zero := (S.erase ρ₀).erase ρm with hS'def
  have hS' : ∀ ρ ∈ S', |ρ.val.im - ρ₀.val.im| < 2 ∧ ρ.val ≠ ρ₀.val ∧ ρ.val ≠ 1 - conj ρ₀.val := by
    intro ρ hρ
    rw [hS'def, Finset.mem_erase, Finset.mem_erase] at hρ
    obtain ⟨h1, h2, h3⟩ := hρ
    rw [hSdef, Set.Finite.mem_toFinset] at h3
    refine ⟨h3, fun h => h2 (Subtype.ext h), fun h => h1 (Subtype.ext h)⟩
  obtain ⟨δ, hδ, hmargin⟩ := exists_margin ρ₀ hpeak S' hS'
  -- the constants
  set K : ℝ := ∑ ρ ∈ S', (ZD.xiOrderNat ρ.val : ℝ) with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  set T₀ : ℝ := ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℝ) * farWeight ρ₀.val.im ρ with hT₀def
  have hT₀ : 0 ≤ T₀ := tsum_nonneg (fun ρ => mul_nonneg (Nat.cast_nonneg _) (farWeight_nonneg _ _))
  -- choose λ
  set lam : ℝ := max (max 1 (Real.log 2 / c)) (max (Real.log (16 * (K + 1)) / (2 * δ)) (Real.log (16 * T₀ + 1) / (2 * c)))
    with hlamdef
  have hlam1 : 1 ≤ lam := le_trans (le_max_left _ _) (le_max_left _ _)
  have hE2 : 2 ≤ Real.exp (c * lam) :=
    exp_ge_of_le hc (by norm_num) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hKe : 16 * (K + 1) ≤ Real.exp (2 * δ * lam) :=
    exp_ge_of_le (by positivity) (by positivity) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hTe : 16 * T₀ + 1 ≤ Real.exp (2 * c * lam) :=
    exp_ge_of_le (by positivity) (by positivity) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨lam, hlam1, ?_⟩
  -- the real part splits
  have hsum := zTerm_summable hlam1 hρ0 hρ1
  rw [Complex.re_tsum hsum]
  have hre_sum : Summable (fun ρ : Zero => (zTerm lam ρ₀.val ρ).re) := Complex.reCLM.summable hsum
  have hfar_sum : Summable (farRe lam ρ₀.val) := by
    have := hre_sum.sub (nearRe_summable lam ρ₀.val)
    refine this.congr fun ρ => ?_
    show (zTerm lam ρ₀.val ρ).re - nearRe lam ρ₀.val ρ = farRe lam ρ₀.val ρ
    rw [re_zTerm_eq]; ring
  have hsplit : ∑' ρ : Zero, (zTerm lam ρ₀.val ρ).re
      = ∑' ρ : Zero, nearRe lam ρ₀.val ρ + ∑' ρ : Zero, farRe lam ρ₀.val ρ := by
    rw [← Summable.tsum_add (nearRe_summable lam ρ₀.val) hfar_sum]
    apply tsum_congr
    intro ρ
    exact re_zTerm_eq lam ρ₀.val ρ
  rw [hsplit, tsum_nearRe]
  -- the far part
  have hfar : -(4 * Real.exp (-6 * (lam - 1)) * T₀) ≤ ∑' ρ : Zero, farRe lam ρ₀.val ρ := by
    have h1 : ∑' ρ : Zero, -farTerm lam ρ₀.val ρ ≤ ∑' ρ : Zero, farRe lam ρ₀.val ρ :=
      Summable.tsum_le_tsum (farRe_ge lam ρ₀.val) (farTerm_summable hlam1 hρ0 hρ1).neg hfar_sum
    rw [tsum_neg] at h1
    have h2 := farTail_le hlam1 hρ0 hρ1
    linarith
  -- the near part: the pair plus the others
  rw [← Finset.add_sum_erase S _ hρ₀S, ← Finset.add_sum_erase (S.erase ρ₀) _ hρmS]
  set E : ℝ := Real.exp (c * lam) with hEdef
  have hEc : Complex.exp ((lam : ℂ) * ((2 * ρ₀.val.re - 1 : ℝ) : ℂ) ^ 2) = (E : ℂ) := by
    rw [hEdef, hcdef, Complex.ofReal_exp]; push_cast; ring_nf
  have hpair0 : (zTerm lam ρ₀.val ρ₀).re = (ZD.xiOrderNat ρ₀.val : ℝ) * (1 - E) ^ 2 := by
    unfold zTerm
    rw [pairDiff_at_zero, hEc]
    have : ((ZD.xiOrderNat ρ₀.val : ℂ) * (1 - (E : ℂ)) ^ 2) = (((ZD.xiOrderNat ρ₀.val : ℝ) * (1 - E) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
  have hpairm : (zTerm lam ρ₀.val ρm).re = (ZD.xiOrderNat ρ₀.val : ℝ) * (E - 1) ^ 2 := by
    unfold zTerm
    show ((ZD.xiOrderNat (1 - conj ρ₀.val) : ℂ) * pairDiff lam ρ₀.val (1 - conj ρ₀.val) ^ 2).re = _
    rw [pairDiff_at_mirror, hEc, mirror_order]
    have : ((ZD.xiOrderNat ρ₀.val : ℂ) * ((E : ℂ) - 1) ^ 2) = (((ZD.xiOrderNat ρ₀.val : ℝ) * (E - 1) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
  have hm₀ : (1 : ℝ) ≤ (ZD.xiOrderNat ρ₀.val : ℝ) :=
    Nat.one_le_cast.mpr (Nat.succ_le_of_lt (ZD.xiOrderNat_pos_of_mem_NontrivialZeros ρ₀.2))
  -- the other near zeros
  have hothers : -(4 * K * Real.exp (2 * c * lam) / Real.exp (2 * δ * lam))
      ≤ ∑ ρ ∈ S', (zTerm lam ρ₀.val ρ).re := by
    have hterm : ∀ ρ ∈ S', -((ZD.xiOrderNat ρ.val : ℝ) * (4 * Real.exp (2 * c * lam) / Real.exp (2 * δ * lam)))
        ≤ (zTerm lam ρ₀.val ρ).re := by
      intro ρ hρ
      have hre : -‖zTerm lam ρ₀.val ρ‖ ≤ (zTerm lam ρ₀.val ρ).re := by
        have := Complex.abs_re_le_norm (zTerm lam ρ₀.val ρ)
        have := neg_abs_le (zTerm lam ρ₀.val ρ).re
        linarith
      have hn : ‖zTerm lam ρ₀.val ρ‖ = (ZD.xiOrderNat ρ.val : ℝ) * ‖pairDiff lam ρ₀.val ρ.val‖ ^ 2 := by
        unfold zTerm; rw [norm_mul, norm_pow, Complex.norm_natCast]
      have hD := pairDiff_norm_le_M (by linarith) ρ₀.val ρ.val (lam := lam)
      have hD2 : ‖pairDiff lam ρ₀.val ρ.val‖ ^ 2 ≤ 4 * Real.exp (2 * (lam * Mexp ρ₀.val ρ.val)) := by
        calc ‖pairDiff lam ρ₀.val ρ.val‖ ^ 2 ≤ (2 * Real.exp (lam * Mexp ρ₀.val ρ.val)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hD 2
          _ = 4 * Real.exp (2 * (lam * Mexp ρ₀.val ρ.val)) := by
              rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
              have : lam * Mexp ρ₀.val ρ.val + lam * Mexp ρ₀.val ρ.val = 2 * (lam * Mexp ρ₀.val ρ.val) := by ring
              rw [this]; norm_num
      have hM : Mexp ρ₀.val ρ.val ≤ c - δ := by rw [hcdef]; exact hmargin ρ hρ
      have hexpM : Real.exp (2 * (lam * Mexp ρ₀.val ρ.val)) ≤ Real.exp (2 * c * lam) / Real.exp (2 * δ * lam) := by
        rw [← Real.exp_sub]
        apply Real.exp_le_exp.mpr
        have hl0 : 0 ≤ lam := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hM hl0]
      have hm : (0 : ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
      calc -((ZD.xiOrderNat ρ.val : ℝ) * (4 * Real.exp (2 * c * lam) / Real.exp (2 * δ * lam)))
          ≤ -((ZD.xiOrderNat ρ.val : ℝ) * (4 * Real.exp (2 * (lam * Mexp ρ₀.val ρ.val)))) := by
            apply neg_le_neg
            apply mul_le_mul_of_nonneg_left _ hm
            rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_left hexpM (by norm_num)
        _ ≤ -((ZD.xiOrderNat ρ.val : ℝ) * ‖pairDiff lam ρ₀.val ρ.val‖ ^ 2) := by
            apply neg_le_neg
            exact mul_le_mul_of_nonneg_left hD2 hm
        _ ≤ (zTerm lam ρ₀.val ρ).re := by rw [hn] at hre; exact hre
    have hrew : ∑ ρ ∈ S', -((ZD.xiOrderNat ρ.val : ℝ) * (4 * Real.exp (2 * c * lam) / Real.exp (2 * δ * lam)))
        = -(4 * (∑ ρ ∈ S', (ZD.xiOrderNat ρ.val : ℝ)) * Real.exp (2 * c * lam) / Real.exp (2 * δ * lam)) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl; intro ρ _; ring
    have hle := Finset.sum_le_sum hterm
    rw [hrew] at hle
    rw [hKdef]
    exact hle
  -- combine
  rw [hpair0, hpairm]
  have hE2' : E ^ 2 = Real.exp (2 * c * lam) := by
    rw [hEdef, sq, ← Real.exp_add]; ring_nf
  have hpairs : Real.exp (2 * c * lam) / 2
      ≤ (ZD.xiOrderNat ρ₀.val : ℝ) * (1 - E) ^ 2 + (ZD.xiOrderNat ρ₀.val : ℝ) * (E - 1) ^ 2 := by
    have h1 : E ^ 2 / 4 ≤ (E - 1) ^ 2 := by nlinarith [sq_nonneg (E - 2), hE2]
    have h2 : (1 - E) ^ 2 = (E - 1) ^ 2 := by ring
    rw [h2, ← hE2']
    have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ (ZD.xiOrderNat ρ₀.val : ℝ))
    have h4 : E ^ 2 / 2 ≤ (ZD.xiOrderNat ρ₀.val : ℝ) * (E ^ 2 / 4) + (ZD.xiOrderNat ρ₀.val : ℝ) * (E ^ 2 / 4) := by
      have : 0 ≤ E ^ 2 := sq_nonneg E
      nlinarith [mul_le_mul_of_nonneg_right hm₀ (by positivity : (0:ℝ) ≤ E ^ 2 / 4)]
    linarith
  have hothers' : -(Real.exp (2 * c * lam) / 4) ≤ ∑ ρ ∈ S', (zTerm lam ρ₀.val ρ).re := by
    have hpos : 0 < Real.exp (2 * δ * lam) := Real.exp_pos _
    have : 4 * K * Real.exp (2 * c * lam) / Real.exp (2 * δ * lam) ≤ Real.exp (2 * c * lam) / 4 := by
      rw [div_le_div_iff₀ hpos (by norm_num)]
      have := mul_le_mul_of_nonneg_left hKe (by positivity : (0:ℝ) ≤ 4 * K * Real.exp (2 * c * lam))
      nlinarith [Real.exp_pos (2 * c * lam), hK]
    linarith
  have hfar' : -(Real.exp (2 * c * lam) / 4) < ∑' ρ : Zero, farRe lam ρ₀.val ρ := by
    have he6 : Real.exp (-6 * (lam - 1)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have : 4 * Real.exp (-6 * (lam - 1)) * T₀ ≤ 4 * T₀ := by
      have := mul_le_mul_of_nonneg_right he6 hT₀
      linarith
    have h16 : 4 * T₀ < Real.exp (2 * c * lam) / 4 := by linarith
    linarith
  linarith

/-- Case A as a corollary: local maximality gives a Gaussian peak. -/
theorem gaussianZeroSide_pos_of_locallyMax (ρ₀ : Zero) (hβ : ρ₀.val.re ≠ 1 / 2)
    (hmax : ∀ ρ : Zero, |ρ.val.im - ρ₀.val.im| < 2 → |ρ.val.re - 1 / 2| ≤ |ρ₀.val.re - 1 / 2|) :
    ∃ lam : ℝ, 1 ≤ lam ∧ 0 < (∑' ρ : Zero, zTerm lam ρ₀.val ρ).re :=
  gaussianZeroSide_pos_of_peak ρ₀ hβ (gaussPeak_of_locallyMax ρ₀ hmax)

/-! ## W2c: the Gaussian-class witness -/

/-- **The Gaussian-class witness at a Gaussian peak**: the zero side of the explicit formula at the
autocorrelation of the pair profile is strictly negative for some `λ ≥ 1`. -/
theorem gaussianWitness_of_peak (ρ₀ : Zero) (hβ : ρ₀.val.re ≠ 1 / 2) (hpeak : GaussPeak ρ₀) :
    ∃ lam : ℝ, 1 ≤ lam ∧
      (∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * laplaceTest (autocorr (pairProfile lam ρ₀.val)) ρ.val).re < 0 := by
  obtain ⟨lam, hlam, hpos⟩ := gaussianZeroSide_pos_of_peak ρ₀ hβ hpeak
  refine ⟨lam, hlam, ?_⟩
  have hlam0 : 0 < lam := by linarith
  have hrw : (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * laplaceTest (autocorr (pairProfile lam ρ₀.val)) ρ.val)
      = fun ρ : Zero => -((Complex.normSq (gaussNorm lam) : ℂ)) * zTerm lam ρ₀.val ρ := by
    funext ρ
    rw [pairProfile_autocorr_eq hlam0]
    unfold zTerm
    ring
  rw [hrw, tsum_mul_left, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  have hN : 0 < Complex.normSq (gaussNorm lam) := Complex.normSq_pos.mpr (gaussNorm_ne_zero hlam0)
  simp only [neg_zero, zero_mul, sub_zero]
  nlinarith [mul_pos hN hpos]

/-- Case A as a corollary of the peak version. -/
theorem gaussianWitness_of_locallyMax (ρ₀ : Zero) (hβ : ρ₀.val.re ≠ 1 / 2)
    (hmax : ∀ ρ : Zero, |ρ.val.im - ρ₀.val.im| < 2 → |ρ.val.re - 1 / 2| ≤ |ρ₀.val.re - 1 / 2|) :
    ∃ lam : ℝ, 1 ≤ lam ∧
      (∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * laplaceTest (autocorr (pairProfile lam ρ₀.val)) ρ.val).re < 0 :=
  gaussianWitness_of_peak ρ₀ hβ (gaussPeak_of_locallyMax ρ₀ hmax)

end CriticalLinePhasor.HelixWeilWitness

end

#print axioms CriticalLinePhasor.HelixWeilWitness.gaussianZeroSide_pos_of_peak
#print axioms CriticalLinePhasor.HelixWeilWitness.gaussianWitness_of_peak
#print axioms CriticalLinePhasor.HelixWeilWitness.gaussianZeroSide_pos_of_locallyMax
#print axioms CriticalLinePhasor.HelixWeilWitness.gaussianWitness_of_locallyMax

#print axioms CriticalLinePhasor.HelixWeilWitness.pairDiff_norm_le_M
#print axioms CriticalLinePhasor.HelixWeilWitness.Mexp_lt_of_near
#print axioms CriticalLinePhasor.HelixWeilWitness.nearSet_finite
#print axioms CriticalLinePhasor.HelixWeilWitness.mirror_mem
