import RequestProject.DVPWeightedCount
import RequestProject.DVPEulerMaclaurin

/-!
# B2‴: polynomial growth of ζ′ on the critical strip

Cauchy's estimate over the compiled quarter-strip bound B2″: for
`σ ∈ [½, 2]`, `|t| ≥ 3`, `‖ζ′(s)‖ ≤ 200·|t|^{3/4}` — the between-station
control for the Backlund segments and the Z-sign ladder.
-/

open Complex Metric

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **B2‴: the ζ′ growth bound.**  Radius-⅛ Cauchy over B2″ (with the
series bound covering the sliver `σ > 2` of the sphere). -/
theorem zeta_deriv_growth {s : ℂ} (him : 3 ≤ |s.im|)
    (hσl : (1:ℝ)/2 ≤ s.re) (hσu : s.re ≤ 2) :
    ‖deriv riemannZeta s‖ ≤ 200 * |s.im| ^ ((3:ℝ)/4) := by
  have himpos : (0:ℝ) < |s.im| := by linarith
  -- ζ is differentiable on the closed ball (1 is far away)
  have hball_ne_one : ∀ z ∈ closedBall s (1/8), z ≠ 1 := by
    intro z hz h1
    rw [mem_closedBall, dist_eq_norm] at hz
    have him' : |z.im - s.im| ≤ 1/8 := by
      calc |z.im - s.im| = |(z - s).im| := by rw [Complex.sub_im]
        _ ≤ ‖z - s‖ := Complex.abs_im_le_norm _
        _ ≤ 1/8 := hz
    rw [h1] at him'
    simp only [Complex.one_im, zero_sub, abs_neg] at him'
    linarith
  have hd : DiffContOnCl ℂ riemannZeta (ball s (1/8)) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    have hz' : z ∈ closedBall s (1/8) := by
      rwa [closure_ball s (by norm_num : (1/8 : ℝ) ≠ 0)] at hz
    exact (differentiableAt_riemannZeta (hball_ne_one z hz')).differentiableWithinAt
  -- the sphere bound
  have hC : ∀ z ∈ sphere s (1/8),
      ‖riemannZeta z‖ ≤ 25 * |s.im| ^ ((3:ℝ)/4) := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hre' : |z.re - s.re| ≤ 1/8 := by
      calc |z.re - s.re| = |(z - s).re| := by rw [Complex.sub_re]
        _ ≤ ‖z - s‖ := Complex.abs_re_le_norm _
        _ ≤ 1/8 := le_of_eq hz
    have him' : |z.im - s.im| ≤ 1/8 := by
      calc |z.im - s.im| = |(z - s).im| := by rw [Complex.sub_im]
        _ ≤ ‖z - s‖ := Complex.abs_im_le_norm _
        _ ≤ 1/8 := le_of_eq hz
    have hzim_lb : 2 ≤ |z.im| := by
      rcases abs_le.mp him' with ⟨h1, h2⟩
      rcases abs_cases s.im with ⟨heq, _⟩ | ⟨heq, _⟩ <;>
        rcases abs_cases z.im with ⟨heq2, _⟩ | ⟨heq2, _⟩ <;> linarith
    have hzim_ub : |z.im| ≤ |s.im| + 1/8 := by
      calc |z.im| = |s.im + (z.im - s.im)| := by ring_nf
        _ ≤ |s.im| + |z.im - s.im| := abs_add_le _ _
        _ ≤ |s.im| + 1/8 := by linarith
    have hgrow : |z.im| ^ ((3:ℝ)/4) ≤ (25/24) * |s.im| ^ ((3:ℝ)/4) := by
      have h1 : |z.im| ≤ (25/24) * |s.im| := by
        have : (1:ℝ)/8 ≤ |s.im| / 24 := by linarith
        linarith
      calc |z.im| ^ ((3:ℝ)/4)
          ≤ ((25/24) * |s.im|) ^ ((3:ℝ)/4) :=
            Real.rpow_le_rpow (abs_nonneg _) h1 (by norm_num)
        _ = (25/24 : ℝ) ^ ((3:ℝ)/4) * |s.im| ^ ((3:ℝ)/4) :=
            Real.mul_rpow (by norm_num) (abs_nonneg _)
        _ ≤ (25/24) * |s.im| ^ ((3:ℝ)/4) := by
            apply mul_le_mul_of_nonneg_right _
              (Real.rpow_nonneg (abs_nonneg _) _)
            calc (25/24 : ℝ) ^ ((3:ℝ)/4)
                ≤ (25/24 : ℝ) ^ ((1:ℝ)) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 25/24 := Real.rpow_one _
    rcases le_or_gt z.re 2 with hcase | hcase
    · -- B2″ region
      have hzσl : (1:ℝ)/4 ≤ z.re := by
        rcases abs_le.mp hre' with ⟨h1, _⟩
        linarith
      have hb := zeta_polynomial_growth_quarter hzim_lb hzσl hcase
      calc ‖riemannZeta z‖ ≤ 24 * |z.im| ^ ((3:ℝ)/4) := hb
        _ ≤ 24 * ((25/24) * |s.im| ^ ((3:ℝ)/4)) := by
            exact mul_le_mul_of_nonneg_left hgrow (by norm_num)
        _ = 25 * |s.im| ^ ((3:ℝ)/4) := by ring
    · -- the series sliver σ > 2
      have hb := zeta_norm_le_of_one_lt (z := z) (by linarith)
      have h2 : (1:ℝ) + 1 / (z.re - 1) ≤ 2 := by
        have : (1:ℝ) ≤ z.re - 1 := by linarith
        have h3 : 1 / (z.re - 1) ≤ 1 := by
          rw [div_le_one (by linarith)]
          linarith
        linarith
      have hone : (1:ℝ) ≤ |s.im| ^ ((3:ℝ)/4) := by
        calc (1:ℝ) = (1:ℝ) ^ ((3:ℝ)/4) := (Real.one_rpow _).symm
          _ ≤ |s.im| ^ ((3:ℝ)/4) :=
            Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
      calc ‖riemannZeta z‖ ≤ 1 + 1 / (z.re - 1) := hb
        _ ≤ 2 := h2
        _ ≤ 25 * |s.im| ^ ((3:ℝ)/4) := by nlinarith
  -- Cauchy
  have hmain := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0:ℝ) < 1/8) hd hC
  calc ‖deriv riemannZeta s‖
      ≤ (25 * |s.im| ^ ((3:ℝ)/4)) / (1/8) := hmain
    _ = 200 * |s.im| ^ ((3:ℝ)/4) := by ring

/-- **The station-to-segment lemma.**  A derivative bound `L` interpolates
endpoint floors across a station gap: `m − L·(b−a)/2` survives everywhere
on `[a, b]`.  With stations at spacing `< 2m/L` this keeps `Re ζ` positive
along a whole Backlund segment. -/
theorem lower_bound_between {f f' : ℝ → ℝ} {a b L m : ℝ} (hab : a ≤ b)
    (hder : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hL : ∀ x ∈ Set.Icc a b, |f' x| ≤ L)
    (hfa : m ≤ f a) (hfb : m ≤ f b) :
    ∀ x ∈ Set.Icc a b, m - L * (b - a) / 2 ≤ f x := by
  have hL0 : 0 ≤ L := by
    rcases hder a (Set.left_mem_Icc.mpr hab) with _
    exact le_trans (abs_nonneg _) (hL a (Set.left_mem_Icc.mpr hab))
  -- Lipschitz control on the interval
  have hlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |f x - f y| ≤ L * |x - y| := by
    intro x hx y hy
    rcases le_total y x with hxy | hxy
    · have hsub : Set.Icc y x ⊆ Set.Icc a b :=
        Set.Icc_subset_Icc hy.1 hx.2
      have h1 := norm_image_sub_le_of_norm_deriv_le_segment'
        (f' := f') (C := L)
        (fun z hz => (hder z (hsub hz)).hasDerivWithinAt)
        (fun z hz => by
          rw [Real.norm_eq_abs]
          exact hL z (hsub (Set.Ico_subset_Icc_self hz)))
        x (Set.right_mem_Icc.mpr hxy)
      have habs : |x - y| = x - y := abs_of_nonneg (by linarith)
      rw [habs]
      exact h1
    · have hsub : Set.Icc x y ⊆ Set.Icc a b :=
        Set.Icc_subset_Icc hx.1 hy.2
      have h1 := norm_image_sub_le_of_norm_deriv_le_segment'
        (f' := f') (C := L)
        (fun z hz => (hder z (hsub hz)).hasDerivWithinAt)
        (fun z hz => by
          rw [Real.norm_eq_abs]
          exact hL z (hsub (Set.Ico_subset_Icc_self hz)))
        y (Set.right_mem_Icc.mpr hxy)
      have habs : |x - y| = y - x := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith)
      rw [habs, abs_sub_comm]
      exact h1
  -- each point is within (b−a)/2 of one endpoint
  intro x hx
  rcases le_total x ((a + b) / 2) with hmid | hmid
  · have h1 := hlip x hx a (Set.left_mem_Icc.mpr hab)
    have h2 : |x - a| ≤ (b - a) / 2 := by
      rw [abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.1]
    have h3 : |f x - f a| ≤ L * ((b - a) / 2) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 hL0)
    have h4 := (abs_le.mp h3).1
    linarith
  · have h1 := hlip x hx b (Set.right_mem_Icc.mpr hab)
    have h2 : |x - b| ≤ (b - a) / 2 := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.2])]
      linarith [hx.2]
    have h3 : |f x - f b| ≤ L * ((b - a) / 2) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 hL0)
    have h4 := (abs_le.mp h3).1
    linarith

/-- **The evaluation-free Re ζ floor**: for `σ > 1`,
`Re ζ(s) ≥ 1 − (2^{−σ} + 2^{1−σ}/(σ−1))` — positive from `σ ≈ 1.88`;
at `σ = 2` the floor is exactly `1/4`.  No station evaluations enter. -/
theorem re_zeta_floor {z : ℂ} (hz : 1 < z.re) :
    1 - ((2:ℝ) ^ (-z.re) + (2:ℝ) ^ (1 - z.re) / (z.re - 1))
      ≤ (riemannZeta z).re := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
    linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hz]
  set g : ℕ → ℝ := fun n => if n = 0 then (0:ℝ) else ((n:ℝ)) ^ (-z.re)
    with hg
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n
    rw [hg]
    dsimp only
    split
    · exact le_refl 0
    · positivity
  have hgsum : Summable g :=
    summable_of_sum_range_le hgnn (partial_inv_rpow_le hz)
  have hterm : ∀ n : ℕ, ‖1 / ((n:ℂ)) ^ z‖ ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [Nat.cast_zero, zero_cpow hz0]
      simpa using hgnn 0
    · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hpos, hg]
      dsimp only
      rw [if_neg hne]
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hpos
      rw [Real.rpow_neg hnpos.le, ← one_div]
  have hnsum : Summable (fun n : ℕ => ‖1 / ((n:ℂ)) ^ z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hgsum
  have hsum : Summable (fun n : ℕ => 1 / ((n:ℂ)) ^ z) := hnsum.of_norm
  have hhs := Complex.hasSum_re hsum.hasSum
  rw [← hhs.tsum_eq]
  have hresum : Summable (fun n : ℕ => (1 / ((n:ℂ)) ^ z).re) := hhs.summable
  -- peel n = 0 and n = 1
  rw [hresum.tsum_eq_zero_add]
  have hresum1 : Summable (fun n : ℕ => (1 / (((n + 1 : ℕ)):ℂ) ^ z).re) :=
    (summable_nat_add_iff 1).mpr hresum
  rw [hresum1.tsum_eq_zero_add]
  have h0 : (1 / (((0:ℕ)):ℂ) ^ z).re = 0 := by
    rw [Nat.cast_zero, zero_cpow hz0]
    simp
  have h1 : (1 / (((0 + 1 : ℕ)):ℂ) ^ z).re = 1 := by
    norm_num
  rw [h0, h1]
  -- the tail: |Σ' r_{n+2}| ≤ Σ' (n+2)^{−σ} ≤ 2^{−σ} + 2^{1−σ}/(σ−1)
  have hresum2 : Summable (fun n : ℕ => (1 / (((n + 1 + 1 : ℕ)):ℂ) ^ z).re) :=
    (summable_nat_add_iff 1).mpr hresum1
  have hmaj : Summable (fun n : ℕ => (((2 + n : ℕ)):ℝ) ^ (-z.re)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-z.re)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hbase.comp_injective (fun a b hab => by omega)
  have htail_abs : |∑' n : ℕ, (1 / (((n + 1 + 1 : ℕ)):ℂ) ^ z).re|
      ≤ (2:ℝ) ^ (-z.re) + (2:ℝ) ^ (1 - z.re) / (z.re - 1) := by
    calc |∑' n : ℕ, (1 / (((n + 1 + 1 : ℕ)):ℂ) ^ z).re|
        ≤ ∑' n : ℕ, |(1 / (((n + 1 + 1 : ℕ)):ℂ) ^ z).re| := by
          have hn : Summable
              (fun n : ℕ => ‖(1 / (((n + 1 + 1 : ℕ)):ℂ) ^ z).re‖) := by
            simp only [Real.norm_eq_abs]
            exact hresum2.abs
          have hb := norm_tsum_le_tsum_norm hn
          simp only [Real.norm_eq_abs] at hb
          exact hb
      _ ≤ ∑' n : ℕ, (((2 + n : ℕ)):ℝ) ^ (-z.re) := by
          apply Summable.tsum_le_tsum _ hresum2.abs hmaj
          intro n
          have hb := hterm (n + 1 + 1)
          have hgval : g (n + 1 + 1) = (((n + 1 + 1 : ℕ)):ℝ) ^ (-z.re) := by
            rw [hg]
            dsimp only
            rw [if_neg (by omega)]
          rw [hgval] at hb
          have hcast : (((n + 1 + 1 : ℕ)):ℝ) = (((2 + n : ℕ)):ℝ) := by
            congr 1
            omega
          rw [hcast] at hb
          exact le_trans (Complex.abs_re_le_norm _) hb
      _ ≤ ((2:ℕ):ℝ) ^ (-z.re) + ((2:ℕ):ℝ) ^ (1 - z.re) / (z.re - 1) :=
          tsum_shift_rpow_le (by norm_num) hz
      _ = (2:ℝ) ^ (-z.re) + (2:ℝ) ^ (1 - z.re) / (z.re - 1) := by
          norm_num
  have htail_lb := (abs_le.mp htail_abs).1
  linarith

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.zeta_deriv_growth
#print axioms CriticalLinePhasor.DVP.lower_bound_between
#print axioms CriticalLinePhasor.DVP.re_zeta_floor
end AxiomAudit
