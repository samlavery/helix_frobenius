import Mathlib
import RequestProject.RieszMultiplicityReadout

/-!
# The Hadamard jets of `ξ′/ξ` (ledger 592)

Off the zeros, `ξ′/ξ(s) = A + Σ'_ρ m_ρ (1/(s−ρ) + 1/ρ)` (`ZD.xi_logDeriv_partial_fraction`). Termwise
differentiation on a ball avoiding the zeros gives, for every `k ≥ 1`,

  `iteratedDeriv k (logDeriv ξ) s = (−1)^k · k! · Σ'_ρ m_ρ (s−ρ)^{−(k+1)}`,

an absolutely convergent sum. These are the JETS of the log-derivative: the moments of the zero
measure with the twisted nodes `1/(s−ρ)`, which the prime side of the seat form (`hermForm`, ledger
589) and the registered flow (velocity `2i·FP`, ledger 570; acceleration and beyond) are built from.
For `Re s > 1` each jet is `arch^{(k)}(s) − Σ_n Λ(n)(−log n)^k n^{−s}`: prime-computable.

Ingredients: positive distance from a non-zero point to the zero set (`exists_pos_dist_nontrivialZeros`,
from `NontrivialZeros_inter_closedBall_finite`), openness of the complement, summability of
`m_ρ/‖s−ρ‖²` (from `summable_xiOrderNat_div_norm_sq_nontrivialZeros`), and Mathlib's
`hasDerivAt_tsum_of_isPreconnected`.
-/

open Complex Set Filter Topology Metric

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. The zero set is locally finite: positive distance, open complement -/

theorem exists_pos_dist_nontrivialZeros {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ ∈ ZD.NontrivialZeros, δ ≤ ‖s - ρ‖ := by
  classical
  have hF : (ZD.NontrivialZeros ∩ Metric.closedBall (0 : ℂ) (‖s‖ + 1)).Finite :=
    ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite _
  have hfar : ∀ ρ ∈ ZD.NontrivialZeros, ρ ∉ Metric.closedBall (0 : ℂ) (‖s‖ + 1) → 1 ≤ ‖s - ρ‖ := by
    intro ρ _ hin
    have h1 : ‖s‖ + 1 < ‖ρ‖ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hin
      exact not_le.mp hin
    have h2 : ‖ρ‖ - ‖s‖ ≤ ‖s - ρ‖ := by
      have := norm_sub_norm_le ρ s
      rwa [norm_sub_rev] at this
    linarith
  set T := hF.toFinset with hT
  by_cases hTne : T.Nonempty
  · obtain ⟨ρ₀, hρ₀T, hρ₀min⟩ := T.exists_min_image (fun ρ => ‖s - ρ‖) hTne
    have hρ₀ : ρ₀ ∈ ZD.NontrivialZeros := (hF.mem_toFinset.mp hρ₀T).1
    have hpos : 0 < ‖s - ρ₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hs (h ▸ hρ₀)))
    refine ⟨min ‖s - ρ₀‖ 1, lt_min hpos one_pos, fun ρ hρ => ?_⟩
    by_cases hin : ρ ∈ Metric.closedBall (0 : ℂ) (‖s‖ + 1)
    · have hmem : ρ ∈ T := hF.mem_toFinset.mpr ⟨hρ, hin⟩
      exact le_trans (min_le_left _ _) (hρ₀min ρ hmem)
    · exact le_trans (min_le_right _ _) (hfar ρ hρ hin)
  · refine ⟨1, one_pos, fun ρ hρ => ?_⟩
    have hin : ρ ∉ Metric.closedBall (0 : ℂ) (‖s‖ + 1) :=
      fun h => hTne ⟨ρ, hF.mem_toFinset.mpr ⟨hρ, h⟩⟩
    exact hfar ρ hρ hin

theorem isOpen_compl_nontrivialZeros : IsOpen (ZD.NontrivialZeros)ᶜ := by
  rw [Metric.isOpen_iff]
  intro s hs
  obtain ⟨δ, hδ, hdist⟩ := exists_pos_dist_nontrivialZeros hs
  refine ⟨δ, hδ, fun y hy hyz => ?_⟩
  have h1 := hdist y hyz
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hy
  linarith

/-! ## 2. Summability of `m_ρ / ‖s − ρ‖²` -/

theorem summable_xiOrder_div_norm_sub_sq (s : ℂ) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℝ) / ‖s - ρ.val‖ ^ 2) := by
  have hg : Summable (fun ρ : Zero => 4 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :=
    ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros.mul_left 4
  apply Summable.of_norm_bounded_eventually hg
  filter_upwards [CriticalLinePhasor.StBridge.eventually_cofinite_norm_ge (2 * ‖s‖ + 2)] with ρ hbig
  have hnorms : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
  have hnormρ : (0 : ℝ) < ‖ρ.val‖ := by
    have : (0 : ℝ) ≤ 2 * ‖s‖ := by positivity
    linarith
  have hlow : ‖ρ.val‖ / 2 ≤ ‖s - ρ.val‖ := by
    have h1 : ‖ρ.val‖ - ‖s‖ ≤ ‖s - ρ.val‖ := by
      calc ‖ρ.val‖ - ‖s‖ ≤ ‖ρ.val - s‖ := norm_sub_norm_le _ _
        _ = ‖s - ρ.val‖ := norm_sub_rev _ _
    linarith
  have hsub0 : (0 : ℝ) < ‖s - ρ.val‖ := by
    have : (0 : ℝ) < ‖ρ.val‖ / 2 := by linarith
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (ZD.xiOrderNat ρ.val : ℝ) / ‖s - ρ.val‖ ^ 2
      ≤ (ZD.xiOrderNat ρ.val : ℝ) / (‖ρ.val‖ / 2) ^ 2 := by gcongr
    _ = 4 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
        field_simp
        ring

/-- On the ball of radius `δ/2` about `s` (with `δ ≤ ‖s−ρ‖` for all zeros), `‖y − ρ‖ ≥ ‖s − ρ‖/2`. -/
theorem norm_sub_ge_half_of_mem_ball {s y ρ : ℂ} {δ : ℝ} (hδρ : δ ≤ ‖s - ρ‖)
    (hy : y ∈ Metric.ball s (δ / 2)) : ‖s - ρ‖ / 2 ≤ ‖y - ρ‖ := by
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have h1 : ‖s - ρ‖ - ‖y - s‖ ≤ ‖y - ρ‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub s y ρ
    -- ‖s − ρ‖ ≤ ‖s − y‖ + ‖y − ρ‖
    rw [norm_sub_rev s y] at this
    linarith
  linarith

/-! ## 3. Termwise differentiation on a ball -/

/-- The `k`-th zero-moment sum `Σ' m_ρ ((y−ρ)⁻¹)^k`. -/
def zeroMoment (k : ℕ) (y : ℂ) : ℂ := ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * ((y - ρ.val)⁻¹) ^ k

/-- For `k ≥ 2` the `k`-th moment converges absolutely at every `s` off the zeros. -/
theorem summable_zeroMoment {k : ℕ} (hk : 2 ≤ k) {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹) ^ k) := by
  obtain ⟨δ, hδ, hdist⟩ := exists_pos_dist_nontrivialZeros hs
  set δ' : ℝ := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hg : Summable (fun ρ : Zero => δ' ^ (2 - k : ℤ) *
      ((ZD.xiOrderNat ρ.val : ℝ) / ‖s - ρ.val‖ ^ 2)) :=
    (summable_xiOrder_div_norm_sub_sq s).mul_left _
  apply Summable.of_norm_bounded hg
  intro ρ
  have hd : δ' ≤ ‖s - ρ.val‖ := le_trans (min_le_left _ _) (hdist ρ.val ρ.2)
  have hpos : 0 < ‖s - ρ.val‖ := lt_of_lt_of_le hδ'0 hd
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
  -- ‖s−ρ‖^{−k} ≤ δ'^{2−k} ‖s−ρ‖^{−2}  since ‖s−ρ‖ ≥ δ' and k ≥ 2
  have hk' : ‖s - ρ.val‖ ^ (k - 2) ≥ δ' ^ (k - 2) := pow_le_pow_left₀ hδ'0.le hd _
  have hsplit : ‖s - ρ.val‖ ^ k = ‖s - ρ.val‖ ^ 2 * ‖s - ρ.val‖ ^ (k - 2) := by
    rw [← pow_add]; congr 1; omega
  have hzpow : δ' ^ (2 - k : ℤ) = (δ' ^ (k - 2))⁻¹ := by
    rw [show (2 - k : ℤ) = -((k - 2 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  rw [hzpow]
  have hδk : 0 < δ' ^ (k - 2) := by positivity
  calc (ZD.xiOrderNat ρ.val : ℝ) * (‖s - ρ.val‖⁻¹) ^ k
      = (ZD.xiOrderNat ρ.val : ℝ) / (‖s - ρ.val‖ ^ 2 * ‖s - ρ.val‖ ^ (k - 2)) := by
        rw [inv_pow, ← div_eq_mul_inv, hsplit]
    _ ≤ (ZD.xiOrderNat ρ.val : ℝ) / (‖s - ρ.val‖ ^ 2 * δ' ^ (k - 2)) := by
        gcongr
    _ = (δ' ^ (k - 2))⁻¹ * ((ZD.xiOrderNat ρ.val : ℝ) / ‖s - ρ.val‖ ^ 2) := by
        field_simp

/-- **Termwise differentiation, `k ≥ 1`:** `d/dy Σ' m_ρ ((y−ρ)⁻¹)^k = −k · Σ' m_ρ ((y−ρ)⁻¹)^{k+1}`
off the zeros (for `k = 1` the sum is the regularised one, see `hasDerivAt_hadamard_sum`). -/
theorem hasDerivAt_zeroMoment {k : ℕ} (hk : 2 ≤ k) {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    HasDerivAt (zeroMoment k) (-(k : ℂ) * zeroMoment (k + 1) s) s := by
  obtain ⟨δ, hδ, hdist⟩ := exists_pos_dist_nontrivialZeros hs
  set δ' : ℝ := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  have hd : ∀ ρ : Zero, δ' ≤ ‖s - ρ.val‖ := fun ρ => le_trans (min_le_left _ _) (hdist ρ.val ρ.2)
  set t : Set ℂ := Metric.ball s (δ' / 2) with ht
  have hne : ∀ (ρ : Zero) (y : ℂ), y ∈ t → y - ρ.val ≠ 0 := by
    intro ρ y hy h0
    have := norm_sub_ge_half_of_mem_ball (hd ρ) hy
    rw [h0, norm_zero] at this
    have := hd ρ
    linarith
  -- the bound: ‖k m (y−ρ)^{−(k+1)}‖ ≤ k m 2^{k+1} ‖s−ρ‖^{−(k+1)} ≤ k 2^{k+1} δ'^{1−k} m ‖s−ρ‖^{−2}
  set u : Zero → ℝ := fun ρ => (k : ℝ) * 2 ^ (k + 1) * δ' ^ (1 - k : ℤ) *
      ((ZD.xiOrderNat ρ.val : ℝ) / ‖s - ρ.val‖ ^ 2) with hu
  have hu_sum : Summable u := (summable_xiOrder_div_norm_sub_sq s).mul_left _
  have hderiv : ∀ (ρ : Zero) (y : ℂ), y ∈ t →
      HasDerivAt (fun y => (ZD.xiOrderNat ρ.val : ℂ) * ((y - ρ.val)⁻¹) ^ k)
        (-(k : ℂ) * ((ZD.xiOrderNat ρ.val : ℂ) * ((y - ρ.val)⁻¹) ^ (k + 1))) y := by
    intro ρ y hy
    have hne' := hne ρ y hy
    have h2 := ((((hasDerivAt_id y).sub_const ρ.val).inv hne').pow k).const_mul
      (ZD.xiOrderNat ρ.val : ℂ)
    refine h2.congr_deriv ?_
    have hk2 : k + 1 = (k - 1) + 2 := by omega
    rw [hk2, pow_add]
    simp only [id, Pi.inv_apply]
    field_simp
  have hbound : ∀ (ρ : Zero) (y : ℂ), y ∈ t →
      ‖-(k : ℂ) * ((ZD.xiOrderNat ρ.val : ℂ) * ((y - ρ.val)⁻¹) ^ (k + 1))‖ ≤ u ρ := by
    intro ρ y hy
    have hhalf := norm_sub_ge_half_of_mem_ball (hd ρ) hy
    have hsρ : 0 < ‖s - ρ.val‖ := lt_of_lt_of_le hδ'0 (hd ρ)
    have hyρ : 0 < ‖y - ρ.val‖ := by linarith
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_natCast, norm_pow, norm_inv]
    simp only [hu]
    -- ‖y−ρ‖^{−(k+1)} ≤ (‖s−ρ‖/2)^{−(k+1)} = 2^{k+1} ‖s−ρ‖^{−(k+1)} ≤ 2^{k+1} δ'^{1−k} ‖s−ρ‖^{−2}
    have hA : (‖y - ρ.val‖⁻¹) ^ (k + 1) ≤ (2 / ‖s - ρ.val‖) ^ (k + 1) := by
      apply pow_le_pow_left₀ (by positivity)
      rw [inv_le_comm₀ hyρ (by positivity), inv_div]
      linarith
    have hB : (2 / ‖s - ρ.val‖) ^ (k + 1)
        ≤ 2 ^ (k + 1) * δ' ^ (1 - k : ℤ) * (‖s - ρ.val‖ ^ 2)⁻¹ := by
      rw [div_pow, show (1 - k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
      have hsplit : ‖s - ρ.val‖ ^ (k + 1) = ‖s - ρ.val‖ ^ 2 * ‖s - ρ.val‖ ^ (k - 1) := by
        rw [← pow_add]; congr 1; omega
      have hk1 : δ' ^ (k - 1) ≤ ‖s - ρ.val‖ ^ (k - 1) := pow_le_pow_left₀ hδ'0.le (hd ρ) _
      have hδk : 0 < δ' ^ (k - 1) := by positivity
      rw [hsplit]
      calc (2 : ℝ) ^ (k + 1) / (‖s - ρ.val‖ ^ 2 * ‖s - ρ.val‖ ^ (k - 1))
          ≤ 2 ^ (k + 1) / (‖s - ρ.val‖ ^ 2 * δ' ^ (k - 1)) := by gcongr
        _ = 2 ^ (k + 1) * (δ' ^ (k - 1))⁻¹ * (‖s - ρ.val‖ ^ 2)⁻¹ := by
            field_simp
    calc (k : ℝ) * ((ZD.xiOrderNat ρ.val : ℝ) * (‖y - ρ.val‖⁻¹) ^ (k + 1))
        ≤ (k : ℝ) * ((ZD.xiOrderNat ρ.val : ℝ) * (2 ^ (k + 1) * δ' ^ (1 - k : ℤ) * (‖s - ρ.val‖ ^ 2)⁻¹)) := by
          gcongr
          exact le_trans hA hB
      _ = (k : ℝ) * 2 ^ (k + 1) * δ' ^ (1 - k : ℤ) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖s - ρ.val‖ ^ 2) := by
          ring
  have hs_mem : s ∈ t := Metric.mem_ball_self (by positivity)
  have h := hasDerivAt_tsum_of_isPreconnected hu_sum Metric.isOpen_ball (convex_ball s _).isPreconnected
    hderiv hbound hs_mem (summable_zeroMoment hk hs) hs_mem
  refine h.congr_deriv ?_
  unfold zeroMoment
  rw [← tsum_mul_left]

/-- The regularised Hadamard sum `Σ' m_ρ (1/(y−ρ) + 1/ρ)` has derivative `−zeroMoment 2` off the zeros. -/
theorem hasDerivAt_hadamard_sum {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    HasDerivAt (fun y => ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val y)
      (-zeroMoment 2 s) s := by
  obtain ⟨δ, hδ, hdist⟩ := exists_pos_dist_nontrivialZeros hs
  set δ' : ℝ := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  have hd : ∀ ρ : Zero, δ' ≤ ‖s - ρ.val‖ := fun ρ => le_trans (min_le_left _ _) (hdist ρ.val ρ.2)
  set t : Set ℂ := Metric.ball s (δ' / 2) with ht
  have hne : ∀ (ρ : Zero) (y : ℂ), y ∈ t → y - ρ.val ≠ 0 := by
    intro ρ y hy h0
    have := norm_sub_ge_half_of_mem_ball (hd ρ) hy
    rw [h0, norm_zero] at this
    have := hd ρ
    linarith
  set u : Zero → ℝ := fun ρ => 4 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖s - ρ.val‖ ^ 2) with hu
  have hu_sum : Summable u := (summable_xiOrder_div_norm_sub_sq s).mul_left _
  have hderiv : ∀ (ρ : Zero) (y : ℂ), y ∈ t →
      HasDerivAt (fun y => (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val y)
        (-(ZD.xiOrderNat ρ.val : ℂ) * ((y - ρ.val)⁻¹) ^ 2) y := by
    intro ρ y hy
    have hne' := hne ρ y hy
    have h2 := ((((hasDerivAt_id y).sub_const ρ.val).inv hne').add_const (1 / ρ.val)).const_mul
      (ZD.xiOrderNat ρ.val : ℂ)
    have hfun : (fun y => (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val y)
        = fun y => (ZD.xiOrderNat ρ.val : ℂ) * ((y - ρ.val)⁻¹ + 1 / ρ.val) := by
      funext y; simp [hadamardTerm, one_div]
    rw [hfun]
    refine h2.congr_deriv ?_
    simp only [id]
    field_simp
  have hbound : ∀ (ρ : Zero) (y : ℂ), y ∈ t →
      ‖-(ZD.xiOrderNat ρ.val : ℂ) * ((y - ρ.val)⁻¹) ^ 2‖ ≤ u ρ := by
    intro ρ y hy
    have hhalf := norm_sub_ge_half_of_mem_ball (hd ρ) hy
    have hsρ : 0 < ‖s - ρ.val‖ := lt_of_lt_of_le hδ'0 (hd ρ)
    have hyρ : 0 < ‖y - ρ.val‖ := by linarith
    rw [norm_mul, norm_neg, Complex.norm_natCast, norm_pow, norm_inv]
    simp only [hu]
    have hA : (‖y - ρ.val‖⁻¹) ^ 2 ≤ (2 / ‖s - ρ.val‖) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [inv_le_comm₀ hyρ (by positivity), inv_div]
      linarith
    calc (ZD.xiOrderNat ρ.val : ℝ) * (‖y - ρ.val‖⁻¹) ^ 2
        ≤ (ZD.xiOrderNat ρ.val : ℝ) * (2 / ‖s - ρ.val‖) ^ 2 := by gcongr
      _ = 4 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖s - ρ.val‖ ^ 2) := by
          rw [div_pow]; ring
  have hs_mem : s ∈ t := Metric.mem_ball_self (by positivity)
  have h := hasDerivAt_tsum_of_isPreconnected hu_sum Metric.isOpen_ball (convex_ball s _).isPreconnected
    hderiv hbound hs_mem (summable_hadamard_term_any s) hs_mem
  refine h.congr_deriv ?_
  unfold zeroMoment
  rw [← tsum_neg]
  congr 1
  funext ρ
  ring

/-! ## 4. The jets of `ξ′/ξ` -/

/-- `ξ′/ξ` agrees with `A + Σ' m_ρ hadamardTerm` on the open complement of the zeros. -/
theorem logDeriv_xi_eventuallyEq {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    logDeriv ZD.riemannXi =ᶠ[𝓝 s]
      fun y => xiHadamardConst + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val y := by
  have hopen : (ZD.NontrivialZeros)ᶜ ∈ 𝓝 s := isOpen_compl_nontrivialZeros.mem_nhds hs
  filter_upwards [hopen] with y hy
  exact (xiFinitePart_eq_logDeriv hy).symm

/-- **First jet:** `(ξ′/ξ)′(s) = −Σ' m_ρ (s−ρ)^{−2}` off the zeros. -/
theorem hasDerivAt_logDeriv_xi {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    HasDerivAt (logDeriv ZD.riemannXi) (-zeroMoment 2 s) s := by
  have h := (hasDerivAt_hadamard_sum hs).const_add xiHadamardConst
  exact h.congr_of_eventuallyEq (logDeriv_xi_eventuallyEq hs)

/-- `zeroMoment (k+1)` is the `k`-th jet, up to `(−1)^k k!`, on the open complement of the zeros. -/
theorem iteratedDeriv_logDeriv_xi_eq_zeroMoment (k : ℕ) (hk : 1 ≤ k) :
    ∀ s ∉ ZD.NontrivialZeros,
      iteratedDeriv k (logDeriv ZD.riemannXi) s = (-1) ^ k * (k.factorial : ℂ) * zeroMoment (k + 1) s := by
  induction k with
  | zero => intro s hs; omega
  | succ n ih =>
    intro s hs
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [iteratedDeriv_one, (hasDerivAt_logDeriv_xi hs).deriv]
      simp
    · have ih' := ih hn
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n (logDeriv ZD.riemannXi)
          =ᶠ[𝓝 s] fun y => (-1) ^ n * (n.factorial : ℂ) * zeroMoment (n + 1) y := by
        have hopen : (ZD.NontrivialZeros)ᶜ ∈ 𝓝 s := isOpen_compl_nontrivialZeros.mem_nhds hs
        filter_upwards [hopen] with y hy
        exact ih' y hy
      rw [heq.deriv_eq]
      have hd := (hasDerivAt_zeroMoment (k := n + 1) (by omega) hs).const_mul
        ((-1) ^ n * (n.factorial : ℂ))
      rw [hd.deriv, Nat.factorial_succ]
      push_cast
      ring

/-- **The Hadamard jets.** For `k ≥ 1` and `s` off the zeros,
`(ξ′/ξ)^{(k)}(s) = (−1)^k k! Σ'_ρ m_ρ (s−ρ)^{−(k+1)}`, absolutely convergent. -/
theorem hadamard_jet {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    iteratedDeriv k (logDeriv ZD.riemannXi) s
      = (-1) ^ k * (k.factorial : ℂ) * ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹) ^ (k + 1) :=
  iteratedDeriv_logDeriv_xi_eq_zeroMoment k hk s hs

theorem hadamard_jet_summable {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * ((s - ρ.val)⁻¹) ^ (k + 1)) :=
  summable_zeroMoment (by omega) hs

#print axioms exists_pos_dist_nontrivialZeros
#print axioms isOpen_compl_nontrivialZeros
#print axioms hasDerivAt_logDeriv_xi
#print axioms hadamard_jet

end CriticalLinePhasor.ContourArgument
