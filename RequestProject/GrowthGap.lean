import RequestProject.SubexponentialAnchor
import RequestProject.DVPLadder1215o2

/-!
# The unconditional growth of the explicit sequence, and the exact gap to RH (ledger 634)

At the anchor `s₀ = −1 + 20i` the coefficient sequence is `μ_k = Σ_ρ m_ρ ω_ρ w_ρ^k`, and its growth rate is
`sup_ρ ‖w_ρ‖`. Zeros with `|Im ρ| ≤ 1215/2` lie on the line (`online_below_1215o2`, compiled), where
`‖w_ρ‖ = 1`; any other zero has `|s₀ − ρ| ≥ |Im ρ| − 20 ≥ 1215/2 − 20`, so
`‖w_ρ‖² = 1 + (2Re ρ − 1)(2Re s₀ − 1)/|s₀−ρ|² ≤ 1 + 3/(1215/2 − 20)²`. Hence, unconditionally,

  `‖μ_k(s₀)‖ ≤ C · R^k`,  `R = √(1 + 3/(1175/2)²) ≈ 1 + 4.3·10⁻⁶`   (`explicit_growth_unconditional`),

while RH is `‖μ_k(s₀)‖ ≤ C(1 + k^p)` (`riemannHypothesis_of_explicit_fixed_anchor_polynomial_growth`).
The whole of RH, at this anchor, is the replacement of the base `R` by `1`.
-/

open Complex Finset

namespace CriticalLinePhasor.SeatingLedger

/-- The anchor `−1 + 20i`. -/
noncomputable def anchor20 : ℂ := (-1 : ℂ) + 20 * I

theorem anchor20_re : anchor20.re = -1 := by simp [anchor20]
theorem anchor20_im : anchor20.im = 20 := by simp [anchor20]

theorem anchor20_notMem : anchor20 ∉ ZD.NontrivialZeros :=
  notMem_nontrivialZeros_of_re_nonpos (by rw [anchor20_re]; norm_num)

/-- The base of the unconditional growth bound. -/
noncomputable def growthBase : ℝ := Real.sqrt (1 + 3 / (1215 / 2 - 20) ^ 2)

/-- **Every transported atom at the anchor has modulus at most `growthBase`**, unconditionally. -/
theorem norm_transport_anchor_le (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    ‖transport anchor20 ρ‖ ≤ growthBase := by
  have h : anchor20 - ρ ≠ 0 := sub_ne_zero_of_notMem anchor20_notMem hρ
  have hsq := norm_transport_sq anchor20 ρ h
  rw [anchor20_re] at hsq
  have hnpos : 0 < Complex.normSq (anchor20 - ρ) := by rw [Complex.normSq_pos]; exact h
  unfold growthBase
  rw [← Real.sqrt_sq (norm_nonneg (transport anchor20 ρ))]
  apply Real.sqrt_le_sqrt
  rw [hsq]
  by_cases hlow : |ρ.im| ≤ 1215 / 2
  · -- on the line: the transported atom is unimodular
    have hre := CriticalLinePhasor.DVP.online_below_1215o2 ρ hρ hlow
    rw [hre]
    have : (2 * (1 / 2 : ℝ) - 1) * (2 * (-1 : ℝ) - 1) / Complex.normSq (anchor20 - ρ) = 0 := by
      norm_num
    rw [this]
    have : (0 : ℝ) ≤ 3 / (1215 / 2 - 20) ^ 2 := by positivity
    linarith
  · -- far from the anchor: the modulus exceeds one by at most `3/|s₀ − ρ|²`
    push Not at hlow
    obtain ⟨h1, h2, -⟩ := hρ
    have hnum : (2 * ρ.re - 1) * (2 * (-1 : ℝ) - 1) ≤ 3 := by
      have : |2 * ρ.re - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      calc (2 * ρ.re - 1) * (2 * (-1 : ℝ) - 1) = -3 * (2 * ρ.re - 1) := by ring
        _ ≤ |(-3) * (2 * ρ.re - 1)| := le_abs_self _
        _ = 3 * |2 * ρ.re - 1| := by rw [abs_mul]; norm_num
        _ ≤ 3 := by linarith
    have hdist : (1215 / 2 - 20 : ℝ) ≤ ‖anchor20 - ρ‖ := by
      have him : |(anchor20 - ρ).im| ≤ ‖anchor20 - ρ‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im, anchor20_im] at him
      have : (1215 / 2 - 20 : ℝ) ≤ |20 - ρ.im| := by
        rcases le_or_gt 0 ρ.im with hpos | hneg
        · rw [abs_of_nonneg hpos] at hlow; rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
        · rw [abs_of_neg hneg] at hlow; rw [abs_of_pos (by linarith)]; linarith
      linarith
    have hn : (1215 / 2 - 20 : ℝ) ^ 2 ≤ Complex.normSq (anchor20 - ρ) := by
      rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (by norm_num) hdist 2
    have hpos' : (0 : ℝ) < (1215 / 2 - 20) ^ 2 := by norm_num
    calc 1 + (2 * ρ.re - 1) * (2 * (-1 : ℝ) - 1) / Complex.normSq (anchor20 - ρ)
        ≤ 1 + 3 / Complex.normSq (anchor20 - ρ) := by gcongr
      _ ≤ 1 + 3 / (1215 / 2 - 20) ^ 2 := by gcongr

/-- **The unconditional growth bound**: `‖μ_k(s₀)‖ ≤ C · growthBase^k`. -/
theorem xiCoeff_anchor_growth :
    ∃ C : ℝ, ∀ k, ‖xiCoeff anchor20 k‖ ≤ C * growthBase ^ k := by
  have hsum := summable_absWeight anchor20_notMem
  refine ⟨∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
    (ZD.xiOrderNat ρ.val : ℝ) * ‖atomWeight anchor20 ρ.val‖, fun k => ?_⟩
  have hb : 0 ≤ growthBase := Real.sqrt_nonneg _
  have hterm : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ‖(ZD.xiOrderNat ρ.val : ℂ) * atomWeight anchor20 ρ.val * transport anchor20 ρ.val ^ k‖
        ≤ ((ZD.xiOrderNat ρ.val : ℝ) * ‖atomWeight anchor20 ρ.val‖) * growthBase ^ k := by
    intro ρ
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
    exact norm_transport_anchor_le ρ.val ρ.property
  have hsn : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖(ZD.xiOrderNat ρ.val : ℂ) * atomWeight anchor20 ρ.val * transport anchor20 ρ.val ^ k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hsum.mul_right _)
  unfold xiCoeff
  calc ‖∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) * atomWeight anchor20 ρ.val * transport anchor20 ρ.val ^ k‖
      ≤ ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ‖(ZD.xiOrderNat ρ.val : ℂ) * atomWeight anchor20 ρ.val * transport anchor20 ρ.val ^ k‖ :=
        norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ((ZD.xiOrderNat ρ.val : ℝ) * ‖atomWeight anchor20 ρ.val‖) * growthBase ^ k :=
        Summable.tsum_le_tsum hterm hsn (hsum.mul_right _)
    _ = _ := tsum_mul_right

/-- **The unconditional growth of the explicit prime-and-Γ sequence at the anchor**:
`‖toeplitzCoeff (−3) (jets explicitLogDeriv anchor20) k‖ ≤ C · growthBase^k`. -/
theorem explicit_growth_unconditional :
    ∃ C : ℝ, ∀ k, ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ ≤ C * growthBase ^ k := by
  obtain ⟨C, hC⟩ := xiCoeff_anchor_growth
  refine ⟨C, fun k => ?_⟩
  have hs : anchor20.re < 0 := by rw [anchor20_re]; norm_num
  have hs' : anchor20.re ≠ 1 / 2 := by rw [anchor20_re]; norm_num
  have hd : ((2 * anchor20.re - 1 : ℝ) : ℂ) = -3 := by rw [anchor20_re]; norm_num
  rw [← hd, ← jets_xiLogDeriv_eq_explicit hs, toeplitzCoeff_jets_eq_xiCoeff anchor20_notMem hs' k]
  exact hC k

/-- The same, in the literal form of the fixed-anchor consumer. -/
theorem explicit_growth_unconditional' :
    ∃ C : ℝ, ∀ k, ‖toeplitzCoeff (-3) (jets explicitLogDeriv ((-1 : ℂ) + 20 * I)) k‖
      ≤ C * growthBase ^ k :=
  explicit_growth_unconditional

theorem growthBase_lt : growthBase < 1 + 5 / 1000000 := by
  unfold growthBase
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.norm_transport_anchor_le
#print axioms CriticalLinePhasor.SeatingLedger.explicit_growth_unconditional
#print axioms CriticalLinePhasor.SeatingLedger.explicit_growth_unconditional'
#print axioms CriticalLinePhasor.SeatingLedger.growthBase_lt
