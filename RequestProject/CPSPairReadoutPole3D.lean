import RequestProject.CPSPairBankDecomposition3D
import RequestProject.CPSStandardEulerIdentification3D

/-!
# The diagonal readout is zeta times entire factors, hence has a simple pole

Primewise assembly of `CPSPairBankDecomposition3D`.  The per-prime identity holds for every test
function, so taking `F u = -log (1 - p^(-s) u)` and summing over primes gives

  `bankEulerLog (pairBank α) = ∑_{j=0}^{r} bankEulerLog (Sym^{2j} bank)`,

and exponentiating turns the sum into a product.  The `j = 0` block is a single root equal to `1`,
so its readout is `riemannZeta`; every other block is a symmetric-power readout, which
`CPSStandardEulerIdentification3D` identifies with an **entire** continuation.

Consequence: `(σ - 1) · ‖D σ‖` is bounded on `(1, 2]` — the companion's pole is exactly the one
zeta contributes, and it is simple.  That is the hypothesis `hDpole` of the pole-tolerant edge
engine, now derived rather than assumed.

Scope: `hDtwist` (boundedness at the doubled ordinate) and the point `y = 0` are not proven here.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate

/-- The rank-zero symmetric-power bank is the constant bank `1`. -/
theorem arithmeticSymmetricPowerRoot_zero_eq_one
    (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)) (p : Nat.Primes) (i : Fin 1) :
    arithmeticSymmetricPowerRoot 0 pi p i = 1 := by
  have hi : (i : ℕ) = 0 := Nat.lt_one_iff.mp i.2
  simp [arithmeticSymmetricPowerRoot, hi]

/-- The rank-zero block readout is the Riemann zeta function. -/
theorem bankEulerReadout_symmetricPowerRoot_zero
    (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)) {s : ℂ} (hs : 1 < s.re) :
    bankEulerReadout (arithmeticSymmetricPowerRoot 0 pi) s = riemannZeta s := by
  have hfun : bankEulerLog (arithmeticSymmetricPowerRoot 0 pi) s =
      ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s)) := by
    unfold bankEulerLog
    refine tsum_congr fun p => ?_
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [arithmeticSymmetricPowerRoot_zero_eq_one pi p i, mul_one])]
    simp
  rw [bankEulerReadout, hfun]
  exact riemannZeta_eulerProduct_exp_log hs

/-- **The Euler logarithm of the pair bank splits into the even blocks.** -/
theorem bankEulerLog_pairBank_eq_sum
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData) (r : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    bankEulerLog (pairBank (arithmeticSymmetricPowerRoot r (maassCPSBase M))) s =
      ∑ j ∈ Finset.range (r + 1),
        bankEulerLog (arithmeticSymmetricPowerRoot (2 * j) (maassCPSBase M)) s := by
  have hsummable : ∀ j ∈ Finset.range (r + 1),
      Summable fun p : Nat.Primes =>
        ∑ l : Fin (2 * j + 1),
          -Complex.log (1 - (p : ℂ) ^ (-s) *
            arithmeticSymmetricPowerRoot (2 * j) (maassCPSBase M) p l) := by
    intro j _
    exact summable_bank_neg_log (maass_symmetricPowerRoot_unit_and_real M hC (2 * j)).1 hs
  unfold bankEulerLog
  rw [← Summable.tsum_finsetSum hsummable]
  refine tsum_congr fun p => ?_
  exact maass_sum_pairBank_eq_sum_evenBlocks M r p
    (fun u => -Complex.log (1 - (p : ℂ) ^ (-s) * u))

/-- **The diagonal readout is the product of the even block readouts.** -/
theorem bankEulerReadout_pairBank_eq_prod
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData) (r : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    bankEulerReadout (pairBank (arithmeticSymmetricPowerRoot r (maassCPSBase M))) s =
      ∏ j ∈ Finset.range (r + 1),
        bankEulerReadout (arithmeticSymmetricPowerRoot (2 * j) (maassCPSBase M)) s := by
  rw [bankEulerReadout, bankEulerLog_pairBank_eq_sum M hC r hs, Complex.exp_sum]
  rfl

/-- Splitting off the zeta factor: the diagonal readout is `zeta` times the positive blocks. -/
theorem bankEulerReadout_pairBank_eq_zeta_mul
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData) (r : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    bankEulerReadout (pairBank (arithmeticSymmetricPowerRoot r (maassCPSBase M))) s =
      riemannZeta s *
        ∏ j ∈ Finset.range r,
          bankEulerReadout
            (arithmeticSymmetricPowerRoot (2 * (j + 1)) (maassCPSBase M)) s := by
  rw [bankEulerReadout_pairBank_eq_prod M hC r hs, Finset.prod_range_succ' _ r]
  rw [mul_comm]
  congr 1
  · simpa using bankEulerReadout_symmetricPowerRoot_zero (maassCPSBase M) hs

/-- The zeta factor along the real approach: `(σ - 1) · ζ(σ)` is bounded on `(1, 2]`.  Near `1`
this is the residue limit; away from `1` it is continuity on a compact segment. -/
theorem exists_zeta_segment_bound :
    ∃ C : ℝ, ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      ‖((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ)‖ ≤ C := by
  have hev : ∀ᶠ sigma : ℝ in 𝓝[>] (1 : ℝ),
      ‖((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ)‖ < 2 :=
    (zeta_residue_real_approach.norm).eventually
      (eventually_lt_nhds (by rw [norm_one]; norm_num))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨delta, hdelta, hball⟩ := hev
  set c : ℝ := min (1 + delta / 2) 2 with hc
  have hc1 : 1 < c := by
    rw [hc]
    exact lt_min (by linarith) (by norm_num)
  have hcont : ContinuousOn
      (fun sigma : ℝ => ‖((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ)‖)
      (Set.Icc c 2) := by
    intro x hx
    have hxne : ((x : ℂ)) ≠ 1 := by
      intro hxe
      have hx1 : (x : ℝ) = 1 := by simpa using congrArg Complex.re hxe
      have hcx : c ≤ x := hx.1
      rw [hx1] at hcx
      linarith
    refine ContinuousAt.continuousWithinAt ?_
    exact ((((Complex.continuous_ofReal.continuousAt).sub continuousAt_const).mul
      ((differentiableAt_riemannZeta hxne).continuousAt.comp
        Complex.continuous_ofReal.continuousAt)).norm)
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc.image_of_continuousOn hcont).isBounded.subset_closedBall 0
  refine ⟨max 2 C₂, fun sigma h1 h2 => ?_⟩
  by_cases hlt : sigma < c
  · have hdist : dist sigma 1 < delta := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      have : sigma < 1 + delta / 2 := lt_of_lt_of_le hlt (by rw [hc]; exact min_le_left _ _)
      linarith
    exact le_trans (le_of_lt (hball hdist h1)) (le_max_left _ _)
  · push_neg at hlt
    have hmem : ‖((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ)‖ ∈
        (fun x : ℝ => ‖((x : ℂ) - 1) * riemannZeta (x : ℂ)‖) '' (Set.Icc c 2) :=
      ⟨sigma, ⟨hlt, h2⟩, rfl⟩
    have := hC₂ hmem
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact le_trans (le_trans (le_abs_self _) this) (le_max_right _ _)

/-- **The companion's pole is simple.**  Given entire continuations matching the positive even
blocks on the readout half-plane, `‖D σ‖ · (σ - 1)` is bounded on `(1, 2]` — the polar hypothesis
of the pole-tolerant edge engine, derived from the tower rather than assumed.  The pole of the
diagonal readout is exactly the one zeta contributes, and it is simple. -/
theorem pairReadout_simplePole_bound
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData) (r : ℕ)
    (block : ℕ → ℂ → ℂ)
    (hblock_entire : ∀ j, Differentiable ℂ (block j))
    (hblock_eq : ∀ j, Set.EqOn (block j)
      (bankEulerReadout (arithmeticSymmetricPowerRoot (2 * (j + 1)) (maassCPSBase M)))
      {s : ℂ | 1 < s.re}) :
    ∃ K : ℝ, ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      ‖bankEulerReadout (pairBank (arithmeticSymmetricPowerRoot r (maassCPSBase M)))
        (sigma : ℂ)‖ * (sigma - 1) ≤ K := by
  obtain ⟨C, hC'⟩ := exists_zeta_segment_bound
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC' (3 / 2) (by norm_num) (by norm_num))
  have hprodcont : ContinuousOn
      (fun sigma : ℝ => ∏ j ∈ Finset.range r, ‖block j (sigma : ℂ)‖) (Set.Icc 1 2) :=
    (continuous_finsetProd _ fun j _ =>
      ((hblock_entire j).continuous.comp Complex.continuous_ofReal).norm).continuousOn
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc.image_of_continuousOn hprodcont).isBounded.subset_closedBall 0
  refine ⟨C * max B 0, fun sigma h1 h2 => ?_⟩
  have hmem : (sigma : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    show 1 < ((sigma : ℂ)).re
    simpa using h1
  have hsplit : ‖bankEulerReadout
        (pairBank (arithmeticSymmetricPowerRoot r (maassCPSBase M))) (sigma : ℂ)‖ * (sigma - 1) =
      ‖((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ)‖ *
        ∏ j ∈ Finset.range r, ‖block j (sigma : ℂ)‖ := by
    rw [bankEulerReadout_pairBank_eq_zeta_mul M hC r (by simpa using h1), norm_mul, norm_prod,
      norm_mul]
    have hsub : ‖((sigma : ℂ) - 1)‖ = sigma - 1 := by
      rw [show (sigma : ℂ) - 1 = ((sigma - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [hsub, Finset.prod_congr rfl (fun j _ => (congrArg norm (hblock_eq j hmem)).symm)]
    ring
  rw [hsplit]
  have hprodmem : (∏ j ∈ Finset.range r, ‖block j (sigma : ℂ)‖) ∈
      (fun x : ℝ => ∏ j ∈ Finset.range r, ‖block j (x : ℂ)‖) '' (Set.Icc 1 2) :=
    ⟨sigma, ⟨le_of_lt h1, h2⟩, rfl⟩
  have hBbound := hB hprodmem
  simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hBbound
  have hple : (∏ j ∈ Finset.range r, ‖block j (sigma : ℂ)‖) ≤ max B 0 :=
    le_trans (le_trans (le_abs_self _) hBbound) (le_max_left _ _)
  have hpnonneg : 0 ≤ ∏ j ∈ Finset.range r, ‖block j (sigma : ℂ)‖ :=
    Finset.prod_nonneg fun j _ => norm_nonneg _
  exact mul_le_mul (hC' sigma h1 h2) hple hpnonneg hCnonneg

/-- **The companion is bounded at the doubled ordinate.**  Off the pole `s = 1`, i.e. for
`y ≠ 0`, the diagonal readout is bounded on the segment `σ ∈ (1, 2]` translated by `2iy` — the
hypothesis `hDtwist` of the pole-tolerant edge engine. -/
theorem pairReadout_twist_bound
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData) (r : ℕ)
    (block : ℕ → ℂ → ℂ)
    (hblock_entire : ∀ j, Differentiable ℂ (block j))
    (hblock_eq : ∀ j, Set.EqOn (block j)
      (bankEulerReadout (arithmeticSymmetricPowerRoot (2 * (j + 1)) (maassCPSBase M)))
      {s : ℂ | 1 < s.re})
    {y : ℝ} (hy : y ≠ 0) :
    ∃ K₂ : ℝ, ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      ‖bankEulerReadout (pairBank (arithmeticSymmetricPowerRoot r (maassCPSBase M)))
        ((sigma : ℂ) + 2 * y * I)‖ ≤ K₂ := by
  have hne : ∀ sigma : ℝ, ((sigma : ℂ) + 2 * y * I) ≠ 1 := by
    intro sigma hcon
    have him : ((sigma : ℂ) + 2 * y * I).im = 0 := by rw [hcon]; simp
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_re, Complex.ofReal_im] at him
    apply hy
    linarith
  have hcont : ContinuousOn
      (fun sigma : ℝ => ‖riemannZeta ((sigma : ℂ) + 2 * y * I)‖ *
        ∏ j ∈ Finset.range r, ‖block j ((sigma : ℂ) + 2 * y * I)‖) (Set.Icc 1 2) := by
    apply ContinuousOn.mul
    · refine Continuous.continuousOn ?_
      refine Continuous.norm ?_
      refine continuous_iff_continuousAt.mpr fun sigma => ?_
      exact ContinuousAt.comp (differentiableAt_riemannZeta (hne sigma)).continuousAt
        ((Complex.continuous_ofReal.add continuous_const).continuousAt)
    · refine Continuous.continuousOn ?_
      exact continuous_finsetProd _ fun j _ =>
        ((hblock_entire j).continuous.comp
          (Complex.continuous_ofReal.add continuous_const)).norm
  obtain ⟨K, hK⟩ := (isCompact_Icc.image_of_continuousOn hcont).isBounded.subset_closedBall 0
  refine ⟨max K 0, fun sigma h1 h2 => ?_⟩
  have hmem : ((sigma : ℂ) + 2 * y * I) ∈ {s : ℂ | 1 < s.re} := by
    show 1 < ((sigma : ℂ) + 2 * y * I).re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_im]
    linarith
  have hsplit : ‖bankEulerReadout
        (pairBank (arithmeticSymmetricPowerRoot r (maassCPSBase M)))
        ((sigma : ℂ) + 2 * y * I)‖ =
      ‖riemannZeta ((sigma : ℂ) + 2 * y * I)‖ *
        ∏ j ∈ Finset.range r, ‖block j ((sigma : ℂ) + 2 * y * I)‖ := by
    rw [bankEulerReadout_pairBank_eq_zeta_mul M hC r hmem, norm_mul, norm_prod]
    rw [Finset.prod_congr rfl (fun j _ => (congrArg norm (hblock_eq j hmem)).symm)]
  rw [hsplit]
  have hmemI : (‖riemannZeta ((sigma : ℂ) + 2 * y * I)‖ *
      ∏ j ∈ Finset.range r, ‖block j ((sigma : ℂ) + 2 * y * I)‖) ∈
      (fun x : ℝ => ‖riemannZeta ((x : ℂ) + 2 * y * I)‖ *
        ∏ j ∈ Finset.range r, ‖block j ((x : ℂ) + 2 * y * I)‖) '' (Set.Icc 1 2) :=
    ⟨sigma, ⟨le_of_lt h1, h2⟩, rfl⟩
  have hb := hK hmemI
  simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hb
  exact le_trans (le_trans (le_abs_self _) hb) (le_max_left _ _)

/-- **Edge nonvanishing for the standard Maass rung off `s = 1`.**  Every input of the
pole-tolerant edge argument is now discharged from the tower: the candidate identification from
the ceiling (`CPSStandardEulerIdentification3D`), the bank hypotheses from the ceiling
(`CPSSymmetricPowerRootReality3D`), and the companion's simple pole and twist bound from the
Clebsch--Gordan decomposition.  The only inputs are the tower's entire continuations at the
positive even ranks.

Not proven here: the point `y = 0`, i.e. `C (1) ≠ 0`. -/
theorem standard_edge_nonvanishing_of_blocks
    {M : GenuineMaassCuspForm3D} (hC : MaassTowerCeiling M.eigenData) {r : ℕ}
    {D : ArithmeticCPSCompletionData r 1}
    (L : ConventionalCompletedRankinSelbergSource3D r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D D)
    (block : ℕ → ℂ → ℂ)
    (hblock_entire : ∀ j, Differentiable ℂ (block j))
    (hblock_eq : ∀ j, Set.EqOn (block j)
      (bankEulerReadout (arithmeticSymmetricPowerRoot (2 * (j + 1)) (maassCPSBase M)))
      {s : ℂ | 1 < s.re})
    {y : ℝ} (hy : y ≠ 0) :
    L.uncompletedContinuation (1 + y * I) ≠ 0 := by
  obtain ⟨K, hK⟩ := pairReadout_simplePole_bound M hC r block hblock_entire hblock_eq
  obtain ⟨K₂, hK₂⟩ := pairReadout_twist_bound M hC r block hblock_entire hblock_eq hy
  exact standard_edge_nonvanishing_of_companion hC L (fun _ _ => rfl) hK hK₂

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.bankEulerReadout_symmetricPowerRoot_zero
#print axioms CriticalLinePhasor.ThreeDConverse.bankEulerLog_pairBank_eq_sum
#print axioms CriticalLinePhasor.ThreeDConverse.bankEulerReadout_pairBank_eq_prod
#print axioms CriticalLinePhasor.ThreeDConverse.bankEulerReadout_pairBank_eq_zeta_mul
#print axioms CriticalLinePhasor.ThreeDConverse.exists_zeta_segment_bound
#print axioms CriticalLinePhasor.ThreeDConverse.pairReadout_simplePole_bound
#print axioms CriticalLinePhasor.ThreeDConverse.pairReadout_twist_bound
#print axioms CriticalLinePhasor.ThreeDConverse.standard_edge_nonvanishing_of_blocks
