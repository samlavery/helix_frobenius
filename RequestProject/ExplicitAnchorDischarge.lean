import RequestProject.GrowthGap

/-!
# Explicit finite stages and growth consumers for the discharge drafts

At s = -1+20i, let mu_k be the existing explicit prime-and-Gamma coefficient.
The finite stage keeps the Gamma jets and replaces each prime L-series by its sum over n < N.
For each fixed k these stages converge to mu_k. All prime powers use the same anchor and
the actual L-series term; there are no independent prime-power phase variables.

Two remaining estimates are made usable by proved consumers:
* fixed C,p with, for each k, eventually in N, |stage_N(k)| <= C*(1+k^p);
* nonnegative bases b_j tending to 1, with |mu_k| <= C_j*b_j^k for every j,k.
The constants C_j need not be uniform in j. No such estimate is asserted here.

Expectation-free decompositions: `have hsum := LSeriesSummable_of_abscissaOfAbsConv_lt_re ...`
gives stage convergence; `exact le_of_tendsto ...` passes eventual bounds to the limit.
For varying rates, `refine squeeze_zero_norm ...` uses one base below each fixed R > 1;
independently, `obtain ⟨j, hj⟩ := ...` selects that base from convergence to 1.

Search commands: `rg -n -i 'prime_?jet_?stage|primeJetStage|anchor_?coeff_?stage|stage_?coefficient|coeff.*tendsto|tendsto.*coeff|normalized.*decay|rates.*tendsto|exp.*bound.*one' RequestProject --glob '*.lean'`;
`rg -n 'LSeriesSummable.*abscissa|LSeriesSummable.*iff|tendsto_sum_nat|le_of_tendsto|abscissaOfAbsConv_logMul' .lake/packages/mathlib/Mathlib --glob '*.lean'`.
LeanSearch: eventual upper bounds pass to a real limit. Loogle: `Filter.Tendsto, (_ <= _)`.
-/

open Complex Finset Filter Topology LSeries
open CriticalLinePhasor.ContourArgument

namespace CriticalLinePhasor.SeatingLedger

/-- Integer cutoff, including every prime power below the cutoff. -/
noncomputable def primeJetStage (s : ℂ) (N : ℕ) : ℕ → ℂ
  | 0 => 0
  | m + 1 => (-1) ^ m / (m.factorial : ℂ) *
      ∑ n ∈ range N, LSeries.term (logMul^[m] vonMangoldtC) (1 - s) n

theorem primeJetStage_tendsto {s : ℂ} (hs : s.re < 0) (m : ℕ) :
    Tendsto (fun N => primeJetStage s N m) atTop (𝓝 (jets primeSide s m)) := by
  cases m with
  | zero => simpa [primeJetStage, jets] using (tendsto_const_nhds (x := (0 : ℂ)))
  | succ m =>
    have hab : abscissaOfAbsConv (logMul^[m] vonMangoldtC) ≤ 1 := by
      simpa only [absicssaOfAbsConv_logPowMul] using abscissa_vonMangoldtC_le_one
    have hsum := LSeriesSummable_of_abscissaOfAbsConv_lt_re (abscissa_lt_one_sub_re hs hab)
    have hlim := hsum.hasSum.tendsto_sum_nat.const_mul ((-1 : ℂ) ^ m / (m.factorial : ℂ))
    simpa only [primeJetStage, jets_primeSide hs, LSeries] using hlim

/-- Finite jet dependence makes each Toeplitz coefficient continuous under pointwise jet limits. -/
theorem toeplitzCoeff_tendsto {J : ℕ → ℕ → ℂ} {S : ℕ → ℂ}
    (hJ : ∀ m, Tendsto (fun N => J N m) atTop (𝓝 (S m))) (d : ℂ) (k : ℕ) :
    Tendsto (fun N => toeplitzCoeff d (J N) k) atTop (𝓝 (toeplitzCoeff d S k)) := by
  cases k with
  | zero =>
    simp only [toeplitzCoeff]
    exact ((Complex.continuous_ofReal.tendsto _).comp
      ((Complex.continuous_re.tendsto _).comp (hJ 1))).const_mul 2 |>.div_const d
  | succ k =>
    simp only [toeplitzCoeff]
    exact tendsto_finsetSum _ (fun i _ => (hJ (k + 2 - i)).const_mul _)

/-- The full completed coefficient stage; the zeroth coefficient uses the original finite part. -/
noncomputable def explicitCoeffStage (N k : ℕ) : ℂ :=
  toeplitzCoeff (-3) (jets archSide anchor20 + primeJetStage anchor20 N) k

theorem explicitCoeffStage_tendsto (k : ℕ) :
    Tendsto (fun N => explicitCoeffStage N k) atTop
      (𝓝 (toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k)) := by
  have hs : anchor20.re < 0 := by rw [anchor20_re]; norm_num
  rw [jets_explicit_split hs]
  exact toeplitzCoeff_tendsto
    (fun m => tendsto_const_nhds.add (primeJetStage_tendsto hs m)) (-3) k

/-- A fixed polynomial envelope may start at a different cutoff for each degree. -/
theorem explicitCoeff_polynomial_bound_of_stage_bound {C : ℝ} {p : ℕ}
    (hbound : ∀ k, ∀ᶠ N in atTop, ‖explicitCoeffStage N k‖ ≤ C * (1 + (k : ℝ) ^ p)) :
    ∀ k, ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ ≤
      C * (1 + (k : ℝ) ^ p) := by
  intro k
  exact le_of_tendsto (explicitCoeffStage_tendsto k).norm (hbound k)

theorem riemannHypothesis_of_explicit_stage_bound
    (hbound : ∃ C : ℝ, ∃ p : ℕ, ∀ k, ∀ᶠ N in atTop,
      ‖explicitCoeffStage N k‖ ≤ C * (1 + (k : ℝ) ^ p)) : RiemannHypothesis := by
  obtain ⟨C, p, hbound⟩ := hbound
  apply riemannHypothesis_of_explicit_fixed_anchor_polynomial_growth
  exact ⟨C, p, explicitCoeff_polynomial_bound_of_stage_bound hbound⟩

/-- A bound with base q strictly below R gives decay after normalization by R. -/
theorem normalized_decay_of_exponential_bound {μ : ℕ → ℂ} {C q R : ℝ}
    (hq : 0 ≤ q) (hR : 0 < R) (hqR : q < R) (hbound : ∀ k, ‖μ k‖ ≤ C * q ^ k) :
    Tendsto (fun k : ℕ => μ k / (R : ℂ) ^ k) atTop (𝓝 0) := by
  refine squeeze_zero_norm (a := fun k => C * (q / R) ^ k) (fun k => ?_) ?_
  · rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    calc ‖μ k‖ / R ^ k ≤ (C * q ^ k) / R ^ k :=
        div_le_div_of_nonneg_right (hbound k) (pow_nonneg hR.le k)
      _ = _ := by rw [div_pow]; ring
  · have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg hq hR.le) ((div_lt_one hR).mpr hqR)).const_mul C
    simpa only [mul_zero] using hlim

/-- No common bound on the constants C_j is needed. -/
theorem normalized_decay_of_rates_tendsto_one {μ : ℕ → ℂ} {b C : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (hlim : Tendsto b atTop (𝓝 1))
    (hbound : ∀ j k, ‖μ k‖ ≤ C j * b j ^ k) {R : ℝ} (hR : 1 < R) :
    Tendsto (fun k : ℕ => μ k / (R : ℂ) ^ k) atTop (𝓝 0) := by
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hR)).exists
  exact normalized_decay_of_exponential_bound (hb j) (by linarith) hj (hbound j)

theorem riemannHypothesis_of_explicit_rates
    (b C : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (hlim : Tendsto b atTop (𝓝 1))
    (hbound : ∀ j k, ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ ≤
      C j * b j ^ k) : RiemannHypothesis := by
  apply RHBridge.no_offline_zeros_implies_rh
  apply rh_of_subexponential anchor20_notMem (by rw [anchor20_re]; norm_num)
  have hs : anchor20.re < 0 := by rw [anchor20_re]; norm_num
  have hseq : ∀ k, toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k =
      xiCoeff anchor20 k := by
    intro k
    have hd : ((2 * anchor20.re - 1 : ℝ) : ℂ) = -3 := by rw [anchor20_re]; norm_num
    rw [← hd, ← jets_xiLogDeriv_eq_explicit hs,
      toeplitzCoeff_jets_eq_xiCoeff anchor20_notMem (by rw [anchor20_re]; norm_num) k]
  simp only [hseq] at hbound
  exact fun R hR => normalized_decay_of_rates_tendsto_one hb hlim hbound hR

/-- The existing unconditional majorant is strictly larger than one. -/
theorem one_lt_growthBase : 1 < growthBase := by
  unfold growthBase
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.primeJetStage_tendsto
#print axioms CriticalLinePhasor.SeatingLedger.explicitCoeffStage_tendsto
#print axioms CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_explicit_stage_bound
#print axioms CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_explicit_rates
#print axioms CriticalLinePhasor.SeatingLedger.one_lt_growthBase
