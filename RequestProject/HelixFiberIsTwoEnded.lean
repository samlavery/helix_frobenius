import RequestProject.HelixFiberEventTrace
import RequestProject.HelixWindowCompletion
import RequestProject.GrownFiberConverges
import RequestProject.NativeNontriviality
import RequestProject.GrownFiberEvolution

/-!
# The full fiber IS the two-ended fiber: a geometric identification, not through the readout (ledger 1269)

1268 found that `HelixFiberEventTrace.fiber_on_line_iff_event` reduces both sides to `ζ = 0`. This file identifies
the two 3D objects directly, without passing through `riemannZeta` (checked mechanically by `#scan_zeta` at the
end).

**One Gaussian η bank, two readings.** The η bank `θ₀₁(x) = 2θ(4x) − θ(x) = Σ_n (−1)^n e^{−πn²x}` (the indexed 3D
bank of 1255). Under the Mellin integral, its mode `n` is the Dirichlet phasor `n^{−s}` with the Γ-profile
(`HelixWindowCompletion.mellin_head`, exact at every finite head in the whole strip).
* **Gaussian side, new here.** The head's bank is an alternating sum of nonincreasing terms, so
  `0 ≤ 1 − windowBank N x ≤ 2e^{−πx}` uniformly in the head (`norm_one_sub_windowBank_le`). Dominated convergence
  passes the head's Mellin integral to the full bank's (`tendsto_mellin_window`). The full bank splits at the
  origin cut into the two-ended form (`mellin_eta_bank`: `Mellin(1 − θ₀₁)(w) = −etaPair.Λ(w)` for `0 < Re w`).
* **Dirichlet side, compiled.** The heads converge to the full lane fiber
  (`GrownFiber.finiteFiber_tendstoLocallyUniformlyOn`, `NativeNontriviality.etaTailLimit_eq_etaLim`,
  `CarrierReadout.laneChart_bank`).
* `etaLim_eq_two_ended`: the full Dirichlet lane fiber equals `−(π^{s/2}/2Γ(s/2))` times the η-bank two-ended
  fiber, for `Re s > 0`, `s ≠ 1`.
* The η bank folds onto the native bank by its own heights (`HelixTwoEndedEta.etaPair_Λ_eq`, a Mellin identity of
  the banks), and the native two-ended fiber at offset `v` is the two feet (`HelixOriginCentered.origin_two_ended`).

Results:
* `laneChart3D_eq_two_ended`: **for every `(σ, y)` with `σ > 0`, the full 3D fiber is a nonzero archimedean factor
  times the native two-ended fiber at offset `v = (σ − ½)/2 + iy/2`.**
* `laneChart3D_half_eq_resultant`: on the line, it is that factor times the resultant of
  `twoEndedConfig (e^y) hc`, at every cut.
* `fiber_vanishes_iff_two_ended`: for `0 < σ < 1`, the full fiber vanishes at `(σ, y)` exactly when the native
  two-ended fiber at offset `v` cancels.
* `fiber_half_vanishes_iff_cancels`: on the line, the full fiber's vanishing IS the two-ended configuration's
  cancellation.

The two objects are one function up to a nonvanishing factor. The identification is established mode by mode at
every finite head, then by limits of the banks. On the Dirichlet side `σ` is the amplitude exponent; on the Gaussian
side it is the transverse offset `Re v`. The native construction is the member `σ = ½`, `Re v = 0`, of both.
-/

open Complex Set MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixFiberIsTwoEnded

open CriticalLinePhasor CriticalLinePhasor.GlobalHelix CriticalLinePhasor.HelixTwoEndedClosure
  CriticalLinePhasor.HelixTwoEndedNative CriticalLinePhasor.HelixTwoEndedEta CriticalLinePhasor.HelixWindowCompletion
  CriticalLinePhasor.HelixOriginCentered CriticalLinePhasor.HelixTwoEndedCancellation
  CriticalLinePhasor.CarrierHeadFiniteFiber CarrierReadout

/-! ## 1. A finite alternating sum of a nonincreasing nonnegative sequence lies in `[0, a 0]` -/

theorem alternating_sum_mem (n : ℕ) : ∀ (a : ℕ → ℝ), Antitone a → (∀ k, 0 ≤ a k) →
    0 ≤ ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * a k ∧ ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * a k ≤ a 0 := by
  induction n with
  | zero => intro a _ h0; simp [h0 0]
  | succ n ih =>
    intro a ha h0
    rw [Finset.sum_range_succ']
    have hs := ih (fun k => a (k + 1)) (fun i j hij => ha (by omega)) (fun k => h0 _)
    have hneg : ∑ k ∈ Finset.range n, (-1 : ℝ) ^ (k + 1) * a (k + 1) =
        -∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * a (k + 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have ha1 : a 1 ≤ a 0 := ha (by norm_num)
    rw [hneg, pow_zero, one_mul]
    constructor <;> linarith [hs.1, hs.2]

/-! ## 2. The head's bank: bounds uniform in the head -/

/-- The head's mode `k` (site `k+1`): window weight times the Gaussian mode. -/
def headTerm (N x : ℝ) (k : ℕ) : ℝ := smoothEntry (((k + 1 : ℕ) : ℝ) / N) * Real.exp (-siteRate k * x)

/-- The head's alternating sum. -/
def headAlt (N x : ℝ) : ℝ := ∑ k ∈ Finset.range ⌈N⌉₊, (-1 : ℝ) ^ k * headTerm N x k

theorem one_sub_windowBank_eq (N x : ℝ) : 1 - windowBank N x = ((2 * headAlt N x : ℝ) : ℂ) := by
  rw [one_sub_windowBank, headAlt]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold headCoeff headTerm
  push_cast
  ring

theorem headTerm_nonneg (N x : ℝ) (k : ℕ) : 0 ≤ headTerm N x k :=
  mul_nonneg (smoothEntry_nonneg _) (Real.exp_pos _).le

theorem headTerm_antitone {N x : ℝ} (hN : 0 < N) (hx : 0 ≤ x) : Antitone (headTerm N x) := by
  intro i j hij
  unfold headTerm
  have hij' : ((i + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hij
  apply mul_le_mul
  · apply GrownFiber.smoothEntry_antitoneOn
    · simp only [Set.mem_Ici]; positivity
    · simp only [Set.mem_Ici]; positivity
    · exact div_le_div_of_nonneg_right hij' hN.le
  · apply Real.exp_le_exp.mpr
    have : siteRate i ≤ siteRate j := by
      unfold siteRate
      have h0 : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
      gcongr
    nlinarith
  · exact (Real.exp_pos _).le
  · exact smoothEntry_nonneg _

theorem siteRate_zero : siteRate 0 = Real.pi := by
  unfold siteRate
  simp

/-- `0 ≤ headAlt ≤ e^{−πx}`, uniformly in the head. -/
theorem headAlt_mem {N x : ℝ} (hN : 0 < N) (hx : 0 ≤ x) :
    0 ≤ headAlt N x ∧ headAlt N x ≤ Real.exp (-Real.pi * x) := by
  obtain ⟨h1, h2⟩ := alternating_sum_mem ⌈N⌉₊ (headTerm N x) (headTerm_antitone hN hx) (headTerm_nonneg N x)
  refine ⟨h1, h2.trans ?_⟩
  unfold headTerm
  rw [siteRate_zero]
  have hle : smoothEntry (((0 + 1 : ℕ) : ℝ) / N) ≤ 1 := GrownFiber.smoothEntry_le_one (by positivity)
  have he := Real.exp_pos (-Real.pi * x)
  nlinarith

/-- **The head's bank never leaves `[0, 2e^{−πx}]`**, at every head. -/
theorem norm_one_sub_windowBank_le {N x : ℝ} (hN : 0 < N) (hx : 0 ≤ x) :
    ‖1 - windowBank N x‖ ≤ 2 * Real.exp (-Real.pi * x) := by
  obtain ⟨h1, h2⟩ := headAlt_mem hN hx
  rw [one_sub_windowBank_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

/-! ## 3. The heads' banks converge to the η bank -/

theorem summable_siteExp {x : ℝ} (hx : 0 < x) : Summable (fun k : ℕ => Real.exp (-siteRate k * x)) := by
  refine (XiKernelBridge.hasSum_xiThetaSeriesTerm (Real.log x / 2)).summable.congr fun n => ?_
  unfold ThetaWronskianSuzukiGram.xiThetaSeriesTerm siteRate
  rw [show 2 * (Real.log x / 2) = Real.log x by ring, Real.exp_log hx]
  push_cast
  ring_nf

theorem headAlt_eq_tsum {N x : ℝ} (hN : 0 < N) :
    headAlt N x = ∑' k : ℕ, (-1 : ℝ) ^ k * headTerm N x k := by
  rw [headAlt, tsum_eq_sum]
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  have hk' : N ≤ ((k + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil N
    have h2 : ((⌈N⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    push_cast
    linarith
  unfold headTerm
  rw [GrownFiber.smoothEntry_of_one_le ((one_le_div hN).mpr hk'), zero_mul, mul_zero]

theorem smoothEntry_zero : smoothEntry 0 = 1 := by
  unfold smoothEntry
  simp

theorem tendsto_headAlt {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => headAlt ((n : ℝ) + 1) x) atTop
      (𝓝 (∑' k : ℕ, (-1 : ℝ) ^ k * Real.exp (-siteRate k * x))) := by
  have hrw : (fun n : ℕ => headAlt ((n : ℝ) + 1) x) =
      fun n : ℕ => ∑' k : ℕ, (-1 : ℝ) ^ k * headTerm ((n : ℝ) + 1) x k := by
    funext n
    exact headAlt_eq_tsum (by positivity)
  rw [hrw]
  refine tendsto_tsum_of_dominated_convergence (summable_siteExp hx) (fun k => ?_) ?_
  · have hcont : ContinuousAt smoothEntry 0 := (GrownFiberEvolution.smoothEntry_hasDerivAt (by norm_num)).continuousAt
    have hdiv : Tendsto (fun n : ℕ => ((k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((k + 1 : ℕ) : ℝ)
      rw [mul_zero] at this
      refine this.congr fun n => ?_
      ring
    have hφ := (hcont.tendsto.comp hdiv)
    rw [smoothEntry_zero] at hφ
    have := (hφ.mul_const (Real.exp (-siteRate k * x))).const_mul ((-1 : ℝ) ^ k)
    rw [one_mul] at this
    refine this.congr fun n => ?_
    unfold headTerm
    simp only [Function.comp]
  · refine Eventually.of_forall fun n k => ?_
    unfold headTerm
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (smoothEntry_nonneg _), abs_of_pos (Real.exp_pos _)]
    have hle : smoothEntry (((k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ≤ 1 :=
      GrownFiber.smoothEntry_le_one (by positivity)
    have he := Real.exp_pos (-siteRate k * x)
    nlinarith

/-- The Gaussian mode of site `k+1` at height `x`. -/
def siteExp (x : ℝ) (k : ℕ) : ℝ := Real.exp (-siteRate k * x)

theorem theta_eq_siteExp {t : ℝ} (ht : 0 < t) : gaussianLatticeTheta t = 1 + 2 * ∑' k : ℕ, siteExp t k := by
  rw [HelixFootMass.theta_eq_thetaSum ht, XiKernelBridge.thetaSum]
  congr 2
  refine tsum_congr fun n => ?_
  unfold ThetaWronskianSuzukiGram.xiThetaSeriesTerm siteExp siteRate
  rw [show 2 * (Real.log t / 2) = Real.log t by ring, Real.exp_log ht]
  push_cast
  ring_nf

theorem siteExp_odd (x : ℝ) (j : ℕ) : siteExp x (2 * j + 1) = siteExp (4 * x) j := by
  unfold siteExp siteRate
  congr 1
  push_cast
  ring

/-- The alternating mode sum splits into even and odd sites. -/
theorem alt_siteExp {x : ℝ} (hx : 0 < x) :
    ∑' k : ℕ, (-1 : ℝ) ^ k * siteExp x k = ∑' j : ℕ, siteExp x (2 * j) - ∑' j : ℕ, siteExp x (2 * j + 1) := by
  have hA : Summable (siteExp x) := summable_siteExp hx
  have he : Summable fun j : ℕ => siteExp x (2 * j) :=
    hA.comp_injective (i := fun j : ℕ => 2 * j) (mul_right_injective₀ (two_ne_zero' ℕ))
  have ho : Summable fun j : ℕ => siteExp x (2 * j + 1) :=
    hA.comp_injective (i := fun j : ℕ => 2 * j + 1) (fun a b h => by simp only at h; omega)
  have h1 : HasSum (fun j : ℕ => (-1 : ℝ) ^ (2 * j) * siteExp x (2 * j)) (∑' j : ℕ, siteExp x (2 * j)) := by
    convert he.hasSum using 1
    funext j
    rw [pow_mul, neg_one_sq, one_pow, one_mul]
  have h2 : HasSum (fun j : ℕ => (-1 : ℝ) ^ (2 * j + 1) * siteExp x (2 * j + 1))
      (-∑' j : ℕ, siteExp x (2 * j + 1)) := by
    convert ho.hasSum.neg using 1
    funext j
    rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul]
  have h := HasSum.even_add_odd (f := fun k : ℕ => (-1 : ℝ) ^ k * siteExp x k) h1 h2
  rw [h.tsum_eq]
  ring

theorem siteExp_split {x : ℝ} (hx : 0 < x) :
    ∑' k : ℕ, siteExp x k = ∑' j : ℕ, siteExp x (2 * j) + ∑' j : ℕ, siteExp x (2 * j + 1) := by
  have hA : Summable (siteExp x) := summable_siteExp hx
  have he : Summable fun j : ℕ => siteExp x (2 * j) :=
    hA.comp_injective (i := fun j : ℕ => 2 * j) (mul_right_injective₀ (two_ne_zero' ℕ))
  have ho : Summable fun j : ℕ => siteExp x (2 * j + 1) :=
    hA.comp_injective (i := fun j : ℕ => 2 * j + 1) (fun a b h => by simp only at h; omega)
  exact (HasSum.even_add_odd (f := siteExp x) he.hasSum ho.hasSum).tsum_eq

/-- The η bank in its mode form: `1 − θ₀₁(x) = 2 Σ_k (−1)^k e^{−π(k+1)²x}`. -/
theorem one_sub_etaHelixBank {x : ℝ} (hx : 0 < x) :
    1 - etaHelixBank x = ((2 * ∑' k : ℕ, (-1 : ℝ) ^ k * siteExp x k : ℝ) : ℂ) := by
  rw [etaHelixBank_eq hx, theta_eq_siteExp (by positivity : (0 : ℝ) < 4 * x), theta_eq_siteExp hx,
    alt_siteExp hx, siteExp_split hx]
  have h4 : ∑' j : ℕ, siteExp (4 * x) j = ∑' j : ℕ, siteExp x (2 * j + 1) :=
    tsum_congr fun j => (siteExp_odd x j).symm
  rw [h4]
  push_cast
  ring

theorem tendsto_windowBank {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => 1 - windowBank ((n : ℝ) + 1) x) atTop (𝓝 (1 - etaHelixBank x)) := by
  rw [one_sub_etaHelixBank hx]
  unfold siteExp
  have h := ((tendsto_headAlt hx).const_mul 2)
  have h' := (continuous_ofReal.tendsto _).comp h
  refine h'.congr fun n => ?_
  rw [one_sub_windowBank_eq]
  rfl

theorem norm_one_sub_etaHelixBank_le {x : ℝ} (hx : 0 < x) :
    ‖1 - etaHelixBank x‖ ≤ 2 * Real.exp (-Real.pi * x) :=
  le_of_tendsto ((tendsto_windowBank hx).norm)
    (Eventually.of_forall fun n => norm_one_sub_windowBank_le (by positivity) hx.le)

/-! ## 4. The Mellin integrals pass to the full bank -/

theorem integrable_bound {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => 2 * ‖(t : ℂ) ^ (w - 1) * ((Real.exp (-Real.pi * t) : ℝ) : ℂ)‖) (Ioi 0) :=
  ((integrableOn_cpow_exp hw Real.pi_pos).norm).const_mul 2

theorem integrableOn_eta_bank {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * (1 - etaHelixBank t)) (Ioi 0) := by
  refine Integrable.mono' (integrable_bound hw) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht.ne')).continuousWithinAt).mul
      (continuousWithinAt_const.sub (etaHelixBank_continuousOn t ht))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have := norm_one_sub_etaHelixBank_le ht
    have hn := norm_nonneg ((t : ℂ) ^ (w - 1))
    nlinarith

/-- **The heads' Mellin integrals converge to the full η bank's**, by dominated convergence. -/
theorem tendsto_mellin_window {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun n : ℕ => mellin (fun x => 1 - windowBank ((n : ℝ) + 1) x) w) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) * (1 - etaHelixBank t))) := by
  simp only [mellin, smul_eq_mul]
  refine tendsto_integral_of_dominated_convergence
    (fun t => 2 * ‖(t : ℂ) ^ (w - 1) * ((Real.exp (-Real.pi * t) : ℝ) : ℂ)‖)
    (fun n => (integrableOn_head ((n : ℝ) + 1) hw).aestronglyMeasurable) (integrable_bound hw)
    (fun n => ?_) ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have := norm_one_sub_windowBank_le (N := (n : ℝ) + 1) (by positivity) ht.le
    have hn := norm_nonneg ((t : ℂ) ^ (w - 1))
    nlinarith
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    exact (tendsto_windowBank ht).const_mul _

/-- **The full η bank's Mellin integral is its two-ended fiber**, at the origin cut: for `0 < Re w`, `w ≠ ½`. -/
theorem mellin_eta_bank {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 1 / 2) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) * (1 - etaHelixBank t) = -etaPair.Λ w := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hint := integrableOn_eta_bank hw
  have hlow : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * (1 - etaHelixBank x)) (Ioc (0 : ℝ) 1) :=
    hint.mono_set fun x hx => hx.1
  have hpow : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1)) (Ioc (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
  have hB : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * etaHelixBank x) (Ioc (0 : ℝ) 1) := by
    refine (hpow.sub hlow).congr_fun (fun x _ => ?_) measurableSet_Ioc
    simp only [Pi.sub_apply]
    ring
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hlow
    (hint.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hsplit : ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (w - 1) * (1 - etaHelixBank x) =
      (∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (w - 1)) - ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (w - 1) * etaHelixBank x := by
    rw [← integral_sub hpow hB]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    ring
  have hpowint : ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (w - 1) = 1 / w := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl (by simp; linarith))]
    simp [sub_add_cancel, Complex.zero_cpow hw0]
  have hrefl : ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (w - 1) * etaHelixBank x =
      ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (1 / 2 - w - 1) * etaAntiHelixBank u := by
    rw [lower_reflect etaHelixBank one_pos w, inv_one]
    refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 1 < u) => ?_
    have hu0 : 0 < u := one_pos.trans hu
    rw [cpow_reflect_weight hu0 w, ← one_div, eta_native_reflection hu0]
    have hh : ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((u ^ (1 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
      rw [← ofReal_mul, ← Real.rpow_add hu0]
      norm_num
    linear_combination ((u : ℂ) ^ (1 / 2 - w - 1) * etaAntiHelixBank u) * hh
  have hcut := eta_two_ended_cut one_pos hw0 hw2
  rw [inv_one, Complex.ofReal_one, Complex.one_cpow] at hcut
  have hS1 : helixStrandAt etaPair 1 w = -∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (w - 1) * (1 - etaHelixBank x) := by
    unfold helixStrandAt
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    show (x : ℂ) ^ (w - 1) * (etaHelixBank x - 1) = _
    ring
  have hS2 : helixStrandAt etaPair.symm 1 (1 / 2 - w) =
      ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (1 / 2 - w - 1) * etaAntiHelixBank u := by
    unfold helixStrandAt
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    show (u : ℂ) ^ (1 / 2 - w - 1) * (etaAntiHelixBank u - 0) = _
    ring
  rw [hsplit, hpowint, hrefl, hcut, hS1, hS2]
  ring

/-! ## 5. The identification -/

/-- **The full Dirichlet lane fiber is the η-bank two-ended fiber**, for `Re s > 0`, `s ≠ 1`. The proof never
passes through `riemannZeta`. -/
theorem etaLim_eq_two_ended {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    DVP.etaLim s = -((Real.pi : ℂ) ^ (s / 2) / (2 * Gamma (s / 2))) * etaPair.Λ (s / 2) := by
  set w : ℂ := s / 2 with hwdef
  have hw : 0 < w.re := by rw [hwdef, Complex.div_ofNat_re]; linarith
  have hw2 : w ≠ 1 / 2 := fun h => hs1 (by rw [hwdef] at h; linear_combination 2 * h)
  have hs2 : 2 * w = s := by rw [hwdef]; ring
  have hΓ : Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  have hπ : (Real.pi : ℂ) ^ w * (Real.pi : ℂ) ^ (-w) = 1 := by
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr Real.pi_ne_zero), add_neg_cancel, cpow_zero]
  have hZ : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hD := (GrownFiber.finiteFiber_tendstoLocallyUniformlyOn _ hZ).tendsto_at (show s ∈ {s : ℂ | 0 < s.re} from hs)
  have hG := tendsto_mellin_window hw
  have hG' : Tendsto (fun n : ℕ => 2 * (Real.pi : ℂ) ^ (-w) * Gamma w * finiteFiber ((n : ℝ) + 1) s) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) * (1 - etaHelixBank t))) := by
    refine hG.congr fun n => ?_
    rw [mellin_head _ hw, hs2]
  have huniq := tendsto_nhds_unique (hD.const_mul (2 * (Real.pi : ℂ) ^ (-w) * Gamma w)) hG'
  rw [mellin_eta_bank hw hw2, NativeNontriviality.etaTailLimit_eq_etaLim hs] at huniq
  have hΛ : etaPair.Λ w = -(2 * (Real.pi : ℂ) ^ (-w) * Gamma w * DVP.etaLim s) := by
    linear_combination huniq
  rw [hΛ]
  calc DVP.etaLim s = ((Real.pi : ℂ) ^ w * (Real.pi : ℂ) ^ (-w)) * DVP.etaLim s := by rw [hπ, one_mul]
    _ = -((Real.pi : ℂ) ^ w / (2 * Gamma w)) * -(2 * (Real.pi : ℂ) ^ (-w) * Gamma w * DVP.etaLim s) := by
        rw [neg_mul_neg, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero two_ne_zero hΓ)]
        ring

/-! ## 6. The native bank and the feet -/

/-- The resultant of the two-ended configuration is the native two-ended fiber at the event offset. -/
theorem resultant_eq_originΛ (Z hc : ℝ) :
    (twoEndedConfig Z hc).resultant = originΛ nativePair (eventOffset Z) := by
  rw [resultant_eq_feet]
  have h := origin_two_ended nativePair nativePair_conj nativePair_conj₀ (Real.exp_pos hc) (offset_ne_zero Z)
    (offset_ne_k Z)
  rw [eventOffset_mirror, show nativePair.ε = 1 from rfl, one_mul, ← Real.exp_neg] at h
  unfold helixFoot antiHelixFoot
  rw [← h]

theorem two_cpow_ne_one {s : ℂ} (h : s.re < 1) : (2 : ℂ) ^ (1 - s) ≠ 1 := by
  intro h0
  have h2 : ((2 : ℝ) : ℂ) ^ (1 - s) = 1 := by
    push_cast
    exact h0
  have hn := congrArg norm h2
  rw [Complex.norm_cpow_eq_rpow_re_of_pos two_pos, norm_one, Complex.sub_re, Complex.one_re] at hn
  have : (1 : ℝ) < 2 ^ (1 - s.re) := Real.one_lt_rpow (by norm_num) (by linarith)
  linarith

theorem factor_ne_zero {w : ℂ} (hw : 0 < w.re) :
    -((Real.pi : ℂ) ^ w / (2 * Gamma w)) ≠ 0 := by
  refine neg_ne_zero.mpr (div_ne_zero ?_ (mul_ne_zero two_ne_zero (Complex.Gamma_ne_zero_of_re_pos hw)))
  exact cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))

theorem fold_ne_zero {w : ℂ} (hw : (2 * w).re < 1) : 2 * (4 : ℂ) ^ (-w) - 1 ≠ 0 := by
  rw [fold_cpow]
  exact sub_ne_zero.mpr (two_cpow_ne_one hw)

/-- **The full 3D fiber is the native two-ended fiber**, at every `(σ, y)` with `σ > 0`: a nonzero archimedean
factor times the fold multiplier times the two-ended fiber of the native bank at offset `v = s/2 − ¼`. -/
theorem laneChart3D_eq_two_ended {σ y : ℝ} (hσ : 0 < σ) (hs1 : (σ : ℂ) + y * I ≠ 1) :
    laneChart3D σ y = -((Real.pi : ℂ) ^ (((σ : ℂ) + y * I) / 2) / (2 * Gamma (((σ : ℂ) + y * I) / 2))) *
      ((2 * (4 : ℂ) ^ (-(((σ : ℂ) + y * I) / 2)) - 1) *
        originΛ nativePair (((σ : ℂ) + y * I) / 2 - 1 / 4)) := by
  set s : ℂ := (σ : ℂ) + y * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs : 0 < s.re := by rw [hsre]; exact hσ
  have hw0 : s / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.div_ofNat_re, hsre, Complex.zero_re] at this
    linarith
  have hw2 : s / 2 ≠ 1 / 2 := fun h => hs1 (by linear_combination 2 * h)
  have hv : (nativePair.k : ℂ) / 2 + (s / 2 - 1 / 4) = s / 2 := by
    rw [nativePair_k]
    ring
  rw [laneChart3D_eq, laneChart_bank, etaLim_eq_two_ended hs hs1, etaPair_Λ_eq hw0 hw2, originΛ, hv]

/-- On the line, the full 3D fiber is the same factor times the resultant of the two-ended configuration at
height `e^y`, at every cut. -/
theorem laneChart3D_half_eq_resultant (y hc : ℝ) :
    laneChart3D (1 / 2) y = -((Real.pi : ℂ) ^ (1 / 4 + y * I / 2) / (2 * Gamma (1 / 4 + y * I / 2))) *
      ((2 * (4 : ℂ) ^ (-(1 / 4 + y * I / 2)) - 1) * (twoEndedConfig (Real.exp y) hc).resultant) := by
  have h1 : (((1 / 2 : ℝ)) : ℂ) + y * I = 1 / 2 + y * I := by push_cast; ring
  have hs1 : (((1 / 2 : ℝ)) : ℂ) + y * I ≠ 1 := by
    rw [h1]
    intro h
    have := congrArg Complex.re h
    norm_num at this
  rw [laneChart3D_eq_two_ended (by norm_num) hs1, resultant_eq_originΛ, h1]
  have hw : (1 / 2 + (y : ℂ) * I) / 2 = 1 / 4 + y * I / 2 := by ring
  have hev : eventOffset (Real.exp y) = (1 / 2 + (y : ℂ) * I) / 2 - 1 / 4 := by
    unfold eventOffset
    rw [Real.log_exp]
    ring
  rw [hev, hw]

/-- **For `0 < σ < 1`: the full fiber vanishes at `(σ, y)` exactly when the native two-ended fiber at offset
`v = s/2 − ¼` cancels.** -/
theorem fiber_vanishes_iff_two_ended {σ y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    laneChart3D σ y = 0 ↔ originΛ nativePair (((σ : ℂ) + y * I) / 2 - 1 / 4) = 0 := by
  set s : ℂ := (σ : ℂ) + y * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre, Complex.one_re] at this
    linarith
  have hw : 0 < (s / 2).re := by rw [Complex.div_ofNat_re, hsre]; linarith
  have h2w : (2 * (s / 2)).re < 1 := by rw [show 2 * (s / 2) = s by ring, hsre]; exact hσ1
  rw [laneChart3D_eq_two_ended hσ0 hs1, mul_eq_zero, mul_eq_zero, or_iff_right (factor_ne_zero hw),
    or_iff_right (fold_ne_zero h2w)]

/-- **On the line, the full fiber's vanishing IS the two-ended configuration's cancellation**, at every cut. The
two are one 3D total up to a nonvanishing factor (`laneChart3D_half_eq_resultant`). -/
theorem fiber_half_vanishes_iff_cancels (y hc : ℝ) :
    laneChart3D (1 / 2) y = 0 ↔ (twoEndedConfig (Real.exp y) hc).Cancels := by
  have hw : 0 < (1 / 4 + (y : ℂ) * I / 2).re := by norm_num
  have h2w : (2 * (1 / 4 + (y : ℂ) * I / 2)).re < 1 := by norm_num
  unfold FocalFeet.PhasorConfig.Cancels
  rw [laneChart3D_half_eq_resultant y hc, mul_eq_zero, mul_eq_zero, or_iff_right (factor_ne_zero hw),
    or_iff_right (fold_ne_zero h2w)]

end CriticalLinePhasor.HelixFiberIsTwoEnded

end

/-! ## Mechanical check: the identification never reaches the analytic readout -/

open Lean Elab Command in
elab "#scan_zeta " ids:ident* : command => do
  let env ← getEnv
  for id in ids do
    let n := id.getId
    let s := reachRP env [n] {}
    logInfo m!"{n}: riemannZeta reachable = {s.contains `riemannZeta}, completedRiemannZeta reachable = \
      {s.contains `completedRiemannZeta}"

-- the new identification
#scan_zeta CriticalLinePhasor.HelixFiberIsTwoEnded.etaLim_eq_two_ended
  CriticalLinePhasor.HelixFiberIsTwoEnded.laneChart3D_eq_two_ended
  CriticalLinePhasor.HelixFiberIsTwoEnded.laneChart3D_half_eq_resultant
  CriticalLinePhasor.HelixFiberIsTwoEnded.fiber_vanishes_iff_two_ended
  CriticalLinePhasor.HelixFiberIsTwoEnded.fiber_half_vanishes_iff_cancels
-- positive control: the 1267 readout-level equivalence goes through ζ
#scan_zeta CriticalLinePhasor.HelixFiberEventTrace.fiber_on_line_iff_event

#print axioms CriticalLinePhasor.HelixFiberIsTwoEnded.etaLim_eq_two_ended
#print axioms CriticalLinePhasor.HelixFiberIsTwoEnded.laneChart3D_eq_two_ended
#print axioms CriticalLinePhasor.HelixFiberIsTwoEnded.laneChart3D_half_eq_resultant
#print axioms CriticalLinePhasor.HelixFiberIsTwoEnded.fiber_vanishes_iff_two_ended
#print axioms CriticalLinePhasor.HelixFiberIsTwoEnded.fiber_half_vanishes_iff_cancels
