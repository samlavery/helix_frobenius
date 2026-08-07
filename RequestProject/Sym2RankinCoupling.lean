import RequestProject.Sym2RankinBank
import RequestProject.Sym2GammaChart
import RequestProject.RSLineAgreementClosure

/-!
# The r = 2 coupling, discharged: the rank-4 Rankin bank meets the averaged lattice profile

`CPSWeakProfileCoupling3D` names the r = 2 rung's frontier as its two identification
hypotheses — the ζ-peel and the coefficient identification with the literal twisted Satake
bank.  This file discharges both and inhabits the coupling, unconditionally from the typed
Hecke package.  The chain:

* `sym2Bank_LSeriesSummable` / `rankinBank_LSeriesSummable` / `LSeries_rankinBank` — the
  Euler line `L(c, s) = ζ(s)·L(sym2Bank, s)` on `2 < Re s`, with its summability inputs;
* `dirichlet_rankinBank` — the carrier's shifted Dirichlet readout of the bank is its
  L-series;
* `gammaClockZero_log_continuous` / `gammaClock_log_integrable` /
  `completionKernelLog_pair_continuousOn` — continuity of the Γℂ-pair kernel on the ray:
  the signed-log convolution of the bounded weight-zero clock with an integrable clock,
  by dominated convergence in the swapped orientation;
* `rankin_readout_gammaC` — **the unpeeled landing**: on `2 < Re s`,
  `mellin (θ̄_f − ‖f‖²)(s) = 2^{−k}·Γℂ(s)Γℂ(s+k−1)·L(c, s)` — the compiled peeled landing
  re-dressed by the Euler line;
* `sym2_primal_line` / `sym2_dual_line` — the two line identities on the engine weight:
  both prescribed readouts' Mellin transforms are the completed Rankin L-series;
* `sym2RankinCoupling` — **the inhabitant**: `WeakBankThetaProfileCoupling3D` for the
  rank-4 pair at conductor `1` and shifts `[0, k−1]`, profiles the `2^k`-scaled averaged
  lattice bank, reflection the lattice theta transformation law under the Petersson
  average, both readout identifications recovered by line-restricted Mellin uniqueness;
* `sym2RankinPair` / `sym2Rankin_selfdual_FE` / `sym2Rankin_lambda_eq` /
  `sym2Rankin_residue` / `sym2Rankin_entire` — the payload, through Mathlib's abstract
  machinery: the completed transform of the literal Satake bank satisfies `Λ(1−s) = Λ(s)`
  globally, equals `Γℂ(s)Γℂ(s+k−1)·L(c, s)` on `2 < Re s`, has residue `2^k·‖f‖²` at the
  edge, and is entire away from its two booked poles.

The hypotheses `0 ≤ k` and `2 ≤ k` delimit the object class (holomorphic cusp forms of
weight at least two); `HeckeEigenData` is the typed classical seed package defining the
eigenform.  Everything else is compiled.

No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane MeasureTheory Set
open scoped MatrixGroups Real LSeries.notation ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace CriticalLinePhasor.Sym2Rankin

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.Sym2Wire
open CriticalLinePhasor.Sym2Join
open CriticalLinePhasor.Unfolding CriticalLinePhasor.Sym2Registration
open CriticalLinePhasor.ThreeDConverse

variable {k : ℤ} {f : CuspForm 𝒮ℒ k}


/-- The weight-zero Γ-clock in the signed-log coordinate: continuous and bounded by `2`. -/
theorem gammaClockZero_log_continuous :
    Continuous (fun u : ℝ => gammaClock 0 (Real.exp (-u))) := by
  have : (fun u : ℝ => gammaClock 0 (Real.exp (-u)))
      = fun u : ℝ => 2 * Complex.exp (-(2 * Real.pi : ℂ) * Real.exp (-u)) := by
    funext u
    unfold gammaClock
    rw [Complex.cpow_zero, mul_one]
  rw [this]
  fun_prop

theorem gammaClockZero_log_bound (u : ℝ) :
    ‖gammaClock 0 (Real.exp (-u))‖ ≤ 2 := by
  unfold gammaClock
  rw [Complex.cpow_zero, mul_one, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have hexp : ‖Complex.exp (-(2 * Real.pi : ℂ) * Real.exp (-u))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    have hre : (-(2 * Real.pi : ℂ) * ((Real.exp (-u) : ℝ) : ℂ)).re
        = -(2 * Real.pi * Real.exp (-u)) := by
      rw [show -(2 * Real.pi : ℂ) = ((-(2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_mul, Complex.ofReal_re]
      ring
    rw [hre]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  nlinarith [norm_nonneg (Complex.exp (-(2 * Real.pi : ℂ) * Real.exp (-u)))]

/-- The `ν`-clock in the signed-log coordinate is integrable when `0 < Re ν`. -/
theorem gammaClock_log_integrable (ν : ℂ) (hν : 0 < ν.re) :
    Integrable (fun u : ℝ => gammaClock ν (Real.exp (-u))) := by
  have h := (mellinConvergent_iff_negLogIntegrable (gammaClock ν) 0).mp
    (gammaClock_mellinConvergent ν 0 (by simpa using hν))
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp

/-- **Continuity of the pair kernel**: the log-Mellin convolution of the weight-zero clock
with an integrable clock is continuous on the positive ray. -/
theorem completionKernelLog_pair_continuousOn (ν : ℂ) (hν : 0 < ν.re) :
    ContinuousOn (completionKernelLog [0, ν]) (Ioi (0 : ℝ)) := by
  set F : ℝ → ℂ := fun u => gammaClock 0 (Real.exp (-u)) with hF
  set G : ℝ → ℂ := fun u => gammaClock ν (Real.exp (-u)) with hG
  have hGint : Integrable G := gammaClock_log_integrable ν hν
  -- the convolution in the dominated orientation
  have hswap : ∀ x : ℝ,
      MeasureTheory.convolution F G (ContinuousLinearMap.mul ℂ ℂ)
        MeasureTheory.volume x = ∫ v : ℝ, F (x - v) * G v := by
    intro x
    exact MeasureTheory.convolution_eq_swap _
  have hcont : Continuous (fun x : ℝ =>
      MeasureTheory.convolution F G (ContinuousLinearMap.mul ℂ ℂ)
        MeasureTheory.volume x) := by
    have : Continuous (fun x : ℝ => ∫ v : ℝ, F (x - v) * G v) := by
      apply MeasureTheory.continuous_of_dominated
        (bound := fun v : ℝ => 2 * ‖G v‖)
      · intro x
        apply AEStronglyMeasurable.mul
        · exact (gammaClockZero_log_continuous.comp
            (continuous_const.sub continuous_id)).aestronglyMeasurable
        · exact hGint.1
      · intro x
        filter_upwards with v
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (gammaClockZero_log_bound (x - v))
          (norm_nonneg _)
      · exact hGint.norm.const_mul 2
      · filter_upwards with v
        exact (gammaClockZero_log_continuous.comp
          (continuous_id.sub continuous_const)).mul continuous_const
    refine this.congr fun x => ?_
    rw [hswap x]
  -- transport along −log to the positive ray
  have hkernel : ∀ x ∈ Ioi (0 : ℝ), completionKernelLog [0, ν] x =
      MeasureTheory.convolution F G (ContinuousLinearMap.mul ℂ ℂ)
        MeasureTheory.volume (-Real.log x) := by
    intro x hx
    show logMellinConvolution (gammaClock 0) (gammaClock ν) x = _
    unfold logMellinConvolution
    rw [if_pos (mem_Ioi.mp hx)]
  refine ContinuousOn.congr ?_ hkernel
  exact hcont.comp_continuousOn
    ((Real.continuousOn_log.mono (fun x hx => by simpa using ne_of_gt hx)).neg)



/-- The Sym² bank is L-series-summable on `2 < Re s`. -/
theorem sym2Bank_LSeriesSummable (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) : LSeriesSummable (⇑(sym2Bank f)) s := by
  have hs2 : 1 < (2 * s).re := by
    have h2 : (2 * s).re = 2 * s.re := by simp [Complex.mul_re]
    rw [h2]; linarith
  have hμs : LSeriesSummable (⇑(μ : ArithmeticFunction ℂ)) s := by
    have hcoe : (⇑(μ : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗μ := by
      funext n; simp
    rw [hcoe]
    exact LSeriesSummable_moebius_iff.mpr (by linarith)
  have hb : LSeriesSummable (⇑(rankinSquareNorm f)) s :=
    rankinSquareNorm_LSeriesSummable f hk hs
  have hsq : LSeriesSummable (⇑sqIndicator) s := sqIndicator_LSeriesSummable hs2
  rw [sym2Bank, ← ArithmeticFunction.coe_mul]
  exact hsq.convolution (by rw [← ArithmeticFunction.coe_mul]; exact hμs.convolution hb)

/-- The Rankin bank is L-series-summable on `2 < Re s`. -/
theorem rankinBank_LSeriesSummable (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) : LSeriesSummable (⇑(rankinBank f)) s := by
  have hζ : LSeriesSummable (⇑((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) s := by
    have hcoe : (⇑((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗ζ := by
      funext n; simp
    rw [hcoe]
    exact LSeriesSummable_zeta_iff.mpr (by linarith)
  rw [rankinBank, ← ArithmeticFunction.coe_mul]
  exact hζ.convolution (sym2Bank_LSeriesSummable f hk hs)

/-- **The Rankin Euler line**: `L(c, s) = ζ(s) · L(sym2Bank, s)` on `2 < Re s`. -/
theorem LSeries_rankinBank (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    LSeries (⇑(rankinBank f)) s = riemannZeta s * LSeries (⇑(sym2Bank f)) s := by
  have hζ : LSeriesSummable (⇑((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) s := by
    have hcoe : (⇑((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗ζ := by
      funext n; simp
    rw [hcoe]
    exact LSeriesSummable_zeta_iff.mpr (by linarith)
  have hζval : LSeries (⇑((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) s
      = riemannZeta s := by
    have hcoe : (⇑((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗ζ := by
      funext n; simp
    rw [hcoe]
    exact LSeries_zeta_eq_riemannZeta (by linarith)
  rw [rankinBank, ← ArithmeticFunction.coe_mul,
    LSeries_convolution' hζ (sym2Bank_LSeriesSummable f hk hs), hζval]

/-- The shifted-coefficient Dirichlet readout of the Rankin bank is its L-series. -/
theorem dirichlet_rankinBank (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    CriticalLinePhasor.CarrierTheta.dirichlet (fun n => rankinBank f (n + 1)) s
      = LSeries (⇑(rankinBank f)) s := by
  have hsum : Summable (LSeries.term (⇑(rankinBank f)) s) :=
    rankinBank_LSeriesSummable f hk hs
  rw [LSeries, hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  unfold CriticalLinePhasor.CarrierTheta.dirichlet
  refine tsum_congr fun n => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
  rw [show ((n + 1 : ℕ) : ℂ) ^ (-s) = (((n + 1 : ℕ) : ℂ) ^ s)⁻¹ from cpow_neg _ s]
  rw [div_eq_mul_inv]





/-- **The unpeeled Γℂ-chart landing**: on `2 < Re s` the Mellin readout of the averaged
lattice tail is the completed rank-4 Rankin L-series in the prescribed chart. -/
theorem rankin_readout_gammaC (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    mellin (fun t : ℝ => averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ)) s =
      (2 : ℂ) ^ (-(k : ℂ)) * (Gammaℂ s * Gammaℂ (s + (k : ℂ) - 1)) *
        LSeries (⇑(rankinBank f)) s := by
  have h1 : 1 < s.re := by linarith
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h1
  have hΛ : (rsAveragedWeakFEPair f hk).Λ s
      = riemannZeta s * mellin (peeledProfile k f) s := by
    rw [peeledProfile_mellin f hk h1]
    field_simp
  rw [rsAveraged_mellin_eq f hk h1, hΛ, sym2_readout_gammaC hk hs,
    LSeries_rankinBank f hk hs]
  ring




/-- The prescribed shift list of the r = 2 rung. -/
noncomputable def sym2Shifts (k : ℤ) : List ℂ := [0, (k : ℂ) - 1]

theorem sym2Shifts_ne (k : ℤ) : sym2Shifts k ≠ [] := by simp [sym2Shifts]

theorem sym2Shifts_pos {k : ℤ} (hk2 : 2 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    ∀ ν ∈ sym2Shifts k, 0 < (s + ν).re := by
  intro ν hν
  simp only [sym2Shifts, List.mem_cons, List.not_mem_nil, or_false] at hν
  rcases hν with rfl | rfl
  · simpa using by linarith
  · simp only [add_re, sub_re, one_re]
    have hkr : ((k : ℂ)).re = (k : ℝ) := by simp
    rw [hkr]
    have h2k : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith

/-- The pair kernel of the r = 2 rung is continuous on the ray. -/
theorem sym2Kernel_continuousOn {k : ℤ} (hk2 : 2 ≤ k) :
    ContinuousOn (conductorScaledCompletionKernelLog 1 (sym2Shifts k)) (Ioi (0 : ℝ)) := by
  have hν : (0 : ℝ) < ((k : ℂ) - 1).re := by
    simp only [sub_re, one_re]
    have h1 : ((k : ℂ)).re = (k : ℝ) := by simp
    rw [h1]
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith
  have hbase := completionKernelLog_pair_continuousOn ((k : ℂ) - 1) hν
  have heq : conductorScaledCompletionKernelLog 1 (sym2Shifts k)
      = completionKernelLog (sym2Shifts k) := by
    funext x
    simp [conductorScaledCompletionKernelLog]
  rw [heq]
  exact hbase

/-- The engine line weight of the r = 2 rung. -/
noncomputable def sym2Sigma (H : HeckeEigenData f) : ℝ :=
  ((4 + rankinExponent H : ℕ) : ℝ) + 3

theorem sym2Sigma_gt (H : HeckeEigenData f) :
    ((Fintype.card (Fin 4) + (rankinSatakePair H).primalExponent : ℕ) : ℝ) + 1
      < sym2Sigma H := by
  show ((4 + rankinExponent H : ℕ) : ℝ) + 1 < ((4 + rankinExponent H : ℕ) : ℝ) + 3
  linarith

theorem sym2Sigma_gt2 (H : HeckeEigenData f) : (2 : ℝ) < sym2Sigma H := by
  unfold sym2Sigma
  have : (0 : ℝ) ≤ ((4 + rankinExponent H : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- **The primal line identity**: on the engine line, the prescribed rank-4 readout's
Mellin transform is the completed Rankin L-series in the Γℂ-pair chart. -/
theorem sym2_primal_line (H : HeckeEigenData f) (hk : 0 ≤ k) (hk2 : 2 ≤ k) (τ : ℝ) :
    mellin (cpsPolynomialFullPrimal3DBankReadout (rankinSatakePair H) 1 (sym2Shifts k))
        ((sym2Sigma H : ℂ) + (τ : ℂ) * Complex.I)
      = Gammaℂ ((sym2Sigma H : ℂ) + (τ : ℂ) * Complex.I) *
          Gammaℂ (((sym2Sigma H : ℂ) + (τ : ℂ) * Complex.I) + (k : ℂ) - 1) *
        LSeries (⇑(rankinBank f))
          ((sym2Sigma H : ℂ) + (τ : ℂ) * Complex.I) := by
  set s : ℂ := (sym2Sigma H : ℂ) + (τ : ℂ) * Complex.I with hsdef
  have hsre : s.re = sym2Sigma H := by
    simp [hsdef]
  have h2 : 2 < s.re := by rw [hsre]; exact sym2Sigma_gt2 H
  have h1 : 1 < s.re := by linarith
  have hνs : ∀ ν ∈ sym2Shifts k, 0 < (s + ν).re := sym2Shifts_pos hk2 h1
  have hσ : ((Fintype.card (Fin 4) + (rankinSatakePair H).primalExponent : ℕ) : ℝ) + 1
      < s.re := by rw [hsre]; exact sym2Sigma_gt H
  rw [cpsPolynomialFullPrimal3D_initialIdentification (rankinSatakePair H) 1 one_pos
    (sym2Shifts k) (sym2Shifts_ne k) s hνs hσ]
  unfold cpsPolynomialFullPrimalCompletedReadout
  have hcoeff : CriticalLinePhasor.CarrierTheta.dirichlet
      (cpsPolynomialPrimalCoeff (rankinSatakePair H)) s
      = LSeries (⇑(rankinBank f)) s := by
    rw [show cpsPolynomialPrimalCoeff (rankinSatakePair H)
        = fun n => rankinBank f (n + 1) from funext (rankinPrimalCoeff_eq H)]
    exact dirichlet_rankinBank f hk h2
  rw [hcoeff]
  simp only [sym2Shifts, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, add_zero, Complex.ofReal_one, Complex.one_cpow, one_mul]
  ring_nf


/-- The reflected dual readout's Mellin transform is the dual theta's. -/
theorem dualReflected_mellin_eq_theta
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μs : List ℂ) (s : ℂ) :
    mellin (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)) s =
      mellin (CriticalLinePhasor.CarrierTheta.theta (cpsPolynomialDualCoeff W)
        (conductorScaledCompletionKernelLog C μs)) s := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [cpsPolynomialFullDual3DTransformedReadout_eq_theta_one_div W C μs
    (one_div_pos.mpr (Set.mem_Ioi.mp hx)), one_div_one_div]

/-- **The dual line identity**: the reflected contragredient readout carries the same
completed Rankin L-series on the engine line — the dual weight multiset is the primal one. -/
theorem sym2_dual_line (H : HeckeEigenData f) (hk : 0 ≤ k) (hk2 : 2 ≤ k) (τ : ℝ) :
    mellin (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout
        (rankinSatakePair H) 1 (sym2Shifts k) (1 / x))
        ((sym2Sigma H : ℂ) + (τ : ℂ) * Complex.I)
      = Gammaℂ ((sym2Sigma H : ℂ) + (τ : ℂ) * Complex.I) *
          Gammaℂ (((sym2Sigma H : ℂ) + (τ : ℂ) * Complex.I) + (k : ℂ) - 1) *
        LSeries (⇑(rankinBank f))
          ((sym2Sigma H : ℂ) + (τ : ℂ) * Complex.I) := by
  set s : ℂ := (sym2Sigma H : ℂ) + (τ : ℂ) * Complex.I with hsdef
  have hsre : s.re = sym2Sigma H := by simp [hsdef]
  have h2 : 2 < s.re := by rw [hsre]; exact sym2Sigma_gt2 H
  have h1 : 1 < s.re := by linarith
  have hνs : ∀ ν ∈ sym2Shifts k, 0 < (s + ν).re := sym2Shifts_pos hk2 h1
  have hσ : ((Fintype.card (Fin 4) + (rankinSatakePair H).dualExponent : ℕ) : ℝ) + 1
      < s.re := by
    rw [hsre]
    show ((4 + rankinExponent H : ℕ) : ℝ) + 1 < ((4 + rankinExponent H : ℕ) : ℝ) + 3
    linarith
  rw [dualReflected_mellin_eq_theta, cpsPolynomialFullDual_initialIdentification
    (rankinSatakePair H) 1 one_pos (sym2Shifts k) (sym2Shifts_ne k) s hνs hσ]
  unfold cpsPolynomialFullDualCompletedReadout
  have hcoeff : CriticalLinePhasor.CarrierTheta.dirichlet
      (cpsPolynomialDualCoeff (rankinSatakePair H)) s
      = LSeries (⇑(rankinBank f)) s := by
    rw [show cpsPolynomialDualCoeff (rankinSatakePair H)
        = fun n => rankinBank f (n + 1) from funext (rankinDualCoeff_eq H)]
    exact dirichlet_rankinBank f hk h2
  rw [hcoeff]
  simp only [sym2Shifts, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, add_zero, Complex.ofReal_one, Complex.one_cpow, one_mul]
  ring_nf


/-- Mellin convergence of the reflected dual readout at the engine weight. -/
theorem sym2_dualReflected_mellinConvergent (H : HeckeEigenData f) (hk2 : 2 ≤ k) :
    MellinConvergent (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout
      (rankinSatakePair H) 1 (sym2Shifts k) (1 / x)) ((sym2Sigma H : ℂ)) := by
  have hνs : ∀ ν ∈ sym2Shifts k, 0 < (((sym2Sigma H : ℂ)) + ν).re := by
    refine sym2Shifts_pos hk2 ?_
    simp only [Complex.ofReal_re]
    linarith [sym2Sigma_gt2 H]
  have hg := conductorScaledCompletionKernelLog_hasMellin 1 one_pos (sym2Shifts k)
    (sym2Shifts_ne k) ((sym2Sigma H : ℂ)) hνs
  have ha : ∀ n : ℕ, ‖cpsPolynomialDualCoeff (rankinSatakePair H) n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card (Fin 4) + (rankinSatakePair H).dualExponent : ℕ) : ℝ)) := by
    intro n
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialDualCoeff_norm_le (rankinSatakePair H) n
  have h := CriticalLinePhasor.CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialDualCoeff (rankinSatakePair H))
    (conductorScaledCompletionKernelLog 1 (sym2Shifts k))
    ((sym2Sigma H : ℂ)) 1
    ((Fintype.card (Fin 4) + (rankinSatakePair H).dualExponent : ℕ) : ℝ)
    hg.1 ha
    (by
      simp only [Complex.ofReal_re]
      show ((4 + rankinExponent H : ℕ) : ℝ) + 1 < sym2Sigma H
      unfold sym2Sigma
      linarith)
  refine h.1.congr_fun ?_ measurableSet_Ioi
  intro x hx
  dsimp only
  rw [cpsPolynomialFullDual3DTransformedReadout_eq_theta_one_div (rankinSatakePair H) 1
    (sym2Shifts k) (one_div_pos.mpr (Set.mem_Ioi.mp hx)), one_div_one_div]

/-- **The r = 2 weak coupling, inhabited**: the prescribed rank-4 Rankin bank coupled to
the (2^k-scaled) averaged lattice profile, with every identification discharged. -/
noncomputable def sym2RankinCoupling (H : HeckeEigenData f) (hk : 0 ≤ k) (hk2 : 2 ≤ k) :
    WeakBankThetaProfileCoupling3D (rankinSatakePair H) 1 (sym2Shifts k) where
  primalProfile := fun t => (2 : ℂ) ^ (k : ℂ) * averagedThetaC k f t
  dualProfile := fun t => (2 : ℂ) ^ (k : ℂ) * averagedThetaC k f t
  primalMass := (2 : ℂ) ^ (k : ℂ) * ((peterssonMass k f : ℝ) : ℂ)
  dualMass := (2 : ℂ) ^ (k : ℂ) * ((peterssonMass k f : ℝ) : ℂ)
  exchangeConstant := 1
  exchangeConstant_ne_zero := one_ne_zero
  weight := 1
  weight_pos := one_pos
  profile_reflection := by
    intro x hx
    show (2 : ℂ) ^ (k : ℂ) * averagedThetaC k f (1 / x) = _
    unfold averagedThetaC
    rw [one_div, averagedTheta_inv f hx, Real.rpow_one]
    push_cast
    ring
  primal_readout := by
    intro x hx
    have hsig1 : (1 : ℝ) < sym2Sigma H := by linarith [sym2Sigma_gt2 H]
    have hsigre : ((sym2Sigma H : ℂ)).re = sym2Sigma H := by simp
    have hνs : ∀ ν ∈ sym2Shifts k, 0 < (((sym2Sigma H : ℂ)) + ν).re :=
      sym2Shifts_pos hk2 (by rw [hsigre]; exact hsig1)
    have hσbound : ((Fintype.card (Fin 4) +
        (rankinSatakePair H).primalExponent : ℕ) : ℝ) + 1 < ((sym2Sigma H : ℂ)).re := by
      rw [hsigre]; exact sym2Sigma_gt H
    have heq := eqOn_pos_of_mellin_eqOn_line
      (f := cpsPolynomialFullPrimal3DBankReadout (rankinSatakePair H) 1 (sym2Shifts k))
      (g := fun t : ℝ => (2 : ℂ) ^ (k : ℂ) •
        (averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ)))
      (σ := sym2Sigma H)
      (cpsPolynomialFullPrimal3DBankReadout_mellinConvergent (rankinSatakePair H) 1
        one_pos (sym2Shifts k) (sym2Shifts_ne k) ((sym2Sigma H : ℂ)) hνs hσbound)
      ((rsAveraged_mellinConvergent f hk (by rw [hsigre]; exact hsig1)).const_smul
        ((2 : ℂ) ^ (k : ℂ)))
      (CriticalLinePhasor.CarrierTheta.mellinPrimal_verticalIntegrable (rankinSatakePair H) 1 one_pos (sym2Shifts k)
        (sym2Shifts_ne k) (sym2Sigma H) hνs (sym2Sigma_gt H))
      (fun τ => by
        rw [sym2_primal_line H hk hk2 τ, mellin_const_smul]
        rw [rankin_readout_gammaC f hk (by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, Complex.ofReal_im]
          ring_nf
          exact sym2Sigma_gt2 H)]
        rw [smul_eq_mul, ← mul_assoc, ← mul_assoc, ← Complex.cpow_add _ _ two_ne_zero]
        simp)
      hx
      (cpsPolynomialFullPrimal3DBankReadout_continuousAt (rankinSatakePair H) 1 one_pos
        (sym2Shifts k) (sym2Kernel_continuousOn hk2) hx)
      (by
        have hc : ContinuousAt (fun t : ℝ =>
            (2 : ℂ) ^ (k : ℂ) * (averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ))) x :=
          continuousAt_const.mul
            ((averagedThetaC_continuousAt f hk hx).sub continuousAt_const)
        exact hc.congr (Filter.Eventually.of_forall fun t => by
          simp only [smul_eq_mul]))
    rw [heq]
    show (2 : ℂ) ^ (k : ℂ) • _ = _
    rw [smul_eq_mul]
    ring
  dual_readout := by
    intro x hx
    have hsig1 : (1 : ℝ) < sym2Sigma H := by linarith [sym2Sigma_gt2 H]
    have hsigre : ((sym2Sigma H : ℂ)).re = sym2Sigma H := by simp
    have hνs : ∀ ν ∈ sym2Shifts k, 0 < (((sym2Sigma H : ℂ)) + ν).re :=
      sym2Shifts_pos hk2 (by rw [hsigre]; exact hsig1)
    have hVprimal := CriticalLinePhasor.CarrierTheta.mellinPrimal_verticalIntegrable (rankinSatakePair H) 1 one_pos
      (sym2Shifts k) (sym2Shifts_ne k) (sym2Sigma H) hνs (sym2Sigma_gt H)
    have hVdual : Complex.VerticalIntegrable
        (mellin (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout
          (rankinSatakePair H) 1 (sym2Shifts k) (1 / x))) (sym2Sigma H) volume := by
      unfold Complex.VerticalIntegrable at hVprimal ⊢
      exact hVprimal.congr (Filter.Eventually.of_forall fun τ => by
        dsimp only
        rw [sym2_primal_line H hk hk2 τ, sym2_dual_line H hk hk2 τ])
    have heq := eqOn_pos_of_mellin_eqOn_line
      (f := fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout
        (rankinSatakePair H) 1 (sym2Shifts k) (1 / x))
      (g := fun t : ℝ => (2 : ℂ) ^ (k : ℂ) •
        (averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ)))
      (σ := sym2Sigma H)
      (sym2_dualReflected_mellinConvergent H hk2)
      ((rsAveraged_mellinConvergent f hk (by rw [hsigre]; exact hsig1)).const_smul
        ((2 : ℂ) ^ (k : ℂ)))
      hVdual
      (fun τ => by
        rw [sym2_dual_line H hk hk2 τ, mellin_const_smul]
        rw [rankin_readout_gammaC f hk (by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, Complex.ofReal_im]
          ring_nf
          exact sym2Sigma_gt2 H)]
        rw [smul_eq_mul, ← mul_assoc, ← mul_assoc, ← Complex.cpow_add _ _ two_ne_zero]
        simp)
      hx
      (cpsPolynomialFullDual3DTransformedReadout_one_div_continuousAt (rankinSatakePair H)
        1 one_pos (sym2Shifts k) (sym2Kernel_continuousOn hk2) hx)
      (by
        have hc : ContinuousAt (fun t : ℝ =>
            (2 : ℂ) ^ (k : ℂ) * (averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ))) x :=
          continuousAt_const.mul
            ((averagedThetaC_continuousAt f hk hx).sub continuousAt_const)
        exact hc.congr (Filter.Eventually.of_forall fun t => by
          simp only [smul_eq_mul]))
    rw [heq]
    show (2 : ℂ) ^ (k : ℂ) • _ = _
    rw [smul_eq_mul]
    ring


/-- **The completed Rankin–Selberg pair of the literal Satake bank.** -/
noncomputable def sym2RankinPair (H : HeckeEigenData f) (hk : 0 ≤ k) (hk2 : 2 ≤ k) :
    WeakFEPair ℂ :=
  (sym2RankinCoupling H hk hk2).toWeakFEPair one_pos (sym2Shifts_ne k)

/-- **The self-dual functional equation**: `Λ(1−s) = Λ(s)`, globally. -/
theorem sym2Rankin_selfdual_FE (H : HeckeEigenData f) (hk : 0 ≤ k) (hk2 : 2 ≤ k)
    (s : ℂ) :
    (sym2RankinPair H hk hk2).Λ (1 - s) = (sym2RankinPair H hk hk2).Λ s := by
  have hsymm : (sym2RankinPair H hk hk2).symm = sym2RankinPair H hk hk2 :=
    weakFEPair_symm_eq_self _ rfl rfl rfl
  have hfe := (sym2RankinPair H hk hk2).functional_equation s
  rw [hsymm, show (sym2RankinPair H hk hk2).ε = 1 from rfl] at hfe
  have hw : ((sym2RankinPair H hk hk2).k : ℂ) = 1 := by
    show (((1 : ℝ) : ℂ)) = 1
    norm_num
  rw [hw] at hfe
  simpa using hfe

/-- **The half-plane identification**: on `2 < Re s` the completed transform is the
Γℂ-pair-completed Rankin L-series of the literal Satake bank. -/
theorem sym2Rankin_lambda_eq (H : HeckeEigenData f) (hk : 0 ≤ k) (hk2 : 2 ≤ k)
    {s : ℂ} (hs : 2 < s.re) :
    (sym2RankinPair H hk hk2).Λ s =
      (2 : ℂ) ^ (k : ℂ) * ((2 : ℂ) ^ (-(k : ℂ)) *
        (Gammaℂ s * Gammaℂ (s + (k : ℂ) - 1)) * LSeries (⇑(rankinBank f)) s) := by
  have h1 : (1 : ℝ) < s.re := by linarith
  have hmell := (sym2RankinPair H hk hk2).hasMellin
    (show (sym2RankinPair H hk hk2).k < s.re from h1)
  rw [← hmell.2]
  have hprofile : (fun t : ℝ => (sym2RankinPair H hk hk2).f t
      - (sym2RankinPair H hk hk2).f₀)
      = fun t : ℝ => (2 : ℂ) ^ (k : ℂ) •
          (averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ)) := by
    funext t
    show (2 : ℂ) ^ (k : ℂ) * averagedThetaC k f t
        - (2 : ℂ) ^ (k : ℂ) * ((peterssonMass k f : ℝ) : ℂ) = _
    rw [smul_eq_mul]
    ring
  rw [hprofile, mellin_const_smul, rankin_readout_gammaC f hk hs, smul_eq_mul]

/-- **The residue at the edge**: `(s−1)·Λ(s) → 2^k·‖f‖²` — the ζ-factor pole of the
Rankin convolution, detected as the profile's constant mode. -/
theorem sym2Rankin_residue (H : HeckeEigenData f) (hk : 0 ≤ k) (hk2 : 2 ≤ k) :
    Filter.Tendsto (fun s : ℂ => (s - 1) * (sym2RankinPair H hk hk2).Λ s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhds ((2 : ℂ) ^ (k : ℂ) * ((peterssonMass k f : ℝ) : ℂ))) := by
  have h := (sym2RankinCoupling H hk hk2).toWeakFEPair_residue one_pos (sym2Shifts_ne k)
  rw [show (sym2RankinCoupling H hk hk2).weight = 1 from rfl,
    show (sym2RankinCoupling H hk hk2).exchangeConstant = 1 from rfl,
    show (sym2RankinCoupling H hk hk2).dualMass
      = (2 : ℂ) ^ (k : ℂ) * ((peterssonMass k f : ℝ) : ℂ) from rfl] at h
  simp only [Complex.ofReal_one, one_smul] at h
  exact h

/-- **The entire part**: the completed transform minus its two poles is entire. -/
theorem sym2Rankin_entire (H : HeckeEigenData f) (hk : 0 ≤ k) (hk2 : 2 ≤ k) :
    Differentiable ℂ (sym2RankinPair H hk hk2).Λ₀ :=
  (sym2RankinCoupling H hk hk2).toWeakFEPair_entire one_pos (sym2Shifts_ne k)

end CriticalLinePhasor.Sym2Rankin

#print axioms CriticalLinePhasor.Sym2Rankin.LSeries_rankinBank
#print axioms CriticalLinePhasor.Sym2Rankin.completionKernelLog_pair_continuousOn
#print axioms CriticalLinePhasor.Sym2Rankin.rankin_readout_gammaC
#print axioms CriticalLinePhasor.Sym2Rankin.sym2_primal_line
#print axioms CriticalLinePhasor.Sym2Rankin.sym2_dual_line
#print axioms CriticalLinePhasor.Sym2Rankin.sym2RankinCoupling
#print axioms CriticalLinePhasor.Sym2Rankin.sym2RankinPair
#print axioms CriticalLinePhasor.Sym2Rankin.sym2Rankin_selfdual_FE
#print axioms CriticalLinePhasor.Sym2Rankin.sym2Rankin_lambda_eq
#print axioms CriticalLinePhasor.Sym2Rankin.sym2Rankin_residue
#print axioms CriticalLinePhasor.Sym2Rankin.sym2Rankin_entire
