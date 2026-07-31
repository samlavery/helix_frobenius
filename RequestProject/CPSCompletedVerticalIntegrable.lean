import RequestProject.CPSGammaVerticalIntegrable
import RequestProject.CPSMellinFEDischarge

/-!
# Vertical-line integrability of the prescribed completed readout — the `VerticalIntegrable`
discharge

On the initial-domain vertical line `Re s = σ > A+1`, the compiled identification
(`cpsPolynomialFullCompletion3D_identification`) displays the primal bank's Mellin transform as
the completed readout `C^s · ∏ⱼ Γ_ℂ(s+μⱼ) · D(s)`, with `D` an absolutely convergent Dirichlet
series (uniformly bounded on the line) and at least one Γ_ℂ factor supplying the vertical
Stirling decay (`CPSGammaVerticalIntegrable`).  Bounded × exponentially-decaying × bounded is
integrable, so the completed readout — hence `mellin` of the bank — is `VerticalIntegrable`.

This **discharges** the primal `VerticalIntegrable` side condition of the coupling converter from
the house Stirling bound; it is not a Mathlib boundary.

* `dirichlet_vline_continuous`, `dirichlet_vline_isBigO_one` — Weierstrass M-test for the
  Dirichlet factor on the line of absolute convergence.
* `completedPrimal_vline_integrable` — the completed readout is integrable along the line.
-/

open Complex Filter Topology Asymptotics MeasureTheory Real
open CriticalLinePhasor.GammaVertical

namespace CriticalLinePhasor.CarrierTheta

/-! ## The Dirichlet factor: Weierstrass M-test on the line of absolute convergence -/

/-- The comparison series `Σ (n+1)^{A-σ}` converges for `σ > A+1`. -/
theorem dirichlet_comparison_summable (A σ : ℝ) (hσ : A + 1 < σ) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (A - σ)) := by
  have hlt : A - σ < -1 := by linarith
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (A - σ)) :=
    (Real.summable_nat_rpow (p := A - σ)).mpr hlt
  exact (summable_nat_add_iff 1).mpr hbase

/-- The per-term norm bound for the Dirichlet series on the vertical line `Re s = σ`. -/
theorem dirichlet_term_norm_bound (a : ℕ → ℂ) (A σ : ℝ)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ A) (n : ℕ) (y : ℝ) :
    ‖a n * ((n + 1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))‖ ≤
      ((n + 1 : ℕ) : ℝ) ^ (A - σ) := by
  rw [norm_mul]
  have hpos : 0 < n + 1 := Nat.succ_pos n
  rw [Complex.norm_natCast_cpow_of_pos hpos]
  have hre : (-((σ : ℂ) + (y : ℂ) * Complex.I)).re = -σ := by
    simp
  rw [hre]
  have hbase : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  calc ‖a n‖ * ((n + 1 : ℕ) : ℝ) ^ (-σ)
      ≤ ((n + 1 : ℕ) : ℝ) ^ A * ((n + 1 : ℕ) : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right (ha n) (Real.rpow_nonneg hbase.le _)
    _ = ((n + 1 : ℕ) : ℝ) ^ (A - σ) := by
        rw [sub_eq_add_neg, Real.rpow_add hbase]

/-- **Continuity of the Dirichlet factor on the line.**  M-test over the summable comparison
series. -/
theorem dirichlet_vline_continuous (a : ℕ → ℂ) (A σ : ℝ)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ A) (hσ : A + 1 < σ) :
    Continuous (fun y : ℝ => dirichlet a ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
  have hcont : ∀ n : ℕ, Continuous
      (fun y : ℝ => a n * ((n + 1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))) := by
    intro n
    have hbase : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    apply continuous_const.mul
    apply Continuous.const_cpow _ (Or.inl hbase)
    fun_prop
  have := continuous_tsum hcont (dirichlet_comparison_summable A σ hσ)
    (fun n y => dirichlet_term_norm_bound a A σ ha n y)
  simpa [dirichlet] using this

/-- **The Dirichlet factor is `O(1)` (uniformly bounded) on the line** — at any filter. -/
theorem dirichlet_vline_isBigO_one {l : Filter ℝ} (a : ℕ → ℂ) (A σ : ℝ)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ A) (hσ : A + 1 < σ) :
    (fun y : ℝ => dirichlet a ((σ : ℂ) + (y : ℂ) * Complex.I)) =O[l]
      fun _ : ℝ => (1 : ℝ) := by
  have hsum := dirichlet_comparison_summable A σ hσ
  set B : ℝ := ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (A - σ) with hB
  rw [isBigO_iff]
  refine ⟨B, Filter.Eventually.of_forall fun y => ?_⟩
  have hterm : Summable fun n : ℕ =>
      ‖a n * ((n + 1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))‖ := by
    apply hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
    exact fun n => dirichlet_term_norm_bound a A σ ha n y
  have hle : ‖dirichlet a ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ B := by
    unfold dirichlet
    calc ‖∑' n : ℕ, a n * ((n + 1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))‖
        ≤ ∑' n : ℕ, ‖a n * ((n + 1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))‖ :=
          norm_tsum_le_tsum_norm hterm
      _ ≤ B := hterm.tsum_le_tsum
          (fun n => dirichlet_term_norm_bound a A σ ha n y) hsum
  simpa using hle

/-! ## Exponential factors are `O(1)` at the far end -/

theorem exp_neg_isBigO_one_atTop {b : ℝ} (hb : 0 ≤ b) :
    (fun y : ℝ => Real.exp (-b * y)) =O[atTop] fun _ : ℝ => (1 : ℝ) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop 0] with y hy
  simp only [norm_one, mul_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-b * y) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hb hy])
    _ = 1 := Real.exp_zero

theorem exp_isBigO_one_atBot {b : ℝ} (hb : 0 ≤ b) :
    (fun y : ℝ => Real.exp (b * y)) =O[atBot] fun _ : ℝ => (1 : ℝ) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_le_atBot 0] with y hy
  simp only [norm_one, mul_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (b * y) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (mul_nonpos_iff.mpr (Or.inl ⟨hb, hy⟩))
    _ = 1 := Real.exp_zero

/-! ## The Γ-product factor -/

/-- The single-factor function in `vline` form, so the Γ_ℂ lemmas apply directly. -/
private theorem gammaFactor_eq (σ : ℝ) (μ : ℂ) :
    (fun y : ℝ => Complex.Gammaℂ ((σ : ℂ) + (y : ℂ) * Complex.I + μ))
      = fun y : ℝ => Complex.Gammaℂ (vline ((σ : ℂ) + μ) y) := by
  funext y; rw [vline_baseAdd]

theorem gammaProd_vline_continuous (μs : List ℂ) (σ : ℝ)
    (hμs : ∀ μ ∈ μs, 0 < ((σ : ℂ) + μ).re) :
    Continuous (fun y : ℝ =>
      (μs.map fun μ => Complex.Gammaℂ ((σ : ℂ) + (y : ℂ) * Complex.I + μ)).prod) := by
  induction μs with
  | nil => simpa using continuous_const
  | cons μ rest ih =>
      have hμ : 0 < ((σ : ℂ) + μ).re := hμs μ (List.mem_cons_self)
      have hrest : ∀ ν ∈ rest, 0 < ((σ : ℂ) + ν).re :=
        fun ν hν => hμs ν (List.mem_cons_of_mem _ hν)
      have h1 : Continuous (fun y : ℝ => Complex.Gammaℂ ((σ : ℂ) + (y : ℂ) * Complex.I + μ)) := by
        rw [gammaFactor_eq]; exact gammaC_vline_continuous (w := (σ : ℂ) + μ) hμ
      simp only [List.map_cons, List.prod_cons]
      exact h1.mul (ih hrest)

theorem gammaProd_vline_isBigO_one_atTop (μs : List ℂ) (σ : ℝ)
    (hμs : ∀ μ ∈ μs, 0 < ((σ : ℂ) + μ).re) :
    (fun y : ℝ => (μs.map fun μ => Complex.Gammaℂ ((σ : ℂ) + (y : ℂ) * Complex.I + μ)).prod)
      =O[atTop] fun _ : ℝ => (1 : ℝ) := by
  induction μs with
  | nil => simpa using isBigO_const_const (1 : ℂ) (c' := (1:ℝ)) one_ne_zero (atTop : Filter ℝ)
  | cons μ rest ih =>
      have hμ : 0 < ((σ : ℂ) + μ).re := hμs μ (List.mem_cons_self)
      have hrest : ∀ ν ∈ rest, 0 < ((σ : ℂ) + ν).re :=
        fun ν hν => hμs ν (List.mem_cons_of_mem _ hν)
      have hg : (fun y : ℝ => Complex.Gammaℂ ((σ : ℂ) + (y : ℂ) * Complex.I + μ))
          =O[atTop] fun y => Real.exp (-(Real.pi / 4) * y) := by
        rw [gammaFactor_eq]; exact gammaC_vline_isBigO_atTop hμ
      have hhead := hg.trans (exp_neg_isBigO_one_atTop (by positivity))
      simpa only [List.map_cons, List.prod_cons, mul_one] using hhead.mul (ih hrest)

theorem gammaProd_vline_isBigO_one_atBot (μs : List ℂ) (σ : ℝ)
    (hμs : ∀ μ ∈ μs, 0 < ((σ : ℂ) + μ).re) :
    (fun y : ℝ => (μs.map fun μ => Complex.Gammaℂ ((σ : ℂ) + (y : ℂ) * Complex.I + μ)).prod)
      =O[atBot] fun _ : ℝ => (1 : ℝ) := by
  induction μs with
  | nil => simpa using isBigO_const_const (1 : ℂ) (c' := (1:ℝ)) one_ne_zero (atBot : Filter ℝ)
  | cons μ rest ih =>
      have hμ : 0 < ((σ : ℂ) + μ).re := hμs μ (List.mem_cons_self)
      have hrest : ∀ ν ∈ rest, 0 < ((σ : ℂ) + ν).re :=
        fun ν hν => hμs ν (List.mem_cons_of_mem _ hν)
      have hg : (fun y : ℝ => Complex.Gammaℂ ((σ : ℂ) + (y : ℂ) * Complex.I + μ))
          =O[atBot] fun y => Real.exp (Real.pi / 4 * y) := by
        rw [gammaFactor_eq]; exact gammaC_vline_isBigO_atBot hμ
      have hhead := hg.trans (exp_isBigO_one_atBot (by positivity))
      simpa only [List.map_cons, List.prod_cons, mul_one] using hhead.mul (ih hrest)

theorem gammaProd_vline_isBigO_exp_atTop (μs : List ℂ) (hne : μs ≠ []) (σ : ℝ)
    (hμs : ∀ μ ∈ μs, 0 < ((σ : ℂ) + μ).re) :
    (fun y : ℝ => (μs.map fun μ => Complex.Gammaℂ ((σ : ℂ) + (y : ℂ) * Complex.I + μ)).prod)
      =O[atTop] fun y => Real.exp (-(Real.pi / 4) * y) := by
  obtain ⟨μ, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hμ : 0 < ((σ : ℂ) + μ).re := hμs μ (List.mem_cons_self)
  have hrest : ∀ ν ∈ rest, 0 < ((σ : ℂ) + ν).re :=
    fun ν hν => hμs ν (List.mem_cons_of_mem _ hν)
  have hhead : (fun y : ℝ => Complex.Gammaℂ ((σ : ℂ) + (y : ℂ) * Complex.I + μ))
      =O[atTop] fun y => Real.exp (-(Real.pi / 4) * y) := by
    rw [gammaFactor_eq]; exact gammaC_vline_isBigO_atTop hμ
  simpa only [List.map_cons, List.prod_cons, mul_one] using
    hhead.mul (gammaProd_vline_isBigO_one_atTop rest σ hrest)

theorem gammaProd_vline_isBigO_exp_atBot (μs : List ℂ) (hne : μs ≠ []) (σ : ℝ)
    (hμs : ∀ μ ∈ μs, 0 < ((σ : ℂ) + μ).re) :
    (fun y : ℝ => (μs.map fun μ => Complex.Gammaℂ ((σ : ℂ) + (y : ℂ) * Complex.I + μ)).prod)
      =O[atBot] fun y => Real.exp (Real.pi / 4 * y) := by
  obtain ⟨μ, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hμ : 0 < ((σ : ℂ) + μ).re := hμs μ (List.mem_cons_self)
  have hrest : ∀ ν ∈ rest, 0 < ((σ : ℂ) + ν).re :=
    fun ν hν => hμs ν (List.mem_cons_of_mem _ hν)
  have hhead : (fun y : ℝ => Complex.Gammaℂ ((σ : ℂ) + (y : ℂ) * Complex.I + μ))
      =O[atBot] fun y => Real.exp (Real.pi / 4 * y) := by
    rw [gammaFactor_eq]; exact gammaC_vline_isBigO_atBot hμ
  simpa only [List.map_cons, List.prod_cons, mul_one] using
    hhead.mul (gammaProd_vline_isBigO_one_atBot rest σ hrest)

/-! ## The conductor factor -/

theorem cpow_vline_continuous (C : ℝ) (hC : 0 < C) (σ : ℝ) :
    Continuous (fun y : ℝ => (C : ℂ) ^ ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
  have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hC
  apply Continuous.const_cpow _ (Or.inl hCne)
  fun_prop

theorem cpow_vline_isBigO_one {l : Filter ℝ} (C : ℝ) (hC : 0 < C) (σ : ℝ) :
    (fun y : ℝ => (C : ℂ) ^ ((σ : ℂ) + (y : ℂ) * Complex.I)) =O[l] fun _ : ℝ => (1 : ℝ) := by
  rw [isBigO_iff]
  refine ⟨C ^ σ, Filter.Eventually.of_forall fun y => ?_⟩
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hC]
  have hre : ((σ : ℂ) + (y : ℂ) * Complex.I).re = σ := by simp
  rw [hre]
  simp

/-! ## The completed readout: continuity and vertical integrability -/

open CriticalLinePhasor.GlobalHelix

/-- The primal coefficient bound, cast to `rpow` form for the M-test. -/
private theorem primalCoeff_rpow_bound {ι : Type*} [Fintype ι]
    (W : PolynomialSatakeDualPair ι) (n : ℕ) :
    ‖cpsPolynomialPrimalCoeff W n‖ ≤
      ((n + 1 : ℕ) : ℝ) ^ ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  exact cpsPolynomialPrimalCoeff_norm_le W n

/-- **Continuity of the prescribed completed readout along the initial-domain vertical line.** -/
theorem completedPrimal_vline_continuous {ι : Type*} [Fintype ι]
    (W : PolynomialSatakeDualPair ι) (C : ℝ) (hC : 0 < C) (μs : List ℂ) (σ : ℝ)
    (hσμ : ∀ μ ∈ μs, 0 < ((σ : ℂ) + μ).re)
    (hσ : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < σ) :
    Continuous (fun y : ℝ =>
      cpsPolynomialFullPrimalCompletedReadout W C μs ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
  unfold cpsPolynomialFullPrimalCompletedReadout
  exact ((cpow_vline_continuous C hC σ).mul (gammaProd_vline_continuous μs σ hσμ)).mul
    (dirichlet_vline_continuous (cpsPolynomialPrimalCoeff W) _ σ
      (primalCoeff_rpow_bound W) hσ)

/-- **The prescribed completed readout is `VerticalIntegrable` on the initial-domain line.**
Bounded conductor factor × exponentially-decaying Γ-product × bounded Dirichlet series, integrated
against the two-sided Stirling decay. -/
theorem completedPrimal_verticalIntegrable {ι : Type*} [Fintype ι]
    (W : PolynomialSatakeDualPair ι) (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ [])
    (σ : ℝ) (hσμ : ∀ μ ∈ μs, 0 < ((σ : ℂ) + μ).re)
    (hσ : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < σ) :
    Complex.VerticalIntegrable
      (cpsPolynomialFullPrimalCompletedReadout W C μs) σ volume := by
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hcont := completedPrimal_vline_continuous W C hC μs σ hσμ hσ
  have hOtop : (fun y : ℝ =>
      cpsPolynomialFullPrimalCompletedReadout W C μs ((σ : ℂ) + (y : ℂ) * Complex.I))
      =O[atTop] fun y => Real.exp (-(Real.pi / 4) * y) := by
    unfold cpsPolynomialFullPrimalCompletedReadout
    have h := ((cpow_vline_isBigO_one (l := atTop) C hC σ).mul
      (gammaProd_vline_isBigO_exp_atTop μs hne σ hσμ)).mul
      (dirichlet_vline_isBigO_one (l := atTop) (cpsPolynomialPrimalCoeff W) _ σ
        (primalCoeff_rpow_bound W) hσ)
    simpa using h
  have hObot : (fun y : ℝ =>
      cpsPolynomialFullPrimalCompletedReadout W C μs ((σ : ℂ) + (y : ℂ) * Complex.I))
      =O[atBot] fun y => Real.exp (Real.pi / 4 * y) := by
    unfold cpsPolynomialFullPrimalCompletedReadout
    have h := ((cpow_vline_isBigO_one (l := atBot) C hC σ).mul
      (gammaProd_vline_isBigO_exp_atBot μs hne σ hσμ)).mul
      (dirichlet_vline_isBigO_one (l := atBot) (cpsPolynomialPrimalCoeff W) _ σ
        (primalCoeff_rpow_bound W) hσ)
    simpa using h
  -- assemble into Integrable via the two-sided dominators
  have hbot : IntegrableAtFilter (fun y : ℝ => Real.exp (Real.pi / 4 * y)) atBot volume := by
    refine ⟨Set.Iio 0, Iio_mem_atBot 0, ?_⟩
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' (Set.Iio 0) = Set.Ioi 0 := by ext y; simp
    have hfun : (fun y : ℝ => Real.exp (Real.pi / 4 * y)) ∘ (Neg.neg : ℝ → ℝ)
        = fun y : ℝ => Real.exp (-(Real.pi / 4) * y) := by
      funext y; simp only [Function.comp_apply]; ring_nf
    refine ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      measurableEmbedding_neg (f := fun y : ℝ => Real.exp (Real.pi / 4 * y))
      (s := Set.Iio 0)).mp ?_
    rw [hpre, hfun]
    exact exp_neg_integrableOn_Ioi 0 hpi4
  have htop : IntegrableAtFilter (fun y : ℝ => Real.exp (-(Real.pi / 4) * y)) atTop volume :=
    ⟨Set.Ioi 0, Ioi_mem_atTop 0, exp_neg_integrableOn_Ioi 0 hpi4⟩
  exact hcont.locallyIntegrable.integrable_of_isBigO_atBot_atTop hObot hbot hOtop htop

/-! ## Transport to the bank Mellin transform, and the reflected side via the FE -/

open CriticalLinePhasor.ThreeDConverse

/-- **The primal bank's Mellin transform is `VerticalIntegrable` on the initial-domain line.**
Transport of `completedPrimal_verticalIntegrable` through the compiled identification (whose
hypotheses depend only on `Re s = σ`, hence hold along the whole line). -/
theorem mellinPrimal_verticalIntegrable {ι : Type*} [Fintype ι]
    (W : PolynomialSatakeDualPair ι) (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ [])
    (σ : ℝ) (hσμ : ∀ μ ∈ μs, 0 < ((σ : ℂ) + μ).re)
    (hσ : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < σ) :
    Complex.VerticalIntegrable
      (mellin (cpsPolynomialFullPrimal3DBankReadout W C μs)) σ volume := by
  have hcompleted := completedPrimal_verticalIntegrable W C hC μs hne σ hσμ hσ
  unfold Complex.VerticalIntegrable at hcompleted ⊢
  refine hcompleted.congr (Filter.Eventually.of_forall fun y => ?_)
  have hμ : ∀ μ ∈ μs, 0 < (((σ : ℂ) + (y : ℂ) * Complex.I) + μ).re := by
    intro μ hmem
    have hre : (((σ : ℂ) + (y : ℂ) * Complex.I) + μ).re = ((σ : ℂ) + μ).re := by simp
    rw [hre]; exact hσμ μ hmem
  have hs : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 <
      ((σ : ℂ) + (y : ℂ) * Complex.I).re := by
    rw [show ((σ : ℂ) + (y : ℂ) * Complex.I).re = σ from by simp]; exact hσ
  exact (cpsPolynomialFullPrimal3D_initialIdentification W C hC μs hne _ hμ hs).symm

/-- **The reflected contragredient Mellin transform equals the primal one under the FE.**  By
`mellin_reflectedTheta` the reflected transform at `w` is `ε · mellin g (k−w)`, which the
completed Mellin functional equation identifies with `mellin(primal) w`. -/
theorem mellin_reflectedDual_eq_primal {ι : Type*} [Fintype ι]
    (W : PolynomialSatakeDualPair ι) (C : ℝ) (μs : List ℂ) (k : ℝ) (ε : ℂ)
    (hFE : ∀ s : ℂ,
      mellin (cpsPolynomialFullPrimal3DBankReadout W C μs) ((k : ℂ) - s) =
        ε • mellin (fun x : ℝ =>
          cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)) s) :
    mellin (reflectedTheta k ε (fun x : ℝ =>
        cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)))
      = mellin (cpsPolynomialFullPrimal3DBankReadout W C μs) := by
  funext w
  have hrefl := mellin_reflectedTheta k ε
    (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)) ((k : ℂ) - w)
  rw [show (k : ℂ) - ((k : ℂ) - w) = w from by ring] at hrefl
  have hfe := hFE ((k : ℂ) - w)
  rw [show (k : ℂ) - ((k : ℂ) - w) = w from by ring] at hfe
  rw [hrefl, hfe]

/-- **The reflected side is `VerticalIntegrable`** — equal to the primal side under the FE. -/
theorem mellinReflected_verticalIntegrable {ι : Type*} [Fintype ι]
    (W : PolynomialSatakeDualPair ι) (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ [])
    (σ : ℝ) (hσμ : ∀ μ ∈ μs, 0 < ((σ : ℂ) + μ).re)
    (hσ : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < σ) (k : ℝ) (ε : ℂ)
    (hFE : ∀ s : ℂ,
      mellin (cpsPolynomialFullPrimal3DBankReadout W C μs) ((k : ℂ) - s) =
        ε • mellin (fun x : ℝ =>
          cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)) s) :
    Complex.VerticalIntegrable
      (mellin (reflectedTheta k ε (fun x : ℝ =>
        cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)))) σ volume := by
  rw [mellin_reflectedDual_eq_primal W C μs k ε hFE]
  exact mellinPrimal_verticalIntegrable W C hC μs hne σ hσμ hσ

end CriticalLinePhasor.CarrierTheta

/-! ## The fully-discharged converter -/

namespace CriticalLinePhasor.GlobalHelix

open CriticalLinePhasor.ThreeDConverse CriticalLinePhasor.CarrierTheta MeasureTheory

/-- **The coupling converter with both vertical integrabilities discharged.**  Given the completed
Mellin functional equation, the reflected-side Mellin convergence, and the initial-domain scope
data, the theta-profile coupling is constructed — the two `VerticalIntegrable` fields of
`ofMellinFE'` are supplied from the house Stirling bound (`mellinPrimal_verticalIntegrable`) and
the FE-induced primal/reflected Mellin equality (`mellinReflected_verticalIntegrable`).  The
per-rung obligation is thereby exactly the completed Mellin FE plus the reflected ray
convergence — nothing about vertical decay. -/
noncomputable def BankThetaProfileCoupling3D.ofMellinFE''
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ [])
    (hgc : ContinuousOn (conductorScaledCompletionKernelLog C μs) (Set.Ioi 0))
    (k σ : ℝ) (ε : ℂ) (hε : ε ≠ 0) (hk : 0 < k)
    (hσμ : ∀ μ ∈ μs, 0 < ((σ : ℂ) + μ).re)
    (hσ : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < σ)
    (hFE : ∀ s : ℂ,
      mellin (cpsPolynomialFullPrimal3DBankReadout W C μs) ((k : ℂ) - s) =
        ε • mellin (fun x : ℝ =>
          cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)) s)
    (hrefConv : MellinConvergent
      (reflectedTheta k ε (fun x : ℝ =>
        cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x))) (σ : ℂ)) :
    BankThetaProfileCoupling3D W C μs :=
  BankThetaProfileCoupling3D.ofMellinFE' W C hC μs hne hgc k σ ε hε hk hσμ hσ hFE hrefConv
    (mellinPrimal_verticalIntegrable W C hC μs hne σ hσμ hσ)
    (mellinReflected_verticalIntegrable W C hC μs hne σ hσμ hσ k ε hFE)

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.CarrierTheta.dirichlet_vline_continuous
#print axioms CriticalLinePhasor.CarrierTheta.completedPrimal_verticalIntegrable
#print axioms CriticalLinePhasor.CarrierTheta.mellinPrimal_verticalIntegrable
#print axioms CriticalLinePhasor.CarrierTheta.mellinReflected_verticalIntegrable
#print axioms CriticalLinePhasor.GlobalHelix.BankThetaProfileCoupling3D.ofMellinFE''
