import RequestProject.CPSProfileFunctoriality3D

/-!
# Discharging the Mellin-inversion side conditions of the coupling converter

`BankThetaProfileCoupling3D.ofMellinFE` consumes six analytic side conditions.  This file
derives four of them from the compiled polynomial-decay layer, for every prescribed bank whose
completion kernel is continuous on the positive ray:

* primal Mellin convergence at every initial-domain weight
  (`cpsPolynomialFullPrimal3DBankReadout_mellinConvergent` — extracted from the compiled
  kernel-Mellin and polynomial-theta machinery);
* continuity of the primal bank on the positive ray
  (`theta_continuousAt_of_polynomial` — an M-test over the compiled rapid decay — instantiated
  by `cpsPolynomialFullPrimal3DBankReadout_continuousAt`);
* continuity of the reflected contragredient readout
  (`reflectedDualReadout_continuousAt` — the same M-test on the dual bank, composed with the
  chart power and inversion);
* the kernel-continuity input itself for every singleton clock
  (`conductorScaledCompletionKernelLog_singleton_continuousOn` — the `Γ`-clock is continuous).

The refined converter `BankThetaProfileCoupling3D.ofMellinFE'` then consumes exactly the
remaining content: the completed Mellin functional equation, the reflected-side Mellin
convergence, and the two vertical integrabilities — the continuation-across-the-strip data,
which is where the per-rung arithmetic lives.

**Vertical integrabilities discharged (2026-07-21, `CPSCompletedVerticalIntegrable`).**  The two
`VerticalIntegrable` fields are *not* a Mathlib boundary — the house tree already carries the
unconditional two-sided vertical Stirling bound `ZD.StirlingBound.gamma_stirling_bound`
(`|Γ(σ+it)| ≤ C·|t|^{σ−1/2}·e^{−π|t|/2}`).  Along the initial-domain line the compiled
identification displays the bank's Mellin transform as `C^s·∏ⱼ Γ_ℂ(s+μⱼ)·D(s)` with `D` a
bounded Dirichlet series; `gammaC_vline_integrable` turns Stirling into `Γ_ℂ` vertical
integrability and `completedPrimal_verticalIntegrable` assembles the whole readout, so
`mellinPrimal_verticalIntegrable` discharges the primal field and — via
`mellin_reflectedDual_eq_primal` (the FE makes the reflected transform equal the primal one) —
`mellinReflected_verticalIntegrable` discharges the reflected field.  The fully-discharged
converter `BankThetaProfileCoupling3D.ofMellinFE''` therefore consumes exactly the completed
Mellin functional equation plus the reflected-ray Mellin convergence, and nothing about vertical
decay.
-/

open Complex MeasureTheory Set Filter Asymptotics

namespace CriticalLinePhasor.CarrierTheta

/-! ## Pointwise summability and the M-test -/

/-- Polynomial coefficients against a kernel of decay `y^{-(A+2)}` sum absolutely at every
positive height. -/
theorem theta_term_summable_of_polynomial
    (a : ℕ → ℂ) (g : ℝ → ℂ) (C A : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (((n + 1 : ℕ) : ℝ) ^ A))
    (hg : g =O[atTop] (fun y : ℝ => y ^ (-(A + 2))))
    {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => a n * g (((n + 1 : ℕ) : ℝ) * x)) := by
  rw [isBigO_iff'] at hg
  obtain ⟨D, hD, hDb⟩ := hg
  obtain ⟨T₀, hT⟩ := eventually_atTop.1 hDb
  set T : ℝ := max T₀ 1 with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_right _ _
  have hTb : ∀ y : ℝ, T ≤ y → ‖g y‖ ≤ D * y ^ (-(A + 2)) := by
    intro y hy
    have h0y : (0 : ℝ) < y := lt_of_lt_of_le one_pos (hT1.trans hy)
    have := hT y ((le_max_left _ _).trans hy)
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg h0y.le _)] at this
  set N : ℕ := ⌈T / x⌉₊ with hNdef
  have hNx : ∀ n : ℕ, T ≤ ((n + N + 1 : ℕ) : ℝ) * x := by
    intro n
    have h1 : T / x ≤ (N : ℝ) := Nat.le_ceil _
    have h2 : (N : ℝ) ≤ ((n + N + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) n]
    calc T = (T / x) * x := by field_simp
      _ ≤ (N : ℝ) * x := by
          exact mul_le_mul_of_nonneg_right h1 hx.le
      _ ≤ ((n + N + 1 : ℕ) : ℝ) * x := mul_le_mul_of_nonneg_right h2 hx.le
  rw [← summable_nat_add_iff N]
  have hmaj : Summable (fun n : ℕ =>
      (C * D * x ^ (-(A + 2))) * (((n + N + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) := by
    apply Summable.mul_left
    have hbase : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) := by
      have h := Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
      simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h
    exact (summable_nat_add_iff N).2 hbase
  refine Summable.of_norm_bounded hmaj ?_
  intro n
  set m : ℝ := ((n + N + 1 : ℕ) : ℝ) with hmdef
  have hm1 : (1 : ℝ) ≤ m := by
    rw [hmdef]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm1
  have harg : ((n + N) + 1 : ℕ) = (n + N + 1 : ℕ) := rfl
  have hgb : ‖g (m * x)‖ ≤ D * (m * x) ^ (-(A + 2)) := hTb (m * x) (hNx n)
  have hsplit : (m * x) ^ (-(A + 2)) = m ^ (-(A + 2)) * x ^ (-(A + 2)) :=
    Real.mul_rpow hm0.le hx.le
  calc ‖a (n + N) * g (((n + N) + 1 : ℕ) * x)‖
      = ‖a (n + N)‖ * ‖g (m * x)‖ := by rw [norm_mul, harg]
    _ ≤ (C * m ^ A) * (D * (m ^ (-(A + 2)) * x ^ (-(A + 2)))) := by
        rw [← hsplit]
        exact mul_le_mul (by simpa [hmdef, harg] using ha (n + N)) hgb (norm_nonneg _)
          (mul_nonneg hC (Real.rpow_nonneg hm0.le _))
    _ = (C * D * x ^ (-(A + 2))) * (m ^ A * m ^ (-(A + 2))) := by ring
    _ = (C * D * x ^ (-(A + 2))) * m ^ (-2 : ℝ) := by
        rw [← Real.rpow_add hm0]
        norm_num

/-- **The M-test continuity of the coefficient theta**: polynomial coefficients, a kernel
continuous on the positive ray with superpolynomial decay — the theta is continuous at every
positive height. -/
theorem theta_continuousAt_of_polynomial
    (a : ℕ → ℂ) (g : ℝ → ℂ) (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (((n + 1 : ℕ) : ℝ) ^ A))
    (hgc : ContinuousOn g (Ioi 0))
    (hg : g =O[atTop] (fun y : ℝ => y ^ (-(A + 2))))
    {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (theta a g) x₀ := by
  set b : ℝ := x₀ / 2 with hbdef
  have hb : (0 : ℝ) < b := by positivity
  -- decay data
  rw [isBigO_iff'] at hg
  obtain ⟨D, hD, hDb⟩ := hg
  obtain ⟨T₀, hT⟩ := eventually_atTop.1 hDb
  set T : ℝ := max T₀ 1 with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_right _ _
  have hTb : ∀ y : ℝ, T ≤ y → ‖g y‖ ≤ D * y ^ (-(A + 2)) := by
    intro y hy
    have h0y : (0 : ℝ) < y := lt_of_lt_of_le one_pos (hT1.trans hy)
    have := hT y ((le_max_left _ _).trans hy)
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg h0y.le _)] at this
  set N : ℕ := ⌈T / b⌉₊ with hNdef
  have hNy : ∀ (n : ℕ) (y : ℝ), y ∈ Ici b → T ≤ ((n + N + 1 : ℕ) : ℝ) * y := by
    intro n y hy
    have h1 : T / b ≤ (N : ℝ) := Nat.le_ceil _
    have h2 : (N : ℝ) ≤ ((n + N + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) n]
    calc T = (T / b) * b := by field_simp
      _ ≤ (N : ℝ) * b := mul_le_mul_of_nonneg_right h1 hb.le
      _ ≤ ((n + N + 1 : ℕ) : ℝ) * b := mul_le_mul_of_nonneg_right h2 hb.le
      _ ≤ ((n + N + 1 : ℕ) : ℝ) * y := by
          exact mul_le_mul_of_nonneg_left hy (by positivity)
  -- the split representative
  set F : ℝ → ℂ := fun x =>
    (∑ i ∈ Finset.range N, a i * g (((i + 1 : ℕ) : ℝ) * x)) +
      ∑' n : ℕ, a (n + N) * g ((((n + N) + 1 : ℕ) : ℝ) * x) with hFdef
  -- theta agrees with the split on positives
  have hEq : EqOn (theta a g) F (Ici b) := by
    intro x hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hb hx
    have hsum := theta_term_summable_of_polynomial a g C A hC ha
      (isBigO_iff'.mpr ⟨D, hD, eventually_atTop.2 ⟨T, fun y hy => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg
          (lt_of_lt_of_le one_pos (hT1.trans hy)).le _)]
        exact hTb y hy⟩⟩) hxpos
    have hsplit := Summable.sum_add_tsum_nat_add
      (f := fun n : ℕ => a n * g (((n + 1 : ℕ) : ℝ) * x)) N hsum
    rw [hFdef]
    exact hsplit.symm
  -- the finite part is continuous on `Ici b`
  have hMaps : ∀ i : ℕ, MapsTo (fun x : ℝ => ((i + 1 : ℕ) : ℝ) * x) (Ici b) (Ioi 0) := by
    intro i x hx
    have : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    exact mul_pos this (lt_of_lt_of_le hb hx)
  have hfin : ContinuousOn (fun x : ℝ =>
      ∑ i ∈ Finset.range N, a i * g (((i + 1 : ℕ) : ℝ) * x)) (Ici b) := by
    apply continuousOn_finsetSum
    intro i _
    exact continuousOn_const.mul
      (hgc.comp ((continuous_const.mul continuous_id).continuousOn) (hMaps i))
  -- the tail is continuous on `Ici b` by the M-test
  have htail : ContinuousOn (fun x : ℝ =>
      ∑' n : ℕ, a (n + N) * g ((((n + N) + 1 : ℕ) : ℝ) * x)) (Ici b) := by
    refine continuousOn_tsum
      (u := fun n : ℕ =>
        (C * D * b ^ (-(A + 2))) * (((n + N + 1 : ℕ) : ℝ) ^ (-2 : ℝ)))
      (fun n => ?_) ?_ ?_
    · exact continuousOn_const.mul
        (hgc.comp ((continuous_const.mul continuous_id).continuousOn) (hMaps _))
    · exact (Summable.mul_left (C * D * b ^ (-(A + 2)))
        (by
          have hbase : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) := by
            have h := Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
            simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h
          exact (summable_nat_add_iff N).2 hbase))
    · intro n x hx
      have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hb hx
      set m : ℝ := ((n + N + 1 : ℕ) : ℝ) with hmdef
      have hm1 : (1 : ℝ) ≤ m := by
        rw [hmdef]
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
      have hm0 : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm1
      have hgb : ‖g (m * x)‖ ≤ D * (m * x) ^ (-(A + 2)) := hTb (m * x) (hNy n x hx)
      -- base-antitone step through inversion
      have hexp2 : (0 : ℝ) ≤ A + 2 := by linarith
      have hmono : (m * x) ^ (-(A + 2)) ≤ (m * b) ^ (-(A + 2)) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
        have hle : (m * b) ^ (A + 2) ≤ (m * x) ^ (A + 2) :=
          Real.rpow_le_rpow (by positivity)
            (mul_le_mul_of_nonneg_left hx hm0.le) hexp2
        exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) hle
      have hsplit : (m * b) ^ (-(A + 2)) = m ^ (-(A + 2)) * b ^ (-(A + 2)) :=
        Real.mul_rpow hm0.le hb.le
      calc ‖a (n + N) * g ((((n + N) + 1 : ℕ) : ℝ) * x)‖
          = ‖a (n + N)‖ * ‖g (m * x)‖ := by rw [norm_mul]
        _ ≤ (C * m ^ A) * (D * (m * b) ^ (-(A + 2))) := by
            refine mul_le_mul (by simpa [hmdef] using ha (n + N))
              (hgb.trans (by
                exact mul_le_mul_of_nonneg_left hmono hD.le)) (norm_nonneg _)
              (mul_nonneg hC (Real.rpow_nonneg hm0.le _))
        _ = (C * D * b ^ (-(A + 2))) * (m ^ A * m ^ (-(A + 2))) := by
            rw [hsplit]; ring
        _ = (C * D * b ^ (-(A + 2))) * m ^ (-2 : ℝ) := by
            rw [← Real.rpow_add hm0]
            congr 1
            congr 1
            ring
  -- assemble
  have hFcont : ContinuousOn F (Ici b) := hfin.add htail
  have hthetacont : ContinuousOn (theta a g) (Ici b) := hFcont.congr hEq
  refine hthetacont.continuousAt ?_
  refine Filter.mem_of_superset (isOpen_Ioi.mem_nhds ?_) Ioi_subset_Ici_self
  exact Set.mem_Ioi.mpr (by rw [hbdef]; linarith)

end CriticalLinePhasor.CarrierTheta

namespace CriticalLinePhasor.GlobalHelix

open CriticalLinePhasor.CarrierTheta CriticalLinePhasor.ThreeDConverse

/-! ## Discharge at the prescribed banks -/

/-- **Primal Mellin convergence, discharged**: at every initial-domain weight the prescribed
primal bank's Mellin integral converges — extracted from the compiled kernel-Mellin and
polynomial-theta machinery. -/
theorem cpsPolynomialFullPrimal3DBankReadout_mellinConvergent
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hμ : ∀ μ ∈ μs, 0 < (s + μ).re)
    (hs : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re) :
    MellinConvergent (cpsPolynomialFullPrimal3DBankReadout W C μs) s := by
  let A : ℝ := (Fintype.card ι + W.primalExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialPrimalCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialPrimalCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialPrimalCoeff_norm_le W n
  have hg := conductorScaledCompletionKernelLog_hasMellin C hC μs hne s hμ
  have h := CarrierTheta.theta_hasMellin_of_polynomial
    (cpsPolynomialPrimalCoeff W) (conductorScaledCompletionKernelLog C μs)
    s 1 A hg.1 ha (by simpa [A] using hs)
  refine h.1.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only
  rw [cpsPolynomialFullPrimal3DBankReadout_eq_theta W C μs hx]

/-- **Primal-bank continuity, discharged** (kernel continuity supplied): the prescribed primal
bank is continuous at every positive height, by the M-test over the compiled rapid decay. -/
theorem cpsPolynomialFullPrimal3DBankReadout_continuousAt
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ)
    (hgc : ContinuousOn (conductorScaledCompletionKernelLog C μs) (Ioi 0))
    {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (cpsPolynomialFullPrimal3DBankReadout W C μs) x₀ := by
  let A : ℝ := (Fintype.card ι + W.primalExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialPrimalCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialPrimalCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialPrimalCoeff_norm_le W n
  have htheta := CarrierTheta.theta_continuousAt_of_polynomial
    (cpsPolynomialPrimalCoeff W) (conductorScaledCompletionKernelLog C μs)
    1 A one_pos.le (by positivity) ha hgc
    (conductorScaledCompletionKernelLog_rapid C hC μs (-(A + 2))) hx₀
  refine htheta.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hx₀] with x hx
  exact (cpsPolynomialFullPrimal3DBankReadout_eq_theta W C μs hx).symm

/-- **Reflected-readout continuity, discharged**: the chart power times the dual theta at the
inverted height — continuous at every positive height. -/
theorem reflectedDualReadout_continuousAt
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ)
    (hgc : ContinuousOn (conductorScaledCompletionKernelLog C μs) (Ioi 0))
    (k : ℝ) (ε : ℂ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (reflectedTheta k ε (fun x : ℝ =>
      cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x))) x₀ := by
  let A : ℝ := (Fintype.card ι + W.dualExponent : ℕ)
  have ha : ∀ n : ℕ, ‖cpsPolynomialDualCoeff W n‖ ≤
      (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ A) := by
    intro n
    change ‖cpsPolynomialDualCoeff W n‖ ≤
      1 * (((n + 1 : ℕ) : ℝ) ^
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ))
    rw [one_mul, Real.rpow_natCast]
    exact cpsPolynomialDualCoeff_norm_le W n
  -- continuity of the dual theta at `1 / x₀`
  have hdual := CarrierTheta.theta_continuousAt_of_polynomial
    (cpsPolynomialDualCoeff W) (conductorScaledCompletionKernelLog C μs)
    1 A one_pos.le (by positivity) ha hgc
    (conductorScaledCompletionKernelLog_rapid C hC μs (-(A + 2)))
    (one_div_pos.mpr hx₀)
  -- the model function, through multiplication
  have hcpow : ContinuousAt (fun x : ℝ => ((x : ℂ) ^ (-(k : ℂ)))) x₀ :=
    (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hx₀)).comp
      Complex.continuous_ofReal.continuousAt
  have hth : ContinuousAt (fun x : ℝ =>
      CarrierTheta.theta (cpsPolynomialDualCoeff W)
        (conductorScaledCompletionKernelLog C μs) (1 / x)) x₀ :=
    hdual.comp (continuousAt_const.div continuousAt_id hx₀.ne')
  have hmodel : ContinuousAt (fun x : ℝ =>
      ε * (((x : ℂ) ^ (-(k : ℂ))) *
        CarrierTheta.theta (cpsPolynomialDualCoeff W)
          (conductorScaledCompletionKernelLog C μs) (1 / x))) x₀ :=
    continuousAt_const.mul (hcpow.mul hth)
  refine hmodel.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hx₀] with x hx
  unfold CriticalLinePhasor.ThreeDConverse.reflectedTheta
  simp only [smul_eq_mul, one_div_one_div]
  rw [cpsPolynomialFullDual3DTransformedReadout_eq_theta_one_div W C μs hx]

/-- The `Γ`-clock is continuous on the positive ray. -/
theorem gammaClock_continuousOn (μ : ℂ) :
    ContinuousOn (gammaClock μ) (Ioi (0 : ℝ)) := by
  intro x hx
  unfold CriticalLinePhasor.GlobalHelix.gammaClock
  apply ContinuousWithinAt.mul
  · apply ContinuousWithinAt.mul continuousWithinAt_const
    exact ((continuousAt_cpow_const
      (Complex.ofReal_mem_slitPlane.2 hx)).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  · exact (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).continuousAt.continuousWithinAt

/-- The singleton-clock prescribed kernel is continuous on the positive ray: the kernel-continuity
input of the discharge theorems, itself discharged for every single-shift completion. -/
theorem conductorScaledCompletionKernelLog_singleton_continuousOn
    (C : ℝ) (hC : 0 < C) (μ : ℂ) :
    ContinuousOn (conductorScaledCompletionKernelLog C [μ]) (Ioi (0 : ℝ)) := by
  have hmaps : MapsTo (fun x : ℝ => x / C) (Ioi 0) (Ioi 0) := by
    intro x hx
    exact div_pos hx hC
  have hker : ∀ x : ℝ, conductorScaledCompletionKernelLog C [μ] x =
      gammaClock μ (x / C) := by
    intro x
    rfl
  refine ContinuousOn.congr ?_ fun x _ => hker x
  exact (gammaClock_continuousOn μ).comp
    ((continuous_id.div_const C).continuousOn) hmaps

/-! ## The refined converter -/

/-- **The converter with its derivable side conditions discharged.**  Given kernel continuity
(automatic for singleton clocks) and an initial-domain weight, the primal Mellin convergence and
both continuity conditions are supplied by the theorems above.  What remains is exactly the
continuation content: the completed Mellin functional equation between the literal banks, the
reflected-side Mellin convergence, and the two vertical integrabilities — the per-rung
arithmetic, and nothing else. -/
noncomputable def BankThetaProfileCoupling3D.ofMellinFE'
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ [])
    (hgc : ContinuousOn (conductorScaledCompletionKernelLog C μs) (Ioi 0))
    (k σ : ℝ) (ε : ℂ) (hε : ε ≠ 0) (hk : 0 < k)
    (hσμ : ∀ μ ∈ μs, 0 < ((σ : ℂ) + μ).re)
    (hσ : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < σ)
    (hFE : ∀ s : ℂ,
      mellin (cpsPolynomialFullPrimal3DBankReadout W C μs) ((k : ℂ) - s) =
        ε • mellin (fun x : ℝ =>
          cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)) s)
    (hrefConv : MellinConvergent
      (reflectedTheta k ε (fun x : ℝ =>
        cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x))) (σ : ℂ))
    (hfVert : VerticalIntegrable
      (mellin (cpsPolynomialFullPrimal3DBankReadout W C μs)) σ volume)
    (hrefVert : VerticalIntegrable
      (mellin (reflectedTheta k ε (fun x : ℝ =>
        cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)))) σ volume) :
    BankThetaProfileCoupling3D W C μs :=
  BankThetaProfileCoupling3D.ofMellinFE W C μs k σ ε hε hk hFE
    (cpsPolynomialFullPrimal3DBankReadout_mellinConvergent W C hC μs hne (σ : ℂ)
      hσμ (by simpa using hσ))
    hrefConv hfVert hrefVert
    (fun x hx => cpsPolynomialFullPrimal3DBankReadout_continuousAt W C hC μs hgc hx)
    (fun x hx => reflectedDualReadout_continuousAt W C hC μs hgc k ε hx)

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.CarrierTheta.theta_term_summable_of_polynomial
#print axioms CriticalLinePhasor.CarrierTheta.theta_continuousAt_of_polynomial
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullPrimal3DBankReadout_mellinConvergent
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialFullPrimal3DBankReadout_continuousAt
#print axioms CriticalLinePhasor.GlobalHelix.reflectedDualReadout_continuousAt
#print axioms CriticalLinePhasor.GlobalHelix.gammaClock_continuousOn
#print axioms CriticalLinePhasor.GlobalHelix.conductorScaledCompletionKernelLog_singleton_continuousOn
#print axioms CriticalLinePhasor.GlobalHelix.BankThetaProfileCoupling3D.ofMellinFE'
