import RequestProject.RealChainCompletion

/-!
# The coefficient-level mechanism and the ramified (level-`N`) bank

The mechanism family (`mechanism`/`mechanismR`/`mechanismG`/`mechanismRR`) consumes a
`PolynomialSatakeDualPair` — a **fixed** finite channel index at every prime.  A
level-`N` object has rank-varying local factors: at a ramified place the local Euler
factor has smaller degree (the inertia-invariant Frobenius weights), at a fully
ramified place degree zero.  This file states the mechanism at its true generality —
the polynomially-bounded coefficient surface — and feeds it the rank-varying bank:

* `CoefficientSurface` — primal/contragredient coefficient sequences with one
  polynomial bound; the exact surface every chart engine consumes;
* `MellinKernel` — a chart kernel packaged with its multiplier, admissibility bar,
  Mellin identity, and rapid decay; `realChainMellinKernel` and
  `generalMellinKernel` instantiate it from the compiled kernel families
  (pure-`Γℝ` chain and `∏Γℝ·∏Γℂ`), so every admissible chart is covered;
* `mechanismK` — **the mechanism, coefficient-level and kernel-generic**: one theta
  identity of the prescribed readouts yields the complete package (`KNicePackage`:
  entire continuation, functional equation, chart identification).  The four fixed-rank
  mechanisms are instances of this statement;
* `RamifiedWeightFamily` — **the level-`N` surface**: a per-prime rank profile
  `rank p` capped by `D`, nonzero local weights with one polynomial bound each way —
  the "ramified degenerate clocks" register of `GeneralSeed`;
* `ramifiedGlobalCoeff` / `ramifiedGlobalCoeff_norm_le` — the all-place bank of a
  rank-varying family and its polynomial bound `(n+1)^(D+B)`: the cap enters only
  through `multichoose (rank p) ≤ (k+1)^D`;
* `ramifiedDual_eq_primal` — self-duality via **per-place** channel permutations
  (each place may reverse its own clock — ramified places included);
* `ramified_package_of_theta` — **the mechanism on any self-dual rank-varying bank
  at every admissible chart**: level-`N` is not a separate obstruction, matching the
  compiled reflection register (`dualPairFiniteProduct_FE`, whose per-place index is
  already arbitrary) and the executed rank-one exchange (`chiRungC`, every
  conductor `q`);
* `RamifiedWeightFamily.ofSeed` / `ofSeed_coeff_eq` — the constant-rank family of any
  seed recovers the compiled unramified `Sym^r` bank coefficients on the nose;
* `RamifiedWeightFamily.unitRamified` / `unitRamified_selfdual` — non-vacuity with
  genuine rank drop: the unit family with rank `0` at `p ∣ N` and rank `1` elsewhere —
  the principal-character bank, the simplest level-`N` object.

No `axiom`, no `sorry`.
-/

open Real Complex Finset Set Filter Topology MeasureTheory Asymptotics
open scoped BigOperators

namespace CriticalLinePhasor.RamifiedMechanism

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.TransportClosure
open CriticalLinePhasor.ThetaMechanism CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GenuineGL2Carrier
open CriticalLinePhasor.RealChainMechanism

/-! ## The coefficient surface and the chart-kernel interface -/

/-- **The coefficient surface**: primal and contragredient all-place coefficient
sequences with one polynomial bound.  This is the exact surface the chart engines
consume; every `PolynomialSatakeDualPair` produces one, and so does every
rank-varying family below. -/
structure CoefficientSurface where
  a : ℕ → ℂ
  adual : ℕ → ℂ
  A : ℕ
  a_bound : ∀ n : ℕ, ‖a n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ A
  adual_bound : ∀ n : ℕ, ‖adual n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ A

/-- **A chart kernel with its multiplier**: the kernel, its chart multiplier `G`, an
admissibility bar `B0`, the Mellin identity beyond the bar, and rapid decay.  The
compiled kernel families instantiate this below. -/
structure MellinKernel where
  K : ℝ → ℂ
  G : ℂ → ℂ
  B0 : ℝ
  hK : ∀ s : ℂ, B0 < s.re → MellinConvergent K s ∧ mellin K s = G s
  hrapid : ∀ q : ℝ, K =O[atTop] fun x : ℝ => x ^ q

/-- The pure-`Γℝ` chain kernel as a chart kernel: multiplier
`∏_{e ∈ d::ds} Γℝ(s+e)`, bar `0` for nonnegative shifts. -/
noncomputable def realChainMellinKernel (d : ℂ) (hd : 0 ≤ d.re) (ds : List ℂ)
    (hds : ∀ e ∈ ds, 0 ≤ e.re) : MellinKernel where
  K := realChainKernelLog d ds
  G := fun s => ((d :: ds).map fun e => Complex.Gammaℝ (s + e)).prod
  B0 := 0
  hK := fun s hs =>
    realChainKernelLog_hasMellin d ds s
      (by simp only [Complex.add_re]; linarith)
      (fun e he => by
        have := hds e he
        simp only [Complex.add_re]
        linarith)
  hrapid := realChainKernelLog_rapid d ds

/-- The general Deligne kernel as a chart kernel: multiplier
`∏Γℝ(s+δ)·∏Γℂ(s+μ)`, bar `0` for nonnegative shifts. -/
noncomputable def generalMellinKernel (dlts : List ℂ) (hdlts : ∀ dlt ∈ dlts, 0 ≤ dlt.re)
    (μs : List ℂ) (hne : μs ≠ []) (hμ : ∀ μ ∈ μs, 0 ≤ μ.re) : MellinKernel where
  K := generalKernelLog dlts μs
  G := fun s => (dlts.map fun dlt => Complex.Gammaℝ (s + dlt)).prod *
    (μs.map fun μ => Complex.Gammaℂ (s + μ)).prod
  B0 := 0
  hK := fun s hs =>
    generalKernelLog_hasMellin dlts μs hne s
      (fun dlt hmem => by
        have := hdlts dlt hmem
        simp only [Complex.add_re]
        linarith)
      (fun μ hmem => by
        have := hμ μ hmem
        simp only [Complex.add_re]
        linarith)
  hrapid := generalKernelLog_rapid dlts μs hne

/-! ## The 3D readouts at coefficient level -/

/-- The primal 3D bank of a coefficient sequence carrying an arbitrary kernel. -/
noncomputable def coeffPrimal3DBankReadout (a : ℕ → ℂ) (K : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor (coefficientFiber a n x) *
      K (multiplicativeHeight (coefficientFiber a n x))

/-- The reciprocal-height contragredient 3D bank. -/
noncomputable def coeffDual3DTransformedReadout (adual : ℕ → ℂ) (K : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor
        (reciprocalCoefficientFiber (fun j => (starRingEnd ℂ) (adual j)) n x) *
      K (multiplicativeHeight
          (reciprocalCoefficientFiber (fun j => (starRingEnd ℂ) (adual j)) n x))

theorem coeffPrimal3DBankReadout_eq_theta (a : ℕ → ℂ) (K : ℝ → ℂ) {x : ℝ}
    (hx : 0 < x) :
    coeffPrimal3DBankReadout a K x =
      CriticalLinePhasor.CarrierTheta.theta a K x := by
  unfold coeffPrimal3DBankReadout CriticalLinePhasor.CarrierTheta.theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_coefficientFiber, multiplicativeHeight_coefficientFiber a n hx]

theorem coeffDual3DTransformedReadout_eq_theta_one_div (adual : ℕ → ℂ) (K : ℝ → ℂ)
    {x : ℝ} (hx : 0 < x) :
    coeffDual3DTransformedReadout adual K x =
      CriticalLinePhasor.CarrierTheta.theta adual K (1 / x) := by
  unfold coeffDual3DTransformedReadout CriticalLinePhasor.CarrierTheta.theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_reciprocalCoefficientFiber_conj,
    multiplicativeHeight_reciprocalCoefficientFiber _ n hx]
  simp [div_eq_mul_inv]

theorem coeffPrimalTheta_locallyIntegrableOn (P : CoefficientSurface) (κ : MellinKernel) :
    MeasureTheory.LocallyIntegrableOn
      (CriticalLinePhasor.CarrierTheta.theta P.a κ.K) (Set.Ioi 0) := by
  set σ : ℝ := max κ.B0 ((P.A : ℝ) + 1) + 1 with hσdef
  have hσB0 : κ.B0 < σ := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hσA : (P.A : ℝ) + 1 < σ := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have ha : ∀ n : ℕ, ‖P.a n‖ ≤ (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ ((P.A : ℝ))) := by
    intro n
    rw [one_mul, Real.rpow_natCast]
    exact P.a_bound n
  have hg := κ.hK (σ : ℂ) (by simp only [Complex.ofReal_re]; exact hσB0)
  have htheta := CriticalLinePhasor.CarrierTheta.theta_hasMellin_of_polynomial
    P.a κ.K (σ : ℂ) 1 (P.A : ℝ) hg.1 ha
      (by simp only [Complex.ofReal_re]; exact hσA)
  exact CriticalLinePhasor.CarrierTheta.locallyIntegrableOn_of_mellinConvergent _ _ htheta.1

theorem coeffDualTheta_locallyIntegrableOn (P : CoefficientSurface) (κ : MellinKernel) :
    MeasureTheory.LocallyIntegrableOn
      (CriticalLinePhasor.CarrierTheta.theta P.adual κ.K) (Set.Ioi 0) := by
  set σ : ℝ := max κ.B0 ((P.A : ℝ) + 1) + 1 with hσdef
  have hσB0 : κ.B0 < σ := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hσA : (P.A : ℝ) + 1 < σ := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have ha : ∀ n : ℕ, ‖P.adual n‖ ≤ (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ ((P.A : ℝ))) := by
    intro n
    rw [one_mul, Real.rpow_natCast]
    exact P.adual_bound n
  have hg := κ.hK (σ : ℂ) (by simp only [Complex.ofReal_re]; exact hσB0)
  have htheta := CriticalLinePhasor.CarrierTheta.theta_hasMellin_of_polynomial
    P.adual κ.K (σ : ℂ) 1 (P.A : ℝ) hg.1 ha
      (by simp only [Complex.ofReal_re]; exact hσA)
  exact CriticalLinePhasor.CarrierTheta.locallyIntegrableOn_of_mellinConvergent _ _ htheta.1

theorem coeffPrimal3DBankReadout_locallyIntegrableOn (P : CoefficientSurface)
    (κ : MellinKernel) :
    MeasureTheory.LocallyIntegrableOn (coeffPrimal3DBankReadout P.a κ.K) (Set.Ioi 0) := by
  apply MeasureTheory.LocallyIntegrableOn.congr _
    (coeffPrimalTheta_locallyIntegrableOn P κ)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  exact (coeffPrimal3DBankReadout_eq_theta P.a κ.K hx).symm

theorem coeffDual3DReflectedReadout_locallyIntegrableOn (P : CoefficientSurface)
    (κ : MellinKernel) :
    MeasureTheory.LocallyIntegrableOn
      (fun x : ℝ => coeffDual3DTransformedReadout P.adual κ.K (1 / x)) (Set.Ioi 0) := by
  apply MeasureTheory.LocallyIntegrableOn.congr _
    (coeffDualTheta_locallyIntegrableOn P κ)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := Set.mem_Ioi.mp hx
  rw [coeffDual3DTransformedReadout_eq_theta_one_div P.adual κ.K
    (one_div_pos.mpr hxpos)]
  simp

theorem coeffPrimal3DBankReadout_rapid (P : CoefficientSurface) (κ : MellinKernel) :
    ∀ q : ℝ, coeffPrimal3DBankReadout P.a κ.K =O[atTop] (fun x : ℝ => x ^ q) := by
  have ha : ∀ n : ℕ, ‖P.a n‖ ≤ (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ ((P.A : ℝ))) := by
    intro n
    rw [one_mul, Real.rpow_natCast]
    exact P.a_bound n
  have htheta := CriticalLinePhasor.CarrierTheta.theta_rapid_of_polynomial_of_kernel_rapid
    P.a κ.K 1 (P.A : ℝ) zero_le_one ha κ.hrapid
  intro q
  have heq :
      CriticalLinePhasor.CarrierTheta.theta P.a κ.K =ᶠ[atTop]
        coeffPrimal3DBankReadout P.a κ.K := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (coeffPrimal3DBankReadout_eq_theta P.a κ.K hx).symm
  simpa using (htheta q).congr' heq Filter.EventuallyEq.rfl

theorem coeffDual3DReflectedReadout_rapid (P : CoefficientSurface) (κ : MellinKernel) :
    ∀ q : ℝ,
      (fun x : ℝ => coeffDual3DTransformedReadout P.adual κ.K (1 / x))
        =O[atTop] (fun x : ℝ => x ^ q) := by
  have ha : ∀ n : ℕ, ‖P.adual n‖ ≤ (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ ((P.A : ℝ))) := by
    intro n
    rw [one_mul, Real.rpow_natCast]
    exact P.adual_bound n
  have htheta := CriticalLinePhasor.CarrierTheta.theta_rapid_of_polynomial_of_kernel_rapid
    P.adual κ.K 1 (P.A : ℝ) zero_le_one ha κ.hrapid
  intro q
  have heq :
      CriticalLinePhasor.CarrierTheta.theta P.adual κ.K =ᶠ[atTop]
        (fun x : ℝ => coeffDual3DTransformedReadout P.adual κ.K (1 / x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [coeffDual3DTransformedReadout_eq_theta_one_div P.adual κ.K (one_div_pos.mpr hx)]
    simp
  simpa using (htheta q).congr' heq Filter.EventuallyEq.rfl

theorem coeffPrimal3D_initialIdentification (P : CoefficientSurface) (κ : MellinKernel)
    (s : ℂ) (hB0 : κ.B0 < s.re) (hA : (P.A : ℝ) + 1 < s.re) :
    mellin (coeffPrimal3DBankReadout P.a κ.K) s =
      κ.G s * CriticalLinePhasor.CarrierTheta.dirichlet P.a s := by
  have heq : mellin (coeffPrimal3DBankReadout P.a κ.K) s =
      mellin (CriticalLinePhasor.CarrierTheta.theta P.a κ.K) s := by
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [coeffPrimal3DBankReadout_eq_theta P.a κ.K (Set.mem_Ioi.mp hx)]
  rw [heq]
  have ha : ∀ n : ℕ, ‖P.a n‖ ≤ (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ ((P.A : ℝ))) := by
    intro n
    rw [one_mul, Real.rpow_natCast]
    exact P.a_bound n
  have hg := κ.hK s hB0
  have h := CriticalLinePhasor.CarrierTheta.theta_hasMellin_of_polynomial
    P.a κ.K s 1 (P.A : ℝ) hg.1 ha hA
  rw [h.2, hg.2]
  ring

theorem coeffDual3D_initialIdentification (P : CoefficientSurface) (κ : MellinKernel)
    (s : ℂ) (hB0 : κ.B0 < s.re) (hA : (P.A : ℝ) + 1 < s.re) :
    mellin (fun x : ℝ => coeffDual3DTransformedReadout P.adual κ.K (1 / x)) s =
      κ.G s * CriticalLinePhasor.CarrierTheta.dirichlet P.adual s := by
  have heq : mellin (fun x : ℝ => coeffDual3DTransformedReadout P.adual κ.K (1 / x)) s =
      mellin (CriticalLinePhasor.CarrierTheta.theta P.adual κ.K) s := by
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := Set.mem_Ioi.mp hx
    dsimp only
    rw [coeffDual3DTransformedReadout_eq_theta_one_div P.adual κ.K
      (one_div_pos.mpr hxpos)]
    simp
  rw [heq]
  have ha : ∀ n : ℕ, ‖P.adual n‖ ≤ (1 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ ((P.A : ℝ))) := by
    intro n
    rw [one_mul, Real.rpow_natCast]
    exact P.adual_bound n
  have hg := κ.hK s hB0
  have h := CriticalLinePhasor.CarrierTheta.theta_hasMellin_of_polynomial
    P.adual κ.K s 1 (P.A : ℝ) hg.1 ha hA
  rw [h.2, hg.2]
  ring

/-- Summability of the shifted coefficient bank beyond `A + 1`. -/
theorem coeffArithmetic_summable (P : CoefficientSurface) {s : ℂ}
    (hs : (P.A : ℝ) + 1 < s.re) :
    LSeriesSummable (⇑(coefficientArithmetic P.a)) s := by
  refine LSeriesSummable_of_le_const_mul_rpow (x := (P.A : ℝ) + 1) hs ⟨1, fun m hm => ?_⟩
  have hnorm : ‖(coefficientArithmetic P.a) m‖ ≤ (1 : ℝ) * (m : ℝ) ^ (P.A : ℕ) := by
    rcases m with - | k
    · simp [coefficientArithmetic]
    · have := P.a_bound k
      calc ‖(coefficientArithmetic P.a) (k + 1)‖ = ‖P.a k‖ := by
            simp [coefficientArithmetic]
        _ ≤ ((k + 1 : ℕ) : ℝ) ^ (P.A : ℕ) := this
        _ = 1 * ((k + 1 : ℕ) : ℝ) ^ (P.A : ℕ) := (one_mul _).symm
  calc ‖(coefficientArithmetic P.a) m‖
      ≤ (1 : ℝ) * (m : ℝ) ^ (P.A : ℕ) := hnorm
    _ ≤ 1 * (m : ℝ) ^ (((P.A : ℝ) + 1) - 1) := by
        rw [one_mul, one_mul, add_sub_cancel_right, Real.rpow_natCast]

/-! ## The mechanism, coefficient-level and kernel-generic -/

/-- The typed conclusion: entire continuation, functional equation, and the chart
identification against the kernel's multiplier. -/
structure KNicePackage (a : ArithmeticFunction ℂ) (G : ℂ → ℂ) (B : ℝ) (ε : ℂ) where
  lam : ℂ → ℂ
  entire : Differentiable ℂ lam
  FE : ∀ s : ℂ, lam (1 - s) = ε * lam s
  chart : ∀ s : ℂ, B < s.re → lam s = G s * LSeries (⇑a) s

/-- Uniqueness of the continuation. -/
theorem KNicePackage.unique {a : ArithmeticFunction ℂ} {G : ℂ → ℂ} {B : ℝ} {ε ε' : ℂ}
    (P : KNicePackage a G B ε) (Q : KNicePackage a G B ε') : P.lam = Q.lam := by
  refine CriticalLinePhasor.CarrierTargetIdentification.entire_eq_of_eqOn_isOpen
    P.entire Q.entire
    (U := {s : ℂ | B < s.re})
    (IsOpen.preimage Complex.continuous_re isOpen_Ioi)
    (z₀ := ((B + 1 : ℝ) : ℂ))
    (by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
    ?_
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  rw [P.chart s hs, Q.chart s hs]

/-- **THE MECHANISM, COEFFICIENT-LEVEL AND KERNEL-GENERIC** — one theta identity of
the prescribed readouts of any polynomially-bounded self-dual coefficient surface, at
any packaged chart kernel, yields the complete analytic package.  The four fixed-rank
mechanisms are instances; the rank-varying (level-`N`) banks below feed it directly. -/
noncomputable def mechanismK (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n) (κ : MellinKernel)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      coeffPrimal3DBankReadout P.a κ.K (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          coeffDual3DTransformedReadout P.adual κ.K (1 / x)) :
    KNicePackage (coefficientArithmetic P.a) κ.G (max κ.B0 ((P.A : ℝ) + 1)) ε := by
  refine
    let pair : StrongFEPair ℂ :=
      { f := coeffPrimal3DBankReadout P.a κ.K
        g := fun x : ℝ => coeffDual3DTransformedReadout P.adual κ.K (1 / x)
        k := 1
        ε := ε
        f₀ := 0
        g₀ := 0
        hf_int := coeffPrimal3DBankReadout_locallyIntegrableOn P κ
        hg_int := coeffDual3DReflectedReadout_locallyIntegrableOn P κ
        hk := one_pos
        hε := hε
        h_feq := fun x hx => hrefl x hx
        hf_top := fun q => by
          simpa using coeffPrimal3DBankReadout_rapid P κ q
        hg_top := fun q => by
          simpa using coeffDual3DReflectedReadout_rapid P κ q
        hf₀ := rfl
        hg₀ := rfl }
    ?_
  have hconds : ∀ s : ℂ, max κ.B0 ((P.A : ℝ) + 1) < s.re →
      κ.B0 < s.re ∧ (P.A : ℝ) + 1 < s.re := fun s hs =>
    ⟨lt_of_le_of_lt (le_max_left _ _) hs, lt_of_le_of_lt (le_max_right _ _) hs⟩
  have hsymm : pair.symm.Λ = pair.Λ := by
    refine CriticalLinePhasor.CarrierTargetIdentification.entire_eq_of_eqOn_isOpen
      pair.symm.differentiable_Λ pair.differentiable_Λ
      (U := {s : ℂ | max κ.B0 ((P.A : ℝ) + 1) < s.re})
      (IsOpen.preimage Complex.continuous_re isOpen_Ioi)
      (z₀ := ((max κ.B0 ((P.A : ℝ) + 1) + 1 : ℝ) : ℂ))
      (by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
      ?_
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    obtain ⟨hc1, hc2⟩ := hconds s hs
    have hid1 := coeffPrimal3D_initialIdentification P κ s hc1 hc2
    have hid2 := coeffDual3D_initialIdentification P κ s hc1 hc2
    have hdualdir : CriticalLinePhasor.CarrierTheta.dirichlet P.adual s
        = CriticalLinePhasor.CarrierTheta.dirichlet P.a s := by
      unfold CriticalLinePhasor.CarrierTheta.dirichlet
      exact tsum_congr fun m => by rw [hdual m]
    refine (hid2.trans ?_).trans hid1.symm
    rw [hdualdir]
  exact
    { lam := pair.Λ
      entire := pair.differentiable_Λ
      FE := by
        intro s
        have h := pair.functional_equation s
        rw [hsymm] at h
        rw [show ((pair.k : ℝ) : ℂ) = 1 from by norm_num] at h
        simpa using h
      chart := by
        intro s hs
        obtain ⟨hc1, hc2⟩ := hconds s hs
        have hid := coeffPrimal3D_initialIdentification P κ s hc1 hc2
        refine hid.trans ?_
        have hcoeff : P.a = fun j => (coefficientArithmetic P.a) (j + 1) := by
          funext j
          simp [coefficientArithmetic]
        conv_lhs => rw [hcoeff]
        rw [dirichlet_shift_eq_LSeries _ (coeffArithmetic_summable P hc2)] }

/-! ## The rank-varying bank: level-`N` -/

/-- **The level-`N` surface**: a per-prime rank profile capped by `D`, nonzero local
weights with one polynomial bound each way.  At a ramified place the rank drops —
the inertia-invariant Frobenius weights; at a fully ramified place it is `0`. -/
structure RamifiedWeightFamily where
  rank : Nat.Primes → ℕ
  w : (p : Nat.Primes) → Fin (rank p) → ℂ
  w_ne_zero : ∀ (p : Nat.Primes) (i : Fin (rank p)), w p i ≠ 0
  D : ℕ
  rank_le : ∀ p : Nat.Primes, rank p ≤ D
  B : ℕ
  w_bound : ∀ (p : Nat.Primes) (i : Fin (rank p)), ‖w p i‖ ≤ (p.1 : ℝ) ^ B
  w_inv_bound : ∀ (p : Nat.Primes) (i : Fin (rank p)), ‖(w p i)⁻¹‖ ≤ (p.1 : ℝ) ^ B

/-- The all-place coefficient bank of a rank-varying weight family. -/
noncomputable def ramifiedGlobalCoeff (rank : Nat.Primes → ℕ)
    (w : (p : Nat.Primes) → Fin (rank p) → ℂ) (n : ℕ) : ℂ :=
  ∏ p : ↑(n + 1).primeFactors,
    radialLocalEulerCoeff
      (w (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
      ((n + 1).factorization p.1)

/-- **The polynomial bound of the rank-varying bank**: the rank cap `D` replaces the
fixed channel count — the only place variability enters is
`multichoose (rank p) k ≤ (k+1)^D`. -/
theorem ramifiedGlobalCoeff_norm_le (rank : Nat.Primes → ℕ)
    (w : (p : Nat.Primes) → Fin (rank p) → ℂ) (D B : ℕ)
    (hD : ∀ p : Nat.Primes, rank p ≤ D)
    (hw : ∀ (p : Nat.Primes) (i : Fin (rank p)), ‖w p i‖ ≤ (p.1 : ℝ) ^ B) (n : ℕ) :
    ‖ramifiedGlobalCoeff rank w n‖ ≤ (((n + 1 : ℕ) : ℝ) ^ (D + B : ℕ)) := by
  classical
  let m : ℕ := n + 1
  have hm : m ≠ 0 := by
    dsimp [m]
    omega
  have hlocal : ∀ p : ↑m.primeFactors,
      ‖radialLocalEulerCoeff
        (w (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
        (m.factorization p.1)‖ ≤
        (((m.factorization p.1 + 1) ^ D : ℕ) : ℝ) *
          (p.1 : ℝ) ^ (B * m.factorization p.1) := by
    intro p
    let pp : Nat.Primes := ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩
    have hraw := norm_radialLocalEulerCoeff_le_multichoose_mul_pow
      (w pp) ((p.1 : ℝ) ^ B) (by positivity) (hw pp) (m.factorization p.1)
    have hcap : (Fintype.card (Fin (rank pp))).multichoose (m.factorization p.1)
        ≤ (m.factorization p.1 + 1) ^ D := by
      rw [Fintype.card_fin]
      calc (rank pp).multichoose (m.factorization p.1)
          ≤ (m.factorization p.1 + 1) ^ rank pp :=
            multichoose_le_add_one_pow (rank pp) (m.factorization p.1)
        _ ≤ (m.factorization p.1 + 1) ^ D :=
            Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (hD pp)
    calc
      ‖radialLocalEulerCoeff (w pp) (m.factorization p.1)‖
          ≤ (((Fintype.card (Fin (rank pp))).multichoose (m.factorization p.1) : ℕ) : ℝ) *
              ((p.1 : ℝ) ^ B) ^ (m.factorization p.1) := hraw
      _ ≤ (((m.factorization p.1 + 1) ^ D : ℕ) : ℝ) *
              ((p.1 : ℝ) ^ B) ^ (m.factorization p.1) := by
            gcongr
      _ = (((m.factorization p.1 + 1) ^ D : ℕ) : ℝ) *
              (p.1 : ℝ) ^ (B * m.factorization p.1) := by rw [pow_mul]
  change ‖∏ p : ↑m.primeFactors, _‖ ≤ (m : ℝ) ^ (D + B)
  rw [norm_prod]
  calc
    ∏ p : ↑m.primeFactors,
        ‖radialLocalEulerCoeff
          (w (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
          (m.factorization p.1)‖
        ≤ ∏ p : ↑m.primeFactors,
          ((((m.factorization p.1 + 1) ^ D : ℕ) : ℝ) *
            (p.1 : ℝ) ^ (B * m.factorization p.1)) := by
          exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p _ => hlocal p)
    _ = (∏ p : ↑m.primeFactors,
          (((m.factorization p.1 + 1) ^ D : ℕ) : ℝ)) *
        (∏ p : ↑m.primeFactors,
          (p.1 : ℝ) ^ (B * m.factorization p.1)) := by rw [Finset.prod_mul_distrib]
    _ = (((m.divisors.card : ℕ) : ℝ) ^ D) * (m : ℝ) ^ B := by
      congr 1
      · simp_rw [Nat.cast_pow]
        rw [show (∏ p : ↑m.primeFactors,
              ((m.factorization p.1 + 1 : ℕ) : ℝ) ^ D) =
            (∏ p : ↑m.primeFactors,
              ((m.factorization p.1 + 1 : ℕ) : ℝ)) ^ D by
              simpa using Finset.prod_pow
                (Finset.univ : Finset ↑m.primeFactors) D
                (fun p => ((m.factorization p.1 + 1 : ℕ) : ℝ))]
        congr 1
        have hnat :
            (∏ p : ↑m.primeFactors, (m.factorization p.1 + 1)) =
              m.divisors.card := by
          rw [Finset.prod_coe_sort
            m.primeFactors (fun p : ℕ => m.factorization p + 1)]
          exact (Nat.card_divisors hm).symm
        exact_mod_cast hnat
      · have hpow : ∀ p : ↑m.primeFactors,
            (p.1 : ℝ) ^ (B * m.factorization p.1) =
              ((p.1 : ℝ) ^ m.factorization p.1) ^ B := by
          intro p
          rw [mul_comm]
          exact pow_mul _ _ _
        simp_rw [hpow]
        rw [show (∏ p : ↑m.primeFactors,
              ((p.1 : ℝ) ^ m.factorization p.1) ^ B) =
            (∏ p : ↑m.primeFactors,
              (p.1 : ℝ) ^ m.factorization p.1) ^ B by
              simpa using Finset.prod_pow
                (Finset.univ : Finset ↑m.primeFactors) B
                (fun p => (p.1 : ℝ) ^ m.factorization p.1)]
        have hmprod := Nat.prod_primeFactors_coe_pow_factorization hm
        congr 1
        exact_mod_cast hmprod.symm
    _ ≤ (m : ℝ) ^ D * (m : ℝ) ^ B := by
      gcongr
      exact_mod_cast Nat.card_divisors_le_self m
    _ = (m : ℝ) ^ (D + B) := by rw [pow_add]

/-- **Self-duality via per-place channel permutations** — each place may reverse its
own clock, ramified places included. -/
theorem ramifiedDual_eq_primal (rank : Nat.Primes → ℕ)
    (w : (p : Nat.Primes) → Fin (rank p) → ℂ)
    (σ : ∀ p : Nat.Primes, Equiv.Perm (Fin (rank p)))
    (hσ : ∀ (p : Nat.Primes) (i : Fin (rank p)), (w p i)⁻¹ = w p (σ p i)) (n : ℕ) :
    ramifiedGlobalCoeff rank (fun p i => (w p i)⁻¹) n
      = ramifiedGlobalCoeff rank w n := by
  unfold ramifiedGlobalCoeff
  refine Finset.prod_congr rfl fun p _ => ?_
  exact Eq.trans
    (congrArg (fun f => radialLocalEulerCoeff f ((n + 1).factorization p.1))
      (funext fun i => hσ (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes) i))
    (radialLocalEulerCoeff_comp_equiv
      (σ (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
      (w (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
      ((n + 1).factorization p.1))

/-- The coefficient surface of a rank-varying family. -/
noncomputable def RamifiedWeightFamily.surface (R : RamifiedWeightFamily) :
    CoefficientSurface where
  a := ramifiedGlobalCoeff R.rank R.w
  adual := ramifiedGlobalCoeff R.rank (fun p i => (R.w p i)⁻¹)
  A := R.D + R.B
  a_bound := ramifiedGlobalCoeff_norm_le R.rank R.w R.D R.B R.rank_le R.w_bound
  adual_bound := ramifiedGlobalCoeff_norm_le R.rank _ R.D R.B R.rank_le R.w_inv_bound

/-- **The mechanism on any self-dual rank-varying bank at every packaged chart** —
level-`N` fed to the engine: one theta identity yields the complete package. -/
noncomputable def ramified_package_of_theta (R : RamifiedWeightFamily)
    (σ : ∀ p : Nat.Primes, Equiv.Perm (Fin (R.rank p)))
    (hσ : ∀ (p : Nat.Primes) (i : Fin (R.rank p)), (R.w p i)⁻¹ = R.w p (σ p i))
    (κ : MellinKernel) (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      coeffPrimal3DBankReadout (ramifiedGlobalCoeff R.rank R.w) κ.K (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          coeffDual3DTransformedReadout
            (ramifiedGlobalCoeff R.rank (fun p i => (R.w p i)⁻¹)) κ.K (1 / x)) :
    KNicePackage (coefficientArithmetic (ramifiedGlobalCoeff R.rank R.w)) κ.G
      (max κ.B0 (((R.D + R.B : ℕ) : ℝ) + 1)) ε :=
  mechanismK R.surface (ramifiedDual_eq_primal R.rank R.w σ hσ) κ ε hε hrefl

/-! ## Witnesses: the unramified bank recovered, and genuine rank drop -/

/-- The constant-rank family of any seed: the unramified `Sym^r` bank. -/
noncomputable def RamifiedWeightFamily.ofSeed (S : SatakeSeed) (r : ℕ) :
    RamifiedWeightFamily where
  rank := fun _ => r + 1
  w := fun p i => symClockWeight r (S.satake p) (i : ℕ)
  w_ne_zero := fun p _ => zpow_ne_zero _ (S.satake_ne_zero p)
  D := r + 1
  rank_le := fun _ => le_rfl
  B := S.E * r
  w_bound := fun p i => symClockWeightOf_norm_bound S r p i
  w_inv_bound := fun p i => symClockWeightOf_inv_norm_bound S r p i

/-- **Recognition**: the constant-rank family's bank is the compiled unramified
`Sym^r` transport bank, on the nose. -/
theorem ofSeed_coeff_eq (S : SatakeSeed) (r : ℕ) (n : ℕ) :
    ramifiedGlobalCoeff (RamifiedWeightFamily.ofSeed S r).rank
      (RamifiedWeightFamily.ofSeed S r).w n
      = cpsPolynomialPrimalCoeff (symrSatakePairOf S r) n := rfl

/-- **Genuine rank drop**: the unit family with rank `0` at `p ∣ N` and rank `1`
elsewhere — the principal-character bank, the simplest level-`N` object.  At a fully
ramified place the local factor is the empty product `1`. -/
noncomputable def RamifiedWeightFamily.unitRamified (N : ℕ) : RamifiedWeightFamily where
  rank := fun p => if p.1 ∣ N then 0 else 1
  w := fun _ _ => 1
  w_ne_zero := fun _ _ => one_ne_zero
  D := 1
  rank_le := fun p => by
    by_cases h : p.1 ∣ N <;> simp [h]
  B := 0
  w_bound := fun _ _ => by simp
  w_inv_bound := fun _ _ => by simp

/-- The rank-dropping unit family is self-dual by the identity permutation. -/
theorem unitRamified_selfdual (N : ℕ) (p : Nat.Primes)
    (i : Fin ((RamifiedWeightFamily.unitRamified N).rank p)) :
    ((RamifiedWeightFamily.unitRamified N).w p i)⁻¹
      = (RamifiedWeightFamily.unitRamified N).w p ((Equiv.refl _) i) :=
  inv_one

end CriticalLinePhasor.RamifiedMechanism

#print axioms CriticalLinePhasor.RamifiedMechanism.realChainMellinKernel
#print axioms CriticalLinePhasor.RamifiedMechanism.generalMellinKernel
#print axioms CriticalLinePhasor.RamifiedMechanism.mechanismK
#print axioms CriticalLinePhasor.RamifiedMechanism.ramifiedGlobalCoeff_norm_le
#print axioms CriticalLinePhasor.RamifiedMechanism.ramifiedDual_eq_primal
#print axioms CriticalLinePhasor.RamifiedMechanism.ramified_package_of_theta
#print axioms CriticalLinePhasor.RamifiedMechanism.ofSeed_coeff_eq
#print axioms CriticalLinePhasor.RamifiedMechanism.unitRamified_selfdual
