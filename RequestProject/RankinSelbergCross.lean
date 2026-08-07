import RequestProject.Sym2RankinCoupling

/-!
# The general Rankin–Selberg pair by polarization: rung 6

The convolution `L(f×g, s)` for an arbitrary pair of level-one cusp forms of one weight,
constructed and proven **by polarization**: the sesquilinear cross object is the
combination `¼[(f+g) − (f−g) + i(f+ig) − i(f−ig)]` of four *diagonal* objects, and the
entire compiled single-form Rankin–Selberg engine — the averaged lattice pair, its
reflection from the theta transformation law, its saddle decay, its Γ-chart landing —
applies to each of the four verbatim.  No new analytic machinery; the diagonal engine
was built once and the cross case is algebra.

* `polarization` — the sesquilinear polarization identity over `ℂ`;
* `polForm₁ … polForm₄` / `cross_coeff_polarization` — the four forms and the coefficient
  law, through the compiled `q`-expansion linearity;
* `crossProfileC` / `crossMass` / `crossPair` — the cross profile, the polarized Petersson
  pairing, and the Mathlib `WeakFEPair` with every field inherited from the four compiled
  diagonal pairs;
* `cross_selfdual_FE` / `cross_residue` / `cross_entire` — the global functional equation
  `Λ(1−s) = Λ(s)`, the residue `⟨f,g⟩`-polarized at the edge, the entire part;
* `mconv_add`/`mconv_sub`/`mellin_add'`/`mellin_sub'` — Mellin linearity;
* `cross_mellin_split` / `LSeries_crossRankinBank` / `cross_lambda_eq` — **the chart
  identification**: on `2 < Re s` the cross transform is
  `2^{−k}·Γℂ(s)Γℂ(s+k−1)·L(crossRankinBank, s)`;
* `rankinBank_eq_sqIndicator_mul` / `crossSquare` / `crossSquare_apply` /
  `crossRankinBank_eq_sq` — **the coefficient identification**: the cross bank is the
  square-indicator dressing of the literal cross Hecke data
  `a_f(n)·conj(a_g(n))/n^{k−1}`;
* `rankin_selberg_rung` — **rung 6, one theorem**: functional equation, polar structure,
  entire part, chart, and coefficients, simultaneously, for every pair.

At `f = g` the cross object recovers the landed r = 2 chain — the diagonal of this rung
is `sym2_rankin_rung`'s pair.  No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane MeasureTheory
open scoped MatrixGroups Real ComplexConjugate

namespace CriticalLinePhasor.RankinSelbergCross

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.Sym2Wire
open CriticalLinePhasor.Sym2Rankin CriticalLinePhasor.Sym2Join CriticalLinePhasor.Unfolding
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

variable {k : ℤ}


/-- **Sesquilinear polarization** over `ℂ`: the cross product from four squared norms. -/
theorem polarization (x y : ℂ) :
    x * conj y = (4⁻¹ : ℂ) *
      ((((‖x + y‖ : ℝ) : ℂ) ^ 2 - ((‖x - y‖ : ℝ) : ℂ) ^ 2) +
        Complex.I * (((‖x + Complex.I * y‖ : ℝ) : ℂ) ^ 2
          - ((‖x - Complex.I * y‖ : ℝ) : ℂ) ^ 2)) := by
  have e : ∀ z : ℂ, (((‖z‖ : ℝ) : ℂ)) ^ 2 = z * conj z := by
    intro z
    rw [← Complex.mul_conj']
  rw [e, e, e, e]
  simp only [map_add, map_sub, map_mul, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring


/-- The four polarization forms of a pair. -/
noncomputable def polForm₁ (f g : CuspForm 𝒮ℒ k) : CuspForm 𝒮ℒ k := f + g
noncomputable def polForm₂ (f g : CuspForm 𝒮ℒ k) : CuspForm 𝒮ℒ k := f - g
noncomputable def polForm₃ (f g : CuspForm 𝒮ℒ k) : CuspForm 𝒮ℒ k := f + Complex.I • g
noncomputable def polForm₄ (f g : CuspForm 𝒮ℒ k) : CuspForm 𝒮ℒ k := f - Complex.I • g

/-- Coefficient polarization: the cross coefficients from the four diagonal norms. -/
theorem cross_coeff_polarization (f g : CuspForm 𝒮ℒ k) (n : ℕ) :
    (qExpansion 1 f).coeff n * conj ((qExpansion 1 g).coeff n)
      = (4⁻¹ : ℂ) *
        (((((‖(qExpansion 1 (polForm₁ f g)).coeff n‖ : ℝ) : ℂ)) ^ 2 -
            ((((‖(qExpansion 1 (polForm₂ f g)).coeff n‖ : ℝ) : ℂ)) ^ 2)) +
          Complex.I * (((((‖(qExpansion 1 (polForm₃ f g)).coeff n‖ : ℝ) : ℂ)) ^ 2 -
            ((((‖(qExpansion 1 (polForm₄ f g)).coeff n‖ : ℝ) : ℂ)) ^ 2)))) := by
  have h1 : (qExpansion 1 (polForm₁ f g)).coeff n
      = (qExpansion 1 f).coeff n + (qExpansion 1 g).coeff n := by
    unfold polForm₁
    rw [show (⇑(f + g) : ℍ → ℂ) = ⇑f + ⇑g from rfl,
      ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL f g]
    simp
  have h2 : (qExpansion 1 (polForm₂ f g)).coeff n
      = (qExpansion 1 f).coeff n - (qExpansion 1 g).coeff n := by
    unfold polForm₂
    rw [show (⇑(f - g) : ℍ → ℂ) = ⇑f - ⇑g from rfl,
      ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL f g]
    simp
  have hsmul : qExpansion 1 (Complex.I • (⇑g : ℍ → ℂ)) = Complex.I • qExpansion 1 ⇑g :=
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL Complex.I g
  have h3 : (qExpansion 1 (polForm₃ f g)).coeff n
      = (qExpansion 1 f).coeff n + Complex.I * (qExpansion 1 g).coeff n := by
    unfold polForm₃
    rw [show (⇑(f + Complex.I • g) : ℍ → ℂ) = ⇑f + ⇑(Complex.I • g) from rfl,
      ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL f (Complex.I • g),
      show (⇑(Complex.I • g) : ℍ → ℂ) = Complex.I • ⇑g from rfl, hsmul]
    simp
  have h4 : (qExpansion 1 (polForm₄ f g)).coeff n
      = (qExpansion 1 f).coeff n - Complex.I * (qExpansion 1 g).coeff n := by
    unfold polForm₄
    rw [show (⇑(f - Complex.I • g) : ℍ → ℂ) = ⇑f - ⇑(Complex.I • g) from rfl,
      ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL f (Complex.I • g),
      show (⇑(Complex.I • g) : ℍ → ℂ) = Complex.I • ⇑g from rfl, hsmul]
    simp
  rw [h1, h2, h3, h4]
  exact polarization _ _



/-- **The cross profile**: the polarization combination of the four averaged lattice
profiles — the theta-side realization of `L(f×g)`. -/
noncomputable def crossProfileC (k : ℤ) (f g : CuspForm 𝒮ℒ k) (t : ℝ) : ℂ :=
  (4⁻¹ : ℂ) *
    ((averagedThetaC k (polForm₁ f g) t - averagedThetaC k (polForm₂ f g) t) +
      Complex.I * (averagedThetaC k (polForm₃ f g) t - averagedThetaC k (polForm₄ f g) t))

/-- **The cross mass**: the polarization combination of the four Petersson masses —
the Petersson inner product `⟨f, g⟩`, up to the same normalization. -/
noncomputable def crossMass (k : ℤ) (f g : CuspForm 𝒮ℒ k) : ℂ :=
  (4⁻¹ : ℂ) *
    ((((peterssonMass k (polForm₁ f g) : ℝ) : ℂ) - ((peterssonMass k (polForm₂ f g) : ℝ) : ℂ)) +
      Complex.I * ((((peterssonMass k (polForm₃ f g) : ℝ) : ℂ))
        - ((peterssonMass k (polForm₄ f g) : ℝ) : ℂ)))

/-- **The cross pair**: the polarization combination of the four compiled averaged pairs —
weight one, root number one, both constant terms the cross mass, reflection inherited
term by term from the lattice theta transformation law. -/
noncomputable def crossPair (f g : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) : WeakFEPair ℂ where
  f := crossProfileC k f g
  g := crossProfileC k f g
  k := 1
  ε := 1
  f₀ := crossMass k f g
  g₀ := crossMass k f g
  hf_int := by
    have h1 := (rsAveragedWeakFEPair (polForm₁ f g) hk).hf_int
    have h2 := (rsAveragedWeakFEPair (polForm₂ f g) hk).hf_int
    have h3 := (rsAveragedWeakFEPair (polForm₃ f g) hk).hf_int
    have h4 := (rsAveragedWeakFEPair (polForm₄ f g) hk).hf_int
    exact (((h1.sub h2).add ((h3.sub h4).smul Complex.I)).smul (4⁻¹ : ℂ))
  hg_int := by
    have h1 := (rsAveragedWeakFEPair (polForm₁ f g) hk).hf_int
    have h2 := (rsAveragedWeakFEPair (polForm₂ f g) hk).hf_int
    have h3 := (rsAveragedWeakFEPair (polForm₃ f g) hk).hf_int
    have h4 := (rsAveragedWeakFEPair (polForm₄ f g) hk).hf_int
    exact (((h1.sub h2).add ((h3.sub h4).smul Complex.I)).smul (4⁻¹ : ℂ))
  hk := one_pos
  hε := one_ne_zero
  h_feq := by
    intro x hx
    unfold crossProfileC
    unfold averagedThetaC
    rw [one_div, averagedTheta_inv (polForm₁ f g) hx, averagedTheta_inv (polForm₂ f g) hx,
      averagedTheta_inv (polForm₃ f g) hx, averagedTheta_inv (polForm₄ f g) hx,
      Real.rpow_one]
    push_cast
    ring
  hf_top := by
    intro r
    have h1 := (rsAveragedWeakFEPair (polForm₁ f g) hk).hf_top r
    have h2 := (rsAveragedWeakFEPair (polForm₂ f g) hk).hf_top r
    have h3 := (rsAveragedWeakFEPair (polForm₃ f g) hk).hf_top r
    have h4 := (rsAveragedWeakFEPair (polForm₄ f g) hk).hf_top r
    have hcomb : (fun t : ℝ => crossProfileC k f g t - crossMass k f g)
        = fun t : ℝ => (4⁻¹ : ℂ) *
            (((averagedThetaC k (polForm₁ f g) t - ((peterssonMass k (polForm₁ f g) : ℝ) : ℂ))
              - (averagedThetaC k (polForm₂ f g) t - ((peterssonMass k (polForm₂ f g) : ℝ) : ℂ)))
            + Complex.I *
              ((averagedThetaC k (polForm₃ f g) t - ((peterssonMass k (polForm₃ f g) : ℝ) : ℂ))
              - (averagedThetaC k (polForm₄ f g) t
                  - ((peterssonMass k (polForm₄ f g) : ℝ) : ℂ)))) := by
      funext t
      unfold crossProfileC crossMass
      ring
    rw [hcomb]
    exact (((h1.sub h2).add ((h3.sub h4).const_mul_left Complex.I)).const_mul_left (4⁻¹ : ℂ))
  hg_top := by
    intro r
    have h1 := (rsAveragedWeakFEPair (polForm₁ f g) hk).hf_top r
    have h2 := (rsAveragedWeakFEPair (polForm₂ f g) hk).hf_top r
    have h3 := (rsAveragedWeakFEPair (polForm₃ f g) hk).hf_top r
    have h4 := (rsAveragedWeakFEPair (polForm₄ f g) hk).hf_top r
    have hcomb : (fun t : ℝ => crossProfileC k f g t - crossMass k f g)
        = fun t : ℝ => (4⁻¹ : ℂ) *
            (((averagedThetaC k (polForm₁ f g) t - ((peterssonMass k (polForm₁ f g) : ℝ) : ℂ))
              - (averagedThetaC k (polForm₂ f g) t - ((peterssonMass k (polForm₂ f g) : ℝ) : ℂ)))
            + Complex.I *
              ((averagedThetaC k (polForm₃ f g) t - ((peterssonMass k (polForm₃ f g) : ℝ) : ℂ))
              - (averagedThetaC k (polForm₄ f g) t
                  - ((peterssonMass k (polForm₄ f g) : ℝ) : ℂ)))) := by
      funext t
      unfold crossProfileC crossMass
      ring
    rw [hcomb]
    exact (((h1.sub h2).add ((h3.sub h4).const_mul_left Complex.I)).const_mul_left (4⁻¹ : ℂ))



/-- **The self-dual functional equation of the cross transform**: `Λ(1−s) = Λ(s)`. -/
theorem cross_selfdual_FE (f g : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) (s : ℂ) :
    (crossPair f g hk).Λ (1 - s) = (crossPair f g hk).Λ s := by
  have hsymm : (crossPair f g hk).symm = crossPair f g hk :=
    weakFEPair_symm_eq_self _ rfl rfl rfl
  have hfe := (crossPair f g hk).functional_equation s
  rw [hsymm, show (crossPair f g hk).ε = 1 from rfl] at hfe
  have hw : (((crossPair f g hk).k : ℝ) : ℂ) = 1 := by
    show (((1 : ℝ)) : ℂ) = 1
    norm_num
  rw [show ((crossPair f g hk).k : ℂ) = 1 from hw] at hfe
  simpa using hfe

/-- **The polar structure**: residue the cross mass — the Petersson pairing `⟨f,g⟩`
in polarized form — at the edge `s = 1`. -/
theorem cross_residue (f g : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    Filter.Tendsto (fun s : ℂ => (s - 1) * (crossPair f g hk).Λ s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (crossMass k f g)) := by
  have h := (crossPair f g hk).Λ_residue_k
  rw [show (crossPair f g hk).k = (1 : ℝ) from rfl] at h
  simp only [Complex.ofReal_one] at h
  rw [show (crossPair f g hk).ε = 1 from rfl, show (crossPair f g hk).g₀
    = crossMass k f g from rfl] at h
  simpa using h

/-- **The entire part.** -/
theorem cross_entire (f g : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    Differentiable ℂ (crossPair f g hk).Λ₀ :=
  (crossPair f g hk).differentiable_Λ₀

/-- **The cross Rankin bank**: the polarization combination of the four diagonal banks —
the Dirichlet coefficients of `L(f×g, s)` in the Deligne chart. -/
noncomputable def crossRankinBank (f g : CuspForm 𝒮ℒ k) : ArithmeticFunction ℂ :=
  (4⁻¹ : ℂ) • ((rankinBank (polForm₁ f g) - rankinBank (polForm₂ f g)) +
    Complex.I • (rankinBank (polForm₃ f g) - rankinBank (polForm₄ f g)))

/-- Mellin convergence: addition. -/
theorem mconv_add {F G : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent F s)
    (hg : MellinConvergent G s) : MellinConvergent (fun t => F t + G t) s := by
  unfold MellinConvergent at *
  simp_rw [smul_add]
  exact hf.add hg

/-- Mellin convergence: subtraction. -/
theorem mconv_sub {F G : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent F s)
    (hg : MellinConvergent G s) : MellinConvergent (fun t => F t - G t) s := by
  unfold MellinConvergent at *
  simp_rw [smul_sub]
  exact hf.sub hg

/-- Mellin linearity: addition. -/
theorem mellin_add' {F G : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent F s)
    (hg : MellinConvergent G s) :
    mellin (fun t => F t + G t) s = mellin F s + mellin G s := by
  unfold mellin
  simp_rw [smul_add]
  exact MeasureTheory.integral_add hf hg

/-- Mellin linearity: subtraction. -/
theorem mellin_sub' {F G : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent F s)
    (hg : MellinConvergent G s) :
    mellin (fun t => F t - G t) s = mellin F s - mellin G s := by
  unfold mellin
  simp_rw [smul_sub]
  exact MeasureTheory.integral_sub hf hg

/-- Mellin transform of the tail combination splits into the four diagonal tails. -/
theorem cross_mellin_split (f g : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 1 < s.re) :
    mellin (fun t : ℝ => crossProfileC k f g t - crossMass k f g) s
      = (4⁻¹ : ℂ) *
        ((mellin (fun t : ℝ => averagedThetaC k (polForm₁ f g) t
            - ((peterssonMass k (polForm₁ f g) : ℝ) : ℂ)) s
          - mellin (fun t : ℝ => averagedThetaC k (polForm₂ f g) t
            - ((peterssonMass k (polForm₂ f g) : ℝ) : ℂ)) s)
        + Complex.I *
          (mellin (fun t : ℝ => averagedThetaC k (polForm₃ f g) t
            - ((peterssonMass k (polForm₃ f g) : ℝ) : ℂ)) s
          - mellin (fun t : ℝ => averagedThetaC k (polForm₄ f g) t
            - ((peterssonMass k (polForm₄ f g) : ℝ) : ℂ)) s)) := by
  have h1 := rsAveraged_mellinConvergent (polForm₁ f g) hk hs
  have h2 := rsAveraged_mellinConvergent (polForm₂ f g) hk hs
  have h3 := rsAveraged_mellinConvergent (polForm₃ f g) hk hs
  have h4 := rsAveraged_mellinConvergent (polForm₄ f g) hk hs
  have hshape : (fun t : ℝ => crossProfileC k f g t - crossMass k f g)
      = fun t : ℝ => (4⁻¹ : ℂ) •
          (((averagedThetaC k (polForm₁ f g) t - ((peterssonMass k (polForm₁ f g) : ℝ) : ℂ))
            - (averagedThetaC k (polForm₂ f g) t - ((peterssonMass k (polForm₂ f g) : ℝ) : ℂ)))
          + Complex.I •
            ((averagedThetaC k (polForm₃ f g) t - ((peterssonMass k (polForm₃ f g) : ℝ) : ℂ))
            - (averagedThetaC k (polForm₄ f g) t
                - ((peterssonMass k (polForm₄ f g) : ℝ) : ℂ)))) := by
    funext t
    unfold crossProfileC crossMass
    simp only [smul_eq_mul]
    ring
  rw [hshape, mellin_const_smul,
    mellin_add' (mconv_sub h1 h2) ((mconv_sub h3 h4).const_smul Complex.I),
    mellin_sub' h1 h2, mellin_const_smul, mellin_sub' h3 h4]
  simp [smul_eq_mul]



set_option maxHeartbeats 800000 in
/-- The cross bank's L-series is the polarization combination of the four diagonal ones. -/
theorem LSeries_crossRankinBank (f g : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    LSeries (⇑(crossRankinBank f g)) s
      = (4⁻¹ : ℂ) *
        ((LSeries (⇑(rankinBank (polForm₁ f g))) s - LSeries (⇑(rankinBank (polForm₂ f g))) s)
        + Complex.I * (LSeries (⇑(rankinBank (polForm₃ f g))) s
          - LSeries (⇑(rankinBank (polForm₄ f g))) s)) := by
  have h1 := rankinBank_LSeriesSummable (polForm₁ f g) hk hs
  have h2 := rankinBank_LSeriesSummable (polForm₂ f g) hk hs
  have h3 := rankinBank_LSeriesSummable (polForm₃ f g) hk hs
  have h4 := rankinBank_LSeriesSummable (polForm₄ f g) hk hs
  have hcoe : (⇑(crossRankinBank f g) : ℕ → ℂ)
      = (4⁻¹ : ℂ) • ((⇑(rankinBank (polForm₁ f g)) - ⇑(rankinBank (polForm₂ f g)))
        + Complex.I • (⇑(rankinBank (polForm₃ f g)) - ⇑(rankinBank (polForm₄ f g)))) := by
    funext n
    show crossRankinBank f g n = _
    unfold crossRankinBank
    show (4⁻¹ : ℂ) * (((rankinBank (polForm₁ f g)) n - (rankinBank (polForm₂ f g)) n) +
      Complex.I * ((rankinBank (polForm₃ f g)) n - (rankinBank (polForm₄ f g)) n)) = _
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, sub_eq_add_neg, Pi.neg_apply]
  rw [hcoe, LSeries_smul,
    LSeries_add ((h1.sub h2)) ((h3.sub h4).smul Complex.I),
    LSeries_sub h1 h2, LSeries_smul, LSeries_sub h3 h4]

/-- **The chart identification**: on `2 < Re s` the cross transform is the completed cross
Rankin L-series in the Deligne chart. -/
theorem cross_lambda_eq (f g : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ} (hs : 2 < s.re) :
    (crossPair f g hk).Λ s
      = (2 : ℂ) ^ (-(k : ℂ)) * (Gammaℂ s * Gammaℂ (s + (k : ℂ) - 1)) *
        LSeries (⇑(crossRankinBank f g)) s := by
  have h1r : (1 : ℝ) < s.re := by linarith
  have hmell := (crossPair f g hk).hasMellin
    (show (crossPair f g hk).k < s.re from h1r)
  rw [← hmell.2]
  rw [show (fun t : ℝ => (crossPair f g hk).f t - (crossPair f g hk).f₀)
      = fun t : ℝ => crossProfileC k f g t - crossMass k f g from rfl]
  rw [cross_mellin_split f g hk h1r,
    rankin_readout_gammaC (polForm₁ f g) hk hs,
    rankin_readout_gammaC (polForm₂ f g) hk hs,
    rankin_readout_gammaC (polForm₃ f g) hk hs,
    rankin_readout_gammaC (polForm₄ f g) hk hs,
    LSeries_crossRankinBank f g hk hs]
  ring



/-- The diagonal Rankin bank is the square-indicator dressing of the normalized square. -/
theorem rankinBank_eq_sqIndicator_mul (f : CuspForm 𝒮ℒ k) :
    rankinBank f = sqIndicator * rankinSquareNorm f := by
  unfold rankinBank sym2Bank
  rw [show ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) *
      (sqIndicator * ((μ : ArithmeticFunction ℂ) * rankinSquareNorm f))
      = sqIndicator * ((((μ : ArithmeticFunction ℂ)) *
        ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) * rankinSquareNorm f) by
    ring]
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]

/-- **The cross square**: the polarization combination of the four normalized squares —
pointwise the literal cross Hecke data `a_f(n)·conj(a_g(n))/n^{k−1}`. -/
noncomputable def crossSquare (f g : CuspForm 𝒮ℒ k) : ArithmeticFunction ℂ :=
  (4⁻¹ : ℂ) • ((rankinSquareNorm (polForm₁ f g) - rankinSquareNorm (polForm₂ f g)) +
    Complex.I • (rankinSquareNorm (polForm₃ f g) - rankinSquareNorm (polForm₄ f g)))

/-- **The cross coefficients are the literal cross Hecke data.** -/
theorem crossSquare_apply (f g : CuspForm 𝒮ℒ k) {n : ℕ} (hn : n ≠ 0) :
    crossSquare f g n
      = (qExpansion 1 f).coeff n * (starRingEnd ℂ) ((qExpansion 1 g).coeff n) /
          ((n : ℝ) ^ ((k : ℝ) - 1) : ℝ) := by
  have hpow : (0 : ℝ) < ((n : ℝ) ^ ((k : ℝ) - 1) : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
  unfold crossSquare
  show (4⁻¹ : ℂ) * (((rankinSquareNorm (polForm₁ f g)) n - (rankinSquareNorm (polForm₂ f g)) n) +
      Complex.I * ((rankinSquareNorm (polForm₃ f g)) n - (rankinSquareNorm (polForm₄ f g)) n)) = _
  rw [rankinSquareNorm_apply' hn, rankinSquareNorm_apply' hn,
    rankinSquareNorm_apply' hn, rankinSquareNorm_apply' hn,
    cross_coeff_polarization f g n]
  push_cast [Real.rpow_natCast]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  ring



/-- **The cross bank is the square-indicator dressing of the literal cross data**:
`crossRankinBank = 1_□ ⋆ crossSquare` — the Dirichlet-coefficient identification of
`L(f×g)` in Deligne normalization. -/
theorem crossRankinBank_eq_sq (f g : CuspForm 𝒮ℒ k) :
    crossRankinBank f g = sqIndicator * crossSquare f g := by
  unfold crossRankinBank crossSquare
  rw [rankinBank_eq_sqIndicator_mul, rankinBank_eq_sqIndicator_mul,
    rankinBank_eq_sqIndicator_mul, rankinBank_eq_sqIndicator_mul]
  rw [mul_smul_comm]
  congr 1
  rw [mul_add, mul_smul_comm, mul_sub, mul_sub]

/-- **Rung 6, one theorem** — the general Rankin–Selberg pair at level one: for every pair
of cusp forms of weight `k ≥ 2`, the completed cross transform satisfies the self-dual
functional equation globally, has residue the polarized Petersson pairing at the edge, is
entire away from its two booked poles, and on `2 < Re s` equals the Γℂ-pair-completed
L-series of the cross bank, whose coefficients are the literal cross Hecke data. -/
theorem rankin_selberg_rung (f g : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    (∀ s : ℂ, (crossPair f g hk).Λ (1 - s) = (crossPair f g hk).Λ s) ∧
    Filter.Tendsto (fun s : ℂ => (s - 1) * (crossPair f g hk).Λ s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (crossMass k f g)) ∧
    Differentiable ℂ (crossPair f g hk).Λ₀ ∧
    (∀ s : ℂ, 2 < s.re → (crossPair f g hk).Λ s
      = (2 : ℂ) ^ (-(k : ℂ)) * (Gammaℂ s * Gammaℂ (s + (k : ℂ) - 1)) *
        LSeries (⇑(crossRankinBank f g)) s) ∧
    (∀ n : ℕ, n ≠ 0 → crossSquare f g n
      = (qExpansion 1 f).coeff n * (starRingEnd ℂ) ((qExpansion 1 g).coeff n) /
          ((n : ℝ) ^ ((k : ℝ) - 1) : ℝ)) :=
  ⟨cross_selfdual_FE f g hk,
   cross_residue f g hk,
   cross_entire f g hk,
   fun _ hs => cross_lambda_eq f g hk hs,
   fun _ hn => crossSquare_apply f g hn⟩

end CriticalLinePhasor.RankinSelbergCross

#print axioms CriticalLinePhasor.RankinSelbergCross.polarization
#print axioms CriticalLinePhasor.RankinSelbergCross.cross_coeff_polarization
#print axioms CriticalLinePhasor.RankinSelbergCross.crossPair
#print axioms CriticalLinePhasor.RankinSelbergCross.cross_selfdual_FE
#print axioms CriticalLinePhasor.RankinSelbergCross.cross_residue
#print axioms CriticalLinePhasor.RankinSelbergCross.cross_entire
#print axioms CriticalLinePhasor.RankinSelbergCross.cross_mellin_split
#print axioms CriticalLinePhasor.RankinSelbergCross.LSeries_crossRankinBank
#print axioms CriticalLinePhasor.RankinSelbergCross.cross_lambda_eq
#print axioms CriticalLinePhasor.RankinSelbergCross.rankinBank_eq_sqIndicator_mul
#print axioms CriticalLinePhasor.RankinSelbergCross.crossSquare_apply
#print axioms CriticalLinePhasor.RankinSelbergCross.crossRankinBank_eq_sq
#print axioms CriticalLinePhasor.RankinSelbergCross.rankin_selberg_rung
