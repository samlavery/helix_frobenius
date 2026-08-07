import RequestProject.Sym3ThetaWall
import RequestProject.GlobalHelixRealClockCompletion

/-!
# The mechanism: one theta identity yields the complete analytic package

Rung 9 of the benchmark ladder, stated as compiled theorems rather than a register
claim.  For **every** admissible self-dual-multiset Satake bank and **every** admissible
archimedean chart — pure complex (`∏ Γℂ`) or mixed real/complex (`Γℝ·∏ Γℂ`) — a single
pointwise theta identity between the two prescribed 3D readouts machine-yields
continuation, entirety, the functional equation, and the chart identification, with
every other input compiled:

* `mechB` — the uniform threshold of a bank;
* `mechanism` — **the pure-complex mechanism**: `NicePackage` from one identity;
* `MixedNicePackage` (+ `unique`) — the typed conclusion at a mixed chart;
* `mechanismR` — **the mixed mechanism**: `MixedNicePackage` from one identity, the
  real clock `gammaRClock` carrying `Γℝ(s+δ)`;
* `symrCoefficientArithmetic_eq` — the shifted radial clock coefficients are the
  `Sym^r` bank;
* `symr_package_of_theta` / `symr_mixed_package_of_theta` — the mechanism at **every
  rank** `Sym^r` of the eigenform seed, at every admissible chart of either type (the
  self-duality input is the compiled clock reversal `symrPair_dual_eq_primal`);
* `sym4Shifts`, `sym4_package_of_theta` — **rung 5's finish**: the `Sym⁴` package from
  one identity at its mixed chart `Γℝ(s+δ)·Γℂ(s+(2n−1))·Γℂ(s+2(2n−1))` — the complex
  shifts are the exponent pairs of `Sym⁴` at weight `2n`; whichever admissible `(δ, ε)`
  satisfies the identity yields the package.

No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups LSeries.notation

namespace CriticalLinePhasor.ThetaMechanism

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.TransportClosure
open CriticalLinePhasor.SymrBank CriticalLinePhasor.SymCubeQuartic
open CriticalLinePhasor.UniformTransport CriticalLinePhasor.SeedStandardRung
open CriticalLinePhasor.GenuineGL2Carrier CriticalLinePhasor.NiceClosure
open CriticalLinePhasor.Sym3ThetaWall CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.Sym2Wire
open Set Filter Topology MeasureTheory Asymptotics

variable {ι : Type*} [Fintype ι]

/-- The mechanism threshold of a bank. -/
noncomputable def mechB (W : PolynomialSatakeDualPair ι) : ℝ :=
  ((Fintype.card ι + max W.primalExponent W.dualExponent : ℕ) : ℝ) + 1

/-- The mechanism clock. -/
noncomputable def mechClock (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ []) :
    CPSCompletionClock :=
  ⟨C, hC, μs, hne⟩

/-- A point of the mechanism half-plane. -/
noncomputable def mechPoint (W : PolynomialSatakeDualPair ι) {C : ℝ} {hC : 0 < C}
    {μs : List ℂ} {hne : μs ≠ []} (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    {s : ℂ} (hs : mechB W < s.re) :
    CPSCompletionPoint W (mechClock C hC μs hne) where
  s := s
  shifts_pos := by
    intro μ hμ
    have h0 : (0 : ℝ) ≤ mechB W := by unfold mechB; positivity
    have := hμpos μ hμ
    simp only [Complex.add_re]
    linarith
  primal_dirichlet := by
    have hle : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ)
        ≤ ((Fintype.card ι + max W.primalExponent W.dualExponent : ℕ) : ℝ) := by
      push_cast
      have := le_max_left W.primalExponent W.dualExponent
      have : (W.primalExponent : ℝ) ≤ (max W.primalExponent W.dualExponent : ℝ) := by
        exact_mod_cast this
      linarith
    unfold mechB at hs
    linarith
  dual_dirichlet := by
    have hle : ((Fintype.card ι + W.dualExponent : ℕ) : ℝ)
        ≤ ((Fintype.card ι + max W.primalExponent W.dualExponent : ℕ) : ℝ) := by
      push_cast
      have := le_max_right W.primalExponent W.dualExponent
      have : (W.dualExponent : ℝ) ≤ (max W.primalExponent W.dualExponent : ℝ) := by
        exact_mod_cast this
      linarith
    unfold mechB at hs
    linarith

/-- Generic summability of the shifted bank beyond the mechanism threshold. -/
theorem bankArithmetic_summable (W : PolynomialSatakeDualPair ι) {s : ℂ}
    (hs : mechB W < s.re) :
    LSeriesSummable (⇑(coefficientArithmetic (cpsPolynomialPrimalCoeff W))) s := by
  have hs' : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re := by
    unfold mechB at hs
    have : (W.primalExponent : ℝ) ≤ (max W.primalExponent W.dualExponent : ℝ) := by
      exact_mod_cast le_max_left W.primalExponent W.dualExponent
    push_cast at hs ⊢
    linarith
  refine LSeriesSummable_of_le_const_mul_rpow
    (x := ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1) hs' ⟨1, fun m hm => ?_⟩
  calc ‖(coefficientArithmetic (cpsPolynomialPrimalCoeff W)) m‖
      ≤ (1 : ℝ) * (m : ℝ) ^ ((Fintype.card ι + W.primalExponent : ℕ)) :=
        cpsPolynomialPrimalArithmetic_norm_le W m
    _ ≤ 1 * (m : ℝ) ^ ((((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1) - 1) := by
        rw [one_mul, one_mul, add_sub_cancel_right, Real.rpow_natCast]

/-- **THE MECHANISM** — for every admissible self-dual-multiset bank and every
nonnegative prescribed chart: one pointwise theta identity of the prescribed readouts
yields the complete analytic package — continuation, entirety, functional equation, and
chart — with every other input compiled. -/
noncomputable def mechanism (W : PolynomialSatakeDualPair ι)
    (hdual : ∀ j : ℕ, cpsPolynomialDualCoeff W j = cpsPolynomialPrimalCoeff W j)
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout W 1 μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          cpsPolynomialFullDual3DTransformedReadout W 1 μs (1 / x)) :
    NicePackage (coefficientArithmetic (cpsPolynomialPrimalCoeff W)) μs (mechB W) ε := by
  refine
    let pair : CriticalLinePhasor.GenuineGL2Carrier.PolynomialBankReflectedThetaSource
        W 1 μs :=
      { pair := {
          toWeakFEPair := {
            f := cpsPolynomialFullPrimal3DBankReadout W 1 μs
            g := fun x : ℝ =>
              cpsPolynomialFullDual3DTransformedReadout W 1 μs (1 / x)
            k := 1
            ε := ε
            f₀ := 0
            g₀ := 0
            hf_int := cpsPolynomialFullPrimal3DBankReadout_locallyIntegrableOn W 1
              one_pos μs hne
            hg_int := cpsPolynomialFullDual3DReflectedReadout_locallyIntegrableOn W 1
              one_pos μs hne
            hk := one_pos
            hε := hε
            h_feq := fun x hx => hrefl x hx
            hf_top := fun q => by
              simpa using cpsPolynomialFullPrimal3DBankReadout_rapid W 1 one_pos μs q
            hg_top := fun q => by
              simpa using cpsPolynomialFullDual3DReflectedReadout_rapid W 1 one_pos μs q
          }
          hf₀ := rfl
          hg₀ := rfl }
        primal_source := rfl
        dual_source := rfl }
    ?_
  have hsymm : pair.pair.symm.Λ = pair.pair.Λ := by
    refine CriticalLinePhasor.CarrierTargetIdentification.entire_eq_of_eqOn_isOpen
      pair.pair.symm.differentiable_Λ pair.pair.differentiable_Λ
      (U := {s : ℂ | mechB W < s.re})
      (IsOpen.preimage Complex.continuous_re isOpen_Ioi)
      (z₀ := ((mechB W + 1 : ℝ) : ℂ))
      (by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
      ?_
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    have hid := cpsPolynomialFullCompletion3D_identification W
      (mechClock 1 one_pos μs hne) (mechPoint W hμpos hs)
    have hdualdir : CriticalLinePhasor.CarrierTheta.dirichlet
        (cpsPolynomialDualCoeff W) s
        = CriticalLinePhasor.CarrierTheta.dirichlet (cpsPolynomialPrimalCoeff W) s := by
      unfold CriticalLinePhasor.CarrierTheta.dirichlet
      exact tsum_congr fun m => by rw [hdual m]
    refine (hid.2.trans ?_).trans hid.1.symm
    unfold cpsPolynomialFullDualCompletedReadout cpsPolynomialFullPrimalCompletedReadout
    rw [show (mechPoint W hμpos hs).s = s from rfl, hdualdir]
  exact
    { lam := pair.pair.Λ
      entire := pair.pair.differentiable_Λ
      FE := by
        intro s
        have h := pair.pair.functional_equation s
        rw [hsymm] at h
        rw [show ((pair.pair.k : ℝ) : ℂ) = 1 from by norm_num] at h
        simpa using h
      chart := by
        intro s hs
        have hid := (cpsPolynomialFullCompletion3D_identification W
          (mechClock 1 one_pos μs hne) (mechPoint W hμpos hs)).1
        refine hid.trans ?_
        show ((1 : ℝ) : ℂ) ^ s * (μs.map fun μ => Complex.Gammaℂ (s + μ)).prod *
          CriticalLinePhasor.CarrierTheta.dirichlet (cpsPolynomialPrimalCoeff W) s = _
        have hcoeff : cpsPolynomialPrimalCoeff W
            = fun j => (coefficientArithmetic (cpsPolynomialPrimalCoeff W)) (j + 1) := by
          funext j
          simp [coefficientArithmetic]
        rw [hcoeff, dirichlet_shift_eq_LSeries _ (bankArithmetic_summable W hs)]
        simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
        rw [← hcoeff] }

/-- The typed conclusion at a mixed real/complex chart: entire continuation, functional
equation, and the `Γℝ·∏Γℂ` chart identification on the initial half-plane. -/
structure MixedNicePackage (a : ArithmeticFunction ℂ) (dlt : ℂ) (μs : List ℂ)
    (B : ℝ) (ε : ℂ) where
  lam : ℂ → ℂ
  entire : Differentiable ℂ lam
  FE : ∀ s : ℂ, lam (1 - s) = ε * lam s
  chart : ∀ s : ℂ, B < s.re →
    lam s = Complex.Gammaℝ (s + dlt) *
      ((μs.map fun μ => Complex.Gammaℂ (s + μ)).prod) * LSeries (⇑a) s

/-- Uniqueness of the mixed continuation. -/
theorem MixedNicePackage.unique {a : ArithmeticFunction ℂ} {dlt : ℂ} {μs : List ℂ}
    {B : ℝ} {ε ε' : ℂ}
    (P : MixedNicePackage a dlt μs B ε) (Q : MixedNicePackage a dlt μs B ε') :
    P.lam = Q.lam := by
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

/-- **THE MECHANISM AT A MIXED CHART** — for every admissible self-dual-multiset bank,
every nonnegative real-place shift, and every nonnegative complex-place chart: one
pointwise theta identity of the prescribed mixed readouts yields the complete analytic
package. -/
noncomputable def mechanismR (W : PolynomialSatakeDualPair ι)
    (hdual : ∀ j : ℕ, cpsPolynomialDualCoeff W j = cpsPolynomialPrimalCoeff W j)
    (dlt : ℂ) (hdlt : 0 ≤ dlt.re)
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      mixedPrimal3DBankReadout W dlt μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          mixedDual3DTransformedReadout W dlt μs (1 / x)) :
    MixedNicePackage (coefficientArithmetic (cpsPolynomialPrimalCoeff W)) dlt μs
      (mechB W) ε := by
  refine
    let pair : StrongFEPair ℂ :=
      { f := mixedPrimal3DBankReadout W dlt μs
        g := fun x : ℝ => mixedDual3DTransformedReadout W dlt μs (1 / x)
        k := 1
        ε := ε
        f₀ := 0
        g₀ := 0
        hf_int := mixedPrimal3DBankReadout_locallyIntegrableOn W dlt μs hne
        hg_int := mixedDual3DReflectedReadout_locallyIntegrableOn W dlt μs hne
        hk := one_pos
        hε := hε
        h_feq := fun x hx => hrefl x hx
        hf_top := fun q => by
          simpa using mixedPrimal3DBankReadout_rapid W dlt μs hne q
        hg_top := fun q => by
          simpa using mixedDual3DReflectedReadout_rapid W dlt μs hne q
        hf₀ := rfl
        hg₀ := rfl }
    ?_
  have hmechB0 : (0 : ℝ) ≤ mechB W := by unfold mechB; positivity
  have hconds : ∀ s : ℂ, mechB W < s.re →
      (0 < (s + dlt).re ∧ (∀ μ ∈ μs, 0 < (s + μ).re) ∧
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re ∧
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ) + 1 < s.re) := by
    intro s hs
    have h1 : (1 : ℝ) ≤ mechB W := by
      unfold mechB
      have : (0 : ℝ) ≤ ((Fintype.card ι + max W.primalExponent W.dualExponent : ℕ) : ℝ) := by
        positivity
      linarith
    refine ⟨by simp only [Complex.add_re]; linarith, fun μ hμ => ?_, ?_, ?_⟩
    · have := hμpos μ hμ
      simp only [Complex.add_re]
      linarith
    · have hle : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ)
          ≤ ((Fintype.card ι + max W.primalExponent W.dualExponent : ℕ) : ℝ) := by
        push_cast
        have : (W.primalExponent : ℝ) ≤ (max W.primalExponent W.dualExponent : ℝ) := by
          exact_mod_cast le_max_left W.primalExponent W.dualExponent
        linarith
      unfold mechB at hs
      linarith
    · have hle : ((Fintype.card ι + W.dualExponent : ℕ) : ℝ)
          ≤ ((Fintype.card ι + max W.primalExponent W.dualExponent : ℕ) : ℝ) := by
        push_cast
        have : (W.dualExponent : ℝ) ≤ (max W.primalExponent W.dualExponent : ℝ) := by
          exact_mod_cast le_max_right W.primalExponent W.dualExponent
        linarith
      unfold mechB at hs
      linarith
  have hsymm : pair.symm.Λ = pair.Λ := by
    refine CriticalLinePhasor.CarrierTargetIdentification.entire_eq_of_eqOn_isOpen
      pair.symm.differentiable_Λ pair.differentiable_Λ
      (U := {s : ℂ | mechB W < s.re})
      (IsOpen.preimage Complex.continuous_re isOpen_Ioi)
      (z₀ := ((mechB W + 1 : ℝ) : ℂ))
      (by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
      ?_
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    obtain ⟨hc1, hc2, hc3, hc4⟩ := hconds s hs
    have hid1 := mixedPrimal3D_initialIdentification W dlt μs hne s hc1 hc2 hc3
    have hid2 := mixedDual3D_initialIdentification W dlt μs hne s hc1 hc2 hc4
    have hdualdir : dirichlet (cpsPolynomialDualCoeff W) s
        = dirichlet (cpsPolynomialPrimalCoeff W) s := by
      unfold dirichlet
      exact tsum_congr fun m => by rw [hdual m]
    refine (hid2.trans ?_).trans hid1.symm
    unfold mixedDualCompletedReadout mixedPrimalCompletedReadout
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
        obtain ⟨hc1, hc2, hc3, _⟩ := hconds s hs
        have hid := mixedPrimal3D_initialIdentification W dlt μs hne s hc1 hc2 hc3
        refine hid.trans ?_
        unfold mixedPrimalCompletedReadout
        have hcoeff : cpsPolynomialPrimalCoeff W
            = fun j => (coefficientArithmetic (cpsPolynomialPrimalCoeff W)) (j + 1) := by
          funext j
          simp [coefficientArithmetic]
        rw [hcoeff, dirichlet_shift_eq_LSeries _ (bankArithmetic_summable W hs)]
        rw [← hcoeff] }

variable {n : ℕ} {f : CuspForm 𝒮ℒ (2 * n : ℤ)}

/-- The shifted radial coefficients of the `Sym^r` clock, as the `Sym^r` bank. -/
theorem symrCoefficientArithmetic_eq (H : HeckeEigenData f) (r : ℕ) :
    coefficientArithmetic (cpsPolynomialPrimalCoeff (symrSatakePair H r))
      = symrBank H r := by
  ext m
  match m with
  | 0 => simp [coefficientArithmetic]
  | (j+1) =>
      show (if (j+1) = 0 then 0 else cpsPolynomialPrimalCoeff (symrSatakePair H r) j)
        = symrBank H r (j+1)
      rw [if_neg (Nat.succ_ne_zero j)]
      exact CriticalLinePhasor.Sym2Join.radialGlobal_eq_symrBank H r j

/-- **The mechanism at every rank, at every admissible complex chart**: one theta identity
of the prescribed `Sym^r` readouts yields the complete package for `L(Sym^r)`. -/
noncomputable def symr_package_of_theta (H : HeckeEigenData f) (r : ℕ)
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout (symrSatakePair H r) 1 μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          cpsPolynomialFullDual3DTransformedReadout (symrSatakePair H r) 1 μs (1 / x)) :
    NicePackage (symrBank H r) μs (mechB (symrSatakePair H r)) ε :=
  symrCoefficientArithmetic_eq H r ▸
    mechanism (symrSatakePair H r) (symrPair_dual_eq_primal H r) μs hne hμpos ε hε hrefl

/-- **The mechanism at every rank, at every admissible mixed chart.** -/
noncomputable def symr_mixed_package_of_theta (H : HeckeEigenData f) (r : ℕ)
    (dlt : ℂ) (hdlt : 0 ≤ dlt.re)
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      mixedPrimal3DBankReadout (symrSatakePair H r) dlt μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          mixedDual3DTransformedReadout (symrSatakePair H r) dlt μs (1 / x)) :
    MixedNicePackage (symrBank H r) dlt μs (mechB (symrSatakePair H r)) ε :=
  symrCoefficientArithmetic_eq H r ▸
    mechanismR (symrSatakePair H r) (symrPair_dual_eq_primal H r) dlt hdlt μs hne hμpos
      ε hε hrefl

/-- The classical `Sym⁴` chart of a weight-`2n` seed: `Γℝ(s+1)·Γℂ(s+(2n−1))·Γℂ(s+2(2n−1))`. -/
noncomputable def sym4Shifts (n : ℕ) : List ℂ :=
  [((2 * (n:ℝ) - 1 : ℝ) : ℂ), ((2 * (2 * (n:ℝ) - 1) : ℝ) : ℂ)]

theorem sym4Shifts_ne (n : ℕ) : sym4Shifts n ≠ [] := by simp [sym4Shifts]

theorem sym4Shifts_nonneg (hn : 0 < n) : ∀ μ ∈ sym4Shifts n, 0 ≤ μ.re := by
  intro μ hμ
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [sym4Shifts, List.mem_cons, List.not_mem_nil, or_false] at hμ
  rcases hμ with rfl | rfl <;> simp only [Complex.ofReal_re] <;> linarith

/-- **The `Sym⁴` package from one identity, at its mixed chart**
`Γℝ(s+δ)·Γℂ(s+(2n−1))·Γℂ(s+2(2n−1))·L(Sym⁴,s)`: the complex shifts are the exponent
pairs of `Sym⁴` at weight `2n`; the real shift is any admissible `δ` — whichever `(δ, ε)`
satisfies the one identity yields the package. -/
noncomputable def sym4_package_of_theta (hn : 0 < n) (H : HeckeEigenData f)
    (dlt : ℂ) (hdlt : 0 ≤ dlt.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      mixedPrimal3DBankReadout (symrSatakePair H 4) dlt (sym4Shifts n) (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          mixedDual3DTransformedReadout (symrSatakePair H 4) dlt (sym4Shifts n) (1 / x)) :
    MixedNicePackage (symrBank H 4) dlt (sym4Shifts n) (mechB (symrSatakePair H 4)) ε :=
  symr_mixed_package_of_theta H 4 dlt hdlt (sym4Shifts n) (sym4Shifts_ne n)
    (sym4Shifts_nonneg hn) ε hε hrefl

end CriticalLinePhasor.ThetaMechanism

#print axioms CriticalLinePhasor.ThetaMechanism.bankArithmetic_summable
#print axioms CriticalLinePhasor.ThetaMechanism.mechanism
#print axioms CriticalLinePhasor.ThetaMechanism.MixedNicePackage.unique
#print axioms CriticalLinePhasor.ThetaMechanism.mechanismR
#print axioms CriticalLinePhasor.ThetaMechanism.symrCoefficientArithmetic_eq
#print axioms CriticalLinePhasor.ThetaMechanism.symr_package_of_theta
#print axioms CriticalLinePhasor.ThetaMechanism.symr_mixed_package_of_theta
#print axioms CriticalLinePhasor.ThetaMechanism.sym4_package_of_theta
