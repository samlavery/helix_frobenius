import RequestProject.ThetaMechanism
import RequestProject.UniformTransport
import RequestProject.GlobalHelixGeneralChartCompletion

/-!
# The mechanism at every transported bank

The remaining banks of the ladder — the transported data `ρ = ⊕ᵢ Sym^{rᵢ}` of rung 7,
which subsume the split base-change, tensor-decomposition, and composite banks — get
their packages: the mechanism applies to every datum at every chart type, because the
transported pair is **self-dual at every datum**.

* `repPerm` / `repWeight_inv_eq` / `repPair_dual_eq_primal` — inverting every channel
  of a datum is the blockwise clock reversal, so the contragredient coefficients equal
  the primal coefficients, for every `ρ`;
* `rep_package_of_theta` / `rep_mixed_package_of_theta` — the mechanism at every datum,
  complex and mixed charts: one theta identity yields the complete package for
  `L(ρ, s) = ∏ᵢ L(Sym^{rᵢ}, s)` over the compiled product bank;
* `GeneralNicePackage` (+ `unique`) and `mechanismG` — **the mechanism at the general
  Deligne chart** `∏ⱼΓℝ(s+δⱼ)·∏ᵢΓℂ(s+μᵢ)`, subsuming the complex and mixed cases;
* `rep_general_package_of_theta` — the mechanism at every datum and every general chart;
* named instances at their classical charts: `tensor23_package_of_theta` (the degree-6
  tensor `std ⊗ Sym²` at datum `[3, 1]`, pure complex chart),
  `tensor33_package_of_theta` (the degree-9 tensor `Sym² ⊗ Sym²` at datum `[4, 2, 0]`,
  general chart, three real clocks parametric), `bc_split_package_of_theta` (split
  base change at datum `[1, 1]`, doubled seed chart).

No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups LSeries.notation

namespace CriticalLinePhasor.RepMechanism

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.TransportClosure
open CriticalLinePhasor.SymrBank CriticalLinePhasor.SymCubeQuartic
open CriticalLinePhasor.UniformTransport CriticalLinePhasor.SeedStandardRung
open CriticalLinePhasor.GenuineGL2Carrier CriticalLinePhasor.NiceClosure
open CriticalLinePhasor.Sym3ThetaWall CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.ThetaMechanism
open Set Filter Topology MeasureTheory Asymptotics

section RepCore

variable {k : ℤ} {f : CuspForm 𝒮ℒ k}

/-- The channel reversal of a representation datum: the clock reversal on every block. -/
def repPerm : ∀ ρ : List ℕ, Equiv.Perm (repIndex ρ)
  | [] => Equiv.refl _
  | _ :: ρ => Equiv.sumCongr Fin.revPerm (repPerm ρ)

/-- Inverting every channel of the datum is the channel reversal. -/
theorem repWeight_inv_eq (H : HeckeEigenData f) :
    ∀ ρ : List ℕ, ∀ (p : Nat.Primes) (x : repIndex ρ),
      (repWeight H ρ p x)⁻¹ = repWeight H ρ p (repPerm ρ x)
  | [], _, x => x.elim
  | r :: ρ, p, x => by
      rcases x with j | y
      · show (symClockWeight r (H.satake p.2) (j : ℕ))⁻¹
          = symClockWeight r (H.satake p.2) ((Fin.rev j : Fin (r + 1)) : ℕ)
        unfold symClockWeight
        rw [← zpow_neg]
        congr 1
        have hrev : ((Fin.rev j : Fin (r + 1)) : ℕ) = r - (j : ℕ) := by
          simp [Fin.rev]
        rw [hrev]
        have hle : (j : ℕ) ≤ r := Nat.lt_succ_iff.mp j.2
        push_cast [Nat.cast_sub hle]
        ring
      · exact repWeight_inv_eq H ρ p y

/-- The `Sym⁰` bank is `ζ`: the rank-zero clock is the unit system. -/
theorem symrBank_zero_eq_zeta (H : HeckeEigenData f) :
    symrBank H 0 = ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
  rw [← bankArithmetic_symClock H 0,
    show (fun p : Nat.Primes => fun i : Fin (0 + 1) =>
        symClockWeight 0 (H.satake p.2) (i : ℕ))
      = (fun _ : Nat.Primes => fun _ : Fin 1 => (1 : ℂ)) by
      funext p i
      unfold symClockWeight
      rw [show ((0 : ℕ) : ℤ) - 2 * ((i : ℕ) : ℤ) = 0 by omega, zpow_zero]]
  exact bankArithmetic_unit_eq_zeta

/-- **Self-duality of the transported pair at every datum**: the contragredient
coefficients equal the primal coefficients — the inverse weight multiset is the
blockwise clock reversal. -/
theorem repPair_dual_eq_primal (H : HeckeEigenData f) (ρ : List ℕ) (j : ℕ) :
    cpsPolynomialDualCoeff (repSatakePair H ρ) j
      = cpsPolynomialPrimalCoeff (repSatakePair H ρ) j := by
  unfold CriticalLinePhasor.GlobalHelix.cpsPolynomialDualCoeff
    CriticalLinePhasor.GlobalHelix.cpsPolynomialPrimalCoeff
  have hswap : (repSatakePair H ρ).dual
      = fun p => (repSatakePair H ρ).primal p ∘ (repPerm ρ) := by
    funext p x
    exact repWeight_inv_eq H ρ p x
  rw [hswap]
  exact CriticalLinePhasor.GenuineGL2Carrier.radialGlobalSatakeCoeff_comp_equiv
    (repPerm ρ) (repSatakePair H ρ).primal j

/-- The shifted radial coefficients of the datum are the product bank. -/
theorem repCoefficientArithmetic_eq (H : HeckeEigenData f) (ρ : List ℕ) :
    coefficientArithmetic (cpsPolynomialPrimalCoeff (repSatakePair H ρ))
      = (ρ.map (fun r => symrBank H r)).prod :=
  repBank_eq H ρ

/-- **The mechanism at every representation datum, complex chart**: one theta identity
of the prescribed `ρ`-readouts yields the complete package for `L(ρ, s)`. -/
noncomputable def rep_package_of_theta (H : HeckeEigenData f) (ρ : List ℕ)
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout (repSatakePair H ρ) 1 μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          cpsPolynomialFullDual3DTransformedReadout (repSatakePair H ρ) 1 μs (1 / x)) :
    NicePackage ((ρ.map (fun r => symrBank H r)).prod) μs
      (mechB (repSatakePair H ρ)) ε :=
  repCoefficientArithmetic_eq H ρ ▸
    mechanism (repSatakePair H ρ) (repPair_dual_eq_primal H ρ) μs hne hμpos ε hε hrefl

/-- **The mechanism at every representation datum, mixed chart.** -/
noncomputable def rep_mixed_package_of_theta (H : HeckeEigenData f) (ρ : List ℕ)
    (dlt : ℂ) (hdlt : 0 ≤ dlt.re)
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      mixedPrimal3DBankReadout (repSatakePair H ρ) dlt μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          mixedDual3DTransformedReadout (repSatakePair H ρ) dlt μs (1 / x)) :
    MixedNicePackage ((ρ.map (fun r => symrBank H r)).prod) dlt μs
      (mechB (repSatakePair H ρ)) ε :=
  repCoefficientArithmetic_eq H ρ ▸
    mechanismR (repSatakePair H ρ) (repPair_dual_eq_primal H ρ) dlt hdlt μs hne hμpos
      ε hε hrefl

end RepCore

section GeneralPackage

variable {ι : Type*} [Fintype ι]

/-- The typed conclusion at the general Deligne chart: entire continuation, functional
equation, and the `∏Γℝ·∏Γℂ` chart identification on the initial half-plane. -/
structure GeneralNicePackage (a : ArithmeticFunction ℂ) (dlts μs : List ℂ)
    (B : ℝ) (ε : ℂ) where
  lam : ℂ → ℂ
  entire : Differentiable ℂ lam
  FE : ∀ s : ℂ, lam (1 - s) = ε * lam s
  chart : ∀ s : ℂ, B < s.re →
    lam s = (dlts.map fun dlt => Complex.Gammaℝ (s + dlt)).prod *
      ((μs.map fun μ => Complex.Gammaℂ (s + μ)).prod) * LSeries (⇑a) s

/-- Uniqueness of the general continuation. -/
theorem GeneralNicePackage.unique {a : ArithmeticFunction ℂ} {dlts μs : List ℂ}
    {B : ℝ} {ε ε' : ℂ}
    (P : GeneralNicePackage a dlts μs B ε) (Q : GeneralNicePackage a dlts μs B ε') :
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

/-- The empty real-shift list is the complex package. -/
noncomputable def GeneralNicePackage.toNice {a : ArithmeticFunction ℂ} {μs : List ℂ}
    {B : ℝ} {ε : ℂ} (P : GeneralNicePackage a [] μs B ε) : NicePackage a μs B ε where
  lam := P.lam
  entire := P.entire
  FE := P.FE
  chart := fun s hs => by simpa using P.chart s hs

/-- A singleton real-shift list is the mixed package. -/
noncomputable def GeneralNicePackage.toMixed {a : ArithmeticFunction ℂ} {dlt : ℂ}
    {μs : List ℂ} {B : ℝ} {ε : ℂ} (P : GeneralNicePackage a [dlt] μs B ε) :
    MixedNicePackage a dlt μs B ε where
  lam := P.lam
  entire := P.entire
  FE := P.FE
  chart := fun s hs => by simpa using P.chart s hs

/-- **The product law at the general chart**: packages compose — product bank,
concatenated real and complex shift lists, larger half-plane, product root number. -/
noncomputable def GeneralNicePackage.mul {a₁ a₂ : ArithmeticFunction ℂ}
    {dlts₁ dlts₂ μs₁ μs₂ : List ℂ} {B₁ B₂ : ℝ} {ε₁ ε₂ : ℂ}
    (P₁ : GeneralNicePackage a₁ dlts₁ μs₁ B₁ ε₁)
    (P₂ : GeneralNicePackage a₂ dlts₂ μs₂ B₂ ε₂)
    (hsum₁ : ∀ s : ℂ, max B₁ B₂ < s.re → LSeriesSummable (⇑a₁) s)
    (hsum₂ : ∀ s : ℂ, max B₁ B₂ < s.re → LSeriesSummable (⇑a₂) s) :
    GeneralNicePackage (a₁ * a₂) (dlts₁ ++ dlts₂) (μs₁ ++ μs₂)
      (max B₁ B₂) (ε₁ * ε₂) where
  lam := fun s => P₁.lam s * P₂.lam s
  entire := P₁.entire.mul P₂.entire
  FE := fun s => by
    rw [P₁.FE s, P₂.FE s]
    ring
  chart := fun s hs => by
    rw [P₁.chart s (lt_of_le_of_lt (le_max_left _ _) hs),
      P₂.chart s (lt_of_le_of_lt (le_max_right _ _) hs),
      List.map_append, List.prod_append, List.map_append, List.prod_append,
      show (⇑(a₁ * a₂) : ℕ → ℂ) = ↗(a₁ * a₂) from rfl,
      ArithmeticFunction.LSeries_mul' (hsum₁ s hs) (hsum₂ s hs)]
    ring

/-- **THE MECHANISM AT THE GENERAL CHART** — for every admissible self-dual-multiset
bank and every general Deligne chart `∏ⱼΓℝ(s+δⱼ)·∏ᵢΓℂ(s+μᵢ)` with nonnegative shifts:
one pointwise theta identity of the prescribed general readouts yields the complete
analytic package. -/
noncomputable def mechanismG (W : PolynomialSatakeDualPair ι)
    (hdual : ∀ j : ℕ, cpsPolynomialDualCoeff W j = cpsPolynomialPrimalCoeff W j)
    (dlts : List ℂ) (hdlts : ∀ dlt ∈ dlts, 0 ≤ dlt.re)
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      generalPrimal3DBankReadout W dlts μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          generalDual3DTransformedReadout W dlts μs (1 / x)) :
    GeneralNicePackage (coefficientArithmetic (cpsPolynomialPrimalCoeff W)) dlts μs
      (mechB W) ε := by
  refine
    let pair : StrongFEPair ℂ :=
      { f := generalPrimal3DBankReadout W dlts μs
        g := fun x : ℝ => generalDual3DTransformedReadout W dlts μs (1 / x)
        k := 1
        ε := ε
        f₀ := 0
        g₀ := 0
        hf_int := generalPrimal3DBankReadout_locallyIntegrableOn W dlts μs hne
        hg_int := generalDual3DReflectedReadout_locallyIntegrableOn W dlts μs hne
        hk := one_pos
        hε := hε
        h_feq := fun x hx => hrefl x hx
        hf_top := fun q => by
          simpa using generalPrimal3DBankReadout_rapid W dlts μs hne q
        hg_top := fun q => by
          simpa using generalDual3DReflectedReadout_rapid W dlts μs hne q
        hf₀ := rfl
        hg₀ := rfl }
    ?_
  have hmechB0 : (0 : ℝ) ≤ mechB W := by unfold mechB; positivity
  have hconds : ∀ s : ℂ, mechB W < s.re →
      ((∀ dlt ∈ dlts, 0 < (s + dlt).re) ∧ (∀ μ ∈ μs, 0 < (s + μ).re) ∧
        ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < s.re ∧
        ((Fintype.card ι + W.dualExponent : ℕ) : ℝ) + 1 < s.re) := by
    intro s hs
    have h1 : (1 : ℝ) ≤ mechB W := by
      unfold mechB
      have : (0 : ℝ) ≤ ((Fintype.card ι + max W.primalExponent W.dualExponent : ℕ) : ℝ) := by
        positivity
      linarith
    refine ⟨fun dlt hdl => ?_, fun μ hμ => ?_, ?_, ?_⟩
    · have := hdlts dlt hdl
      simp only [Complex.add_re]
      linarith
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
    have hid1 := generalPrimal3D_initialIdentification W dlts μs hne s hc1 hc2 hc3
    have hid2 := generalDual3D_initialIdentification W dlts μs hne s hc1 hc2 hc4
    have hdualdir : dirichlet (cpsPolynomialDualCoeff W) s
        = dirichlet (cpsPolynomialPrimalCoeff W) s := by
      unfold dirichlet
      exact tsum_congr fun m => by rw [hdual m]
    refine (hid2.trans ?_).trans hid1.symm
    unfold generalDualCompletedReadout generalPrimalCompletedReadout
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
        have hid := generalPrimal3D_initialIdentification W dlts μs hne s hc1 hc2 hc3
        refine hid.trans ?_
        unfold generalPrimalCompletedReadout
        have hcoeff : cpsPolynomialPrimalCoeff W
            = fun j => (coefficientArithmetic (cpsPolynomialPrimalCoeff W)) (j + 1) := by
          funext j
          simp [coefficientArithmetic]
        rw [hcoeff, dirichlet_shift_eq_LSeries _ (bankArithmetic_summable W hs)]
        rw [← hcoeff] }

end GeneralPackage

section Instances

/-- **The mechanism at every representation datum, general chart**: one theta identity
of the prescribed general `ρ`-readouts yields the complete package for `L(ρ, s)` at the
full Deligne chart `∏ⱼΓℝ(s+δⱼ)·∏ᵢΓℂ(s+μᵢ)`. -/
noncomputable def rep_general_package_of_theta {k : ℤ} {f : CuspForm 𝒮ℒ k}
    (H : HeckeEigenData f) (ρ : List ℕ)
    (dlts : List ℂ) (hdlts : ∀ dlt ∈ dlts, 0 ≤ dlt.re)
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      generalPrimal3DBankReadout (repSatakePair H ρ) dlts μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          generalDual3DTransformedReadout (repSatakePair H ρ) dlts μs (1 / x)) :
    GeneralNicePackage ((ρ.map (fun r => symrBank H r)).prod) dlts μs
      (mechB (repSatakePair H ρ)) ε :=
  repCoefficientArithmetic_eq H ρ ▸
    mechanismG (repSatakePair H ρ) (repPair_dual_eq_primal H ρ) dlts hdlts μs hne hμpos
      ε hε hrefl

variable {n : ℕ} {f : CuspForm 𝒮ℒ (2 * n : ℤ)}

/-- Readable product form of a two-entry datum bank. -/
theorem repBank_pair (H : HeckeEigenData f) (r₁ r₂ : ℕ) :
    (([r₁, r₂] : List ℕ).map (fun r => symrBank H r)).prod
      = symrBank H r₁ * symrBank H r₂ := by
  simp

/-- Readable product form of a three-entry datum bank. -/
theorem repBank_triple (H : HeckeEigenData f) (r₁ r₂ r₃ : ℕ) :
    (([r₁, r₂, r₃] : List ℕ).map (fun r => symrBank H r)).prod
      = symrBank H r₁ * (symrBank H r₂ * symrBank H r₃) := by
  simp

/-- The full complex chart of the degree-6 tensor datum `[3, 1]`:
the `Sym³` pair and the seed shift. -/
noncomputable def tensor23ChartShifts (n : ℕ) : List ℂ :=
  sym3Shifts n ++ [standardShift n]

theorem tensor23ChartShifts_ne (n : ℕ) : tensor23ChartShifts n ≠ [] := by
  simp [tensor23ChartShifts, sym3Shifts]

theorem tensor23ChartShifts_nonneg (hn : 0 < n) :
    ∀ μ ∈ tensor23ChartShifts n, 0 ≤ μ.re := by
  intro μ hμ
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsh : (0 : ℝ) ≤ standardShiftR n := by
    unfold standardShiftR
    linarith
  simp only [tensor23ChartShifts, sym3Shifts, standardShift, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hμ
  rcases hμ with (rfl | rfl) | rfl <;>
    simp only [Complex.ofReal_re] <;> nlinarith [hsh]

/-- **The degree-6 tensor object from one identity on its joint bank**: rung 4's full
tensor product `std ⊗ Sym²`, directly — one identity at the datum `[3, 1]` and its
complete complex chart, no per-factor input. -/
noncomputable def tensor23_package_of_theta (hn : 0 < n) (H : HeckeEigenData f)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout (repSatakePair H [3, 1]) 1
          (tensor23ChartShifts n) (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          cpsPolynomialFullDual3DTransformedReadout (repSatakePair H [3, 1]) 1
            (tensor23ChartShifts n) (1 / x)) :
    NicePackage (symrBank H 3 * symrBank H 1) (tensor23ChartShifts n)
      (mechB (repSatakePair H [3, 1])) ε :=
  repBank_pair H 3 1 ▸
    rep_package_of_theta H [3, 1] (tensor23ChartShifts n) (tensor23ChartShifts_ne n)
      (tensor23ChartShifts_nonneg hn) ε hε hrefl

/-- The complex half of the degree-9 chart: the `Sym⁴` pair and the `Sym²` shift. -/
noncomputable def tensor33ChartShifts (n : ℕ) : List ℂ :=
  sym4Shifts n ++ [((2 * (n : ℝ) - 1 : ℝ) : ℂ)]

theorem tensor33ChartShifts_ne (n : ℕ) : tensor33ChartShifts n ≠ [] := by
  simp [tensor33ChartShifts, sym4Shifts]

theorem tensor33ChartShifts_nonneg (hn : 0 < n) :
    ∀ μ ∈ tensor33ChartShifts n, 0 ≤ μ.re := by
  intro μ hμ
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [tensor33ChartShifts, sym4Shifts, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hμ
  rcases hμ with (rfl | rfl) | rfl <;>
    simp only [Complex.ofReal_re] <;> linarith

/-- **The degree-9 tensor object from one identity on its joint bank**: rung 5's full
tensor product `Sym² ⊗ Sym²` at the datum `[4, 2, 0]` and its general chart — three
real clocks parametric, the complex shifts pinned to the exponent pairs. -/
noncomputable def tensor33_package_of_theta (hn : 0 < n) (H : HeckeEigenData f)
    (dlts : List ℂ) (hdlts : ∀ dlt ∈ dlts, 0 ≤ dlt.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      generalPrimal3DBankReadout (repSatakePair H [4, 2, 0]) dlts
          (tensor33ChartShifts n) (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          generalDual3DTransformedReadout (repSatakePair H [4, 2, 0]) dlts
            (tensor33ChartShifts n) (1 / x)) :
    GeneralNicePackage (symrBank H 4 * (symrBank H 2 * symrBank H 0)) dlts
      (tensor33ChartShifts n) (mechB (repSatakePair H [4, 2, 0])) ε :=
  repBank_triple H 4 2 0 ▸
    rep_general_package_of_theta H [4, 2, 0] dlts hdlts (tensor33ChartShifts n)
      (tensor33ChartShifts_ne n) (tensor33ChartShifts_nonneg hn) ε hε hrefl

/-- The split base-change chart: the seed shift, doubled. -/
noncomputable def bcSplitChartShifts (n : ℕ) : List ℂ :=
  [standardShift n, standardShift n]

theorem bcSplitChartShifts_ne (n : ℕ) : bcSplitChartShifts n ≠ [] := by
  simp [bcSplitChartShifts]

theorem bcSplitChartShifts_nonneg (hn : 0 < n) :
    ∀ μ ∈ bcSplitChartShifts n, 0 ≤ μ.re := by
  intro μ hμ
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [bcSplitChartShifts, standardShift, List.mem_cons,
    List.not_mem_nil, or_false] at hμ
  rcases hμ with rfl | rfl <;>
    simp only [Complex.ofReal_re] <;> (unfold standardShiftR; linarith)

/-- **The split base-change object from one identity on its joint bank**: rung 1's
doubled datum `[1, 1]` at its doubled seed chart. -/
noncomputable def bc_split_package_of_theta (hn : 0 < n) (H : HeckeEigenData f)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout (repSatakePair H [1, 1]) 1
          (bcSplitChartShifts n) (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          cpsPolynomialFullDual3DTransformedReadout (repSatakePair H [1, 1]) 1
            (bcSplitChartShifts n) (1 / x)) :
    NicePackage (symrBank H 1 * symrBank H 1) (bcSplitChartShifts n)
      (mechB (repSatakePair H [1, 1])) ε :=
  repBank_pair H 1 1 ▸
    rep_package_of_theta H [1, 1] (bcSplitChartShifts n) (bcSplitChartShifts_ne n)
      (bcSplitChartShifts_nonneg hn) ε hε hrefl

end Instances

end CriticalLinePhasor.RepMechanism

#print axioms CriticalLinePhasor.RepMechanism.repPair_dual_eq_primal
#print axioms CriticalLinePhasor.RepMechanism.rep_package_of_theta
#print axioms CriticalLinePhasor.RepMechanism.rep_mixed_package_of_theta
#print axioms CriticalLinePhasor.RepMechanism.GeneralNicePackage.unique
#print axioms CriticalLinePhasor.RepMechanism.GeneralNicePackage.toNice
#print axioms CriticalLinePhasor.RepMechanism.GeneralNicePackage.toMixed
#print axioms CriticalLinePhasor.RepMechanism.GeneralNicePackage.mul
#print axioms CriticalLinePhasor.RepMechanism.mechanismG
#print axioms CriticalLinePhasor.RepMechanism.rep_general_package_of_theta
#print axioms CriticalLinePhasor.RepMechanism.symrBank_zero_eq_zeta
#print axioms CriticalLinePhasor.RepMechanism.tensor23_package_of_theta
#print axioms CriticalLinePhasor.RepMechanism.tensor33_package_of_theta
#print axioms CriticalLinePhasor.RepMechanism.bc_split_package_of_theta
