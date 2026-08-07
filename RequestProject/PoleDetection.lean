import RequestProject.RepMechanism

/-!
# Pole detection: the beyond-endoscopy dichotomy at the carrier

Langlands' beyond-endoscopy principle detects functorial origin through the pole of
`L(s, π, r)` at `s = 1` — the pole appears exactly when `r` contains the trivial
representation.  This file compiles that detection at the level of the mechanism's
packages, for the transported data `ρ = ⊕ᵢ Sym^{rᵢ}` of the seed:

* `repBank_zeta_factor` / `LSeries_repBank_zeta_factor` — a trivial constituent splits
  a `ζ`-factor off the datum bank, and the factor is explicit in the L-readout on the
  joint half-plane (both unconditional);
* `one_le_mechB` — the mechanism threshold clears the edge;
* `trivial_constituent_detection` — **the detection**: a datum containing the trivial
  representation admits no strict theta reflection.  From the strict joint identity the
  mechanism yields an entire completed transform; the `ζ`-constituent forces the simple
  pole at `s = 1` (Mathlib's `riemannZeta_residue_one`); analytic continuation across
  `{Re s > 1}` and a ray limit collide the two — unless the completed erased factor
  vanishes at the edge, which is the named classical input.

Contrapositive register: a datum satisfying the strict (mass-free) reflection has no
trivial constituent.  The masses `f₀, g₀` of the weak reflection pair are the carrier
avatar of the pole: `ζ`-containing objects reflect only with mass terms.
No `axiom`, no `sorry`.
-/

open Finset ArithmeticFunction Complex UpperHalfPlane
open scoped MatrixGroups ArithmeticFunction.zeta LSeries.notation

namespace CriticalLinePhasor.PoleDetection

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.TransportClosure
open CriticalLinePhasor.SymrBank CriticalLinePhasor.SymCubeQuartic
open CriticalLinePhasor.UniformTransport CriticalLinePhasor.SeedStandardRung
open CriticalLinePhasor.GenuineGL2Carrier CriticalLinePhasor.NiceClosure
open CriticalLinePhasor.Sym3ThetaWall CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.ThetaMechanism
open CriticalLinePhasor.RepMechanism
open Set Filter Topology

variable {k : ℤ} {f : CuspForm 𝒮ℒ k}

/-- `ζ` splits off the datum bank at a trivial constituent. -/
theorem repBank_zeta_factor (H : HeckeEigenData f) (ρ : List ℕ) (h0 : 0 ∈ ρ) :
    (ρ.map (fun r => symrBank H r)).prod
      = ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) *
        ((ρ.erase 0).map (fun r => symrBank H r)).prod := by
  have hperm : List.Perm (ρ.map (fun r => symrBank H r))
      ((0 :: ρ.erase 0).map (fun r => symrBank H r)) :=
    (List.perm_cons_erase h0).map _
  rw [hperm.prod_eq, List.map_cons, List.prod_cons, symrBank_zero_eq_zeta]

/-- On the joint half-plane the `ζ`-factor is explicit in the L-readout. -/
theorem LSeries_repBank_zeta_factor (H : HeckeEigenData f) (ρ : List ℕ) (h0 : 0 ∈ ρ)
    {s : ℂ} (hrest : ((repBound H (ρ.erase 0) : ℕ) : ℝ) + 1 < s.re) (hs1 : 1 < s.re) :
    LSeries (⇑((ρ.map (fun r => symrBank H r)).prod)) s
      = riemannZeta s *
        LSeries (⇑(((ρ.erase 0).map (fun r => symrBank H r)).prod)) s := by
  have hcoe : (⇑((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗ζ := by
    funext n; simp
  have hζ : LSeriesSummable
      (⇑((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) s := by
    rw [hcoe]
    exact LSeriesSummable_zeta_iff.mpr hs1
  have hζval : LSeries (⇑((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) s
      = riemannZeta s := by
    rw [hcoe]
    exact LSeries_zeta_eq_riemannZeta hs1
  rw [repBank_zeta_factor H ρ h0,
    show (⇑(((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) *
        ((ρ.erase 0).map (fun r => symrBank H r)).prod) : ℕ → ℂ)
      = ↗(((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) *
        ((ρ.erase 0).map (fun r => symrBank H r)).prod) from rfl,
    ArithmeticFunction.LSeries_mul' hζ (repBank_LSeriesSummable H (ρ.erase 0) hrest),
    hζval]

/-- One is below the mechanism threshold. -/
theorem one_le_mechB {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) :
    (1 : ℝ) ≤ mechB W := by
  unfold mechB
  have : (0 : ℝ) ≤ ((Fintype.card ι + max W.primalExponent W.dualExponent : ℕ) : ℝ) := by
    positivity
  linarith

/-- **Pole detection of the trivial constituent** — the beyond-endoscopy dichotomy at
the carrier: a datum containing the trivial representation admits no strict theta
reflection.  From the strict joint identity the mechanism yields an entire completed
transform; the `ζ`-constituent forces the simple pole at `s = 1`; the two collide
unless the completed erased factor vanishes there. -/
theorem trivial_constituent_detection (H : HeckeEigenData f) (ρ : List ℕ) (h0 : 0 ∈ ρ)
    (dlts : List ℂ) (hdlts : ∀ dlt ∈ dlts, 0 ≤ dlt.re)
    (μs : List ℂ) (hne : μs ≠ []) (hμpos : ∀ μ ∈ μs, 0 ≤ μ.re)
    (ε : ℂ) (hε : ε ≠ 0)
    (hrefl : ∀ x : ℝ, 0 < x →
      generalPrimal3DBankReadout (repSatakePair H ρ) dlts μs (1 / x) =
        (ε * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
          generalDual3DTransformedReadout (repSatakePair H ρ) dlts μs (1 / x))
    {Bq : ℝ} {εq : ℂ}
    (Q : GeneralNicePackage (((ρ.erase 0).map (fun r => symrBank H r)).prod)
      dlts μs Bq εq)
    (hQ1 : Q.lam 1 ≠ 0) : False := by
  have P := rep_general_package_of_theta H ρ dlts hdlts μs hne hμpos ε hε hrefl
  set T : ℝ := max (max (mechB (repSatakePair H ρ)) Bq)
    (((repBound H (ρ.erase 0) : ℕ) : ℝ) + 1) with hTdef
  have hT1 : (1 : ℝ) ≤ T :=
    le_trans (one_le_mechB (repSatakePair H ρ))
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have hEqOn : ∀ s : ℂ, T < s.re → P.lam s = riemannZeta s * Q.lam s := by
    intro s hs
    have hsP : mechB (repSatakePair H ρ) < s.re :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hs
    have hsQ : Bq < s.re :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hs
    have hsrest : ((repBound H (ρ.erase 0) : ℕ) : ℝ) + 1 < s.re :=
      lt_of_le_of_lt (le_max_right _ _) hs
    have hs1 : 1 < s.re := lt_of_lt_of_le (lt_of_le_of_lt hT1 hs) le_rfl
    rw [P.chart s hsP, Q.chart s hsQ, LSeries_repBank_zeta_factor H ρ h0 hsrest hs1]
    ring
  have hUopen : IsOpen {s : ℂ | 1 < s.re} :=
    IsOpen.preimage Complex.continuous_re isOpen_Ioi
  have hUpre : IsPreconnected {s : ℂ | 1 < s.re} :=
    (convex_halfSpace_re_gt 1).isPreconnected
  have hPan : AnalyticOnNhd ℂ P.lam {s : ℂ | 1 < s.re} :=
    P.entire.differentiableOn.analyticOnNhd hUopen
  have hGdiff : DifferentiableOn ℂ (fun s => riemannZeta s * Q.lam s)
      {s : ℂ | 1 < s.re} := by
    intro s hs
    have hs1 : s ≠ 1 := by
      intro hcontra
      rw [hcontra] at hs
      simp only [Set.mem_setOf_eq, Complex.one_re] at hs
      exact lt_irrefl 1 hs
    exact ((differentiableAt_riemannZeta hs1).mul
      (Q.entire s)).differentiableWithinAt
  have hGan : AnalyticOnNhd ℂ (fun s => riemannZeta s * Q.lam s) {s : ℂ | 1 < s.re} :=
    hGdiff.analyticOnNhd hUopen
  have hz₀ : ((T + 1 : ℝ) : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    show (1:ℝ) < ((T + 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    linarith
  have hfg : P.lam =ᶠ[𝓝 ((T + 1 : ℝ) : ℂ)] (fun s => riemannZeta s * Q.lam s) := by
    have hmem : {s : ℂ | T < s.re} ∈ 𝓝 ((T + 1 : ℝ) : ℂ) :=
      (IsOpen.preimage Complex.continuous_re isOpen_Ioi).mem_nhds
        (by show T < ((T + 1 : ℝ) : ℂ).re
            rw [Complex.ofReal_re]
            linarith)
    filter_upwards [hmem] with s hs
    exact hEqOn s hs
  have hEqU : Set.EqOn P.lam (fun s => riemannZeta s * Q.lam s) {s : ℂ | 1 < s.re} :=
    hPan.eqOn_of_preconnected_of_eventuallyEq hGan hUpre hz₀ hfg
  have hA : Tendsto (fun t : ℝ => ((1 + t : ℝ) : ℂ)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => ((1 + t : ℝ) : ℂ)) := by continuity
    have h := hc.tendsto 0
    rw [show ((1 + 0 : ℝ) : ℂ) = 1 by norm_num] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hmemU : ∀ᶠ t in 𝓝[>] (0:ℝ), ((1 + t : ℝ) : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    show (1:ℝ) < ((1 + t : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    have : (0:ℝ) < t := ht
    linarith
  have hL1 : Tendsto (fun t : ℝ => ((((1 + t : ℝ) : ℂ)) - 1) * P.lam ((1 + t : ℝ) : ℂ))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h₁ : Tendsto (fun t : ℝ => ((((1 + t : ℝ) : ℂ)) - 1)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have := hA.sub_const 1
      simpa using this
    have h₂ : Tendsto (fun t : ℝ => P.lam ((1 + t : ℝ) : ℂ)) (𝓝[>] (0:ℝ))
        (𝓝 (P.lam 1)) := (P.entire.continuous.tendsto 1).comp hA
    simpa using h₁.mul h₂
  have hAne : Tendsto (fun t : ℝ => ((1 + t : ℝ) : ℂ)) (𝓝[>] (0:ℝ)) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hA ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0:ℝ) < t := ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcontra
    have := congrArg Complex.re hcontra
    simp only [Complex.ofReal_re, Complex.one_re] at this
    linarith
  have hres : Tendsto (fun t : ℝ =>
      ((((1 + t : ℝ) : ℂ)) - 1) * riemannZeta ((1 + t : ℝ) : ℂ))
      (𝓝[>] (0:ℝ)) (𝓝 1) := riemannZeta_residue_one.comp hAne
  have hQcont : Tendsto (fun t : ℝ => Q.lam ((1 + t : ℝ) : ℂ)) (𝓝[>] (0:ℝ))
      (𝓝 (Q.lam 1)) := (Q.entire.continuous.tendsto 1).comp hA
  have hL2 : Tendsto (fun t : ℝ => ((((1 + t : ℝ) : ℂ)) - 1) *
      (riemannZeta ((1 + t : ℝ) : ℂ) * Q.lam ((1 + t : ℝ) : ℂ)))
      (𝓝[>] (0:ℝ)) (𝓝 (Q.lam 1)) := by
    have := hres.mul hQcont
    rw [one_mul] at this
    refine this.congr fun t => ?_
    ring
  have hL1' : Tendsto (fun t : ℝ => ((((1 + t : ℝ) : ℂ)) - 1) *
      (riemannZeta ((1 + t : ℝ) : ℂ) * Q.lam ((1 + t : ℝ) : ℂ)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    refine hL1.congr' ?_
    filter_upwards [hmemU] with t ht
    rw [hEqU ht]
  exact hQ1 (tendsto_nhds_unique hL1' hL2).symm

end CriticalLinePhasor.PoleDetection

#print axioms CriticalLinePhasor.PoleDetection.repBank_zeta_factor
#print axioms CriticalLinePhasor.PoleDetection.LSeries_repBank_zeta_factor
#print axioms CriticalLinePhasor.PoleDetection.one_le_mechB
#print axioms CriticalLinePhasor.PoleDetection.trivial_constituent_detection
