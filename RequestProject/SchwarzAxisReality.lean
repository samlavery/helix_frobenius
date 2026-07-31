import RequestProject.TransferContinuation
import RequestProject.CPSCompletedVerticalIntegrable

/-!
# Schwarz pairing of the transfer continuations and the axis-reality converter

The Poisson-free reduction of the per-rung registration wall (gate 2): given the transfer
exponent, the whole completed Mellin functional equation collapses to ONE real condition on
the fixed locus of the reflection — the standing wave.  This file compiles the two bricks:

1. **Schwarz pairing of the two transfer continuations** (`transfer_schwarz_pairing`): the
   Abel-summed continuation of the conjugated coefficients is *termwise* the Schwarz
   reflection `conj ∘ F ∘ conj` of the primal continuation, on all of `ℂ`
   (`abelContinuation_conj`), and `dual_primitive_norm` hands the dual continuation the
   same exponent for free.  No automorphy, no functional equation, no Poisson summation.

2. **Axis reality ⟹ functional equation** (`fe_of_axisReality`): for an entire readout,
   the FE-on-axis shape `G = ε·conj G` on `Re s = k/2` propagates by the identity theorem
   to the full reflection identity `G(k−s) = ε·conj(G(s̄))` on all of `ℂ`.  Reality is not
   weaker than the FE — it *is* the FE on the natural locus.  `axis_eq_conj_of_standing`
   converts the square-root form (`ε^{-1/2}·G` real on the axis, the standing wave) into
   the consumed shape.

3. **The coupling converter from one real condition**
   (`BankThetaProfileCoupling3D.ofAxisReality`): the FE input of `ofMellinFE''` is replaced
   by two structural inputs (entirety of the completed primal Mellin readout, Schwarz
   pairing of the two completed readouts) and ONE arithmetic input — the standing wave on
   the weld axis.  The registration's arithmetic content is thereby exactly the axis
   reality of `mellin`-primal; nothing about the reflected side beyond the pairing.

Scope: this file does not discharge any rung's standing wave — it relocates the
per-rung obligation onto the axis, where the three certifiers (carrier-lattice
self-duality, seed crossing lattice, pure extinction) attack.
-/

open Finset Filter Complex Topology ComplexConjugate

namespace TransferContinuation

/-! ## Brick 1 — the Schwarz pairing of the two transfer continuations -/

/-- The Abel-summed transfer continuation: the explicit limit function of
`transfer_analytic`, named so the primal and dual continuations can be *compared*. -/
noncomputable def abelContinuation (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  0 - ∑' i : ℕ,
    (((i + 1 + 1 : ℕ) : ℂ) ^ (-s) - ((i + 1 : ℕ) : ℂ) ^ (-s)) * (∑ k ∈ range (i + 1), a k)

/-- The Dirichlet partial sums converge to the Abel continuation on `Re s > θ`
(restatement of `transfer_tendsto_tsum` at the named limit). -/
theorem tendsto_abelContinuation (a : ℕ → ℂ) (C θ : ℝ) (hθ : 0 ≤ θ)
    (hA : ∀ n : ℕ, ‖∑ k ∈ range n, a k‖ ≤ C * (n : ℝ) ^ θ)
    (s : ℂ) (hs : θ < s.re) :
    Tendsto (fun N => ∑ n ∈ range N, a n * ((n + 1 : ℕ) : ℂ) ^ (-s)) atTop
      (𝓝 (abelContinuation a s)) :=
  transfer_tendsto_tsum a C θ hθ hA s hs

/-- The Abel continuation is analytic on the half-plane `Re s > θ` (the `transfer_analytic`
witness is this function, by uniqueness of limits). -/
theorem abelContinuation_differentiableOn (a : ℕ → ℂ) (C θ : ℝ) (hθ : 0 ≤ θ)
    (hA : ∀ n : ℕ, ‖∑ k ∈ range n, a k‖ ≤ C * (n : ℝ) ^ θ) :
    DifferentiableOn ℂ (abelContinuation a) {s : ℂ | θ < s.re} := by
  obtain ⟨F, hFdiff, hFlim⟩ := transfer_analytic a C θ hθ hA
  refine hFdiff.congr fun s hs => ?_
  exact tendsto_nhds_unique (tendsto_abelContinuation a C θ hθ hA s hs) (hFlim s hs)

/-- The unitary dual inherits the primitive bound verbatim (`dual_primitive_norm` made
consumable): same constant, same exponent. -/
theorem dual_primitive_bound {a : ℕ → ℂ} {C θ : ℝ}
    (hA : ∀ n : ℕ, ‖∑ k ∈ range n, a k‖ ≤ C * (n : ℝ) ^ θ) (n : ℕ) :
    ‖∑ k ∈ range n, conj (a k)‖ ≤ C * (n : ℝ) ^ θ := by
  rw [dual_primitive_norm]; exact hA n

/-- Conjugation swaps the natural-base complex power across the reflection:
`conj (n^(-s̄)) = n^(-s)`. -/
lemma conj_natCast_cpow_neg_conj (n : ℕ) (s : ℂ) :
    conj (((n : ℕ) : ℂ) ^ (-(conj s))) = ((n : ℕ) : ℂ) ^ (-s) := by
  have harg : ((n : ℕ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  rw [show -(conj s) = conj (-s) from (map_neg (starRingEnd ℂ) s).symm,
    Complex.cpow_conj _ _ harg, Complex.conj_conj, map_natCast]

/-- **The Schwarz pairing is termwise-exact on all of `ℂ`**: the Abel continuation of the
conjugated coefficients is the Schwarz reflection of the primal continuation.  No identity
theorem is consumed — the identity holds tsum-by-tsum. -/
theorem abelContinuation_conj (a : ℕ → ℂ) (s : ℂ) :
    abelContinuation (fun n => conj (a n)) s = conj (abelContinuation a (conj s)) := by
  unfold abelContinuation
  rw [map_sub, map_zero]
  congr 1
  calc ∑' i : ℕ,
        (((i + 1 + 1 : ℕ) : ℂ) ^ (-s) - ((i + 1 : ℕ) : ℂ) ^ (-s)) *
          (∑ k ∈ range (i + 1), conj (a k))
      = ∑' i : ℕ, conj
          ((((i + 1 + 1 : ℕ) : ℂ) ^ (-(conj s)) - ((i + 1 : ℕ) : ℂ) ^ (-(conj s))) *
            (∑ k ∈ range (i + 1), a k)) := by
        refine tsum_congr fun i => ?_
        rw [map_mul, map_sub, map_sum, conj_natCast_cpow_neg_conj, conj_natCast_cpow_neg_conj]
    _ = conj (∑' i : ℕ,
          ((((i + 1 + 1 : ℕ) : ℂ) ^ (-(conj s)) - ((i + 1 : ℕ) : ℂ) ^ (-(conj s))) *
            (∑ k ∈ range (i + 1), a k))) := tsum_star.symm

/-- **Schwarz pairing of the two transfer continuations** (`lem:transfer`'s dual half made
free): under one primitive bound, both continuations are analytic on the common half-plane
`Re s > θ` — the dual via `dual_primitive_norm`, no separate input — and the dual *is* the
Schwarz reflection `conj ∘ F ∘ conj` of the primal, everywhere. -/
theorem transfer_schwarz_pairing (a : ℕ → ℂ) (C θ : ℝ) (hθ : 0 ≤ θ)
    (hA : ∀ n : ℕ, ‖∑ k ∈ range n, a k‖ ≤ C * (n : ℝ) ^ θ) :
    DifferentiableOn ℂ (abelContinuation a) {s : ℂ | θ < s.re} ∧
    DifferentiableOn ℂ (abelContinuation fun n => conj (a n)) {s : ℂ | θ < s.re} ∧
    ∀ s : ℂ, abelContinuation (fun n => conj (a n)) s = conj (abelContinuation a (conj s)) :=
  ⟨abelContinuation_differentiableOn a C θ hθ hA,
   abelContinuation_differentiableOn _ C θ hθ (dual_primitive_bound hA),
   fun s => abelContinuation_conj a s⟩

end TransferContinuation

namespace CriticalLinePhasor.AxisReality

/-! ## Brick 2 — axis reality is the functional equation -/

/-- Schwarz reflection preserves entirety: if `f` is entire, so is `s ↦ conj (f (conj s))`. -/
theorem differentiable_conj_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ fun s => conj (f (conj s)) := by
  intro z
  have h := (hf (conj z)).conj_conj
  rw [Complex.conj_conj] at h
  exact h

/-- The square-root-free standing wave: if `conj δ · G` is real on the axis, with `δ² = ε`
and `‖δ‖ = 1` (so `δ = ε^{1/2}` up to sign), then `G = ε · conj G` on the axis — the shape
consumed by `fe_of_axisReality`. -/
theorem axis_eq_conj_of_standing {G : ℂ → ℂ} {k : ℝ} {ε δ : ℂ}
    (hδε : δ * δ = ε) (hδ : ‖δ‖ = 1)
    (hreal : ∀ t : ℝ, (conj δ * G ((k : ℂ) / 2 + (t : ℂ) * I)).im = 0) :
    ∀ t : ℝ, G ((k : ℂ) / 2 + (t : ℂ) * I)
      = ε * conj (G ((k : ℂ) / 2 + (t : ℂ) * I)) := by
  intro t
  set w := G ((k : ℂ) / 2 + (t : ℂ) * I) with hw
  have hc : conj (conj δ * w) = conj δ * w := Complex.conj_eq_iff_im.mpr (hreal t)
  rw [map_mul, Complex.conj_conj] at hc
  have hone : δ * conj δ = 1 := by
    rw [Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, hδ, one_pow]
  calc w = (δ * conj δ) * w := by rw [hone, one_mul]
    _ = δ * (conj δ * w) := by ring
    _ = δ * (δ * conj w) := by rw [← hc]
    _ = ε * conj w := by rw [← hδε]; ring

/-- **Axis reality is the functional equation.**  For an entire readout `G`, the FE-on-axis
shape `G = ε·conj G` on the weld axis `Re s = k/2` propagates, by the identity theorem on
the connected plane, to the full reflection identity `G(k−s) = ε·conj(G(s̄))` — the
completed Mellin FE in Schwarz-paired form.  One real condition, nothing else. -/
theorem fe_of_axisReality {G : ℂ → ℂ} (k : ℝ) (ε : ℂ)
    (hG : Differentiable ℂ G)
    (haxis : ∀ t : ℝ, G ((k : ℂ) / 2 + (t : ℂ) * I)
      = ε * conj (G ((k : ℂ) / 2 + (t : ℂ) * I))) :
    ∀ s : ℂ, G ((k : ℂ) - s) = ε * conj (G (conj s)) := by
  have hf : Differentiable ℂ fun s : ℂ => G ((k : ℂ) - s) :=
    hG.comp ((differentiable_const ((k : ℂ))).sub differentiable_id)
  have hg : Differentiable ℂ fun s : ℂ => ε * conj (G (conj s)) :=
    (differentiable_conj_conj hG).const_mul ε
  -- the two entire functions agree at every axis point
  have haxis' : ∀ t : ℝ, G ((k : ℂ) - ((k : ℂ) / 2 + (t : ℂ) * I))
      = ε * conj (G (conj ((k : ℂ) / 2 + (t : ℂ) * I))) := by
    intro t
    have h1 : (k : ℂ) - ((k : ℂ) / 2 + (t : ℂ) * I)
        = (k : ℂ) / 2 + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    have h2 : conj ((k : ℂ) / 2 + (t : ℂ) * I)
        = (k : ℂ) / 2 + ((-t : ℝ) : ℂ) * I := by
      have hsplit : (k : ℂ) / 2 + (t : ℂ) * I = ((k / 2 : ℝ) : ℂ) + (t : ℂ) * I := by
        push_cast; ring
      rw [hsplit, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [h1, h2]
    exact haxis (-t)
  -- the axis accumulates at its own center
  have hfreq : ∃ᶠ z in 𝓝[≠] ((k : ℂ) / 2),
      G ((k : ℂ) - z) = ε * conj (G (conj z)) := by
    have hmem : ∀ n : ℕ,
        ((k : ℂ) / 2 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) ≠ (k : ℂ) / 2 := by
      intro n h
      have h' : (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) * I = 0 := by
        have hsub := congrArg (fun z => z - (k : ℂ) / 2) h
        simpa using hsub
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact Complex.ofReal_ne_zero.mpr (by positivity) h''
      · exact Complex.I_ne_zero h''
    have hlim : Tendsto
        (fun n : ℕ => (k : ℂ) / 2 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I)
        atTop (𝓝[≠] ((k : ℂ) / 2)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h1 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
            (𝓝 ((0 : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto _).comp h0
        have h2 := (h1.mul_const I).const_add ((k : ℂ) / 2)
        simpa using h2
      · exact Eventually.of_forall fun n => hmem n
    exact hlim.frequently (Frequently.of_forall fun n => haxis' _)
  have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    (hf.differentiableOn.analyticOnNhd isOpen_univ)
    (hg.differentiableOn.analyticOnNhd isOpen_univ)
    isPreconnected_univ (Set.mem_univ ((k : ℂ) / 2)) hfreq
  exact fun s => hEq (Set.mem_univ s)

end CriticalLinePhasor.AxisReality

/-! ## Brick 3 — the coupling converter from one real condition -/

namespace CriticalLinePhasor.GlobalHelix

open CriticalLinePhasor.ThreeDConverse CriticalLinePhasor.CarrierTheta MeasureTheory

/-- **The coupling converter from the standing wave.**  The completed-Mellin FE input of
`ofMellinFE''` is replaced by: two *structural* inputs — entirety of the literal primal
Mellin readout (`hmell`) and the Schwarz pairing of the two completed readouts (`hpair`,
free for the Dirichlet layer by `TransferContinuation.abelContinuation_conj`; the Γ- and
conductor factors are Schwarz-symmetric per rung) — and ONE *arithmetic* input: the
standing wave `haxis`, reality of the primal readout on the weld axis in FE-on-axis form.
The identity theorem (`fe_of_axisReality`) rebuilds the full FE, and the vertical
integrabilities remain discharged by the house Stirling bound.  Per-rung arithmetic
obligation: one real condition on the fixed locus of `J`. -/
noncomputable def BankThetaProfileCoupling3D.ofAxisReality
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ [])
    (hgc : ContinuousOn (conductorScaledCompletionKernelLog C μs) (Set.Ioi 0))
    (k σ : ℝ) (ε : ℂ) (hε : ε ≠ 0) (hk : 0 < k)
    (hσμ : ∀ μ ∈ μs, 0 < ((σ : ℂ) + μ).re)
    (hσ : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < σ)
    (hmell : Differentiable ℂ (mellin (cpsPolynomialFullPrimal3DBankReadout W C μs)))
    (hpair : ∀ s : ℂ,
      mellin (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)) s
        = conj (mellin (cpsPolynomialFullPrimal3DBankReadout W C μs) (conj s)))
    (haxis : ∀ t : ℝ,
      mellin (cpsPolynomialFullPrimal3DBankReadout W C μs) ((k : ℂ) / 2 + (t : ℂ) * Complex.I)
        = ε * conj (mellin (cpsPolynomialFullPrimal3DBankReadout W C μs)
            ((k : ℂ) / 2 + (t : ℂ) * Complex.I)))
    (hrefConv : MellinConvergent
      (reflectedTheta k ε (fun x : ℝ =>
        cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x))) (σ : ℂ)) :
    BankThetaProfileCoupling3D W C μs :=
  BankThetaProfileCoupling3D.ofMellinFE'' W C hC μs hne hgc k σ ε hε hk hσμ hσ
    (fun s => by
      rw [hpair s, smul_eq_mul]
      exact CriticalLinePhasor.AxisReality.fe_of_axisReality k ε hmell haxis s)
    hrefConv

end CriticalLinePhasor.GlobalHelix

#print axioms TransferContinuation.transfer_schwarz_pairing
#print axioms TransferContinuation.abelContinuation_conj
#print axioms CriticalLinePhasor.AxisReality.axis_eq_conj_of_standing
#print axioms CriticalLinePhasor.AxisReality.fe_of_axisReality
#print axioms CriticalLinePhasor.GlobalHelix.BankThetaProfileCoupling3D.ofAxisReality
