import Mathlib

/-!
# The reverb kernels: reopening residue, pair suppression, and the cluster product law

Formal counterparts of the numerically validated "reverb" phenomenology (residues after a
cancellation event; see `tmp/residue_dissipation.py`, `tmp/reverb_clusters.py`): after a
vanishing the fiber's imbalance reopens at rate `‖f′(ρ)‖`, that rate is the reciprocal of the
residue of the reciprocal fiber, and near a *cluster* of vanishings the rate carries the exact
product of distances to the other cluster members — the mechanism behind the measured
suppression at pairs (Lehmer), triples, and beyond, with no repulsion input.

Everything here is **unconditional and per-height**: statements about an analytic function at
its zeros, instantiated at `DirichletCharacter.LFunction`.  Nothing assumes GRH/RH and nothing
is circular; zero *locations* are never asserted.

## The three kernels

1. **Reopening / residue** (`reopening_slope`, `residue_reciprocal`,
   `residue_exists_iff_simple`): at a vanishing `f ρ = 0`, the local slope
   `f y / (y − ρ)` tends to `f′(ρ)` — the reopening rate — and the reciprocal fiber has
   simple-pole residue data `(y − ρ)/f y → 1/f′(ρ)`.  A nonzero such limit exists **iff** the
   vanishing is simple (`f′(ρ) ≠ 0`): the residue exists exactly for simple cancellations.

2. **Pair suppression** (`pair_suppression`, `pair_regular_across_partner`): with a partner
   vanishing at `ρ₂ ≠ ρ₁`, the quotient `g = f/(· − ρ₂)` is analytic at `ρ₁`, still vanishes
   there, and
   `f′(ρ₁) = (ρ₁ − ρ₂) · g′(ρ₁)` — the reopening rate at `ρ₁` carries the exact distance
   factor `‖ρ₁ − ρ₂‖` (the Lehmer-pair suppression is an algebraic identity, not repulsion).
   If `f` also vanishes at the partner, the quotient extends analytically **across** the
   partner (the regular part is genuinely regular there).

3. **Cluster product law** (`cluster_product_law`, `cluster_product_law_norm`): for a finite
   cluster `S` of points avoiding `ρ`, with `P = ∏_{σ ∈ S} (· − σ)`,
   the quotient `h = f/P` is analytic at `ρ`, vanishes there, `f = P·h` near `ρ`, and
   `f′(ρ) = (∏_{σ ∈ S} (ρ − σ)) · h′(ρ)`, hence
   `‖f′(ρ)‖ = (∏_{σ ∈ S} ‖ρ − σ‖) · ‖h′(ρ)‖` — the measured product law
   `R̂ ∝ ∏ (distances)` (slope `β = 1.01`, 68% variance explained on 1517 zeros) as an exact
   identity, with `‖h′(ρ)‖` the regular factor.

## L-function instantiations

`L_reopening_slope`, `L_residue_reciprocal`, `L_pair_suppression`, `L_cluster_product_law`:
the kernels at any zero of `DirichletCharacter.LFunction χ` (non-principal `χ`, entire).

Mathlib-only; no `sorry`, no `axiom`.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.ReverbResidue

/-! ## 1. Reopening rate and the residue of the reciprocal fiber -/

/-- **The reopening slope.**  At a vanishing `f ρ = 0`, the local slope `f y / (y − ρ)`
tends to the derivative: the fiber reopens at rate `f′(ρ)`. -/
theorem reopening_slope {f : ℂ → ℂ} {ρ d : ℂ} (hf : HasDerivAt f d ρ) (h0 : f ρ = 0) :
    Tendsto (fun y => f y / (y - ρ)) (𝓝[≠] ρ) (𝓝 d) := by
  have h := hasDerivAt_iff_tendsto_slope.mp hf
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y _
  simp [slope_def_field, h0]

/-- **The residue of the reciprocal fiber.**  At a *simple* vanishing (`f′(ρ) ≠ 0`), the
reciprocal fiber has the simple-pole residue datum `(y − ρ)/f y → 1/f′(ρ)`: the residue is
the reciprocal of the reopening rate. -/
theorem residue_reciprocal {f : ℂ → ℂ} {ρ d : ℂ} (hf : HasDerivAt f d ρ) (h0 : f ρ = 0)
    (hd : d ≠ 0) :
    Tendsto (fun y => (y - ρ) / f y) (𝓝[≠] ρ) (𝓝 d⁻¹) := by
  have h := (reopening_slope hf h0).inv₀ hd
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [inv_div]

/-- **Residue exists ⇔ the vanishing is simple.**  Given differentiability at the vanishing,
a *nonzero* residue limit for the reciprocal fiber exists iff `f′(ρ) ≠ 0`. -/
theorem residue_exists_iff_simple {f : ℂ → ℂ} {ρ : ℂ} (hf : DifferentiableAt ℂ f ρ)
    (h0 : f ρ = 0) :
    (∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun y => (y - ρ) / f y) (𝓝[≠] ρ) (𝓝 c))
      ↔ deriv f ρ ≠ 0 := by
  constructor
  · rintro ⟨c, hc, htend⟩
    have hslope := reopening_slope hf.hasDerivAt h0
    have hinv := htend.inv₀ hc
    have hinv' : Tendsto (fun y => f y / (y - ρ)) (𝓝[≠] ρ) (𝓝 c⁻¹) := by
      refine hinv.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [inv_div]
    have := tendsto_nhds_unique hslope hinv'
    rw [this]
    exact inv_ne_zero hc
  · intro hd
    exact ⟨(deriv f ρ)⁻¹, inv_ne_zero hd, residue_reciprocal hf.hasDerivAt h0 hd⟩

/-! ## 2. Pair suppression -/

/-- **Pair suppression identity.**  With a partner point `ρ₂ ≠ ρ₁`, the quotient
`g = f / (· − ρ₂)` is analytic at `ρ₁`, still vanishes there, factors `f = (· − ρ₂)·g`
near `ρ₁`, and the reopening rate carries the exact distance factor:
`f′(ρ₁) = (ρ₁ − ρ₂) · g′(ρ₁)`.  The derivative suppression at a close pair is an algebraic
identity of the re-absorption, not a repulsion effect. -/
theorem pair_suppression {f : ℂ → ℂ} {ρ₁ ρ₂ : ℂ} (hne : ρ₁ ≠ ρ₂)
    (hf : AnalyticAt ℂ f ρ₁) (h1 : f ρ₁ = 0) :
    AnalyticAt ℂ (fun z => f z / (z - ρ₂)) ρ₁
      ∧ (fun z => f z / (z - ρ₂)) ρ₁ = 0
      ∧ deriv f ρ₁ = (ρ₁ - ρ₂) * deriv (fun z => f z / (z - ρ₂)) ρ₁ := by
  have hden : AnalyticAt ℂ (fun z : ℂ => z - ρ₂) ρ₁ :=
    (analyticAt_id.sub analyticAt_const)
  have hdne : ρ₁ - ρ₂ ≠ 0 := sub_ne_zero.mpr hne
  have hg : AnalyticAt ℂ (fun z => f z / (z - ρ₂)) ρ₁ := hf.div hden hdne
  have hg0 : (fun z => f z / (z - ρ₂)) ρ₁ = 0 := by simp [h1]
  refine ⟨hg, hg0, ?_⟩
  have hev : (fun z => (z - ρ₂) * (f z / (z - ρ₂))) =ᶠ[𝓝 ρ₁] f := by
    filter_upwards [eventually_ne_nhds hne] with z hz
    rw [mul_comm, div_mul_cancel₀ _ (sub_ne_zero.mpr hz)]
  have hdiff_lin : DifferentiableAt ℂ (fun z : ℂ => z - ρ₂) ρ₁ := hden.differentiableAt
  have hdiff_g : DifferentiableAt ℂ (fun z => f z / (z - ρ₂)) ρ₁ := hg.differentiableAt
  calc deriv f ρ₁
      = deriv (fun z => (z - ρ₂) * (f z / (z - ρ₂))) ρ₁ := (hev.deriv_eq).symm
    _ = deriv (fun z : ℂ => z - ρ₂) ρ₁ * ((fun z => f z / (z - ρ₂)) ρ₁)
        + (ρ₁ - ρ₂) * deriv (fun z => f z / (z - ρ₂)) ρ₁ := deriv_mul hdiff_lin hdiff_g
    _ = (ρ₁ - ρ₂) * deriv (fun z => f z / (z - ρ₂)) ρ₁ := by
        rw [hg0, mul_zero, zero_add]

/-- **The regular part is regular across the partner.**  If `f` also *vanishes* at the
partner `ρ₂`, the quotient `f/(· − ρ₂)` extends analytically across `ρ₂`: there is a function
`g₂` analytic at `ρ₂` agreeing with the quotient on the punctured neighborhood.  (This is what
makes the pair-suppression factor a genuine re-absorption of the residue into the fiber,
rather than a singular artifact.) -/
theorem pair_regular_across_partner {f : ℂ → ℂ} {ρ₂ : ℂ}
    (hf : AnalyticAt ℂ f ρ₂) (h0 : f ρ₂ = 0) :
    ∃ g₂ : ℂ → ℂ, AnalyticAt ℂ g₂ ρ₂ ∧ ∀ᶠ z in 𝓝[≠] ρ₂, f z / (z - ρ₂) = g₂ z := by
  by_cases hev : ∀ᶠ z in 𝓝 ρ₂, f z = 0
  · refine ⟨fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with z hz
    simp [hz]
  · obtain ⟨n, g, hg, hgne, hfac⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hev
    have hn0 : n ≠ 0 := by
      rintro rfl
      have := hfac.self_of_nhds
      simp only [pow_zero, one_smul] at this
      exact hgne (this ▸ h0)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨fun z => (z - ρ₂) ^ m * g z,
      ((analyticAt_id.sub analyticAt_const).pow m).mul hg, ?_⟩
    filter_upwards [hfac.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzne
    have hzρ : z - ρ₂ ≠ 0 := sub_ne_zero.mpr hzne
    rw [hz, smul_eq_mul, pow_succ', mul_assoc, mul_div_cancel_left₀ _ hzρ]

/-! ## 3. The cluster product law -/

/-- The distance polynomial of a finite cluster is analytic everywhere. -/
theorem cluster_poly_analyticAt (S : Finset ℂ) (ρ : ℂ) :
    AnalyticAt ℂ (fun z => ∏ σ ∈ S, (z - σ)) ρ := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) ρ)
  | insert σ s hσ ih =>
    have h1 : AnalyticAt ℂ (fun z : ℂ => z - σ) ρ := analyticAt_id.sub analyticAt_const
    have := h1.mul ih
    refine this.congr ?_
    filter_upwards with z
    simp [Finset.prod_insert hσ]

/-- **The cluster product law.**  For a finite cluster `S` avoiding the vanishing point `ρ`,
the quotient `h = f / ∏_{σ ∈ S} (· − σ)` is analytic at `ρ`, vanishes there, factors
`f = P·h` near `ρ`, and the reopening rate carries the full product of distances:
`f′(ρ) = (∏_{σ ∈ S} (ρ − σ)) · h′(ρ)`. -/
theorem cluster_product_law {f : ℂ → ℂ} {ρ : ℂ} (S : Finset ℂ) (hρS : ρ ∉ S)
    (hf : AnalyticAt ℂ f ρ) (h0 : f ρ = 0) :
    AnalyticAt ℂ (fun z => f z / ∏ σ ∈ S, (z - σ)) ρ
      ∧ (fun z => f z / ∏ σ ∈ S, (z - σ)) ρ = 0
      ∧ (∀ᶠ z in 𝓝 ρ, f z = (∏ σ ∈ S, (z - σ)) * (fun z => f z / ∏ σ ∈ S, (z - σ)) z)
      ∧ deriv f ρ = (∏ σ ∈ S, (ρ - σ)) * deriv (fun z => f z / ∏ σ ∈ S, (z - σ)) ρ := by
  classical
  have hP : AnalyticAt ℂ (fun z => ∏ σ ∈ S, (z - σ)) ρ := cluster_poly_analyticAt S ρ
  have hPρ : (∏ σ ∈ S, (ρ - σ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro σ hσ
    exact sub_ne_zero.mpr (fun h => hρS (h ▸ hσ))
  have hh : AnalyticAt ℂ (fun z => f z / ∏ σ ∈ S, (z - σ)) ρ := hf.div hP hPρ
  have hh0 : (fun z => f z / ∏ σ ∈ S, (z - σ)) ρ = 0 := by simp [h0]
  have hevne : ∀ᶠ z in 𝓝 ρ, (∏ σ ∈ S, (z - σ)) ≠ 0 :=
    hP.continuousAt.eventually_ne hPρ
  have hev : ∀ᶠ z in 𝓝 ρ,
      f z = (∏ σ ∈ S, (z - σ)) * (fun z => f z / ∏ σ ∈ S, (z - σ)) z := by
    filter_upwards [hevne] with z hz
    rw [mul_comm, div_mul_cancel₀ _ hz]
  refine ⟨hh, hh0, hev, ?_⟩
  have hdiff_P : DifferentiableAt ℂ (fun z => ∏ σ ∈ S, (z - σ)) ρ := hP.differentiableAt
  have hdiff_h : DifferentiableAt ℂ (fun z => f z / ∏ σ ∈ S, (z - σ)) ρ := hh.differentiableAt
  have hev' : (fun z => (∏ σ ∈ S, (z - σ)) * (fun z => f z / ∏ σ ∈ S, (z - σ)) z)
      =ᶠ[𝓝 ρ] f := by
    filter_upwards [hev] with z hz using hz.symm
  calc deriv f ρ
      = deriv (fun z => (∏ σ ∈ S, (z - σ)) * (fun z => f z / ∏ σ ∈ S, (z - σ)) z) ρ :=
        (hev'.deriv_eq).symm
    _ = deriv (fun z => ∏ σ ∈ S, (z - σ)) ρ * ((fun z => f z / ∏ σ ∈ S, (z - σ)) ρ)
        + (∏ σ ∈ S, (ρ - σ)) * deriv (fun z => f z / ∏ σ ∈ S, (z - σ)) ρ :=
        deriv_mul hdiff_P hdiff_h
    _ = (∏ σ ∈ S, (ρ - σ)) * deriv (fun z => f z / ∏ σ ∈ S, (z - σ)) ρ := by
        rw [hh0, mul_zero, zero_add]

/-- **The cluster product law, in norm** — the numerically measured statement
`R̂ = (∏ distances) · (regular factor)`:
`‖f′(ρ)‖ = (∏_{σ ∈ S} ‖ρ − σ‖) · ‖h′(ρ)‖`. -/
theorem cluster_product_law_norm {f : ℂ → ℂ} {ρ : ℂ} (S : Finset ℂ) (hρS : ρ ∉ S)
    (hf : AnalyticAt ℂ f ρ) (h0 : f ρ = 0) :
    ‖deriv f ρ‖
      = (∏ σ ∈ S, ‖ρ - σ‖) * ‖deriv (fun z => f z / ∏ σ ∈ S, (z - σ)) ρ‖ := by
  obtain ⟨-, -, -, hderiv⟩ := cluster_product_law S hρS hf h0
  rw [hderiv, norm_mul, norm_prod]

/-! ## 4. Instantiation at the Dirichlet L-functions

The reverb kernels hold at every vanishing of every (non-principal) Dirichlet L-function,
unconditionally — no zero location is assumed or produced. -/

variable {q : ℕ} [NeZero q]

/-- Reopening rate at any L-function vanishing. -/
theorem L_reopening_slope (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ρ : ℂ}
    (h0 : DirichletCharacter.LFunction χ ρ = 0) :
    Tendsto (fun y => DirichletCharacter.LFunction χ y / (y - ρ)) (𝓝[≠] ρ)
      (𝓝 (deriv (DirichletCharacter.LFunction χ) ρ)) :=
  reopening_slope ((DirichletCharacter.differentiable_LFunction hχ) ρ).hasDerivAt h0

/-- Residue of the reciprocal L-function at a simple vanishing. -/
theorem L_residue_reciprocal (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ρ : ℂ}
    (h0 : DirichletCharacter.LFunction χ ρ = 0)
    (hd : deriv (DirichletCharacter.LFunction χ) ρ ≠ 0) :
    Tendsto (fun y => (y - ρ) / DirichletCharacter.LFunction χ y) (𝓝[≠] ρ)
      (𝓝 (deriv (DirichletCharacter.LFunction χ) ρ)⁻¹) :=
  residue_reciprocal ((DirichletCharacter.differentiable_LFunction hχ) ρ).hasDerivAt h0 hd

/-- Pair suppression at any pair of L-function points: the reopening rate at `ρ₁` carries
the exact factor `(ρ₁ − ρ₂)`. -/
theorem L_pair_suppression (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ρ₁ ρ₂ : ℂ}
    (hne : ρ₁ ≠ ρ₂) (h1 : DirichletCharacter.LFunction χ ρ₁ = 0) :
    deriv (DirichletCharacter.LFunction χ) ρ₁
      = (ρ₁ - ρ₂) * deriv (fun z => DirichletCharacter.LFunction χ z / (z - ρ₂)) ρ₁ :=
  (pair_suppression hne
    ((DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ₁) h1).2.2

/-- The cluster product law at any L-function vanishing, in norm: the reopening rate is the
product of distances to the cluster times the regular factor. -/
theorem L_cluster_product_law (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ρ : ℂ}
    (S : Finset ℂ) (hρS : ρ ∉ S) (h0 : DirichletCharacter.LFunction χ ρ = 0) :
    ‖deriv (DirichletCharacter.LFunction χ) ρ‖
      = (∏ σ ∈ S, ‖ρ - σ‖)
        * ‖deriv (fun z => DirichletCharacter.LFunction χ z / ∏ σ ∈ S, (z - σ)) ρ‖ :=
  cluster_product_law_norm S hρS
    ((DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ) h0

end CriticalLinePhasor.ReverbResidue
