import RequestProject.CPSEdgePoleTolerantEngine3D

/-!
# The edge argument needs differentiability at one point, not entirety

`h_feq` — the arithmetic theta reflection `θ_a(1/x) = ε·x^k·θ_{a∨}(x)` — enters the CPS tower for
exactly one purpose: it builds the `StrongFEPair` whose Mellin transform `Λ` is **entire**.  So
every consumer that asks the tower for `Differentiable ℂ C` is, transitively, asking for the
functional equation, i.e. for automorphy of `Sym^r`.

This file audits how much of that the edge argument actually consumes, and the answer is: almost
none of it.  Reading the proof of `edge_nonvanishing_of_simplePole_product_bound`:

* the factorization `C s = (s - ρ) · dslope C ρ s` is `sub_smul_dslope` together with `C ρ = 0`,
  and `sub_smul_dslope` holds for an arbitrary function — no differentiability at all;
* the only limit taken in the `C` factor is **at `ρ` itself**, and
  `continuousAt_dslope_same` says `ContinuousAt (dslope C ρ) ρ ↔ DifferentiableAt ℂ C ρ`.

So the engine runs on `DifferentiableAt ℂ C (1 + iy)` — differentiability at the single boundary
point being tested.  Entirety, the functional equation, and hence `h_feq` are not used.

This is the "another route": the analytic input the edge needs is local, and the global
reflection was only ever a way of manufacturing it.  What remains genuinely global in the wider
chain is stated honestly in the closing remark below — this file does not claim to remove
`h_feq` from the whole program, only from the edge argument.
-/

open Filter Topology Complex

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.RectResidue

variable {m : ℕ}

/-- **The edge-nonvanishing engine, localized.**  Only `DifferentiableAt ℂ C ρ` is used: the
factorization through `dslope` is unconditional, and the sole limit in the `C` factor is taken at
`ρ`.  No entirety, no functional equation. -/
theorem edge_nonvanishing_of_simplePole_product_bound_local
    {C D : ℂ → ℂ} {y K K₂ : ℝ}
    (hC : DifferentiableAt ℂ C (1 + y * I))
    (hDpole : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D (σ : ℂ)‖ * (σ - 1) ≤ K)
    (hDtwist : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D ((σ : ℂ) + 2 * y * I)‖ ≤ K₂)
    (hprod : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      1 ≤ ‖riemannZeta (σ : ℂ)‖ ^ 2 * ‖D (σ : ℂ)‖
        * ‖C ((σ : ℂ) + y * I)‖ ^ 4 * ‖D ((σ : ℂ) + 2 * y * I)‖) :
    C (1 + y * I) ≠ 0 := by
  intro hzero
  -- the factorization is unconditional
  have hfac : ∀ s : ℂ, C s = (s - (1 + y * I)) * dslope C (1 + y * I) s := by
    intro s
    have h := sub_smul_dslope C (1 + y * I) s
    rw [smul_eq_mul] at h
    rw [h, hzero, sub_zero]
  -- the only analytic input: continuity of the difference quotient at the tested point
  have hdsl : ContinuousAt (dslope C (1 + y * I)) (1 + y * I) :=
    continuousAt_dslope_same.mpr hC
  have hK₂ : 0 ≤ K₂ :=
    le_trans (norm_nonneg _) (hDtwist (3 / 2) (by norm_num) (by norm_num))
  have hK : 0 ≤ K :=
    le_trans (by positivity) (hDpole (3 / 2) (by norm_num) (by norm_num))
  have hkey : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      ‖riemannZeta (σ : ℂ)‖ ^ 2 * ‖D (σ : ℂ)‖
          * ‖C ((σ : ℂ) + y * I)‖ ^ 4 * ‖D ((σ : ℂ) + 2 * y * I)‖ ≤
        (‖((σ : ℂ) - 1) * riemannZeta (σ : ℂ)‖ ^ 2 *
          ‖dslope C (1 + y * I) ((σ : ℂ) + y * I)‖ ^ 4 * K * K₂) * (σ - 1) := by
    intro σ h1 h2
    have ht : (0 : ℝ) < σ - 1 := by linarith
    have hCval : ‖C ((σ : ℂ) + y * I)‖ =
        (σ - 1) * ‖dslope C (1 + y * I) ((σ : ℂ) + y * I)‖ := by
      rw [hfac ((σ : ℂ) + y * I), norm_mul]
      congr 1
      rw [show ((σ : ℂ) + y * I) - (1 + y * I) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hzeta : ‖((σ : ℂ) - 1) * riemannZeta (σ : ℂ)‖ =
        (σ - 1) * ‖riemannZeta (σ : ℂ)‖ := by
      rw [norm_mul]
      congr 1
      rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hstep : (‖D (σ : ℂ)‖ * (σ - 1)) * ‖D ((σ : ℂ) + 2 * y * I)‖ ≤ K * K₂ :=
      mul_le_mul (hDpole σ h1 h2) (hDtwist σ h1 h2) (norm_nonneg _) hK
    have hfac2 : (0 : ℝ) ≤ ‖riemannZeta (σ : ℂ)‖ ^ 2 *
        ‖dslope C (1 + y * I) ((σ : ℂ) + y * I)‖ ^ 4 * (σ - 1) ^ 3 := by positivity
    rw [hCval, hzeta]
    calc
      ‖riemannZeta (σ : ℂ)‖ ^ 2 * ‖D (σ : ℂ)‖
            * ((σ - 1) * ‖dslope C (1 + y * I) ((σ : ℂ) + y * I)‖) ^ 4
            * ‖D ((σ : ℂ) + 2 * y * I)‖ =
          (‖riemannZeta (σ : ℂ)‖ ^ 2 *
            ‖dslope C (1 + y * I) ((σ : ℂ) + y * I)‖ ^ 4 * (σ - 1) ^ 3) *
            ((‖D (σ : ℂ)‖ * (σ - 1)) * ‖D ((σ : ℂ) + 2 * y * I)‖) := by ring
      _ ≤ (‖riemannZeta (σ : ℂ)‖ ^ 2 *
            ‖dslope C (1 + y * I) ((σ : ℂ) + y * I)‖ ^ 4 * (σ - 1) ^ 3) * (K * K₂) :=
          mul_le_mul_of_nonneg_left hstep hfac2
      _ = ((σ - 1) * ‖riemannZeta (σ : ℂ)‖) ^ 2 *
            ‖dslope C (1 + y * I) ((σ : ℂ) + y * I)‖ ^ 4 * K * K₂ * (σ - 1) := by ring
  have hlim : Tendsto (fun σ : ℝ =>
      (‖((σ : ℂ) - 1) * riemannZeta (σ : ℂ)‖ ^ 2 *
        ‖dslope C (1 + y * I) ((σ : ℂ) + y * I)‖ ^ 4 * K * K₂) * (σ - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hζ : Tendsto (fun σ : ℝ => ‖((σ : ℂ) - 1) * riemannZeta (σ : ℂ)‖ ^ 2)
        (𝓝[>] (1 : ℝ)) (𝓝 1) := by
      have h := (zeta_residue_real_approach.norm).pow 2
      simpa using h
    have hgt : Tendsto (fun σ : ℝ => ‖dslope C (1 + y * I) ((σ : ℂ) + y * I)‖ ^ 4)
        (𝓝[>] (1 : ℝ)) (𝓝 (‖dslope C (1 + y * I) (1 + y * I)‖ ^ 4)) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      have hmap : Tendsto (fun σ : ℝ => ((σ : ℂ) + y * I)) (𝓝 (1 : ℝ))
          (𝓝 (1 + y * I)) := by
        have : Continuous fun σ : ℝ => ((σ : ℂ) + y * I) :=
          Complex.continuous_ofReal.add continuous_const
        simpa using this.tendsto 1
      simpa [Function.comp] using ((Tendsto.comp hdsl hmap).norm).pow 4
    have hsub : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      have hc : Continuous fun σ : ℝ => σ - 1 := by continuity
      have := hc.tendsto 1
      simpa using this
    have hall :=
      ((((hζ.mul hgt).mul (tendsto_const_nhds (x := K) (f := 𝓝[>] (1 : ℝ)))).mul
        (tendsto_const_nhds (x := K₂) (f := 𝓝[>] (1 : ℝ)))).mul hsub)
    simpa using hall
  have hev : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      1 ≤ (‖((σ : ℂ) - 1) * riemannZeta (σ : ℂ)‖ ^ 2 *
        ‖dslope C (1 + y * I) ((σ : ℂ) + y * I)‖ ^ 4 * K * K₂) * (σ - 1) := by
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with σ hσ
    exact le_trans (hprod σ hσ.1 hσ.2) (hkey σ hσ.1 hσ.2)
  have hlt : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      (‖((σ : ℂ) - 1) * riemannZeta (σ : ℂ)‖ ^ 2 *
        ‖dslope C (1 + y * I) ((σ : ℂ) + y * I)‖ ^ 4 * K * K₂) * (σ - 1) < 1 :=
    hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨σ, hA, hB⟩ := (hev.and hlt).exists
  linarith

/-- The bank-level face of the localized engine: the candidate is asked only for differentiability
at the boundary point under test. -/
theorem bank_edge_nonvanishing_of_simplePole_local (α : Nat.Primes → Fin m → ℂ)
    (hα : ∀ p i, ‖α p i‖ = 1)
    (hreal : ∀ (p : Nat.Primes) (n : ℕ), (∑ i, α p i ^ n).im = 0)
    {C D : ℂ → ℂ} {y K K₂ : ℝ}
    (hC : DifferentiableAt ℂ C (1 + y * I))
    (hCeq : Set.EqOn C (bankEulerReadout α) {s : ℂ | 1 < s.re})
    (hDeq : Set.EqOn D (bankEulerReadout (pairBank α)) {s : ℂ | 1 < s.re})
    (hDpole : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D (σ : ℂ)‖ * (σ - 1) ≤ K)
    (hDtwist : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D ((σ : ℂ) + 2 * y * I)‖ ≤ K₂) :
    C (1 + y * I) ≠ 0 := by
  apply edge_nonvanishing_of_simplePole_product_bound_local hC hDpole hDtwist
  intro σ hσ _
  obtain ⟨h₀, h₁, h₂⟩ := one_lt_re_triple hσ y
  rw [hCeq (Set.mem_setOf.mpr h₁), hDeq (Set.mem_setOf.mpr h₀),
    hDeq (Set.mem_setOf.mpr h₂)]
  exact norm_bank_product_ge_one α hα hreal hσ y

/-- The original entirety-based engine is the special case, so nothing downstream is lost. -/
theorem edge_nonvanishing_of_simplePole_product_bound_of_entire
    {C D : ℂ → ℂ} {y K K₂ : ℝ}
    (hC : Differentiable ℂ C)
    (hDpole : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D (σ : ℂ)‖ * (σ - 1) ≤ K)
    (hDtwist : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D ((σ : ℂ) + 2 * y * I)‖ ≤ K₂)
    (hprod : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      1 ≤ ‖riemannZeta (σ : ℂ)‖ ^ 2 * ‖D (σ : ℂ)‖
        * ‖C ((σ : ℂ) + y * I)‖ ^ 4 * ‖D ((σ : ℂ) + 2 * y * I)‖) :
    C (1 + y * I) ≠ 0 :=
  edge_nonvanishing_of_simplePole_product_bound_local (hC _) hDpole hDtwist hprod

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.edge_nonvanishing_of_simplePole_product_bound_local
#print axioms CriticalLinePhasor.ThreeDConverse.bank_edge_nonvanishing_of_simplePole_local
#print axioms CriticalLinePhasor.ThreeDConverse.edge_nonvanishing_of_simplePole_product_bound_of_entire
