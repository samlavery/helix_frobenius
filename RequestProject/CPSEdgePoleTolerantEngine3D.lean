import RequestProject.CPSEdgeProductAssembly3D

/-!
# The edge-nonvanishing engine with a genuine polar companion

`CPSEdgeNonvanishingEngine3D.edge_nonvanishing_of_product_bound` asks its companion `D` to be
continuous on all of `ℂ`.  That hypothesis is not inhabited by the object the Mertens bound
actually supplies.  The companion is pinned by `Set.EqOn D (bankEulerReadout (pairBank α))`
on `{1 < re s}`, and for the rank-`r` symmetric-power bank `α p i = a ^ (r - 2i)` the pair bank
`{α p i * α p k}` contains the root `1` once for every pair with `i + k = r`; its Euler readout
therefore diverges along `σ → 1⁺`.  A function continuous at `1` cannot agree with it on the
open half-plane.  So the continuous-companion form is vacuous exactly where it was meant to fire.

The order count does not need a pole-free companion.  Writing `t = σ - 1`, a zero of order `m`
of `C` at `1 + iy` contributes `t ^ (4 * m)` through the fourth power, `ζ ^ 2` contributes
`t ^ (-2)`, and a companion with at worst a simple pole contributes `t ^ (-1)`:

  `‖ζ(σ)‖² ‖D(σ)‖ ‖C(σ + iy)‖⁴ ‖D(σ + 2iy)‖  =  O(t ^ (4 * m - 3))`,

which still tends to `0` for every `m ≥ 1` and so still contradicts the Mertens lower bound `1`.
This file runs that count.  The polar hypothesis is stated multiplicatively,
`‖D σ‖ * (σ - 1) ≤ K`, so it is satisfied by a simple pole, by a removable singularity, and by
any bounded companion; the companion at the doubled ordinate is asked only to be bounded, which
is what holds off the pole, i.e. for `y ≠ 0`.

`edge_nonvanishing_of_simplePole_product_bound` is the engine and
`bank_edge_nonvanishing_of_simplePole` is its bank-level face; the latter consumes exactly the
Mertens product bound already compiled in `CPSEdgeProductAssembly3D`.
-/

open Filter Topology Complex

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.RectResidue

variable {m : ℕ}

/-- **The pole-tolerant edge-nonvanishing engine.**  `C` entire, a companion `D` whose norm on
the real approach segment is dominated by a simple pole, bounded at the doubled ordinate, and the
Mertens product bound on `(1, 2]` force `C (1 + iy) ≠ 0`.  A zero of order `m ≥ 1` makes the
assembled product `O((σ - 1) ^ (4 * m - 3))`, hence `O(σ - 1)`, which cannot stay `≥ 1`. -/
theorem edge_nonvanishing_of_simplePole_product_bound
    {C D : ℂ → ℂ} {y K K₂ : ℝ}
    (hC : Differentiable ℂ C)
    (hDpole : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D (σ : ℂ)‖ * (σ - 1) ≤ K)
    (hDtwist : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D ((σ : ℂ) + 2 * y * I)‖ ≤ K₂)
    (hprod : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      1 ≤ ‖riemannZeta (σ : ℂ)‖ ^ 2 * ‖D (σ : ℂ)‖
        * ‖C ((σ : ℂ) + y * I)‖ ^ 4 * ‖D ((σ : ℂ) + 2 * y * I)‖) :
    C (1 + y * I) ≠ 0 := by
  intro hzero
  have hg : Differentiable ℂ (dslope C (1 + y * I)) :=
    differentiable_dslope_of_entire hC _
  have hfac : ∀ s : ℂ, C s = (s - (1 + y * I)) * dslope C (1 + y * I) s := by
    intro s
    have h := sub_smul_dslope C (1 + y * I) s
    rw [smul_eq_mul] at h
    rw [h, hzero, sub_zero]
  have hK₂ : 0 ≤ K₂ :=
    le_trans (norm_nonneg _) (hDtwist (3 / 2) (by norm_num) (by norm_num))
  have hK : 0 ≤ K :=
    le_trans (by positivity) (hDpole (3 / 2) (by norm_num) (by norm_num))
  -- the assembled product is dominated by an explicit multiple of `σ - 1`
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
  -- the dominating expression tends to zero along the real approach
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
      have hc : Continuous fun σ : ℝ =>
          ‖dslope C (1 + y * I) ((σ : ℂ) + y * I)‖ ^ 4 := by
        apply Continuous.pow
        apply Continuous.norm
        exact hg.continuous.comp ((Complex.continuous_ofReal).add continuous_const)
      have := hc.tendsto 1
      simpa using this
    have hsub : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      have hc : Continuous fun σ : ℝ => σ - 1 := by continuity
      have := hc.tendsto 1
      simpa using this
    have hall :=
      ((((hζ.mul hgt).mul (tendsto_const_nhds (x := K) (f := 𝓝[>] (1 : ℝ)))).mul
        (tendsto_const_nhds (x := K₂) (f := 𝓝[>] (1 : ℝ)))).mul hsub)
    simpa using hall
  -- the two conclusions collide
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

/-- **Bank edge nonvanishing with a polar companion.**  The tempered self-dual bank supplies the
Mertens product bound; the companion is allowed the simple pole its Euler readout genuinely has
at `s = 1`, and is asked only for boundedness at the doubled ordinate.  Both hypotheses hold for
the diagonal Rankin--Selberg readout away from `y = 0`. -/
theorem bank_edge_nonvanishing_of_simplePole (α : Nat.Primes → Fin m → ℂ)
    (hα : ∀ p i, ‖α p i‖ = 1)
    (hreal : ∀ (p : Nat.Primes) (n : ℕ), (∑ i, α p i ^ n).im = 0)
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C)
    (hCeq : Set.EqOn C (bankEulerReadout α) {s : ℂ | 1 < s.re})
    (hDeq : Set.EqOn D (bankEulerReadout (pairBank α)) {s : ℂ | 1 < s.re})
    {y K K₂ : ℝ}
    (hDpole : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D (σ : ℂ)‖ * (σ - 1) ≤ K)
    (hDtwist : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D ((σ : ℂ) + 2 * y * I)‖ ≤ K₂) :
    C (1 + y * I) ≠ 0 := by
  apply edge_nonvanishing_of_simplePole_product_bound hC hDpole hDtwist
  intro σ hσ _
  obtain ⟨h₀, h₁, h₂⟩ := one_lt_re_triple hσ y
  rw [hCeq (Set.mem_setOf.mpr h₁), hDeq (Set.mem_setOf.mpr h₀),
    hDeq (Set.mem_setOf.mpr h₂)]
  exact norm_bank_product_ge_one α hα hreal hσ y

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.edge_nonvanishing_of_simplePole_product_bound
#print axioms CriticalLinePhasor.ThreeDConverse.bank_edge_nonvanishing_of_simplePole
