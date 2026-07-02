import RequestProject.UnitMidpoint

/-!
# The antihelix growth window: the two-strand kernel formalized

The strand-topology finding (`tmp/strand_topology.py`, `tmp/bsd_rank_ladder.py`): a degree-2
fiber does not converge at the hinge — the completed L exists there only as TWO strands,
each starting at one ending (cusp) and integrating inward to the Fricke midpoint:

    Λ(s) = Σ aₙ [ rₙ^s · Γ(s, xₙ)  +  ε · rₙ^{2−s} · Γ(2−s, xₙ) ],   rₙ·xₙ = 1,

(numerically validated to 5×10⁻¹² against the absolutely-convergent region and 7.5×10⁻¹³
per term; it read the BSD rank ladder 0–5 at worst 0.99974).  This file proves the
kernel-level structure, unconditionally, with no L-functions:

* `upperGamma_zero` / `upperGamma_antitone` / `upperGamma_tendsto_zero` — the incomplete-Γ
  factor IS a growth window: full weight `Γ(s)` at the cut `x = 0`, monotone dying, → 0.
  Each phasor of a strand enters at full strength and is windowed off smoothly — the
  antihelix has its own growth window, and it is the same `Γ`-tail as the helix's.
* `gamma_splits_at_cut` — the complete `Γ(s)` splits exactly into the two path-halves at
  any cut: the geodesic between the endings, cut at the midpoint.
* `strand_weights_det_one` — **Frobenius det 1 in the s-direction** (Sam's identification):
  the normalized strand weights `r^{s−1}` and `r^{1−s}` multiply to `1` identically — the
  helix/antihelix pair is the same determinant-one conjugate block as
  `frobenius_conjugate_det_one`, realized in the functional-equation reflection.
* `strand_swap_fixed_iff` — the strand swap `s ↦ 2−s` fixes exactly the hinge `s = 1`:
  UNIT/2 with the reflection unit (the weight) as the unit.
* `weld_kills_each_phasor` / `weld_doubles_each_phasor` — at the hinge the two strands of
  EVERY phasor are equal, so `ε = −1` annihilates each term individually (the forced
  central zero is term-local, not a conspiracy of the sum) and `ε = +1` doubles it to
  `2·r·e^{−x}` — the measured equal-weight-at-the-hinge, as algebra.

Mathlib-only + this repo; unconditional; no `sorry`, no `axiom`; no zero-location claims.
The identification of this kernel with a specific completed L is the numerics' job.
-/

open MeasureTheory Real Set Filter

namespace CriticalLinePhasor.AntihelixWindow

/-- The upper incomplete Gamma — the tail of the Gamma integrand beyond the cut `x`:
one strand's growth window, in the same integrand normalization as
`Real.Gamma_eq_integral`. -/
noncomputable def upperGamma (s x : ℝ) : ℝ := ∫ t in Ioi x, Real.exp (-t) * t ^ (s - 1)

/-- At cut `0` the window is fully open: `Γ(s, 0) = Γ(s)`. -/
theorem upperGamma_zero {s : ℝ} (hs : 0 < s) : upperGamma s 0 = Real.Gamma s :=
  (Real.Gamma_eq_integral hs).symm

/-- The window is nonnegative beyond a nonnegative cut. -/
theorem upperGamma_nonneg (s : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ upperGamma s x := by
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  have h0 : 0 < t := lt_of_le_of_lt hx ht
  positivity

/-- The window only closes as the cut advances: monotone dying. -/
theorem upperGamma_antitone {s : ℝ} (hs : 0 < s) {x₁ x₂ : ℝ} (h0 : 0 ≤ x₁) (h : x₁ ≤ x₂) :
    upperGamma s x₂ ≤ upperGamma s x₁ := by
  refine setIntegral_mono_set
    ((Real.GammaIntegral_convergent hs).mono_set (Ioi_subset_Ioi h0)) ?_
    (HasSubset.Subset.eventuallyLE (Ioi_subset_Ioi h))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have h0t : 0 < t := lt_of_le_of_lt h0 ht
  positivity

/-- The window dies completely: `Γ(s, k) → 0`. -/
theorem upperGamma_tendsto_zero {s : ℝ} (hs : 0 < s) :
    Tendsto (fun k : ℕ => upperGamma s k) atTop (nhds 0) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (s - 1)) (Ioi ((0 : ℕ) : ℝ)) := by
    simpa using Real.GammaIntegral_convergent hs
  have h := Antitone.tendsto_setIntegral (s := fun k : ℕ => Ioi (k : ℝ))
    (fun _ => measurableSet_Ioi)
    (fun i j hij => Ioi_subset_Ioi (by exact_mod_cast hij)) hint
  have hempty : (⋂ k : ℕ, Ioi ((k : ℕ) : ℝ)) = (∅ : Set ℝ) := by
    ext t
    simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨k, hk⟩ := exists_nat_gt t
    exact ⟨k, hk.le⟩
  rw [hempty] at h
  simpa [upperGamma] using h

/-- **The path between the endings splits exactly at the cut**: `Γ(s)` = near half + far
half.  The completed object's geodesic from cusp to cusp, cut at the (Fricke) midpoint. -/
theorem gamma_splits_at_cut {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    (∫ t in Ioc 0 x, Real.exp (-t) * t ^ (s - 1)) + upperGamma s x = Real.Gamma s := by
  rw [Real.Gamma_eq_integral hs, ← Set.Ioc_union_Ioi_eq_Ioi hx, upperGamma]
  exact (setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    ((Real.GammaIntegral_convergent hs).mono_set
      (Set.Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi le_rfl)))
    ((Real.GammaIntegral_convergent hs).mono_set (Ioi_subset_Ioi hx))).symm

/-- `Γ(1, x) = e^{−x}`: the weight-one window is the pure exponential — the hinge
phasor's surviving profile. -/
theorem upperGamma_one (x : ℝ) : upperGamma 1 x = Real.exp (-x) := by
  unfold upperGamma
  rw [show (1 : ℝ) - 1 = 0 by norm_num]
  simp only [Real.rpow_zero, mul_one]
  exact integral_exp_neg_Ioi x

/-- The two-strand kernel term: helix strand + `ε` · antihelix strand, both windowed by
the same `Γ`-tail at the same cut. -/
noncomputable def strandPair (ε r x s : ℝ) : ℝ :=
  r ^ s * upperGamma s x + ε * (r ^ (2 - s) * upperGamma (2 - s) x)

/-- **Frobenius det 1 in the s-direction**: the hinge-normalized strand weights `r^{s−1}`
(helix) and `r^{1−s}` (antihelix) multiply to `1` identically in `s` — the strand pair is
the determinant-one conjugate block (`frobenius_conjugate_det_one`) realized in the
functional-equation reflection: what one strand gains, the other loses exactly. -/
theorem strand_weights_det_one {r : ℝ} (hr : 0 < r) (s : ℝ) :
    r ^ (s - 1) * r ^ (1 - s) = 1 := by
  rw [← Real.rpow_add hr]
  norm_num

/-- The strand swap `s ↦ 2 − s` fixes exactly the hinge `s = 1`: UNIT/2 again, with the
reflection unit `2` (the weight) as the unit. -/
theorem strand_swap_fixed_iff (s : ℝ) : 2 - s = s ↔ s = 1 := by
  simpa using CriticalLinePhasor.UnitMidpoint.affine_reflection_fixed_iff 2 s

/-- **The weld kills every phasor individually at the hinge** (`ε = −1`): at `s = 1` the
helix and antihelix strands of each term are equal, so their difference vanishes term by
term — the forced central zero is term-local. -/
theorem weld_kills_each_phasor (r x : ℝ) : strandPair (-1) r x 1 = 0 := by
  unfold strandPair
  rw [show (2 : ℝ) - 1 = 1 by norm_num]
  ring

/-- **The weld doubles every phasor at the hinge** (`ε = +1`): the surviving term is
`2·r·e^{−x}` — the two equal strands add. -/
theorem weld_doubles_each_phasor (r x : ℝ) :
    strandPair 1 r x 1 = 2 * (r ^ (1 : ℝ) * Real.exp (-x)) := by
  unfold strandPair
  rw [show (2 : ℝ) - 1 = 1 by norm_num, upperGamma_one]
  ring

end CriticalLinePhasor.AntihelixWindow
