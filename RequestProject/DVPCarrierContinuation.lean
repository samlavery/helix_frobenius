import RequestProject.DVPCarrierOrderedSum
import RequestProject.DVPArgumentPrinciple

/-!
# The ordered readout continues ζ into the strip

`DVPCarrierOrderedSum.etaPartial_tendsto` gives the carrier's bank a limit on
the whole half-plane `Re s > 0`.  This module identifies that limit.

* `etaLim_differentiableOn` — the limit is holomorphic on `Re s > 0`.  Proof:
  the paired phasors are entire, and on each ball inside the half-plane the
  bounded-variation estimate `‖a^{−s} − (a+1)^{−s}‖ ≤ ‖s‖·a^{−σ−1}` is a
  summable majorant, so the series differentiates termwise.
* `etaLim_eq_zeta` — on `Re s > 0`, `s ≠ 1`,

      `etaLim s = (1 − 2^{1−s})·ζ(s)`.

  Proof: the two sides agree on `Re s > 1` (where the bank is absolutely
  summable and `alternating_zeta_identity` applies), and the punctured
  half-plane is preconnected, so the identity theorem carries the agreement
  across `Re s = 1`.

What this supplies that the DIRICHLET SERIES does not: an ORDERED sum whose
truncation error at `N` terms is one elementary quantity — the tail of an
absolutely convergent majorant — valid INSIDE the critical strip, where the
Dirichlet series does not converge at all.

SCOPE — what it does NOT supply.  It does not extend the region in which this
repository can write `ζ` unconditionally.  `DVPTruncatedZeta.truncated_zeta_pos_re`
already gives `ζ` on `0 < Re s`, `s ≠ 1`, by Euler–Maclaurin.  The gain here
is the summation ORDER and the shape of the error term, not the reach.

Neither Mathlib nor `PrimeNumberTheoremAnd` carries a Dirichlet eta function
(checked by search over both source trees, 2026-08-21).
-/

open Complex Filter Topology Set

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The limit of the ordered readout: the carrier's bank, summed in the order
its phasors enter. -/
def etaLim (s : ℂ) : ℂ := ∑' k : ℕ, pairTerm s k

/-- Each paired phasor is entire in `s`. -/
theorem pairTerm_differentiable (k : ℕ) :
    Differentiable ℂ (fun s : ℂ => pairTerm s k) := by
  have h : (fun s : ℂ => pairTerm s k)
      = fun s : ℂ => (((2 * k + 1 : ℕ) : ℝ) : ℂ) ^ (-s)
          - (((2 * k + 2 : ℕ) : ℝ) : ℂ) ^ (-s) := by
    funext s; exact pairTerm_eq s k
  rw [h]
  have hA : ((((2 * k + 1 : ℕ) : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hB : ((((2 * k + 2 : ℕ) : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  exact (differentiable_id.neg.const_cpow (Or.inl hA)).sub
    (differentiable_id.neg.const_cpow (Or.inl hB))

/-- **The ordered readout is holomorphic on the carrier's half-plane.** -/
theorem etaLim_differentiableOn :
    DifferentiableOn ℂ etaLim {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hre : 0 < s₀.re := hs₀
  set δ : ℝ := s₀.re / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  set M : ℝ := ‖s₀‖ + δ with hMdef
  have hu : Summable (fun k : ℕ => M * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1)) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-δ - 1)) := by
      rw [Real.summable_nat_rpow]; linarith
    exact ((hbase.comp_injective (fun a b hab => by omega)).mul_left _)
  have hbd : ∀ (k : ℕ) (w : ℂ), w ∈ Metric.ball s₀ δ →
      ‖pairTerm w k‖ ≤ M * ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1) := by
    intro k w hw
    have hdist : ‖w - s₀‖ < δ := by
      rw [← Complex.dist_eq]; exact Metric.mem_ball.mp hw
    have hred : |w.re - s₀.re| ≤ ‖w - s₀‖ := by
      simpa [Complex.sub_re] using abs_re_le_norm (w - s₀)
    have hwre : δ ≤ w.re := by
      have h1 : s₀.re - w.re ≤ |w.re - s₀.re| := by
        rw [abs_sub_comm]; exact le_abs_self _
      rw [hδdef]; linarith
    have hwnorm : ‖w‖ ≤ M := by
      have := norm_sub_norm_le w s₀
      rw [hMdef]; linarith
    rw [pairTerm_eq]
    have hk : (0:ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
    have hk1 : (1:ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * k + 1)
    have hcast : (((2 * k + 2 : ℕ) : ℝ)) = ((2 * k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    refine (cpow_diff_norm_le w _ hk (by linarith)).trans ?_
    have hmono : ((2 * k + 1 : ℕ) : ℝ) ^ (-w.re - 1)
        ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (-δ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
    exact mul_le_mul hwnorm hmono (Real.rpow_nonneg (le_of_lt hk) _)
      (le_trans (norm_nonneg _) hwnorm)
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => ∑' k : ℕ, pairTerm w k)
      (Metric.ball s₀ δ) :=
    differentiableOn_tsum_of_summable_norm hu
      (fun k => (pairTerm_differentiable k).differentiableOn) Metric.isOpen_ball hbd
  exact (hdiff.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδpos))).differentiableWithinAt

/-- On `Re s > 1` the bank is absolutely summable, so the ordered limit is the
unordered one. -/
theorem etaLim_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    etaLim s = ∑' n : ℕ, etaTerm s n := by
  have ha : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have h1 : Summable (fun n : ℕ => 1 / ((n : ℂ)) ^ s) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    have h2 := (summable_nat_add_iff 1).mpr h1
    apply Summable.congr h2
    intro n; push_cast; rfl
  have hsum : Summable (etaTerm s) := by
    refine Summable.of_norm_bounded (summable_norm_iff.mpr ha) (fun n => ?_)
    simp [etaTerm, norm_div]
  exact tendsto_nhds_unique (etaPartial_tendsto (by linarith)) hsum.hasSum.tendsto_sum_nat

/-- The punctured carrier half-plane. -/
def puncturedCarrier : Set ℂ := {s : ℂ | 0 < s.re} \ {1}

theorem isOpen_puncturedCarrier : IsOpen puncturedCarrier :=
  (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton

theorem isPreconnected_puncturedCarrier : IsPreconnected puncturedCarrier := by
  set P : Set ℂ := {c : ℂ | 0 < c.re} ∩ {c : ℂ | c.re < 1} with hP
  set C : Set ℂ := {c : ℂ | 0 < c.re} ∩ {c : ℂ | 0 < c.im} with hC
  set D : Set ℂ := {c : ℂ | 0 < c.re} ∩ {c : ℂ | c.im < 0} with hD
  set F : Set ℂ := {c : ℂ | 1 < c.re} with hF
  have hPc : IsPreconnected P :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hCc : IsPreconnected C :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hDc : IsPreconnected D :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hFc : IsPreconnected F := (convex_halfSpace_re_gt 1).isPreconnected
  have h1 : IsPreconnected (P ∪ C) := by
    refine IsPreconnected.union (⟨1/2, 1⟩ : ℂ) ?_ ?_ hPc hCc
    · exact ⟨by norm_num [hP], by norm_num [hP]⟩
    · exact ⟨by norm_num [hC], by norm_num [hC]⟩
  have h2 : IsPreconnected ((P ∪ C) ∪ D) := by
    refine IsPreconnected.union (⟨1/2, -1⟩ : ℂ) ?_ ?_ h1 hDc
    · exact Or.inl ⟨by norm_num [hP], by norm_num [hP]⟩
    · exact ⟨by norm_num [hD], by norm_num [hD]⟩
  have h3 : IsPreconnected (((P ∪ C) ∪ D) ∪ F) := by
    refine IsPreconnected.union (⟨2, 1⟩ : ℂ) ?_ ?_ h2 hFc
    · exact Or.inl (Or.inr ⟨by norm_num [hC], by norm_num [hC]⟩)
    · exact by norm_num [hF]
  have hset : puncturedCarrier = ((P ∪ C) ∪ D) ∪ F := by
    ext s
    simp only [puncturedCarrier, hP, hC, hD, hF, Set.mem_diff, Set.mem_setOf_eq,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_inter_iff]
    constructor
    · rintro ⟨hre, hne⟩
      rcases lt_trichotomy s.re 1 with h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hre, h⟩))
      · have him : s.im ≠ 0 := by
          intro h0; exact hne (Complex.ext (by simpa using h) (by simpa using h0))
        rcases lt_or_gt_of_ne him with h1 | h1
        · exact Or.inl (Or.inr ⟨hre, h1⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨hre, h1⟩))
      · exact Or.inr h
    · rintro (((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩) | h)
      · exact ⟨ha, fun hEq => by rw [hEq] at hb; simp at hb⟩
      · exact ⟨ha, fun hEq => by rw [hEq] at hb; simp at hb⟩
      · exact ⟨ha, fun hEq => by rw [hEq] at hb; simp at hb⟩
      · exact ⟨by linarith, fun hEq => by rw [hEq] at h; simp at h⟩
  rw [hset]; exact h3

/-- **The carrier's ordered bank continues `ζ` into the strip.**  For every `s`
with `Re s > 0` and `s ≠ 1`, the ordered limit of the alternating phasor bank
equals `(1 − 2^{1−s})·ζ(s)`.  Unconditional. -/
theorem etaLim_eq_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    etaLim s = (1 - 2 ^ ((1:ℂ) - s)) * riemannZeta s := by
  set g : ℂ → ℂ := fun z => (1 - 2 ^ ((1:ℂ) - z)) * riemannZeta z with hg
  have hsub : puncturedCarrier ⊆ {z : ℂ | 0 < z.re} := fun z hz => hz.1
  have hfA : AnalyticOnNhd ℂ etaLim puncturedCarrier :=
    (etaLim_differentiableOn.mono hsub).analyticOnNhd isOpen_puncturedCarrier
  have hgd : DifferentiableOn ℂ g puncturedCarrier := by
    intro z hz
    have hz1 : z ≠ 1 := fun h => hz.2 (by simp [h])
    have hpow : DifferentiableAt ℂ (fun y : ℂ => (2:ℂ) ^ ((1:ℂ) - y)) z :=
      (((differentiable_const (1:ℂ)).sub differentiable_id).const_cpow
        (Or.inl two_ne_zero)) z
    exact ((differentiableAt_const (1:ℂ)).sub hpow).mul
      (differentiableAt_riemannZeta hz1) |>.differentiableWithinAt
  have hgA : AnalyticOnNhd ℂ g puncturedCarrier :=
    hgd.analyticOnNhd isOpen_puncturedCarrier
  have h2mem : (2 : ℂ) ∈ puncturedCarrier := by
    refine ⟨by norm_num, by norm_num⟩
  have hloc : etaLim =ᶠ[nhds (2 : ℂ)] g := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds (by norm_num)) (fun z hz => ?_)
    have hz' : 1 < z.re := hz
    rw [etaLim_eq_tsum hz', hg]
    exact (alternating_zeta_identity hz').symm
  have hEq := hfA.eqOn_of_preconnected_of_eventuallyEq hgA
    isPreconnected_puncturedCarrier h2mem hloc
  exact hEq ⟨hs, hs1⟩

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.etaLim_differentiableOn
#print axioms CriticalLinePhasor.DVP.etaLim_eq_zeta
end AxiomAudit
