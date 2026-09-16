import RequestProject.XiFlowCascade
import RequestProject.XiHadamardQuotient

/-!
# The flow frontier: the constructive leaf of T2c (ledger 685)

The flow cascade (674) is the frame's warp of the kernel: `flowStage λ z = ∫ e^{λu²} K(u) e^{izu} du`, real on the
axis, entire, converging to `ξ(½ + iz)` as `λ ↓ 0`.  Its door (`rh_of_oneVanishingPerHeight_flow`) consumes one
vanishing per height at every stage.  Here that hypothesis is put in its constructive form — **every stage is
real-rooted** — and the target is made a FRONTIER in the warp parameter:

* `FlowFrontier λ₀` : every stage with `λ₀ ≤ λ ≤ 1` has only real zeros.
* `rh_of_flowFrontier` : if `FlowFrontier λ₀` holds for every `λ₀ > 0`, the Riemann Hypothesis holds.
* `xiSection_zero_im_lt_half` : at `λ = 0` the zeros lie in the strip `|Im z| < ½` (the classical strip) — the input
  of the strip-narrowing theorem.

De Bruijn's theorem (1950, Thm 13 — VERIFIED 846c: Thm 13 is the strip-contraction statement, and in his
normalisation `e^{λt²/2}` it reads `|Im z| ≤ √(Δ² − λ)⁺`, which with our `e^{λu²}` is `√(Δ² − 2λ)⁺`),
in this normalisation, is `FlowFrontier (1/8)`: the heat operator `e^{λu²}` on a
kernel whose transform has zeros in `|Im z| ≤ Δ` narrows the strip to `√(Δ² − 2λ)⁺`, so `Δ = ½` gives real zeros for
`λ ≥ 1/8` at EVERY height.

**COMPILED (ledger 700, `DeBruijnFlowFrontier.lean`): `flowFrontier_one_eighth : FlowFrontier (1/8)`**,
unconditional, axioms `{propext, Classical.choice, Quot.sound}`.  It discharges stages `n ≤ 7` of the cascade at
all heights (`flowCascade_realRooted_of_le_seven`) — the first all-heights discharge of any stage — so the
remaining target is the bounded interval `λ ∈ (0, 1/8)`, not an all-heights quantifier.

Beyond de Bruijn, NEITHER of the following is compiled, and they are two different results, not one:
Ki–Kim–Lee (2009) sharpen de Bruijn's `Λ ≤ ½` to the STRICT `Λ < ½`; Polymath 15 (2019) gives `Λ ≤ 0.22`,
which is `λ ≤ 0.055` here (their `Δ = 1` normalisation, `Λ = 4λ`).  Only the latter is a numerical
improvement on the compiled frontier.  Exposition: `automorph/debruijn_lean.tex`.
-/

open Complex Filter Topology
open CriticalLinePhasor.Cascade

namespace CriticalLinePhasor.XiKernel

/-- **The flow frontier at `λ₀`:** every stage with `λ₀ ≤ λ ≤ 1` is real-rooted. -/
def FlowFrontier (lam₀ : ℝ) : Prop :=
  ∀ lam : ℝ, lam₀ ≤ lam → lam ≤ 1 → ∀ z : ℂ, flowStage lam z = 0 → z.im = 0

theorem lamSeq_pos (n : ℕ) : 0 < lamSeq n := by unfold lamSeq; positivity

/-- Real-rooted stages give one vanishing per height. -/
theorem oneVanishingPerHeight_of_realRooted
    (h : ∀ n : ℕ, ∀ z : ℂ, flowStage (lamSeq n) z = 0 → z.im = 0) :
    OneVanishingPerHeight flowCascade := by
  intro n z w hz hw hre
  have hz' : z.im = 0 := h n z hz
  have hw' : w.im = 0 := h n w hw
  exact Complex.ext hre (by rw [hz', hw'])

/-- **RH from the flow frontier at every positive `λ₀`.** -/
theorem rh_of_flowFrontier (h : ∀ lam₀ : ℝ, 0 < lam₀ → FlowFrontier lam₀) : RiemannHypothesis := by
  apply rh_of_oneVanishingPerHeight_flow
  apply oneVanishingPerHeight_of_realRooted
  intro n z hz
  exact h (lamSeq n) (lamSeq_pos n) (lamSeq n) le_rfl (lamSeq_le_one n) z hz

/-- Monotone frontiers: a frontier at `λ₀` is a frontier at every `λ₁ ≥ λ₀`. -/
theorem FlowFrontier.mono {lam₀ lam₁ : ℝ} (h : FlowFrontier lam₀) (hle : lam₀ ≤ lam₁) : FlowFrontier lam₁ :=
  fun lam hlam hlam1 z hz => h lam (hle.trans hlam) hlam1 z hz

/-- **The strip at `λ = 0`:** zeros of `ξ(½ + iz)` satisfy `|Im z| < ½`. -/
theorem xiSection_zero_im_lt_half {z : ℂ} (hz : CriticalLinePhasor.XiChannel.xiSection z = 0) : |z.im| < 1 / 2 := by
  unfold CriticalLinePhasor.XiChannel.xiSection at hz
  have hmem := (ZD.riemannXi_eq_zero_iff _).mp hz
  obtain ⟨h0, h1, -⟩ := hmem
  have hre : (1 / 2 + I * z).re = 1 / 2 - z.im := by simp; ring
  rw [hre] at h0 h1
  rw [abs_lt]
  constructor <;> linarith

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.rh_of_flowFrontier
#print axioms CriticalLinePhasor.XiKernel.xiSection_zero_im_lt_half
