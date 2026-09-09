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

De Bruijn's theorem (1950, Thm 13), in this normalisation, is `FlowFrontier (1/8)`: the heat operator `e^{λu²}` on a
kernel whose transform has zeros in `|Im z| ≤ Δ` narrows the strip to `√(Δ² − 2λ)⁺`, so `Δ = ½` gives real zeros for
`λ ≥ 1/8` at EVERY height.  Ki–Kim–Lee and Polymath 15 push the frontier to `λ ≥ 0.055` here (their `0.22` with `Δ = 1`).
Neither is compiled; de Bruijn's is the next compile, and it would discharge stages `n ≤ 7` of the cascade for all
heights — the first all-heights discharge of any stage.  The remaining target is then a bounded interval of the
warp parameter, `λ ∈ (0, λ₀)`, not an all-heights quantifier.
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
