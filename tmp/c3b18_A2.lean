import c3b18_A1

/-!
# C3 batch 18, block A2 — the signed-lobe lemma that antitonicity unlocks

Batch 17 named the missing ingredient for the `k`-lobe programme: *"a half-period change of
variables relating consecutive lobe masses `J_k`"*.  It is supplied here, and it is **just a
translation**.

With `s := π/(2x)` the half period of `v ↦ |cos(2xv)|`:

* `|cos(2x(v+s))| = |cos(2xv + π)| = |cos(2xv)|` — the weight is `s`-periodic;
* `Rker (v+s) ≤ Rker v` for `v ≥ 0` — antitonicity (batch 18 A1, hypothesis: `Φ` log-concave);
* hence, block by block, `∫_{c+s}^{c+2s} R|cos| = ∫_c^{c+s} R(v+s)|cos(2xv)| ≤ ∫_c^{c+s} R|cos|`.

So consecutive half-period blocks have **decreasing** mass.  That is exactly the `(J_k)`
monotonicity the alternating-lobe lower bound needs.

**What is compiled and what is not.**  `lobe_block_antitone` is compiled (given the `Φ`
hypothesis).  Assembling it into `cosMom R (2x) ≥ 2(J₀ − J₁ + …)` additionally needs an
alternating-series argument over infinitely many blocks, which is **not** formalised here.
Note also, from batch 16's measurements, that the *first* block is special: it has half the
length of the others, so `J₀ ≥ J₁` is **not** implied by this lemma — measured `J₀ − J₁ < 0`
for `x ≳ 8.86`.  That asymmetry is stated, not hidden.

SCOPE: one periodicity fact and one block inequality.  Nothing here decides the target.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B18

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open C3B10
open C3B14
open C3B17

/-- The clock weight `|cos(2xv)|` has half period `π/(2x)`. -/
theorem abs_cos_half_period {x : ℝ} (hx : x ≠ 0) (v : ℝ) :
    |Real.cos (2 * x * (v + Real.pi / (2 * x)))| = |Real.cos (2 * x * v)| := by
  have h2x : (2:ℝ) * x ≠ 0 := by
    simpa using mul_ne_zero (two_ne_zero) hx
  have harg : 2 * x * (v + Real.pi / (2 * x)) = 2 * x * v + Real.pi := by
    field_simp
  rw [harg, Real.cos_add_pi, abs_neg]

/-- **THE HALF-PERIOD BLOCK INEQUALITY.**  Consecutive half-period blocks of the clocked
kernel have decreasing mass.  The only inputs are antitonicity of `Rker` (hence the `Φ`
hypothesis) and translation invariance of the interval integral. -/
theorem lobe_block_antitone
    (hlc : ConcaveOn ℝ univ (fun t : ℝ => Real.log (riemannXiKernel t)))
    {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 ≤ c) :
    (∫ v in (c + Real.pi / (2 * x))..(c + Real.pi / x),
        Rker v * |Real.cos (2 * x * v)|)
      ≤ ∫ v in c..(c + Real.pi / (2 * x)), Rker v * |Real.cos (2 * x * v)| := by
  set s : ℝ := Real.pi / (2 * x) with hs
  have hspos : 0 < s := by
    rw [hs]
    have : (0:ℝ) < 2 * x := by linarith
    positivity
  have hends : c + Real.pi / x = (c + s) + s := by
    rw [hs]
    field_simp
    ring
  -- translate the right-hand block back by one half period
  have hshift : (∫ v in (c + s)..((c + s) + s), Rker v * |Real.cos (2 * x * v)|)
      = ∫ v in c..(c + s), Rker (v + s) * |Real.cos (2 * x * (v + s))| := by
    rw [intervalIntegral.integral_comp_add_right
      (fun v => Rker v * |Real.cos (2 * x * v)|) s]
  rw [hends, hshift]
  -- pointwise comparison on the block
  have hle : ∀ v ∈ Set.uIcc c (c + s),
      Rker (v + s) * |Real.cos (2 * x * (v + s))| ≤ Rker v * |Real.cos (2 * x * v)| := by
    intro v hv
    have hvc : c ≤ v := by
      rcases Set.mem_uIcc.mp hv with h | h
      · exact h.1
      · exact le_trans (by linarith [hspos]) h.1
    have hv0 : 0 ≤ v := le_trans hc hvc
    have hper := abs_cos_half_period (ne_of_gt hx) v
    rw [hper]
    have hR : Rker (v + s) ≤ Rker v :=
      Rker_antitone_of_logConcave' hlc hv0 (by linarith [hspos])
    exact mul_le_mul_of_nonneg_right hR (abs_nonneg _)
  have hint1 : IntervalIntegrable (fun v => Rker (v + s) * |Real.cos (2 * x * (v + s))|)
      volume c (c + s) := ((Rker_abscos_integrable x).comp_add_right s).intervalIntegrable
  have hint2 : IntervalIntegrable (fun v => Rker v * |Real.cos (2 * x * v)|)
      volume c (c + s) := (Rker_abscos_integrable x).intervalIntegrable
  exact intervalIntegral.integral_mono_on (by linarith [hspos]) hint1 hint2
    (fun v hv => hle v (Set.mem_uIcc_of_le hv.1 hv.2))

/-- Iterated: block `k+1` is dominated by block `k`, for every `k`. -/
theorem lobe_block_antitone_succ
    (hlc : ConcaveOn ℝ univ (fun t : ℝ => Real.log (riemannXiKernel t)))
    {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (∫ v in ((k+1 : ℕ) * (Real.pi / (2 * x)))..((k+2 : ℕ) * (Real.pi / (2 * x))),
        Rker v * |Real.cos (2 * x * v)|)
      ≤ ∫ v in ((k : ℕ) * (Real.pi / (2 * x)))..((k+1 : ℕ) * (Real.pi / (2 * x))),
        Rker v * |Real.cos (2 * x * v)| := by
  have hspos : (0:ℝ) < Real.pi / (2 * x) := by
    have : (0:ℝ) < 2 * x := by linarith
    positivity
  have hc : (0:ℝ) ≤ (k : ℕ) * (Real.pi / (2 * x)) := by positivity
  have h := lobe_block_antitone hlc hx hc
  have e1 : ((k : ℕ) : ℝ) * (Real.pi / (2 * x)) + Real.pi / (2 * x)
      = ((k+1 : ℕ) : ℝ) * (Real.pi / (2 * x)) := by
    push_cast
    ring
  have e2 : ((k : ℕ) : ℝ) * (Real.pi / (2 * x)) + Real.pi / x
      = ((k+2 : ℕ) : ℝ) * (Real.pi / (2 * x)) := by
    push_cast
    field_simp
  rw [e1, e2] at h
  exact h

end C3B18

section AxiomAudit
#print axioms C3B18.abs_cos_half_period
#print axioms C3B18.lobe_block_antitone
#print axioms C3B18.lobe_block_antitone_succ
end AxiomAudit
