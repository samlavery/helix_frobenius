import c3b16_A3

/-!
# C3 batch 17, block A1 — `Rker` antitone, reduced to ONE inequality about `Φ`

## The reduction, and why it needs no Prékopa

`Rker v = ∫ p²·Φ(v+p)Φ(v−p) dp`.  Fix `p` and look at the **pair**

  `G_p(w) := log Φ(w+p) + log Φ(w−p)`.

* `G_p` is **even** in `w`: `G_p(−w) = logΦ(−w+p) + logΦ(−w−p) = logΦ(w−p) + logΦ(w+p)`,
  using only `riemannXiKernel_neg` — the Jacobi reflection.
* `G_p` is **concave** in `w` whenever `log Φ` is concave: each summand is `log Φ` composed
  with a translation.

An even concave function is **antitone on `[0,∞)`** — elementary: for `0 ≤ u ≤ v` write
`u = λ(−v) + (1−λ)v` with `λ = (v−u)/(2v)`, and concavity plus evenness give `G(u) ≥ G(v)`.

Exponentiating gives the **four-point inequality** `Φ(v+p)Φ(v−p) ≤ Φ(u+p)Φ(u−p)` for every
`p`, and integrating against `p² ≥ 0` gives `Rker v ≤ Rker u`.  **This is pointwise in `p`:
no marginal theorem, no Prékopa–Leindler** (which Mathlib does not have — searched).

So the entire target reduces to one inequality about `Φ` alone:

  **`ConcaveOn ℝ univ (fun t => Real.log (riemannXiKernel t))`**

— displayed as a hypothesis everywhere below, never assumed silently.

## Status of that hypothesis — audited, not smuggled

* **Measured** (`tmp/c3b17_num1_out.txt` §R2, mpmath 50 dps, 477 points on `[0,3.5]`):
  `(logΦ)″ > 0` at **0** points; `max (logΦ)″ = −18.7269049295` at `t = 0`.  Also
  `Φ′(0) = 0` exactly and `Φ` increases at `0/476` steps.
* **Closest compiled fact in this repository**, found by search before construction:
  `CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernelTerm_log_strictConcaveOn (n : ℕ)`
  — `StrictConcaveOn ℝ (Set.Ici 0) (fun u => Real.log (riemannXiKernelTerm n u))`.  That is
  **per-summand and on `Ici 0` only**.  A sum of log-concave functions need **not** be
  log-concave, so it does **not** yield the hypothesis, and it is not used as if it did.
* Nothing here assumes anything target-shaped: the hypothesis is about `Φ`, not about `Rker`,
  not about `cosMom`, and not about any zero.

SCOPE: one general convexity lemma, the pair construction, the four-point inequality, and the
integral consequence.  The `Φ`-hypothesis is open and is named as such.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B17

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open C3B10
open C3B12
open C3B13
open C3B14

/-! ### 1. Even + concave ⟹ antitone on `[0,∞)` -/

/-- **THE CONVEXITY LEMMA.**  An even concave function on `ℝ` is antitone on `[0,∞)`.
Pure real analysis; no measure theory, no kernel. -/
theorem even_concaveOn_antitone {G : ℝ → ℝ} (hev : ∀ w : ℝ, G (-w) = G w)
    (hcc : ConcaveOn ℝ univ G) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : G v ≤ G u := by
  rcases eq_or_lt_of_le hu with h0 | hupos
  · -- `u = 0`
    rcases eq_or_lt_of_le huv with hv | hvpos
    · rw [← hv]
    · have hvp : 0 < v := by linarith [h0, hvpos]
      have hhalf : ((2:ℝ)⁻¹) • (-v) + ((2:ℝ)⁻¹) • v = (0:ℝ) := by
        simp only [smul_eq_mul]; ring
      have h := hcc.2 (mem_univ (-v)) (mem_univ v) (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)
        (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹) (by norm_num)
      rw [hhalf, hev v] at h
      simp only [smul_eq_mul] at h
      rw [← h0]
      linarith [h]
  · -- `0 < u ≤ v`
    have hvp : 0 < v := lt_of_lt_of_le hupos huv
    set lam : ℝ := (v - u) / (2 * v) with hlam
    have hden : (0:ℝ) < 2 * v := by linarith
    have hlam0 : 0 ≤ lam := by
      rw [hlam]; positivity
    have hlam1 : 0 ≤ 1 - lam := by
      rw [hlam, sub_nonneg, div_le_one hden]
      linarith
    have hsum : lam + (1 - lam) = 1 := by ring
    have hcomb : lam • (-v) + (1 - lam) • v = u := by
      simp only [smul_eq_mul, hlam]
      field_simp
      ring
    have h := hcc.2 (mem_univ (-v)) (mem_univ v) hlam0 hlam1 hsum
    rw [hcomb, hev v] at h
    simp only [smul_eq_mul] at h
    nlinarith [h, hlam0, hlam1]

/-! ### 2. Translation preserves concavity on `univ` -/

theorem concaveOn_univ_shift {f : ℝ → ℝ} (hf : ConcaveOn ℝ univ f) (c : ℝ) :
    ConcaveOn ℝ univ (fun w : ℝ => f (w + c)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h := hf.2 (mem_univ (x + c)) (mem_univ (y + c)) ha hb hab
  have hx : a • (x + c) + b • (y + c) = a • x + b • y + c := by
    simp only [smul_eq_mul]
    linear_combination c * hab
  rw [hx] at h
  exact h

/-! ### 3. The pair, its parity and its concavity -/

/-- `G_p(w) = log Φ(w+p) + log Φ(w−p)`. -/
def pairLog (p w : ℝ) : ℝ :=
  Real.log (riemannXiKernel (w + p)) + Real.log (riemannXiKernel (w - p))

/-- **EVEN**, from the Jacobi reflection alone. -/
theorem pairLog_even (p w : ℝ) : pairLog p (-w) = pairLog p w := by
  unfold pairLog
  have h1 : riemannXiKernel (-w + p) = riemannXiKernel (w - p) := by
    rw [show -w + p = -(w - p) by ring, riemannXiKernel_neg]
  have h2 : riemannXiKernel (-w - p) = riemannXiKernel (w + p) := by
    rw [show -w - p = -(w + p) by ring, riemannXiKernel_neg]
  rw [h1, h2]
  ring

/-- **CONCAVE**, given the `Φ`-hypothesis. -/
theorem pairLog_concaveOn
    (hlc : ConcaveOn ℝ univ (fun t : ℝ => Real.log (riemannXiKernel t))) (p : ℝ) :
    ConcaveOn ℝ univ (pairLog p) := by
  have h1 : ConcaveOn ℝ univ (fun w : ℝ => Real.log (riemannXiKernel (w + p))) :=
    concaveOn_univ_shift hlc p
  have h2 : ConcaveOn ℝ univ (fun w : ℝ => Real.log (riemannXiKernel (w + -p))) :=
    concaveOn_univ_shift hlc (-p)
  have h2' : ConcaveOn ℝ univ (fun w : ℝ => Real.log (riemannXiKernel (w - p))) := by
    convert h2 using 2 with w
    ring_nf
  exact h1.add h2'

/-! ### 4. THE FOUR-POINT INEQUALITY -/

/-- **THE FOUR-POINT INEQUALITY.**  For `0 ≤ u ≤ v` and every half-gap `p`, translating the
cell centre outward decreases the carrier product.  Verified numerically at 32 hostile
`(u,v,p)` before formalisation (§R4, 0 violations). -/
theorem carrier_pair_antitone
    (hlc : ConcaveOn ℝ univ (fun t : ℝ => Real.log (riemannXiKernel t)))
    (p : ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    riemannXiKernel (v + p) * riemannXiKernel (v - p)
      ≤ riemannXiKernel (u + p) * riemannXiKernel (u - p) := by
  have hlog := even_concaveOn_antitone (pairLog_even p) (pairLog_concaveOn hlc p) hu huv
  have hpv : 0 < riemannXiKernel (v + p) := C3B5.A1.riemannXiKernel_pos_all _
  have hmv : 0 < riemannXiKernel (v - p) := C3B5.A1.riemannXiKernel_pos_all _
  have hpu : 0 < riemannXiKernel (u + p) := C3B5.A1.riemannXiKernel_pos_all _
  have hmu : 0 < riemannXiKernel (u - p) := C3B5.A1.riemannXiKernel_pos_all _
  have hv : Real.log (riemannXiKernel (v + p) * riemannXiKernel (v - p)) = pairLog p v := by
    unfold pairLog
    exact Real.log_mul (ne_of_gt hpv) (ne_of_gt hmv)
  have hu' : Real.log (riemannXiKernel (u + p) * riemannXiKernel (u - p)) = pairLog p u := by
    unfold pairLog
    exact Real.log_mul (ne_of_gt hpu) (ne_of_gt hmu)
  rw [← Real.log_le_log_iff (by positivity) (by positivity), hv, hu']
  exact hlog

/-- The same with the `p²` weight already attached — the exact integrand of `Rker`. -/
theorem carrier_pair_antitone_weighted
    (hlc : ConcaveOn ℝ univ (fun t : ℝ => Real.log (riemannXiKernel t)))
    (p : ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    p ^ 2 * (riemannXiKernel (v + p) * riemannXiKernel (v - p))
      ≤ p ^ 2 * (riemannXiKernel (u + p) * riemannXiKernel (u - p)) :=
  mul_le_mul_of_nonneg_left (carrier_pair_antitone hlc p hu huv) (sq_nonneg p)

/-! ### 5. THE TARGET, given the `Φ`-hypothesis -/

/-- **`Rker` IS ANTITONE ON `[0,∞)`**, given log-concavity of `Φ` and integrability of the
inner slice at `u`.  Only the `u`-slice is needed: the `v`-slice is nonnegative and dominated,
so `integral_mono_of_nonneg` applies.

The slice hypothesis is genuine and displayed; batch 14's `pair_slice_ae` supplies it for
almost every `u`, and `C3B14.cell_p2_split` exhibits the three legs at any particular `u`. -/
theorem Rker_antitone_of_logConcave
    (hlc : ConcaveOn ℝ univ (fun t : ℝ => Real.log (riemannXiKernel t)))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hint : Integrable
      (fun p : ℝ => p ^ 2 * (riemannXiKernel (u + p) * riemannXiKernel (u - p)))) :
    Rker v ≤ Rker u := by
  unfold Rker
  refine integral_mono_of_nonneg ?_ hint ?_
  · filter_upwards with p
    have h1 := (C3B5.A1.riemannXiKernel_pos_all (v + p)).le
    have h2 := (C3B5.A1.riemannXiKernel_pos_all (v - p)).le
    positivity
  · filter_upwards with p
    exact carrier_pair_antitone_weighted hlc p hu huv

/-- The a.e. form, which needs **no** slice hypothesis: batch 14's `pair_slice_ae` gives the
integrability for almost every `u`. -/
theorem Rker_antitone_ae_of_logConcave
    (hlc : ConcaveOn ℝ univ (fun t : ℝ => Real.log (riemannXiKernel t))) (v : ℝ) :
    ∀ᵐ u : ℝ, 0 ≤ u → u ≤ v → Rker v ≤ Rker u := by
  filter_upwards [C3B14.pair_slice_ae kM2_integrable kM2_measurable
      xiKernel_integrable riemannXiKernel_measurable,
    C3B14.pair_slice_ae kM1_integrable kM1_measurable kM1_integrable kM1_measurable,
    C3B14.pair_slice_ae xiKernel_integrable riemannXiKernel_measurable
      kM2_integrable kM2_measurable] with u h1 h2 h3 hu huv
  refine Rker_antitone_of_logConcave hlc hu huv ?_
  have h2' : Integrable (fun p : ℝ => 2 * (kM1 (u + p) * kM1 (u - p))) := h2.const_mul 2
  have hcomb : Integrable (fun p : ℝ =>
      4⁻¹ * (kM2 (u + p) * riemannXiKernel (u - p) - 2 * (kM1 (u + p) * kM1 (u - p))
        + riemannXiKernel (u + p) * kM2 (u - p))) :=
    ((h1.sub h2').add h3).const_mul _
  refine hcomb.congr ?_
  filter_upwards with p
  have h := C3B14.cell_p2_split u p
  linear_combination h / 4

end C3B17

section AxiomAudit
#print axioms C3B17.even_concaveOn_antitone
#print axioms C3B17.concaveOn_univ_shift
#print axioms C3B17.pairLog_even
#print axioms C3B17.pairLog_concaveOn
#print axioms C3B17.carrier_pair_antitone
#print axioms C3B17.carrier_pair_antitone_weighted
#print axioms C3B17.Rker_antitone_of_logConcave
#print axioms C3B17.Rker_antitone_ae_of_logConcave
end AxiomAudit
