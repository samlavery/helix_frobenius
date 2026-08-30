import c3b17_A2

/-!
# C3 batch 18, block A1 — **all-centre slice integrability**, from the explicit majorant

## What this repairs

Batch 17's `Rker_antitone_of_logConcave` carries **two** hypotheses: log-concavity of `Φ`
**and** `Integrable (fun p => p²·Φ(u+p)Φ(u−p))` at the comparison centre `u`.  The
hypothesis-free variant is only **almost-everywhere in `u`** (it routes through
`C3B14.pair_slice_ae`, which is a Fubini statement and gives no particular `u`).  So global
log-concavity alone did **not** compile the pointwise theorem.  Batch 17's headline is
corrected accordingly; this block removes the integrability hypothesis outright, for **every**
centre, with no Fubini.

## The mechanism — an explicit majorant, not an a.e. argument

The repository already proves a **global exponential majorant on the physical half-line**:

  `ThetaWronskianSuzukiGram.riemannXiKernel_le_majorant (hu : 0 ≤ u) :`
  `riemannXiKernel u ≤ xiKernelMajorantConstant * Real.exp (-3 * u / 2)`

Since `exp (-3u/2) ≤ 1` for `u ≥ 0`, this gives `Φ ≤ C` on `[0,∞)`; and `Φ` is **even**
(`riemannXiKernel_neg`, the Jacobi reflection), so `Φ ≤ C` on the **whole line**.  Then

  `p²·Φ(u+p)Φ(u−p) ≤ C · p²·Φ(u−p)`,

and `p ↦ p²Φ(u−p)` is integrable because, writing `p² = (u − (u−p))²` and expanding,
`(u−q)²Φ(q) = u²Φ(q) − 2u·kM1(q) + kM2(q)` is a combination of the three compiled
integrabilities `xiKernel_integrable`, `kM1_integrable`, `kM2_integrable`, and `p ↦ g(u−p)`
is integrable whenever `g` is (reflection then translation).

**No Fubini, no a.e. qualifier, every centre.**

Search record before construction: batches 10–14 were searched for reusable shifted-product
and polynomial-weight integrability lemmas.  Found and used: `C3B12.xiKernel_integrable`,
`C3B12.kM1_integrable`, `C3B12.kM2_integrable`, `riemannXiKernel_neg`,
`riemannXiKernel_le_majorant`, `xiKernelMajorantConstant_nonneg`.  `C3B14.pair_slice_ae` is
the a.e. Fubini route and is **deliberately not used here**.

SCOPE: one global bound, one integrability theorem, and the resulting pointwise antitonicity
statement whose only remaining hypothesis is about `Φ`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B18

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open C3B10
open C3B12
open C3B13
open C3B14
open C3B17

/-! ### 1. `Φ` is globally bounded -/

/-- `Φ ≤ C` on the whole line: the half-line majorant plus the Jacobi reflection. -/
theorem xiKernel_le_const (t : ℝ) :
    riemannXiKernel t ≤ xiKernelMajorantConstant := by
  have key : ∀ s : ℝ, 0 ≤ s → riemannXiKernel s ≤ xiKernelMajorantConstant := by
    intro s hs
    have h := riemannXiKernel_le_majorant hs
    have hexp : Real.exp (-3 * s / 2) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      linarith
    have hC : (0:ℝ) ≤ xiKernelMajorantConstant := xiKernelMajorantConstant_nonneg
    calc riemannXiKernel s ≤ xiKernelMajorantConstant * Real.exp (-3 * s / 2) := h
      _ ≤ xiKernelMajorantConstant * 1 := by
          exact mul_le_mul_of_nonneg_left hexp hC
      _ = xiKernelMajorantConstant := by ring
  rcases le_total 0 t with ht | ht
  · exact key t ht
  · have h := key (-t) (by linarith)
    rwa [riemannXiKernel_neg] at h

theorem xiKernelMajorantConstant_nonneg' : (0:ℝ) ≤ xiKernelMajorantConstant :=
  xiKernelMajorantConstant_nonneg

/-! ### 2. The polynomial-weight slice, at every centre -/

/-- `q ↦ (u−q)²·Φ(q)` is integrable: expand and use the three compiled moments. -/
theorem shifted_sq_xiKernel_integrable (u : ℝ) :
    Integrable (fun q : ℝ => (u - q) ^ 2 * riemannXiKernel q) := by
  have h : Integrable (fun q : ℝ =>
      u ^ 2 * riemannXiKernel q - 2 * u * kM1 q + kM2 q) :=
    ((xiKernel_integrable.const_mul (u ^ 2)).sub
      (kM1_integrable.const_mul (2 * u))).add kM2_integrable
  refine h.congr ?_
  filter_upwards with q
  show u ^ 2 * riemannXiKernel q - 2 * u * kM1 q + kM2 q
      = (u - q) ^ 2 * riemannXiKernel q
  unfold kM1 kM2
  ring

/-- Hence `p ↦ p²·Φ(u−p)` is integrable, by reflect-and-translate. -/
theorem sq_xiKernel_reflect_integrable (u : ℝ) :
    Integrable (fun p : ℝ => p ^ 2 * riemannXiKernel (u - p)) := by
  have h := (shifted_sq_xiKernel_integrable u).comp_sub_left u
  refine h.congr ?_
  filter_upwards with p
  show (u - (u - p)) ^ 2 * riemannXiKernel (u - p) = p ^ 2 * riemannXiKernel (u - p)
  ring_nf

/-! ### 3. THE ALL-CENTRE SLICE INTEGRABILITY -/

/-- **THE SLICE IS INTEGRABLE AT EVERY CENTRE.**  No Fubini, no almost-everywhere: the
explicit majorant `Φ ≤ C` dominates one leg and the three compiled moments carry the other. -/
theorem pair_slice_integrable (u : ℝ) :
    Integrable (fun p : ℝ => p ^ 2 * (riemannXiKernel (u + p) * riemannXiKernel (u - p))) := by
  have hmaj : Integrable
      (fun p : ℝ => xiKernelMajorantConstant * (p ^ 2 * riemannXiKernel (u - p))) :=
    (sq_xiKernel_reflect_integrable u).const_mul _
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ => p ^ 2 * (riemannXiKernel (u + p) * riemannXiKernel (u - p))) volume := by
    refine ((continuous_id.pow 2).aestronglyMeasurable.mul ?_)
    exact ((riemannXiKernel_measurable.comp (measurable_const.add measurable_id))).mul
      ((riemannXiKernel_measurable.comp (measurable_const.sub measurable_id)))
      |>.aestronglyMeasurable
  refine Integrable.mono hmaj hmeas ?_
  filter_upwards with p
  have h1 : 0 ≤ riemannXiKernel (u + p) := xiKernel_nonneg _
  have h2 : 0 ≤ riemannXiKernel (u - p) := xiKernel_nonneg _
  have hb : riemannXiKernel (u + p) ≤ xiKernelMajorantConstant := xiKernel_le_const _
  have hC : (0:ℝ) ≤ xiKernelMajorantConstant := xiKernelMajorantConstant_nonneg
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ p ^ 2 * (riemannXiKernel (u + p) * riemannXiKernel (u - p))),
    abs_of_nonneg (by positivity :
      (0:ℝ) ≤ xiKernelMajorantConstant * (p ^ 2 * riemannXiKernel (u - p)))]
  have hstep : riemannXiKernel (u + p) * riemannXiKernel (u - p)
      ≤ xiKernelMajorantConstant * riemannXiKernel (u - p) :=
    mul_le_mul_of_nonneg_right hb h2
  nlinarith [hstep, sq_nonneg p, h2, hC]

/-! ### 4. THE POINTWISE ANTITONICITY, hypothesis reduced to `Φ` alone -/

/-- **`Rker` ANTITONE ON `[0,∞)`, POINTWISE, with the ONLY remaining hypothesis about `Φ`.**
This is the statement batch 17's headline claimed; the slice hypothesis is now discharged for
every centre by `pair_slice_integrable`. -/
theorem Rker_antitone_of_logConcave'
    (hlc : ConcaveOn ℝ univ (fun t : ℝ => Real.log (riemannXiKernel t)))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : Rker v ≤ Rker u :=
  Rker_antitone_of_logConcave hlc hu huv (pair_slice_integrable u)

/-- Packaged as an `AntitoneOn`. -/
theorem Rker_antitoneOn_of_logConcave
    (hlc : ConcaveOn ℝ univ (fun t : ℝ => Real.log (riemannXiKernel t))) :
    AntitoneOn Rker (Ici (0:ℝ)) := by
  intro u hu v _ huv
  exact Rker_antitone_of_logConcave' hlc hu huv

end C3B18

section AxiomAudit
#print axioms C3B18.xiKernel_le_const
#print axioms C3B18.xiKernelMajorantConstant_nonneg'
#print axioms C3B18.shifted_sq_xiKernel_integrable
#print axioms C3B18.sq_xiKernel_reflect_integrable
#print axioms C3B18.pair_slice_integrable
#print axioms C3B18.Rker_antitone_of_logConcave'
#print axioms C3B18.Rker_antitoneOn_of_logConcave
end AxiomAudit
