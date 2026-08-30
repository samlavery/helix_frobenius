import c3b7_B3

/-!
# C3 batch 8, block A1 — TARGET A: the genuine `IntegrableOn` for the weighted ramp

Batch-7 ledger §0.3 recorded the defect: `C3B6.Theta.UTail` is a raw Bochner integral, so
`UTail_nonneg_of_cellDensity_nonneg` is *vacuously* available whenever the integrand fails
to be integrable (`C3B7.UTail_eq_zero_of_not_integrable`).  This file removes the defect.

Two ingredients, both elementary once `C3B7.cellDensity_abs_le` is in hand.

**(i) Measurability.**  `cellDensity x u = ∫_ℝ Φ(u+p)Φ(u−p)cos(2xp) dp` is a parametric
Bochner integral whose integrand is jointly measurable, because
`CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_measurable` is compiled in the
repository.  `MeasureTheory.StronglyMeasurable.integral_prod_right'` then gives
`StronglyMeasurable (cellDensity x)` directly — no continuity, no uniform convergence, no
`tsum` measurability needed.

**(ii) Super-exponential decay.**  From `C3B7.cellDensity_abs_le`, with `A₁(u) = 2πe^{2u}`,

  `|C(u,x)| ≤ 16(π²e^{5u}·2(A₁+3)²e^{−A₁} + π²e^{5u}·128(A₁+3)²e^{−2A₁})`
           ≤ `2080·π²e^{5u}(A₁+3)²e^{−A₁}`          (`e^{−2A₁} ≤ e^{−A₁}`)
           ≤ `33280·π⁴e^{9u}e^{−A₁}`                (`(A₁+3)² ≤ 4A₁²` at `A₁ ≥ 3`,
                                                     `A₁² = 4π²e^{4u}`)

and, for `u ≥ s` with `A₁(s) ≥ 20`, `A₁(u) = A₁(s)e^{2(u−s)} ≥ A₁(s) + 2A₁(s)(u−s)
≥ A₁(s) + 40(u−s)`, so `e^{9u}e^{−A₁(u)} ≤ e^{9s}e^{−A₁(s)}·e^{−31(u−s)}`.  Finally
`(u−s)²/2 ≤ e^{u−s}` turns the ramp weight into one more unit of exponent, leaving
`e^{−30(u−s)}`, which `exp_neg_integrableOn_Ioi` integrates.

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B8

open C3B6.Bessel
open C3B6.Theta
open C3B7
open CriticalLinePhasor.ThetaWronskianSuzukiGram

/-! ### 1. Monotonicity of the head radial variable -/

theorem modeA_head_mono {s u : ℝ} (h : s ≤ u) : modeA 0 0 s ≤ modeA 0 0 u := by
  rw [modeA_head, modeA_head]
  have hpi := Real.pi_pos
  have hexp : Real.exp (2 * s) ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
  nlinarith [hexp, Real.exp_pos (2 * s)]

/-- `A₁(u) = A₁(s)·e^{2(u−s)}` — the head radial variable is a pure exponential in height. -/
theorem modeA_head_ratio (s u : ℝ) :
    modeA 0 0 u = modeA 0 0 s * Real.exp (2 * (u - s)) := by
  have he : Real.exp (2 * u) = Real.exp (2 * s) * Real.exp (2 * (u - s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [modeA_head, modeA_head, he]
  ring

/-- The linear-in-height lower bound driving the decay: `A₁(u) ≥ A₁(s) + 40(u−s)`. -/
theorem modeA_head_lin {s u : ℝ} (hs : 20 ≤ modeA 0 0 s) (hsu : s ≤ u) :
    modeA 0 0 s + 40 * (u - s) ≤ modeA 0 0 u := by
  have hexp : 1 + 2 * (u - s) ≤ Real.exp (2 * (u - s)) := by
    have := Real.add_one_le_exp (2 * (u - s))
    linarith
  have hratio := modeA_head_ratio s u
  have hnn : (0 : ℝ) ≤ u - s := by linarith
  nlinarith [hexp, hratio, hs, hnn]

/-! ### 2. Measurability of the cell density -/

theorem cellDensity_stronglyMeasurable (x : ℝ) :
    StronglyMeasurable (fun u : ℝ => cellDensity x u) := by
  have hmeas : Measurable (fun q : ℝ × ℝ =>
      riemannXiKernel (q.1 + q.2) * riemannXiKernel (q.1 - q.2)
        * Real.cos (2 * x * q.2)) := by
    have h1 : Measurable (fun q : ℝ × ℝ => riemannXiKernel (q.1 + q.2)) :=
      riemannXiKernel_measurable.comp (measurable_fst.add measurable_snd)
    have h2 : Measurable (fun q : ℝ × ℝ => riemannXiKernel (q.1 - q.2)) :=
      riemannXiKernel_measurable.comp (measurable_fst.sub measurable_snd)
    have h3 : Measurable (fun q : ℝ × ℝ => Real.cos (2 * x * q.2)) :=
      Real.continuous_cos.measurable.comp (measurable_const.mul measurable_snd)
    exact (h1.mul h2).mul h3
  exact hmeas.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))

theorem cellDensity_aestronglyMeasurable (x : ℝ) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun u : ℝ => cellDensity x u) μ :=
  (cellDensity_stronglyMeasurable x).aestronglyMeasurable

/-! ### 3. The simplified decay bound -/

theorem cellDensity_abs_le_simple (x : ℝ) {u : ℝ} (hA : 20 ≤ modeA 0 0 u) :
    |cellDensity x u|
      ≤ 2080 * Real.pi ^ 2 * Real.exp (5 * u) * (modeA 0 0 u + 3) ^ 2
        * Real.exp (-modeA 0 0 u) := by
  have h := cellDensity_abs_le x hA
  have hA0 : (0 : ℝ) < modeA 0 0 u := by linarith
  have hm : modeBndS x u (0, 0)
      = Real.pi ^ 2 * Real.exp (5 * u)
        * (2 * (modeA 0 0 u + 3) ^ 2 * Real.exp (-modeA 0 0 u)) := by
    unfold modeBndS
    norm_num
  rw [hm] at h
  have he2 : Real.exp (-(2 * modeA 0 0 u)) ≤ Real.exp (-modeA 0 0 u) :=
    Real.exp_le_exp.mpr (by linarith)
  have hbase : (0 : ℝ) ≤ Real.pi ^ 2 * Real.exp (5 * u) * (modeA 0 0 u + 3) ^ 2 := by
    have := Real.pi_pos
    positivity
  nlinarith [h, he2, hbase, Real.exp_pos (-modeA 0 0 u)]

/-- **THE DECAY BOUND.**  `|C(u,x)| ≤ 33280π⁴e^{9s}e^{−A₁(s)}·e^{−31(u−s)}` for `u ≥ s`. -/
theorem cellDensity_decay (x : ℝ) {s u : ℝ} (hs : 20 ≤ modeA 0 0 s) (hsu : s ≤ u) :
    |cellDensity x u|
      ≤ 33280 * Real.pi ^ 4 * Real.exp (9 * s) * Real.exp (-modeA 0 0 s)
        * Real.exp (-(31 * (u - s))) := by
  have hpi := Real.pi_pos
  have hAu : 20 ≤ modeA 0 0 u := le_trans hs (modeA_head_mono hsu)
  have hAu0 : (0 : ℝ) < modeA 0 0 u := by linarith
  have hstep1 := cellDensity_abs_le_simple x hAu
  have hsq : (modeA 0 0 u + 3) ^ 2 ≤ 4 * modeA 0 0 u ^ 2 := by nlinarith [hAu]
  have hA2 : modeA 0 0 u ^ 2 = 4 * Real.pi ^ 2 * Real.exp (4 * u) := by
    have hsqe : Real.exp (2 * u) ^ 2 = Real.exp (4 * u) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [modeA_head]
    nlinarith [hsqe]
  have hE : (0 : ℝ) < Real.exp (-modeA 0 0 u) := Real.exp_pos _
  have hcoef : (0 : ℝ) ≤ 2080 * Real.pi ^ 2 * Real.exp (5 * u) := by positivity
  have hexp94 : Real.exp (5 * u) * Real.exp (4 * u) = Real.exp (9 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hstep2 : |cellDensity x u|
      ≤ 33280 * Real.pi ^ 4 * Real.exp (9 * u) * Real.exp (-modeA 0 0 u) := by
    refine hstep1.trans ?_
    have hprod : (modeA 0 0 u + 3) ^ 2 * Real.exp (-modeA 0 0 u)
        ≤ (16 * Real.pi ^ 2 * Real.exp (4 * u)) * Real.exp (-modeA 0 0 u) := by
      refine mul_le_mul_of_nonneg_right ?_ hE.le
      calc (modeA 0 0 u + 3) ^ 2 ≤ 4 * modeA 0 0 u ^ 2 := hsq
        _ = 16 * Real.pi ^ 2 * Real.exp (4 * u) := by rw [hA2]; ring
    calc
      2080 * Real.pi ^ 2 * Real.exp (5 * u) * (modeA 0 0 u + 3) ^ 2
          * Real.exp (-modeA 0 0 u)
          = (2080 * Real.pi ^ 2 * Real.exp (5 * u))
            * ((modeA 0 0 u + 3) ^ 2 * Real.exp (-modeA 0 0 u)) := by ring
      _ ≤ (2080 * Real.pi ^ 2 * Real.exp (5 * u))
            * ((16 * Real.pi ^ 2 * Real.exp (4 * u))
              * Real.exp (-modeA 0 0 u)) :=
          mul_le_mul_of_nonneg_left hprod hcoef
      _ = 33280 * Real.pi ^ 4 * Real.exp (9 * u)
            * Real.exp (-modeA 0 0 u) := by rw [← hexp94]; ring
  refine hstep2.trans ?_
  have hlin := modeA_head_lin hs hsu
  have hexpA : Real.exp (-modeA 0 0 u)
      ≤ Real.exp (-modeA 0 0 s) * Real.exp (-(40 * (u - s))) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hexp9 : Real.exp (9 * u) = Real.exp (9 * s) * Real.exp (9 * (u - s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcomb : Real.exp (9 * (u - s)) * Real.exp (-(40 * (u - s)))
      = Real.exp (-(31 * (u - s))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc 33280 * Real.pi ^ 4 * Real.exp (9 * u) * Real.exp (-modeA 0 0 u)
      ≤ 33280 * Real.pi ^ 4 * (Real.exp (9 * s) * Real.exp (9 * (u - s)))
          * (Real.exp (-modeA 0 0 s) * Real.exp (-(40 * (u - s)))) := by
        rw [hexp9]
        refine mul_le_mul_of_nonneg_left hexpA ?_
        positivity
    _ = 33280 * Real.pi ^ 4 * Real.exp (9 * s) * Real.exp (-modeA 0 0 s)
          * (Real.exp (9 * (u - s)) * Real.exp (-(40 * (u - s)))) := by ring
    _ = 33280 * Real.pi ^ 4 * Real.exp (9 * s) * Real.exp (-modeA 0 0 s)
          * Real.exp (-(31 * (u - s))) := by rw [hcomb]

/-! ### 4. The ramp weight costs one unit of exponent -/

theorem sq_le_two_exp {w : ℝ} (hw : 0 ≤ w) : w ^ 2 / 2 ≤ Real.exp w := by
  have h := Real.quadratic_le_exp_of_nonneg hw
  linarith

/-! ### 5. TARGET A -/

/-- **TARGET A.**  The weighted ramp is genuinely integrable on `(s,∞)`, so
`C3B6.Theta.UTail x s` is the analytic `U_x(s)` and not the Bochner default `0`. -/
theorem cellDensity_ramp_integrableOn (x : ℝ) {s : ℝ} (hs : 20 ≤ modeA 0 0 s) :
    IntegrableOn (fun u => (u - s) ^ 2 / 2 * cellDensity x u) (Ioi s) := by
  have hpi := Real.pi_pos
  set K : ℝ := 33280 * Real.pi ^ 4 * Real.exp (9 * s) * Real.exp (-modeA 0 0 s) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  have hmaj : IntegrableOn
      (fun u : ℝ => K * Real.exp (30 * s) * Real.exp (-30 * u)) (Ioi s) :=
    (exp_neg_integrableOn_Ioi s (by norm_num : (0 : ℝ) < 30)).const_mul _
  refine Integrable.mono hmaj ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ (cellDensity_aestronglyMeasurable x _)
    exact (((continuous_id.sub continuous_const).pow 2).div_const 2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := s))] with u hu
    have hsu : s ≤ u := le_of_lt hu
    have hw : (0 : ℝ) ≤ u - s := by linarith
    have hdec := cellDensity_decay x hs hsu
    have hramp : (u - s) ^ 2 / 2 ≤ Real.exp (u - s) := sq_le_two_exp hw
    have hprod : Real.exp (u - s) * Real.exp (-(31 * (u - s)))
        = Real.exp (-(30 * (u - s))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hshift : Real.exp (-(30 * (u - s)))
        = Real.exp (30 * s) * Real.exp (-30 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (u - s) ^ 2 / 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ K * Real.exp (30 * s) * Real.exp (-30 * u))]
    calc (u - s) ^ 2 / 2 * |cellDensity x u|
        ≤ (u - s) ^ 2 / 2 * (K * Real.exp (-(31 * (u - s)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hKdef]
          exact hdec
      _ ≤ Real.exp (u - s) * (K * Real.exp (-(31 * (u - s)))) := by
          refine mul_le_mul_of_nonneg_right hramp ?_
          positivity
      _ = K * (Real.exp (u - s) * Real.exp (-(31 * (u - s)))) := by ring
      _ = K * Real.exp (-(30 * (u - s))) := by rw [hprod]
      _ = K * Real.exp (30 * s) * Real.exp (-30 * u) := by rw [hshift]; ring

/-- The batch-7 defect is closed on the certified range: `UTail` is the analytic object and
is nonnegative there. -/
theorem UTail_nonneg_analytic (x : ℝ) {s : ℝ}
    (hs : ∀ u ∈ Ioi s, 20 * (|x| + 1) ^ 2 ≤ modeA 0 0 u) :
    0 ≤ UTail x s :=
  UTail_nonneg_of_cellDensity_nonneg fun u hu => (cellDensity_pos_uncond x (hs u hu)).le

end C3B8

section AxiomAudit
#print axioms C3B8.modeA_head_mono
#print axioms C3B8.modeA_head_ratio
#print axioms C3B8.modeA_head_lin
#print axioms C3B8.cellDensity_stronglyMeasurable
#print axioms C3B8.cellDensity_abs_le_simple
#print axioms C3B8.cellDensity_decay
#print axioms C3B8.sq_le_two_exp
#print axioms C3B8.cellDensity_ramp_integrableOn
#print axioms C3B8.UTail_nonneg_analytic
end AxiomAudit
