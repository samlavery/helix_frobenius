import c3b14_A2

/-!
# C3 batch 15, block A1 — the **corrected window bound**, and two central lower bounds

## The retraction this block repairs

Batch 14's ledger proposed, as its "smallest next Lean theorem":

```
-- FALSE:
    2 * (∫ v in Ioo (-a) a, Rker v * cos (2*x*v)) - 2 * (∫ v in Ioi a, Rker v)
      ≤ cosMom Rker (2*x)
```

**It is false, and it fails at `x = 0`.**  Write `S := ∫_{(0,∞)}R`, so `cosMom Rker 0 = 2S`.
As `a → ∞` the left side tends to `2·(2S) − 0 = 4S` and the right side is `2S`, so the claim
asserts `S ≤ 0`; but `2S = 1.14198308344e−02 > 0`.  The window and its complement
**partition** the line, so the central piece enters with coefficient `1`.  Measured
(`tmp/c3b15_num1_out.txt` §W0/W1): over 30 hostile `(a,x)` pairs the retracted form is
violated **24** times and the corrected form **0** times.

## What is proved here

`window_lower_compl` and `window_lower_tail` — the corrected bound, in the complement form
(no set algebra) and in the `Ioi a` form requested, the latter through the even-tail change
of variables `tail_reflect`.  Then two independent central lower bounds, both from Mathlib
and both pre-tested numerically before formalisation (§C1/C2 of the same output, where every
printed bound is checked against the exact central integral):

* `central_ge_quadratic` — from `Real.one_sub_sq_div_two_le_cos`, valid for **all** `x, a`;
* `central_ge_linear` — from `Real.one_sub_mul_le_cos`, valid on `2|x|a ≤ π/2`, and sharper
  than the quadratic near the endpoint (at `z = π/2` it is exact, where the quadratic gives
  `−0.2337`).

SCOPE: one corrected inequality, one change of variables, two central bounds.  Nothing here
decides the sign of `cosMom Rker (2x)`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B15

open C3B10
open C3B14

/-! ### 0. Integrability of the clocked kernel and of its window restrictions -/

theorem Rker_cos_integrable (x : ℝ) : Integrable (fun v : ℝ => Rker v * Real.cos (2 * x * v)) := by
  refine Rker_integrable.mul_bdd (c := 1) ?_ ?_
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with v; simpa using Real.abs_cos_le_one (2 * x * v)

theorem Rker_aesm : AEStronglyMeasurable Rker volume := Rker_integrable.aestronglyMeasurable

/-- On a bounded window, `v² · R` is integrable: `v²` is bounded there. -/
theorem sq_Rker_integrableOn (a : ℝ) :
    IntegrableOn (fun v : ℝ => v ^ 2 * Rker v) (Ioo (-a) a) := by
  refine Integrable.mono' (g := fun v : ℝ => a ^ 2 * Rker v)
    ((Rker_integrable.const_mul (a ^ 2)).integrableOn) ?_ ?_
  · exact ((continuous_id.pow 2).aestronglyMeasurable.mul Rker_aesm).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have hR : 0 ≤ Rker v := Rker_nonneg v
    have hv2 : v ^ 2 ≤ a ^ 2 := by
      have h1 : -a < v := hv.1
      have h2 : v < a := hv.2
      nlinarith [sq_nonneg (a - v), sq_nonneg (a + v)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ v ^ 2 * Rker v)]
    nlinarith [hv2, hR]

/-- On a bounded window, `|v| · R` is integrable. -/
theorem abs_Rker_integrableOn (a : ℝ) (_ha : 0 ≤ a) :
    IntegrableOn (fun v : ℝ => |v| * Rker v) (Ioo (-a) a) := by
  refine Integrable.mono' (g := fun v : ℝ => a * Rker v)
    ((Rker_integrable.const_mul a).integrableOn) ?_ ?_
  · exact (continuous_abs.aestronglyMeasurable.mul Rker_aesm).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have hR : 0 ≤ Rker v := Rker_nonneg v
    have hva : |v| ≤ a := by
      rw [abs_le]; exact ⟨le_of_lt hv.1, le_of_lt hv.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ |v| * Rker v)]
    nlinarith [hva, hR, abs_nonneg v]

/-! ### 1. The even-tail change of variables -/

/-- **THE EVEN-TAIL CHANGE OF VARIABLES.**  `R` is even, so the left tail equals the right
tail.  `Mathlib.integral_comp_neg_Iic` supplies the reflection; `C3B14.Rker_even` supplies
the invariance of the integrand. -/
theorem tail_reflect (a : ℝ) : (∫ v in Iic (-a), Rker v) = ∫ v in Ioi a, Rker v := by
  have h := integral_comp_neg_Iic (-a) Rker
  rw [neg_neg] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Iic fun v _ => ?_
  exact (Rker_even v).symm

/-! ### 2. THE CORRECTED WINDOW BOUND -/

/-- The complement form: no set algebra, and the tail appears as the complement mass. -/
theorem window_lower_compl (a x : ℝ) :
    (∫ v in Ioo (-a) a, Rker v * Real.cos (2 * x * v))
        - (∫ v in (Ioo (-a) a)ᶜ, Rker v)
      ≤ cosMom Rker (2 * x) := by
  have hInt := Rker_cos_integrable x
  have hsplit : (∫ v in Ioo (-a) a, Rker v * Real.cos (2 * x * v))
      + (∫ v in (Ioo (-a) a)ᶜ, Rker v * Real.cos (2 * x * v))
      = ∫ v : ℝ, Rker v * Real.cos (2 * x * v) :=
    integral_add_compl measurableSet_Ioo hInt
  have htail : -(∫ v in (Ioo (-a) a)ᶜ, Rker v)
      ≤ ∫ v in (Ioo (-a) a)ᶜ, Rker v * Real.cos (2 * x * v) := by
    rw [← integral_neg]
    refine integral_mono_ae (Rker_integrable.integrableOn.neg) hInt.integrableOn ?_
    filter_upwards with v
    have hR : 0 ≤ Rker v := Rker_nonneg v
    have hc : -1 ≤ Real.cos (2 * x * v) := Real.neg_one_le_cos _
    nlinarith [hR, hc]
  have hval : cosMom Rker (2 * x) = ∫ v : ℝ, Rker v * Real.cos (2 * x * v) := rfl
  rw [hval, ← hsplit]
  linarith [htail]

/-- **THE CORRECTED WINDOW BOUND, in the `Ioi a` form.**  This is the repaired version of
batch 14's proposal: the central piece carries coefficient **1**, and the tail mass enters
doubled because `R` is even. -/
theorem compl_mass (a : ℝ) (ha : 0 ≤ a) :
    (∫ v in (Ioo (-a) a)ᶜ, Rker v) = 2 * ∫ v in Ioi a, Rker v := by
  have hset : (Ioo (-a) a)ᶜ = Iic (-a) ∪ Ici a := by
    ext v
    simp only [mem_compl_iff, mem_Ioo, mem_union, mem_Iic, mem_Ici, not_and_or, not_lt]
  have hdisj : AEDisjoint volume (Iic (-a)) (Ici a) := by
    have hsub : Iic (-a) ∩ Ici a ⊆ Icc a (-a) := fun v hv => ⟨hv.2, hv.1⟩
    have hz : volume (Icc a (-a)) = 0 := by
      rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]
      linarith
    exact measure_mono_null hsub hz
  rw [hset, integral_union_ae hdisj measurableSet_Ici.nullMeasurableSet
    Rker_integrable.integrableOn Rker_integrable.integrableOn, tail_reflect a,
    integral_Ici_eq_integral_Ioi]
  ring

/-- The window carries all the mass except the two tails. -/
theorem window_mass (a : ℝ) (ha : 0 ≤ a) :
    (∫ v in Ioo (-a) a, Rker v) = cosMom Rker 0 - 2 * ∫ v in Ioi a, Rker v := by
  have hsplit : (∫ v in Ioo (-a) a, Rker v) + (∫ v in (Ioo (-a) a)ᶜ, Rker v)
      = ∫ v : ℝ, Rker v := integral_add_compl measurableSet_Ioo Rker_integrable
  have h0 : cosMom Rker 0 = ∫ v : ℝ, Rker v := by
    unfold cosMom
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show Rker v * Real.cos (0 * v) = Rker v
    rw [zero_mul, Real.cos_zero, mul_one]
  rw [h0, ← hsplit, compl_mass a ha]
  ring

theorem window_lower_tail (a x : ℝ) (ha : 0 ≤ a) :
    (∫ v in Ioo (-a) a, Rker v * Real.cos (2 * x * v))
        - 2 * (∫ v in Ioi a, Rker v)
      ≤ cosMom Rker (2 * x) := by
  have h := window_lower_compl a x
  rwa [compl_mass a ha] at h

/-! ### 3. CENTRAL LOWER BOUND I — the global quadratic

`Real.one_sub_sq_div_two_le_cos : 1 - z^2/2 ≤ cos z`, at `z = 2xv`, gives
`1 - 2x²v² ≤ cos(2xv)`.  Valid for every `x` and every `a`. -/

theorem central_ge_quadratic (a x : ℝ) :
    (∫ v in Ioo (-a) a, Rker v) - 2 * x ^ 2 * (∫ v in Ioo (-a) a, v ^ 2 * Rker v)
      ≤ ∫ v in Ioo (-a) a, Rker v * Real.cos (2 * x * v) := by
  have hR : IntegrableOn Rker (Ioo (-a) a) := Rker_integrable.integrableOn
  have hV : IntegrableOn (fun v : ℝ => v ^ 2 * Rker v) (Ioo (-a) a) := sq_Rker_integrableOn a
  have hC : IntegrableOn (fun v : ℝ => Rker v * Real.cos (2 * x * v)) (Ioo (-a) a) :=
    (Rker_cos_integrable x).integrableOn
  have hsub : (∫ v in Ioo (-a) a, (Rker v - 2 * x ^ 2 * (v ^ 2 * Rker v)))
      = (∫ v in Ioo (-a) a, Rker v)
        - 2 * x ^ 2 * (∫ v in Ioo (-a) a, v ^ 2 * Rker v) := by
    rw [integral_sub hR (hV.const_mul _), integral_const_mul]
  rw [← hsub]
  refine integral_mono_ae (hR.sub (hV.const_mul _)) hC ?_
  filter_upwards with v
  have hRn : 0 ≤ Rker v := Rker_nonneg v
  have hcos : 1 - (2 * x * v) ^ 2 / 2 ≤ Real.cos (2 * x * v) :=
    Real.one_sub_sq_div_two_le_cos
  have hkey : 1 - 2 * x ^ 2 * v ^ 2 ≤ Real.cos (2 * x * v) := by nlinarith [hcos]
  nlinarith [hkey, hRn]

/-! ### 4. CENTRAL LOWER BOUND II — the piecewise-linear bound

`Real.one_sub_mul_le_cos (0 ≤ z) (z ≤ π/2) : 1 - (2/π)·z ≤ cos z`.  On `|v| ≤ a` with
`2|x|a ≤ π/2` this gives `1 - (4|x|/π)|v| ≤ cos(2xv)`, which is **sharper than the quadratic
near the endpoint** — at `z = π/2` it is exact (`0`), where the quadratic gives `−0.2337`.
Pre-tested against the exact central integral (§C1/C2). -/

theorem central_ge_linear (a x : ℝ) (ha : 0 ≤ a) (hax : 2 * |x| * a ≤ Real.pi / 2) :
    (∫ v in Ioo (-a) a, Rker v) - (4 * |x| / Real.pi) * (∫ v in Ioo (-a) a, |v| * Rker v)
      ≤ ∫ v in Ioo (-a) a, Rker v * Real.cos (2 * x * v) := by
  have hR : IntegrableOn Rker (Ioo (-a) a) := Rker_integrable.integrableOn
  have hV : IntegrableOn (fun v : ℝ => |v| * Rker v) (Ioo (-a) a) := abs_Rker_integrableOn a ha
  have hC : IntegrableOn (fun v : ℝ => Rker v * Real.cos (2 * x * v)) (Ioo (-a) a) :=
    (Rker_cos_integrable x).integrableOn
  have hsub : (∫ v in Ioo (-a) a, (Rker v - (4 * |x| / Real.pi) * (|v| * Rker v)))
      = (∫ v in Ioo (-a) a, Rker v)
        - (4 * |x| / Real.pi) * (∫ v in Ioo (-a) a, |v| * Rker v) := by
    rw [integral_sub hR (hV.const_mul _), integral_const_mul]
  rw [← hsub]
  refine integral_mono_ae (hR.sub (hV.const_mul _)) hC ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  have hRn : 0 ≤ Rker v := Rker_nonneg v
  have hva : |v| ≤ a := by rw [abs_le]; exact ⟨le_of_lt hv.1, le_of_lt hv.2⟩
  have hz0 : (0 : ℝ) ≤ |2 * x * v| := abs_nonneg _
  have habs : |2 * x * v| = 2 * |x| * |v| := by
    rw [abs_mul, abs_mul, abs_two]
  have hzle : |2 * x * v| ≤ Real.pi / 2 := by
    rw [habs]
    have h1 : 2 * |x| * |v| ≤ 2 * |x| * a :=
      mul_le_mul_of_nonneg_left hva (by positivity)
    linarith [hax, h1]
  have hcos0 : 1 - 2 / Real.pi * |2 * x * v| ≤ Real.cos |2 * x * v| :=
    Real.one_sub_mul_le_cos hz0 hzle
  rw [Real.cos_abs, habs] at hcos0
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have heq : 2 / Real.pi * (2 * |x| * |v|) = 4 * |x| / Real.pi * |v| := by
    field_simp
    ring
  rw [heq] at hcos0
  have hmul := mul_le_mul_of_nonneg_left hcos0 hRn
  nlinarith [hmul]

end C3B15

section AxiomAudit
#print axioms C3B15.Rker_cos_integrable
#print axioms C3B15.sq_Rker_integrableOn
#print axioms C3B15.abs_Rker_integrableOn
#print axioms C3B15.tail_reflect
#print axioms C3B15.window_lower_compl
#print axioms C3B15.compl_mass
#print axioms C3B15.window_mass
#print axioms C3B15.window_lower_tail
#print axioms C3B15.central_ge_quadratic
#print axioms C3B15.central_ge_linear
end AxiomAudit
