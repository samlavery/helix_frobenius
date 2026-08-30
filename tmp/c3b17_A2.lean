import c3b17_A1

/-!
# C3 batch 17, block A2 — the signed refinement of the window bound

Batches 15/16 bounded the complement by its **mass**: `∫_{compl} R cos ≥ −∫_{compl} R`.  The
cosine-lobe idea is to use the fact that `|cos|` is small on most of the complement.  The
compilable core of that idea is the **signed** bound

  `cosMom R (2x) ≥ ∫_{(-a,a)} R cos(2xv) dv − ∫_{compl} R·|cos(2xv)| dv`,

which is pointwise better than the mass bound (`|cos| ≤ 1`) and needs no monotonicity at all.

Two further facts are compiled here:

* `central_nonneg_first_lobe` — on `|v| ≤ π/(4|x|)` the clock has not yet turned, so the
  central integral is **nonnegative for free**; at that window the whole lower bound is
  `−∫_{compl}R|cos|`;
* `window_lower_compl_of_signed` — the mass bound is recovered from the signed one, so nothing
  is lost.

**What is NOT compiled, named exactly.**  The full `k`-lobe alternating bound
`cosMom R (2x) ≥ 2(J₀ − J₁ + … ± J_{k−1})` additionally needs the lobe masses `(J_k)` to be
**decreasing**, which follows from `Rker` antitone (available conditionally as
`C3B17.Rker_antitone_of_logConcave`) **plus a half-period change of variables** relating
consecutive lobes.  That change of variables is not formalised here.  Measured reaches of the
partial sums (batch 16 §P4): `2-lobe 8.863342`, `4-lobe 12.558529`, `6-lobe 15.563725`,
`8-lobe 18.331719`, against the quadratic window's `6.638679`.

SCOPE: one refined inequality and two corollaries.  Nothing here decides the target.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B17

open C3B10
open C3B14
open C3B15

/-- `R·|cos|` is integrable — dominated by `R`. -/
theorem Rker_abscos_integrable (x : ℝ) :
    Integrable (fun v : ℝ => Rker v * |Real.cos (2 * x * v)|) := by
  refine Rker_integrable.mul_bdd (c := 1) ?_ ?_
  · exact ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).abs).aestronglyMeasurable
  · filter_upwards with v
    simpa using Real.abs_cos_le_one (2 * x * v)

/-- **THE SIGNED WINDOW BOUND.**  The complement contributes at worst `−∫R|cos|`, not
`−∫R`.  No monotonicity, no hypothesis. -/
theorem window_lower_signed (a x : ℝ) :
    (∫ v in Ioo (-a) a, Rker v * Real.cos (2 * x * v))
        - (∫ v in (Ioo (-a) a)ᶜ, Rker v * |Real.cos (2 * x * v)|)
      ≤ cosMom Rker (2 * x) := by
  have hInt := Rker_cos_integrable x
  have hAbs := Rker_abscos_integrable x
  have hsplit : (∫ v in Ioo (-a) a, Rker v * Real.cos (2 * x * v))
      + (∫ v in (Ioo (-a) a)ᶜ, Rker v * Real.cos (2 * x * v))
      = ∫ v : ℝ, Rker v * Real.cos (2 * x * v) :=
    integral_add_compl measurableSet_Ioo hInt
  have htail : -(∫ v in (Ioo (-a) a)ᶜ, Rker v * |Real.cos (2 * x * v)|)
      ≤ ∫ v in (Ioo (-a) a)ᶜ, Rker v * Real.cos (2 * x * v) := by
    rw [← integral_neg]
    refine integral_mono_ae (hAbs.integrableOn.neg) hInt.integrableOn ?_
    filter_upwards with v
    have hR : 0 ≤ Rker v := Rker_nonneg v
    have hc : -|Real.cos (2 * x * v)| ≤ Real.cos (2 * x * v) := neg_abs_le _
    nlinarith [hR, hc]
  have hval : cosMom Rker (2 * x) = ∫ v : ℝ, Rker v * Real.cos (2 * x * v) := rfl
  rw [hval, ← hsplit]
  linarith [htail]

/-- The signed bound implies the mass bound of batch 15, so nothing is lost by using it. -/
theorem window_lower_compl_of_signed (a x : ℝ) :
    (∫ v in Ioo (-a) a, Rker v * Real.cos (2 * x * v))
        - (∫ v in (Ioo (-a) a)ᶜ, Rker v)
      ≤ cosMom Rker (2 * x) := by
  refine le_trans ?_ (window_lower_signed a x)
  have hmono : (∫ v in (Ioo (-a) a)ᶜ, Rker v * |Real.cos (2 * x * v)|)
      ≤ ∫ v in (Ioo (-a) a)ᶜ, Rker v := by
    refine integral_mono_ae (Rker_abscos_integrable x).integrableOn
      Rker_integrable.integrableOn ?_
    filter_upwards with v
    have hR : 0 ≤ Rker v := Rker_nonneg v
    have hc : |Real.cos (2 * x * v)| ≤ 1 := by
      simpa using Real.abs_cos_le_one (2 * x * v)
    nlinarith [hR, hc]
  linarith [hmono]

/-- **THE FIRST LOBE IS FREE.**  Inside `|v| ≤ π/(4|x|)` the clock has not turned, so the
central integrand is nonnegative and the central integral is `≥ 0` with no estimate. -/
theorem central_nonneg_first_lobe {a x : ℝ} (ha : 0 ≤ a) (hax : 2 * |x| * a ≤ Real.pi / 2) :
    0 ≤ ∫ v in Ioo (-a) a, Rker v * Real.cos (2 * x * v) := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  have hR : 0 ≤ Rker v := Rker_nonneg v
  have hva : |v| ≤ a := by rw [abs_le]; exact ⟨le_of_lt hv.1, le_of_lt hv.2⟩
  have habs : |2 * x * v| = 2 * |x| * |v| := by
    rw [abs_mul, abs_mul, abs_two]
  have hle : |2 * x * v| ≤ Real.pi / 2 := by
    rw [habs]
    have h1 : 2 * |x| * |v| ≤ 2 * |x| * a :=
      mul_le_mul_of_nonneg_left hva (by positivity)
    linarith [hax, h1]
  have hcos : 0 ≤ Real.cos (2 * x * v) := by
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · have := abs_le.mp hle
      linarith [this.1]
    · have := abs_le.mp hle
      linarith [this.2]
  positivity

/-- Consequently, at the first-lobe window the entire lower bound is the signed complement
term — the exact statement the `k`-lobe programme refines. -/
theorem first_lobe_lower {a x : ℝ} (ha : 0 ≤ a) (hax : 2 * |x| * a ≤ Real.pi / 2) :
    -(∫ v in (Ioo (-a) a)ᶜ, Rker v * |Real.cos (2 * x * v)|) ≤ cosMom Rker (2 * x) := by
  have h1 := window_lower_signed a x
  have h2 := central_nonneg_first_lobe ha hax
  linarith [h1, h2]

end C3B17

section AxiomAudit
#print axioms C3B17.Rker_abscos_integrable
#print axioms C3B17.window_lower_signed
#print axioms C3B17.window_lower_compl_of_signed
#print axioms C3B17.central_nonneg_first_lobe
#print axioms C3B17.first_lobe_lower
end AxiomAudit
