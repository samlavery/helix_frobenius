import c3b16_A2

/-!
# C3 batch 16, block A3 — closing the witness gap: the exclusion, UNCONDITIONAL

`C3B16.no_adaptive_window_of_exists_witness` reduces the adaptive-window exclusion to a single
existential: some `c > 0` with `mass/4 < Tail c`.  Block A2 proved `Tail 0 = mass/2` and
`0 < mass`, so the witness exists as soon as `Tail` does not jump at `0` — i.e. as soon as
`c ↦ ∫_{(0,c]}R` is continuous at `0`, which is exactly continuity of the primitive of the
integrable `R`.

That is supplied here by `intervalIntegral.continuous_primitive`, and the exclusion becomes
**unconditional**: no numeric input, no witness hypothesis, nothing about zeros.

SCOPE: one continuity argument and its consequence.  Nothing here decides the target; the
conclusion is a statement about the *criterion* of batch 15, not about `Ξ`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B16

open C3B10
open C3B14
open C3B15

/-- `R` is interval-integrable on every interval, being globally integrable. -/
theorem Rker_intervalIntegrable (a b : ℝ) : IntervalIntegrable Rker volume a b :=
  Rker_integrable.intervalIntegrable

/-- The primitive `c ↦ ∫_0^c R` is continuous. -/
theorem Rker_primitive_continuous :
    Continuous fun c : ℝ => ∫ v in (0:ℝ)..c, Rker v :=
  intervalIntegral.continuous_primitive Rker_intervalIntegrable 0

/-- The tail decreases from `Tail 0` by exactly the mass swept: `Tail 0 − Tail c = ∫_0^c R`
for `c ≥ 0`. -/
theorem Tail_sub (c : ℝ) (hc : 0 ≤ c) :
    Tail 0 - Tail c = ∫ v in (0:ℝ)..c, Rker v := by
  have hunion : Ioc (0:ℝ) c ∪ Ioi c = Ioi (0:ℝ) := Ioc_union_Ioi_eq_Ioi hc
  have hdisj : Disjoint (Ioc (0:ℝ) c) (Ioi c) := by
    rw [Set.disjoint_left]
    intro v hv hv'
    exact absurd hv.2 (not_le.mpr hv')
  have hsplit : (∫ v in Ioc (0:ℝ) c, Rker v) + (∫ v in Ioi c, Rker v)
      = ∫ v in Ioi (0:ℝ), Rker v := by
    rw [← hunion]
    exact (setIntegral_union hdisj measurableSet_Ioi
      Rker_integrable.integrableOn Rker_integrable.integrableOn).symm
  have hiv : (∫ v in (0:ℝ)..c, Rker v) = ∫ v in Ioc (0:ℝ) c, Rker v :=
    intervalIntegral.integral_of_le hc
  unfold Tail
  rw [hiv]
  linarith [hsplit]

/-- **THE WITNESS EXISTS.**  `Tail 0 = mass/2 > mass/4` and the primitive is continuous at
`0` with value `0`, so some positive radius still keeps more than a quarter of the mass. -/
theorem exists_witness : ∃ c : ℝ, 0 < c ∧ cosMom Rker 0 / 4 < Tail c := by
  have hm := mass_pos
  have hcont := Rker_primitive_continuous
  have hz : (fun c : ℝ => ∫ v in (0:ℝ)..c, Rker v) 0 = 0 := by
    simp
  -- pick `c` so small that the swept mass is under `mass/4`
  have hpos : (0:ℝ) < cosMom Rker 0 / 4 := by linarith
  have hmem : Set.Iio (cosMom Rker 0 / 4) ∈ nhds ((fun c : ℝ => ∫ v in (0:ℝ)..c, Rker v) 0) := by
    rw [hz]
    exact Iio_mem_nhds hpos
  have hpre := hcont.continuousAt.preimage_mem_nhds hmem
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨δ / 2, by linarith, ?_⟩
  have hin : δ / 2 ∈ Metric.ball (0:ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  have hlt : (∫ v in (0:ℝ)..(δ/2), Rker v) < cosMom Rker 0 / 4 := hball hin
  have hsub := Tail_sub (δ/2) (by linarith)
  rw [Tail_zero] at hsub
  linarith [hsub, hlt]

/-- **THE ADAPTIVE-WINDOW EXCLUSION, UNCONDITIONAL.**  There is a single cap `X`, independent
of `a`, such that every `(a,x)` satisfying batch 15's criterion has `x² ≤ X`.  No adaptive
window `a(x)` can push the criterion past it.

This is what batch 15's ledger claimed and did not have; the missing pieces were `Tail`
antitone, `Qwin` monotone, the annulus lower bound, and this existence step. -/
theorem no_adaptive_window :
    ∃ X : ℝ, ∀ a x : ℝ, 0 ≤ a → 4 * Tail a ≤ cosMom Rker 0 →
      2 * x ^ 2 * Qwin a + 4 * Tail a ≤ cosMom Rker 0 → x ^ 2 ≤ X :=
  no_adaptive_window_of_exists_witness exists_witness

end C3B16

section AxiomAudit
#print axioms C3B16.Rker_intervalIntegrable
#print axioms C3B16.Rker_primitive_continuous
#print axioms C3B16.Tail_sub
#print axioms C3B16.exists_witness
#print axioms C3B16.no_adaptive_window
end AxiomAudit
