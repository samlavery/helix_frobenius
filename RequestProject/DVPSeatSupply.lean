import RequestProject.DVPWindowCount
import RequestProject.DVPSeatResonance

/-!
# The seat channel's K-supply

The deep-window multiplicity mass at an anchor `w` — the `hsummult`/`hK`
inputs of `seat_channel_off_tubes` — is finite and explicitly bounded by
the unit-window count (414): every zero in the deep window lies in the
strip window `(Re w − 1/2, Re w + 1/2]`, whose census mass is
`≤ 41·log(Re w + 3/2) + 6`.  UNCONDITIONAL, at every anchor with
`Re w ≥ e⁶ + 3/2`.
-/

open Complex
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The strip census finset is monotone. -/
theorem stripZeroFinset_subset {a b : ℝ} (hab : a ≤ b) :
    stripZeroFinset a ⊆ stripZeroFinset b := by
  unfold stripZeroFinset
  rw [Set.Finite.toFinset_subset_toFinset]
  intro ρ hρ
  exact ⟨hρ.1, hρ.2.1, le_trans hρ.2.2 hab⟩

/-- The deep window at a high anchor is a finite family. -/
theorem deep_window_finite {w : ℂ} (hre : (1:ℝ) ≤ w.re) :
    Finite {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|} := by
  have hj : Function.Injective
      (fun x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
          |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|} =>
        (⟨x.val.val, by
          show x.val.val ∈ (stripZeroWindow_finite (w.re + 1/2)).toFinset
          rw [Set.Finite.mem_toFinset]
          refine ⟨x.val.property, ?_, ?_⟩
          · have := (abs_lt.mp x.property.1).1
            linarith
          · have := (abs_lt.mp x.property.1).2
            linarith⟩ : ↥(stripZeroFinset (w.re + 1/2)))) := by
    intro x y hxy
    have h1 : x.val.val = y.val.val := by
      have h2 := congrArg
        (fun z : ↥(stripZeroFinset (w.re + 1/2)) => z.val) hxy
      simpa using h2
    exact Subtype.ext (Subtype.ext h1)
  have : Finite ↥(stripZeroFinset (w.re + 1/2)) := by
    infer_instance
  exact Finite.of_injective _ hj

/-- **The deep-window mass bound**: at every anchor with
`Re w ≥ e⁶ + 3/2`, the deep multiplicity family is summable and its total
is at most `41·log(Re w + 3/2) + 6` — the `hsummult`/`hK` supply of
`seat_channel_off_tubes` with explicit `K`, unconditional. -/
theorem deep_window_mass_bound {w : ℂ} (hre : Real.exp 6 + 3/2 ≤ w.re) :
    Summable (fun x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|} =>
      (ZD.xiOrderNat x.val.val : ℝ))
    ∧ (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|},
      (ZD.xiOrderNat x.val.val : ℝ))
      ≤ 41 * Real.log (w.re + 3/2) + 6 := by
  have he6 : (403:ℝ) ≤ Real.exp 6 := by
    have h3 : (20.08:ℝ) ≤ Real.exp 3 := by
      have h33 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        norm_num
      nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
    have h6 : Real.exp 6 = Real.exp 3 * Real.exp 3 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h3, Real.exp_pos 3]
  haveI hfin := deep_window_finite (w := w) (by linarith)
  letI := Fintype.ofFinite {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
    |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|}
  constructor
  · exact Summable.of_finite
  · rw [tsum_fintype]
    -- compare with the census difference over the unit window
    set a : ℝ := w.re - 1/2 with hadef
    set b : ℝ := w.re + 1/2 with hbdef
    have hab : a ≤ b := by rw [hadef, hbdef]; linarith
    have hsub := stripZeroFinset_subset hab
    -- the ℕ-level comparison
    have hemb : Function.Injective
        (fun x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
            |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|} =>
          x.val.val) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext hxy)
    have himg : ∀ x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|},
        x.val.val ∈ stripZeroFinset b \ stripZeroFinset a := by
      intro x
      rw [Finset.mem_sdiff]
      constructor
      · show x.val.val ∈ (stripZeroWindow_finite b).toFinset
        rw [Set.Finite.mem_toFinset]
        refine ⟨x.val.property, ?_, ?_⟩
        · have h1 := (abs_lt.mp x.property.1).1
          linarith
        · have h1 := (abs_lt.mp x.property.1).2
          rw [hbdef]
          linarith
      · show x.val.val ∉ (stripZeroWindow_finite a).toFinset
        rw [Set.Finite.mem_toFinset]
        intro hmem
        have h2 := hmem.2.2
        have := (abs_lt.mp x.property.1).1
        rw [hadef] at h2
        linarith
    have hsum_le : (∑ x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|},
        ZD.xiOrderNat x.val.val)
        ≤ ∑ ρ ∈ stripZeroFinset b \ stripZeroFinset a, ZD.xiOrderNat ρ := by
      have hmap : (∑ x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
          |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|},
          ZD.xiOrderNat x.val.val)
          = ∑ ρ ∈ Finset.univ.map
              ⟨fun x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
                  |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|} =>
                x.val.val, hemb⟩,
              ZD.xiOrderNat ρ := by
        rw [Finset.sum_map]
        simp only [Function.Embedding.coeFn_mk]
      rw [hmap]
      apply Finset.sum_le_sum_of_subset
      intro ρ hρ
      rw [Finset.mem_map] at hρ
      obtain ⟨x, _, hx⟩ := hρ
      rw [← hx]
      simp only [Function.Embedding.coeFn_mk]
      exact himg x
    have hdiff : (∑ ρ ∈ stripZeroFinset b \ stripZeroFinset a,
        ZD.xiOrderNat ρ) + (∑ ρ ∈ stripZeroFinset a, ZD.xiOrderNat ρ)
        = ∑ ρ ∈ stripZeroFinset b, ZD.xiOrderNat ρ :=
      Finset.sum_sdiff hsub
    have hcensus_a : (∑ ρ ∈ stripZeroFinset a, ZD.xiOrderNat ρ)
        = stripZeroCountMult a := rfl
    have hcensus_b : (∑ ρ ∈ stripZeroFinset b, ZD.xiOrderNat ρ)
        = stripZeroCountMult b := rfl
    -- apply 414 with T := a
    have h414 := zero_count_unit_window (T := a)
      (by rw [hadef]; linarith)
    have hb_eq : b = a + 1 := by rw [hadef, hbdef]; ring
    have hlog_eq : a + 2 = w.re + 3/2 := by rw [hadef]; ring
    -- assemble over ℝ
    have hsum_leR : (∑ x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|},
        (ZD.xiOrderNat x.val.val : ℝ))
        ≤ ((∑ ρ ∈ stripZeroFinset b \ stripZeroFinset a,
            ZD.xiOrderNat ρ : ℕ) : ℝ) := by
      exact_mod_cast hsum_le
    have hdiffR : ((∑ ρ ∈ stripZeroFinset b \ stripZeroFinset a,
        ZD.xiOrderNat ρ : ℕ) : ℝ)
        = (stripZeroCountMult b : ℝ) - (stripZeroCountMult a : ℝ) := by
      have hcast : ((∑ ρ ∈ stripZeroFinset b \ stripZeroFinset a,
          ZD.xiOrderNat ρ : ℕ) : ℝ) + (stripZeroCountMult a : ℝ)
          = (stripZeroCountMult b : ℝ) := by
        rw [← hcensus_a, ← hcensus_b]
        exact_mod_cast hdiff
      linarith
    calc (∑ x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1/2 ∧ |w.im| < |ρ.val.re - 1/2|},
        (ZD.xiOrderNat x.val.val : ℝ))
        ≤ (stripZeroCountMult b : ℝ) - (stripZeroCountMult a : ℝ) := by
          rw [← hdiffR]
          exact hsum_leR
      _ ≤ 41 * Real.log (a + 2) + 6 := by
          rw [hb_eq] at *
          exact h414
      _ = 41 * Real.log (w.re + 3/2) + 6 := by
          rw [hlog_eq]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.stripZeroFinset_subset
#print axioms CriticalLinePhasor.DVP.deep_window_finite
#print axioms CriticalLinePhasor.DVP.deep_window_mass_bound
end AxiomAudit
