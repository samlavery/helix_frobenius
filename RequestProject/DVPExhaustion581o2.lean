import RequestProject.DVPHardyDetector
import RequestProject.DVPLift581o2

/-!
# The exhaustion at height 581/2 (rung-290.5)

Twelve sign changes of the Hardy detector below height 58 produce fourteen
DISTINCT on-line strip zeros; the compiled census `N_all(58) = 12` then
leaves no room for anything else: **every nontrivial zero of ordinate
`|γ| ≤ 58` lies on the critical line** — conditional here on the ladder
hypothesis (the thirteen certified station signs), which the station
tables discharge.
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- Detector continuity to height 132 (same proof as the 58 version). -/
theorem hardyG_continuousOn581o2 : ContinuousOn hardyG (Set.Icc (10:ℝ) (581/2)) := by
  intro t ht
  have hline0 : line t ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    rw [lineIm] at this
    simp at this
    linarith [ht.1]
  have hline1 : line t ≠ 1 := by
    intro h0
    have := congrArg Complex.im h0
    rw [lineIm] at this
    simp at this
    linarith [ht.1]
  have hlinecont : Continuous line := by
    unfold CriticalLinePhasor.CarrierScale.line
      CriticalLinePhasor.CarrierScale.lineC
    fun_prop
  have hc : ContinuousAt
      (Complex.re ∘ completedRiemannZeta ∘ line) t := by
    apply ContinuousAt.comp
    · exact Complex.continuous_re.continuousAt
    · apply ContinuousAt.comp
      · exact (differentiableAt_completedZeta hline0 hline1).continuousAt
      · exact hlinecont.continuousAt
  exact hc.continuousWithinAt

/-- Sign change to height 132. -/
theorem hardyG_sign_change581o2 {a b : ℝ} (hab : a ≤ b) (h10 : 10 ≤ a)
    (h132 : b ≤ 581/2) (hsign : hardyG a * hardyG b < 0) :
    ∃ t : ℝ, a < t ∧ t < b ∧ line t ∈ ZD.NontrivialZeros := by
  have hsub : Set.Icc a b ⊆ Set.Icc (10:ℝ) (581/2) :=
    Set.Icc_subset_Icc h10 h132
  have hcont : ContinuousOn hardyG (Set.Icc a b) :=
    hardyG_continuousOn581o2.mono hsub
  have hane : hardyG a ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsign
    exact lt_irrefl _ hsign
  have hbne : hardyG b ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsign
    exact lt_irrefl _ hsign
  have hzero : ∃ t ∈ Set.Icc a b, hardyG t = 0 := by
    rcases lt_or_gt_of_ne hane with hneg | hpos
    · have hbpos : 0 < hardyG b := by
        rcases lt_trichotomy (hardyG b) 0 with h | h | h
        · nlinarith
        · exact absurd h hbne
        · exact h
      have := intermediate_value_Icc hab hcont
      obtain ⟨t, htmem, hteq⟩ := this ⟨hneg.le, hbpos.le⟩
      exact ⟨t, htmem, hteq⟩
    · have hbneg : hardyG b < 0 := by
        rcases lt_trichotomy (hardyG b) 0 with h | h | h
        · exact h
        · exact absurd h hbne
        · nlinarith
      have := intermediate_value_Icc' hab hcont
      obtain ⟨t, htmem, hteq⟩ := this ⟨hbneg.le, hpos.le⟩
      exact ⟨t, htmem, hteq⟩
  obtain ⟨t, htmem, hteq⟩ := hzero
  have htne_a : t ≠ a := fun h => hane (h ▸ hteq)
  have htne_b : t ≠ b := fun h => hbne (h ▸ hteq)
  refine ⟨t, lt_of_le_of_ne htmem.1 (Ne.symm htne_a),
    lt_of_le_of_ne htmem.2 htne_b, ?_⟩
  exact hardyG_online (by linarith [htmem.1]) hteq


/-- **The ladder hypothesis**: thirteen stations in `[10, 58]`, strictly
increasing, with alternating-sign detector values (formulated as fourteen
adjacent sign changes). -/
def LadderData581o2 : Prop :=
  ∃ t : Fin 133 → ℝ, StrictMono t
    ∧ (∀ i, 10 ≤ t i ∧ t i ≤ 581/2)
    ∧ ∀ i : Fin 132, hardyG (t i.castSucc) * hardyG (t i.succ) < 0

/-- **Exhaustion**: the ladder plus the census force every strip zero of
ordinate `≤ 58` onto the line. -/
theorem online_below_581o2_of_ladder (hL : LadderData581o2) :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 581/2 → ρ.re = 1/2 := by
  obtain ⟨t, htmono, htrange, hsign⟩ := hL
  -- the fourteen interior zeros
  have hex : ∀ i : Fin 132, ∃ z : ℝ, t i.castSucc < z ∧ z < t i.succ
      ∧ line z ∈ ZD.NontrivialZeros := by
    intro i
    exact hardyG_sign_change581o2
      (htmono (Fin.castSucc_lt_succ (i := i))).le
      (htrange i.castSucc).1 (htrange i.succ).2 (hsign i)
  choose zs hz1 hz2 hz3 using hex
  have hzs_lt : ∀ i j : Fin 132, i < j → zs i < zs j := by
    intro i j hij
    have h1 : zs i < t i.succ := hz2 i
    have h2 : t j.castSucc < zs j := hz1 j
    have h3 : i.succ ≤ j.castSucc := by
      rw [Fin.le_def]
      simp only [Fin.val_succ, Fin.coe_castSucc]
      exact hij
    have h4 : t i.succ ≤ t j.castSucc := htmono.monotone h3
    linarith
  have hzs_pos : ∀ i, 0 < zs i := by
    intro i
    have := hz1 i
    have := (htrange i.castSucc).1
    linarith
  have hzs_le : ∀ i, zs i ≤ 581/2 := by
    intro i
    have := hz2 i
    have := (htrange i.succ).2
    linarith
  -- the target
  intro ρ hρ him
  by_contra hoff
  -- normalize to the upper half
  have him_ne : ρ.im ≠ 0 := by
    intro h0
    have hρre : ρ = ((ρ.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using h0
    obtain ⟨ha, hb, hc⟩ := hρ
    rw [hρre] at hc
    exact zeta_ne_zero_of_real_unit ha hb hc
  set ρ' : ℂ := if 0 < ρ.im then ρ else (starRingEnd ℂ) ρ with hρ'def
  have hρ'_mem : ρ' ∈ ZD.NontrivialZeros := by
    rw [hρ'def]
    split_ifs with h
    · exact hρ
    · obtain ⟨ha, hb, hc⟩ := hρ
      refine ⟨by simpa using ha, by simpa using hb, ?_⟩
      rw [riemannZeta_conj, hc, map_zero]
  have hρ'_im_pos : 0 < ρ'.im := by
    rw [hρ'def]
    split_ifs with h
    · exact h
    · simp only [Complex.conj_im]
      rcases lt_trichotomy ρ.im 0 with h1 | h1 | h1
      · linarith
      · exact absurd h1 him_ne
      · exact absurd h1 h
  have hρ'_im_le : ρ'.im ≤ 581/2 := by
    rw [hρ'def]
    split_ifs with h
    · calc ρ.im ≤ |ρ.im| := le_abs_self _
        _ ≤ 581/2 := him
    · simp only [Complex.conj_im]
      calc -ρ.im ≤ |ρ.im| := neg_le_abs _
        _ ≤ 581/2 := him
  have hρ'_re : ρ'.re ≠ 1/2 := by
    rw [hρ'def]
    split_ifs with h
    · exact hoff
    · simpa using hoff
  -- the thirteen distinct members of the strip finset
  have hmem_line : ∀ i : Fin 132, line (zs i) ∈ stripZeroFinset (581/2) := by
    intro i
    apply (stripZeroWindow_finite (581/2)).mem_toFinset.mpr
    exact ⟨hz3 i, by rw [lineIm]; exact hzs_pos i,
      by rw [lineIm]; exact hzs_le i⟩
  have hmem_ρ' : ρ' ∈ stripZeroFinset (581/2) := by
    apply (stripZeroWindow_finite (581/2)).mem_toFinset.mpr
    exact ⟨hρ'_mem, hρ'_im_pos, hρ'_im_le⟩
  set S : Finset ℂ :=
    insert ρ' (Finset.image (fun i => line (zs i)) Finset.univ) with hSdef
  have hinj : Function.Injective (fun i : Fin 132 => line (zs i)) := by
    intro i j hij
    have him' : zs i = zs j := by
      have := congrArg Complex.im hij
      rwa [lineIm, lineIm] at this
    by_contra hne
    rcases lt_trichotomy i j with h | h | h
    · exact absurd him' (ne_of_lt (hzs_lt i j h))
    · exact hne h
    · exact absurd him'.symm (ne_of_lt (hzs_lt j i h))
  have hρ'_notmem : ρ' ∉ Finset.image (fun i => line (zs i)) Finset.univ := by
    intro hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    have := congrArg Complex.re hi
    rw [line_re] at this
    exact hρ'_re this.symm
  have hcard : S.card = 133 := by
    rw [hSdef, Finset.card_insert_of_notMem hρ'_notmem,
      Finset.card_image_of_injective _ hinj]
    simp
  have hsub : S ⊆ stripZeroFinset (581/2) := by
    intro x hx
    rw [hSdef] at hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact hmem_ρ'
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      rw [← hi]; exact hmem_line i
  -- count: 13 ≤ 12
  have hone : ∀ x ∈ S, 1 ≤ ZD.xiOrderNat x := by
    intro x hx
    have hx' := hsub hx
    have hmem := (stripZeroWindow_finite (581/2)).mem_toFinset.mp hx'
    exact ZD.xiOrderNat_pos_of_mem_NontrivialZeros hmem.1
  have h13 : 133 ≤ ∑ x ∈ S, ZD.xiOrderNat x := by
    calc (133:ℕ) = S.card := hcard.symm
      _ = ∑ _x ∈ S, 1 := by rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ x ∈ S, ZD.xiOrderNat x := Finset.sum_le_sum hone
  have h12 : ∑ x ∈ S, ZD.xiOrderNat x ≤ stripZeroCountMult (581/2) := by
    rw [stripZeroCountMult]
    exact Finset.sum_le_sum_of_subset hsub
  rw [stripZeroCountMult_581o2] at h12
  omega

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.online_below_581o2_of_ladder
end AxiomAudit
