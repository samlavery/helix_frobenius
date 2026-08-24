import RequestProject.DVPHardyDetector

/-!
# The exhaustion at height 58

Twelve sign changes of the Hardy detector below height 58 produce twelve
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

/-- **The ladder hypothesis**: thirteen stations in `[10, 58]`, strictly
increasing, with alternating-sign detector values (formulated as twelve
adjacent sign changes). -/
def LadderData : Prop :=
  ∃ t : Fin 13 → ℝ, StrictMono t
    ∧ (∀ i, 10 ≤ t i ∧ t i ≤ 58)
    ∧ ∀ i : Fin 12, hardyG (t i.castSucc) * hardyG (t i.succ) < 0

/-- **Exhaustion**: the ladder plus the census force every strip zero of
ordinate `≤ 58` onto the line. -/
theorem online_below_58_of_ladder (hL : LadderData) :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 58 → ρ.re = 1/2 := by
  obtain ⟨t, htmono, htrange, hsign⟩ := hL
  -- the twelve interior zeros
  have hex : ∀ i : Fin 12, ∃ z : ℝ, t i.castSucc < z ∧ z < t i.succ
      ∧ line z ∈ ZD.NontrivialZeros := by
    intro i
    exact hardyG_sign_change
      (htmono (Fin.castSucc_lt_succ (i := i))).le
      (htrange i.castSucc).1 (htrange i.succ).2 (hsign i)
  choose zs hz1 hz2 hz3 using hex
  have hzs_lt : ∀ i j : Fin 12, i < j → zs i < zs j := by
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
  have hzs_le : ∀ i, zs i ≤ 58 := by
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
  have hρ'_im_le : ρ'.im ≤ 58 := by
    rw [hρ'def]
    split_ifs with h
    · calc ρ.im ≤ |ρ.im| := le_abs_self _
        _ ≤ 58 := him
    · simp only [Complex.conj_im]
      calc -ρ.im ≤ |ρ.im| := neg_le_abs _
        _ ≤ 58 := him
  have hρ'_re : ρ'.re ≠ 1/2 := by
    rw [hρ'def]
    split_ifs with h
    · exact hoff
    · simpa using hoff
  -- the thirteen distinct members of the strip finset
  have hmem_line : ∀ i : Fin 12, line (zs i) ∈ stripZeroFinset 58 := by
    intro i
    apply (stripZeroWindow_finite 58).mem_toFinset.mpr
    exact ⟨hz3 i, by rw [lineIm]; exact hzs_pos i,
      by rw [lineIm]; exact hzs_le i⟩
  have hmem_ρ' : ρ' ∈ stripZeroFinset 58 := by
    apply (stripZeroWindow_finite 58).mem_toFinset.mpr
    exact ⟨hρ'_mem, hρ'_im_pos, hρ'_im_le⟩
  set S : Finset ℂ :=
    insert ρ' (Finset.image (fun i => line (zs i)) Finset.univ) with hSdef
  have hinj : Function.Injective (fun i : Fin 12 => line (zs i)) := by
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
  have hcard : S.card = 13 := by
    rw [hSdef, Finset.card_insert_of_notMem hρ'_notmem,
      Finset.card_image_of_injective _ hinj]
    simp
  have hsub : S ⊆ stripZeroFinset 58 := by
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
    have hmem := (stripZeroWindow_finite 58).mem_toFinset.mp hx'
    exact ZD.xiOrderNat_pos_of_mem_NontrivialZeros hmem.1
  have h13 : 13 ≤ ∑ x ∈ S, ZD.xiOrderNat x := by
    calc (13:ℕ) = S.card := hcard.symm
      _ = ∑ _x ∈ S, 1 := by rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ x ∈ S, ZD.xiOrderNat x := Finset.sum_le_sum hone
  have h12 : ∑ x ∈ S, ZD.xiOrderNat x ≤ stripZeroCountMult 58 := by
    rw [stripZeroCountMult]
    exact Finset.sum_le_sum_of_subset hsub
  rw [stripZeroCountMult_58] at h12
  omega

/-- **Conjunct 1 of the seat split, from the ladder**: every zero of
ordinate `|γ| < e⁴ + 5/2` is on the line. -/
theorem conjunct_one_of_ladder (hL : LadderData) :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| < Real.exp 4 + 5/2 → ρ.re = 1/2 := by
  intro ρ hρ him
  apply online_below_58_of_ladder hL ρ hρ
  have he4 : Real.exp 4 ≤ 55 := by
    have h1 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h2 : Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := by
      apply pow_le_pow_left₀ (Real.exp_pos 1).le
      linarith [Real.exp_one_lt_d9]
    nlinarith [h1, h2]
  linarith

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.online_below_58_of_ladder
#print axioms CriticalLinePhasor.DVP.conjunct_one_of_ladder
end AxiomAudit
