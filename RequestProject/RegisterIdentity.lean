import RequestProject.DVPExhaustion1269o2
import RequestProject.DoubleCoshProgram

/-!
# The register identity: the crossing register names the census integer at every height (ledger 676)

The DVP method, compiled height by height (58, 63, 109, …, 634.5), is one argument: a ladder of stations in
[10, T] with N adjacent sign changes of the Hardy detector locates N distinct on-line zeros; the census
`stripZeroCountMult T = N` (the winding, counted with multiplicity) then leaves no room for an off-line zero
below T.  Here the argument is compiled ONCE for every height and count (`online_of_ladder`), and the
register identity — every good height has such a ladder with exactly the census count — is shown to imply
the Riemann Hypothesis (`rh_of_registerIdentity`).  This is the register door of ledger 675 in Lean: no
winding without a cell.
-/

open Complex Set CriticalLinePhasor.CarrierScale CriticalLinePhasor.ContourArgument DoubleCoshProgram

namespace CriticalLinePhasor.DVP

/-- Detector continuity on `[10, T]`. -/
theorem hardyG_continuousOn_gen (T : ℝ) : ContinuousOn hardyG (Set.Icc (10:ℝ) T) := by
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
    unfold CriticalLinePhasor.CarrierScale.line CriticalLinePhasor.CarrierScale.lineC
    fun_prop
  have hc : ContinuousAt (Complex.re ∘ completedRiemannZeta ∘ line) t := by
    apply ContinuousAt.comp
    · exact Complex.continuous_re.continuousAt
    · apply ContinuousAt.comp
      · exact (differentiableAt_completedZeta hline0 hline1).continuousAt
      · exact hlinecont.continuousAt
  exact hc.continuousWithinAt

/-- A sign change of the detector between two stations above height 10 locates an on-line zero. -/
theorem hardyG_sign_change_gen {a b : ℝ} (hab : a ≤ b) (h10 : 10 ≤ a)
    (hsign : hardyG a * hardyG b < 0) :
    ∃ t : ℝ, a < t ∧ t < b ∧ line t ∈ ZD.NontrivialZeros := by
  have hcont : ContinuousOn hardyG (Set.Icc a b) :=
    (hardyG_continuousOn_gen b).mono (Set.Icc_subset_Icc h10 le_rfl)
  have hane : hardyG a ≠ 0 := by
    intro h; rw [h, zero_mul] at hsign; exact lt_irrefl _ hsign
  have hbne : hardyG b ≠ 0 := by
    intro h; rw [h, mul_zero] at hsign; exact lt_irrefl _ hsign
  have hzero : ∃ t ∈ Set.Icc a b, hardyG t = 0 := by
    rcases lt_or_gt_of_ne hane with hneg | hpos
    · have hbpos : 0 < hardyG b := by
        rcases lt_trichotomy (hardyG b) 0 with h | h | h
        · nlinarith
        · exact absurd h hbne
        · exact h
      obtain ⟨t, htmem, hteq⟩ := intermediate_value_Icc hab hcont ⟨hneg.le, hbpos.le⟩
      exact ⟨t, htmem, hteq⟩
    · have hbneg : hardyG b < 0 := by
        rcases lt_trichotomy (hardyG b) 0 with h | h | h
        · exact h
        · exact absurd h hbne
        · nlinarith
      obtain ⟨t, htmem, hteq⟩ := intermediate_value_Icc' hab hcont ⟨hbneg.le, hpos.le⟩
      exact ⟨t, htmem, hteq⟩
  obtain ⟨t, htmem, hteq⟩ := hzero
  have htne_a : t ≠ a := fun h => hane (h ▸ hteq)
  have htne_b : t ≠ b := fun h => hbne (h ▸ hteq)
  refine ⟨t, lt_of_le_of_ne htmem.1 (Ne.symm htne_a), lt_of_le_of_ne htmem.2 htne_b, ?_⟩
  exact hardyG_online (by linarith [htmem.1]) hteq

/-- **A ladder at height `T` with `N` crossings:** `N+1` stations in `[10, T]`, strictly increasing,
with `N` adjacent sign changes of the detector. -/
def LadderData (T : ℝ) (N : ℕ) : Prop :=
  ∃ t : Fin (N + 1) → ℝ, StrictMono t ∧ (∀ i, 10 ≤ t i ∧ t i ≤ T)
    ∧ ∀ i : Fin N, hardyG (t i.castSucc) * hardyG (t i.succ) < 0

/-- **The exhaustion, for every height and count.**  A ladder with `N` crossings and census `N` at height
`T` force every strip zero of ordinate `≤ T` onto the line. -/
theorem online_of_ladder {T : ℝ} {N : ℕ} (hcensus : stripZeroCountMult T = N) (hL : LadderData T N) :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ T → ρ.re = 1/2 := by
  obtain ⟨t, htmono, htrange, hsign⟩ := hL
  have hex : ∀ i : Fin N, ∃ z : ℝ, t i.castSucc < z ∧ z < t i.succ ∧ line z ∈ ZD.NontrivialZeros := by
    intro i
    exact hardyG_sign_change_gen (htmono (Fin.castSucc_lt_succ (i := i))).le
      (htrange i.castSucc).1 (hsign i)
  choose zs hz1 hz2 hz3 using hex
  have hzs_lt : ∀ i j : Fin N, i < j → zs i < zs j := by
    intro i j hij
    have h1 : zs i < t i.succ := hz2 i
    have h2 : t j.castSucc < zs j := hz1 j
    have h3 : i.succ ≤ j.castSucc := by
      rw [Fin.le_def]
      simp only [Fin.val_succ, Fin.val_castSucc]
      exact hij
    have h4 : t i.succ ≤ t j.castSucc := htmono.monotone h3
    linarith
  have hzs_pos : ∀ i, 0 < zs i := by
    intro i
    have := hz1 i
    have := (htrange i.castSucc).1
    linarith
  have hzs_le : ∀ i, zs i ≤ T := by
    intro i
    have := hz2 i
    have := (htrange i.succ).2
    linarith
  intro ρ hρ him
  by_contra hoff
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
  have hρ'_im_le : ρ'.im ≤ T := by
    rw [hρ'def]
    split_ifs with h
    · exact (le_abs_self _).trans him
    · simp only [Complex.conj_im]
      exact (neg_le_abs _).trans him
  have hρ'_re : ρ'.re ≠ 1/2 := by
    rw [hρ'def]
    split_ifs with h
    · exact hoff
    · simpa using hoff
  have hmem_line : ∀ i : Fin N, line (zs i) ∈ stripZeroFinset T := by
    intro i
    apply (stripZeroWindow_finite T).mem_toFinset.mpr
    exact ⟨hz3 i, by rw [lineIm]; exact hzs_pos i, by rw [lineIm]; exact hzs_le i⟩
  have hmem_ρ' : ρ' ∈ stripZeroFinset T := by
    apply (stripZeroWindow_finite T).mem_toFinset.mpr
    exact ⟨hρ'_mem, hρ'_im_pos, hρ'_im_le⟩
  set S : Finset ℂ := insert ρ' (Finset.image (fun i => line (zs i)) Finset.univ) with hSdef
  have hinj : Function.Injective (fun i : Fin N => line (zs i)) := by
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
  have hcard : S.card = N + 1 := by
    rw [hSdef, Finset.card_insert_of_notMem hρ'_notmem, Finset.card_image_of_injective _ hinj]
    simp
  have hsub : S ⊆ stripZeroFinset T := by
    intro x hx
    rw [hSdef] at hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact hmem_ρ'
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      rw [← hi]; exact hmem_line i
  have hone : ∀ x ∈ S, 1 ≤ ZD.xiOrderNat x := by
    intro x hx
    have hx' := hsub hx
    have hmem := (stripZeroWindow_finite T).mem_toFinset.mp hx'
    exact ZD.xiOrderNat_pos_of_mem_NontrivialZeros hmem.1
  have hN1 : N + 1 ≤ ∑ x ∈ S, ZD.xiOrderNat x := by
    calc N + 1 = S.card := hcard.symm
      _ = ∑ _x ∈ S, 1 := by rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ x ∈ S, ZD.xiOrderNat x := Finset.sum_le_sum hone
  have hN : ∑ x ∈ S, ZD.xiOrderNat x ≤ stripZeroCountMult T := by
    rw [stripZeroCountMult]
    exact Finset.sum_le_sum_of_subset hsub
  rw [hcensus] at hN
  omega

/-- **The register identity:** at every good height `T ≥ 10`, the crossing register carries exactly the census
integer — a ladder with `stripZeroCountMult T` sign changes exists.  (No winding without a cell.) -/
def RegisterIdentity : Prop :=
  ∀ T : ℝ, 10 ≤ T → GoodHeight T → LadderData T (stripZeroCountMult T)

/-- **The register door, compiled:** the register identity implies the Riemann Hypothesis. -/
theorem noOffline_of_registerIdentity (h : RegisterIdentity) : NoOfflineZeros := by
  intro ρ hρ
  obtain ⟨T, hT, hgood⟩ := exists_goodHeight_gt (max 10 |ρ.im|)
  have h10 : 10 ≤ T := le_trans (le_max_left _ _) hT.le
  have hρT : |ρ.im| ≤ T := le_trans (le_max_right _ _) hT.le
  exact online_of_ladder rfl (h T h10 hgood) ρ hρ hρT

theorem rh_of_registerIdentity (h : RegisterIdentity) : RiemannHypothesis :=
  RiemannHypothesis_of_no_offline (noOffline_of_registerIdentity h)

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.online_of_ladder
#print axioms CriticalLinePhasor.DVP.rh_of_registerIdentity
