import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import RequestProject.DVPLadder1269o2

/-!
# The verified window in PNT+'s language (ledger 931)

* `pnt_RH_up_to_1269o2 : riemannZeta.RH_up_to (1269/2)` — the statement of the PrimeNumberTheoremAnd
  project (`IEANTN/ZetaDefinitions.lean`): no zero of `riemannZeta` with real part in `(0.5, 1)` and
  imaginary part in `[0, 1269/2]`.  Derived from `CriticalLinePhasor.DVP.online_below_1269o2`.
* `xiOrder_eq_one_below_1269o2` — every nontrivial zero with `0 < Im ρ ≤ 1269/2` is a simple zero of
  the completed zeta function `riemannXi`.  The 366 sign changes of the Hardy function give 366
  distinct zeros on the line; the argument-principle census counts 366 zeros with multiplicity in
  the same window (`stripZeroCountMult_1269o2`); so every order is one.

No `sorry`, no `axiom`, no `native_decide`.
-/

open CriticalLinePhasor CriticalLinePhasor.DVP CriticalLinePhasor.ContourArgument
  CriticalLinePhasor.CarrierScale

namespace VerifiedWindow

/-- **PNT+'s `RH_up_to` at height `1269/2`, proved.** -/
theorem pnt_RH_up_to_1269o2 : riemannZeta.RH_up_to (1269 / 2) := by
  unfold riemannZeta.RH_up_to
  refine ⟨fun ⟨s, hs⟩ => ?_⟩
  simp only [riemannZeta.zeroes_rect, riemannZeta.zeroes, Set.mem_setOf_eq, Set.mem_Ioo,
    Set.mem_Icc] at hs
  obtain ⟨⟨hre1, hre2⟩, ⟨him0, him1⟩, hz⟩ := hs
  have h05 : (0.5 : ℝ) = 1 / 2 := by norm_num
  rw [h05] at hre1
  have hmem : s ∈ ZD.NontrivialZeros := ⟨by linarith, hre2, hz⟩
  have habs : |s.im| ≤ 1269 / 2 := by rw [abs_of_nonneg him0]; exact him1
  have hline := online_below_1269o2 s hmem habs
  linarith

/-- **Simplicity in the window**: every nontrivial zero with `0 < Im ρ ≤ 1269/2` has
`ξ`-order exactly one. -/
theorem xiOrder_eq_one_below_1269o2 {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros)
    (hpos : 0 < ρ.im) (hle : ρ.im ≤ 1269 / 2) : ZD.xiOrderNat ρ = 1 := by
  obtain ⟨t, htmono, htrange, hsign⟩ := ladder1269o2Data_holds
  have hex : ∀ i : Fin 366, ∃ z : ℝ, t i.castSucc < z ∧ z < t i.succ
      ∧ line z ∈ ZD.NontrivialZeros := by
    intro i
    exact hardyG_sign_change1269o2
      (htmono (Fin.castSucc_lt_succ (i := i))).le
      (htrange i.castSucc).1 (htrange i.succ).2 (hsign i)
  choose zs hz1 hz2 hz3 using hex
  have hzs_lt : ∀ i j : Fin 366, i < j → zs i < zs j := by
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
  have hzs_le : ∀ i, zs i ≤ 1269 / 2 := by
    intro i
    have := hz2 i
    have := (htrange i.succ).2
    linarith
  have hinj : Function.Injective (fun i : Fin 366 => line (zs i)) := by
    intro i j hij
    have him' : zs i = zs j := by
      have := congrArg Complex.im hij
      rwa [lineIm, lineIm] at this
    by_contra hne
    rcases lt_trichotomy i j with h | h | h
    · exact absurd him' (ne_of_lt (hzs_lt i j h))
    · exact hne h
    · exact absurd him'.symm (ne_of_lt (hzs_lt j i h))
  set S : Finset ℂ := insert ρ (Finset.image (fun i => line (zs i)) Finset.univ) with hSdef
  have hsub : S ⊆ stripZeroFinset (1269 / 2) := by
    intro x hx
    rw [hSdef] at hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]
      exact (stripZeroWindow_finite (1269 / 2)).mem_toFinset.mpr ⟨hρ, hpos, hle⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      rw [← hi]
      exact (stripZeroWindow_finite (1269 / 2)).mem_toFinset.mpr
        ⟨hz3 i, by rw [lineIm]; exact hzs_pos i, by rw [lineIm]; exact hzs_le i⟩
  have hcardS : 366 ≤ S.card := by
    calc (366 : ℕ) = (Finset.image (fun i => line (zs i)) Finset.univ).card := by
          rw [Finset.card_image_of_injective _ hinj]; simp
      _ ≤ S.card := Finset.card_le_card (Finset.subset_insert _ _)
  have hone : ∀ x ∈ S, 1 ≤ ZD.xiOrderNat x := by
    intro x hx
    have hmem := (stripZeroWindow_finite (1269 / 2)).mem_toFinset.mp (hsub hx)
    exact ZD.xiOrderNat_pos_of_mem_NontrivialZeros hmem.1
  have hcensus : ∑ x ∈ stripZeroFinset (1269 / 2), ZD.xiOrderNat x = 366 := by
    have h := stripZeroCountMult_1269o2
    unfold stripZeroCountMult at h
    exact h
  have hsum_le : ∑ x ∈ S, ZD.xiOrderNat x ≤ 366 := by
    rw [← hcensus]
    exact Finset.sum_le_sum_of_subset hsub
  have hρS : ρ ∈ S := Finset.mem_insert_self _ _
  rw [← Finset.add_sum_erase S _ hρS] at hsum_le
  have hrest : (S.erase ρ).card ≤ ∑ x ∈ S.erase ρ, ZD.xiOrderNat x := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun x hx => hone x (Finset.mem_of_mem_erase hx))
  have hcard_erase : (S.erase ρ).card = S.card - 1 := Finset.card_erase_of_mem hρS
  have hρone := hone ρ hρS
  omega

end VerifiedWindow

#print axioms VerifiedWindow.pnt_RH_up_to_1269o2
#print axioms VerifiedWindow.xiOrder_eq_one_below_1269o2
