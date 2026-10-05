import RequestProject.SeatingRDefect

/-!
# Door strength: the repaired open-census flip door and what each door carries

The T★ equivalence exposed an EDGE DEFECT in the 08-28 flip door shape
(encountered in construction, not theorized): `rh_of_high_flip_visibility`
demands census-many flips against the CLOSED-edge census `Ioc T₁ T₂`, but a
zero at ordinate exactly `T₂` books no flip inside `[T₁, T₂]` (its window
needs both sides), so every box whose right edge sits on a zero ordinate
falsifies that hypothesis IN EVERY WORLD — the old door is sound but its
hypothesis is unsatisfiable once high zeros exist.  Repair: compare against
the OPEN census.  This file compiles:

* `stripBoxOpen` — the open strip census;
* `rh_of_high_open_flip_census` / `rh_of_high_open_flip_visibility` — the
  healthy doors (open census domination, resp. open-census-many flips,
  above the ladder ⟹ RH);
* what each door's hypothesis carries beyond the line:
  - `online_and_odd_of_high_open_flip_census` — the open flip door's
    hypothesis also gives odd ξ-multiplicity above the ladder;
  - `online_and_simple_of_high_R_defect` — the R-defect door's hypothesis
    also gives SIMPLE zeros above the ladder.

No `sorry`, no `axiom`.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- The OPEN strip census box: ordinates strictly inside `(T₁, T₂)`. -/
def stripBoxOpen (T₁ T₂ : ℝ) : Set ℂ :=
  {ρ ∈ ZD.NontrivialZeros | ρ.im ∈ Set.Ioo T₁ T₂}

theorem stripBoxOpen_subset (T₁ T₂ : ℝ) :
    stripBoxOpen T₁ T₂ ⊆ stripBox T₁ T₂ :=
  fun _ h => ⟨h.1, h.2.1, h.2.2.le⟩

theorem stripBoxOpen_finite (T₁ T₂ : ℝ) : (stripBoxOpen T₁ T₂).Finite :=
  (stripBox_finite T₁ T₂).subset (stripBoxOpen_subset T₁ T₂)

/-- **The repaired census door**: open-census domination by the odd on-line
census, in every box above the compiled ladder, forces RH. -/
theorem rh_of_high_open_flip_census
    (h : ∀ T₁ T₂ : ℝ, 1269/2 ≤ T₁ → T₁ < T₂ →
      (stripBoxOpen T₁ T₂).ncard ≤ (oddOnLineBox T₁ T₂).ncard) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2 := by
  apply rh_of_high_seating
  intro T₁ T₂ hT₁ hT
  have hsub : stripBox T₁ T₂ ⊆ onLineBox T₁ T₂ := by
    intro ρ hρ
    by_contra hoff
    have hre : ρ.re ≠ 1/2 := fun hre => hoff ⟨hρ, hre⟩
    have him : 1269/2 < ρ.im := lt_of_le_of_lt hT₁ hρ.2.1
    set S₁ : ℝ := max (ρ.im - 1) (1269/2) with hS₁
    have hS₁le : 1269/2 ≤ S₁ := le_max_right _ _
    have hS₁lt : S₁ < ρ.im := by
      rw [hS₁, max_lt_iff]
      exact ⟨by linarith, him⟩
    have hcen := h S₁ (ρ.im + 1) hS₁le (by linarith)
    have hssub : oddOnLineBox S₁ (ρ.im + 1) ⊂ stripBoxOpen S₁ (ρ.im + 1) := by
      constructor
      · rintro z ⟨hNT, hIoo, _, _⟩
        exact ⟨hNT, hIoo⟩
      · intro hcon
        have hmem : ρ ∈ oddOnLineBox S₁ (ρ.im + 1) :=
          hcon ⟨hρ.1, hS₁lt, by linarith⟩
        exact hre hmem.2.2.1
    have hlt := Set.ncard_lt_ncard hssub (stripBoxOpen_finite _ _)
    omega
  rw [Set.Subset.antisymm hsub (fun ρ hρ => hρ.1)]

/-- **The repaired flip door**: open-census-many consecutive sign flips in
every box above the ladder forces RH — with the flip supply capped by the
T★ upper bound, this is the healthy form of `rh_of_high_flip_visibility`. -/
theorem rh_of_high_open_flip_visibility
    (h : ∀ T₁ T₂ : ℝ, 1269/2 ≤ T₁ → T₁ < T₂ → ∃ (n : ℕ) (a : Fin (n+1) → ℝ),
      (stripBoxOpen T₁ T₂).ncard ≤ n ∧ StrictMono a ∧ T₁ ≤ a 0 ∧
      a (Fin.last n) ≤ T₂ ∧
      ∀ i : Fin n, XiLine (a i.castSucc) * XiLine (a i.succ) < 0) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2 := by
  apply rh_of_high_open_flip_census
  intro T₁ T₂ hT₁ hT
  obtain ⟨n, a, hcen, hmono, hlo, hhi, hflip⟩ := h T₁ T₂ hT₁ hT
  have h0 : (0:ℝ) < T₁ := lt_of_lt_of_le (by norm_num) hT₁
  exact le_trans hcen (flips_le_oddOnLine_ncard h0 a hmono hlo hhi hflip)

/-- **What the open flip door's hypothesis carries**: every nontrivial zero
on the line, and every zero above the ladder of odd ξ-multiplicity. -/
theorem online_and_odd_of_high_open_flip_census
    (h : ∀ T₁ T₂ : ℝ, 1269/2 ≤ T₁ → T₁ < T₂ →
      (stripBoxOpen T₁ T₂).ncard ≤ (oddOnLineBox T₁ T₂).ncard) :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2)
        ∧ ∀ ρ ∈ ZD.NontrivialZeros, 1269/2 < ρ.im →
            Odd (Zeta23.zeroMult ρ) := by
  · have hon := rh_of_high_open_flip_census h
    refine ⟨hon, fun ρ hρ him => ?_⟩
    by_contra hodd
    set S₁ : ℝ := max (ρ.im - 1) (1269/2) with hS₁
    have hS₁le : 1269/2 ≤ S₁ := le_max_right _ _
    have hS₁lt : S₁ < ρ.im := by
      rw [hS₁, max_lt_iff]
      exact ⟨by linarith, him⟩
    have hcen := h S₁ (ρ.im + 1) hS₁le (by linarith)
    have hssub : oddOnLineBox S₁ (ρ.im + 1) ⊂ stripBoxOpen S₁ (ρ.im + 1) := by
      constructor
      · rintro z ⟨hNT, hIoo, _, _⟩
        exact ⟨hNT, hIoo⟩
      · intro hcon
        have hmem : ρ ∈ oddOnLineBox S₁ (ρ.im + 1) :=
          hcon ⟨hρ, hS₁lt, by linarith⟩
        exact hodd hmem.2.2.2
    have hlt := Set.ncard_lt_ncard hssub (stripBoxOpen_finite _ _)
    omega

/-- **What the R-defect door's hypothesis carries**: if the residue ledger
vanishes in every high box, every nontrivial zero is on the line and every
zero above the ladder is SIMPLE. -/
theorem online_and_simple_of_high_R_defect
    (h : ∀ T₁ T₂ : ℝ, 1269/2 ≤ T₁ → T₁ < T₂ → rBoxLedger T₁ T₂ = 0) :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2)
        ∧ ∀ ρ ∈ ZD.NontrivialZeros, 1269/2 < ρ.im →
            ZD.xiOrderNat ρ = 1 := by
  · have hon := rh_of_high_R_defect h
    refine ⟨hon, fun ρ hρ him => ?_⟩
    set S₁ : ℝ := max (ρ.im - 1) (1269/2) with hS₁
    have hS₁le : 1269/2 ≤ S₁ := le_max_right _ _
    have hS₁lt : S₁ < ρ.im := by
      rw [hS₁, max_lt_iff]
      exact ⟨by linarith, him⟩
    have hbox := h S₁ (ρ.im + 1) hS₁le (by linarith)
    have hmem : ρ ∈ (stripBox_finite S₁ (ρ.im + 1)).toFinset :=
      (stripBox_finite S₁ (ρ.im + 1)).mem_toFinset.mpr
        ⟨hρ, hS₁lt, by linarith⟩
    have hw : rDefectWeight ρ = 0 := by
      unfold rBoxLedger at hbox
      exact (Finset.sum_eq_zero_iff.mp hbox) ρ hmem
    exact ((rDefectWeight_eq_zero_iff hρ).mp hw).2

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.rh_of_high_open_flip_census
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_high_open_flip_visibility
#print axioms CriticalLinePhasor.SeatingLedger.online_and_odd_of_high_open_flip_census
#print axioms CriticalLinePhasor.SeatingLedger.online_and_simple_of_high_R_defect
