import RequestProject.SeatingDetector
import RequestProject.DVPLadder1269o2

/-!
# The ladder fold: seating is settled below ordinate 634.5

The compiled DVP ladder (`online_below_1269o2`) verifies every nontrivial zero
of ordinate `|γ| ≤ 1269/2` on the line.  Folding into the ledger: below the
ladder the strip and on-line boxes coincide, the per-box seating equality is a
theorem, and the RH-sufficient hypothesis shrinks to boxes above `1269/2`:

  `rh_of_high_seating` — **RH ⟸ census equality in boxes above 634.5 only.**

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- Conjugation closure of the zero set (the reflection to positive height). -/
theorem conj_mem {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    conj ρ ∈ ZD.NontrivialZeros := by
  rw [← ZD.riemannXi_eq_zero_iff, ContourArgument.riemannXi_conj,
    (ZD.riemannXi_eq_zero_iff ρ).mpr hρ, map_zero]

/-- **Below the ladder the boxes coincide.** -/
theorem seating_below_ladder {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) (hT₂ : T₂ ≤ 1269/2) :
    stripBox T₁ T₂ = onLineBox T₁ T₂ := by
  ext ρ
  constructor
  · intro h
    refine ⟨h, ?_⟩
    apply CriticalLinePhasor.DVP.online_below_1269o2 ρ h.1
    have h1 := h.2.1
    have h2 := h.2.2
    rw [abs_of_pos (by linarith)]
    linarith
  · exact fun h => h.1

/-- **RH from high seating alone**: the census equality is needed only in
boxes above the compiled ladder height `1269/2 = 634.5`. -/
theorem rh_of_high_seating
    (h : ∀ T₁ T₂ : ℝ, 1269/2 ≤ T₁ → T₁ < T₂ →
      (stripBox T₁ T₂).ncard = (onLineBox T₁ T₂).ncard) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2 := by
  -- first, the positive-height claim
  have hpos : ∀ ρ ∈ ZD.NontrivialZeros, 0 < ρ.im → ρ.re = 1/2 := by
    intro ρ hρ him
    by_cases hlow : ρ.im ≤ 1269/2
    · exact CriticalLinePhasor.DVP.online_below_1269o2 ρ hρ
        (by rw [abs_of_pos him]; exact hlow)
    · push_neg at hlow
      by_contra hre
      set T₁ : ℝ := max (ρ.im - 1) (1269/2) with hT₁
      have hT₁lt : T₁ < ρ.im := by
        rw [hT₁, max_lt_iff]
        constructor <;> linarith
      have hmem : ρ ∈ offLineBox T₁ ρ.im :=
        ⟨⟨hρ, ⟨hT₁lt, le_refl _⟩⟩, hre⟩
      have hempty := seating_kills_offline
        (h T₁ ρ.im (le_max_right _ _) hT₁lt)
      rw [hempty] at hmem
      exact hmem
  intro ρ hρ
  rcases lt_trichotomy ρ.im 0 with hlt | heq | hgt
  · -- reflect to positive height
    have hconj := conj_mem hρ
    have : (conj ρ).re = 1/2 := by
      apply hpos _ hconj
      rw [Complex.conj_im]
      linarith
    rwa [Complex.conj_re] at this
  · -- zero height: covered by the ladder
    exact CriticalLinePhasor.DVP.online_below_1269o2 ρ hρ
      (by rw [heq]; norm_num)
  · exact hpos ρ hρ hgt

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.seating_below_ladder
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_high_seating
