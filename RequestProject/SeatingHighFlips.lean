import RequestProject.SeatingLadderFold

/-!
# The high flip capstone: census-many flips above the ladder alone

Localizing `rh_of_flip_visibility` by the compiled DVP ladder exactly as the
seating and receiver forms were localized: the Hardy-detector hypothesis —
census-many sign changes of the on-line readout per box — is needed only in
boxes above `1269/2 = 634.5`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- **RH from high flip visibility**: census-many sign flips of `XiLine`,
demanded only in boxes above the compiled ladder height `1269/2`. -/
theorem rh_of_high_flip_visibility
    (h : ∀ T₁ T₂ : ℝ, 1269/2 ≤ T₁ → T₁ < T₂ → ∃ (n : ℕ) (a : Fin (n+1) → ℝ),
      (stripBox T₁ T₂).ncard ≤ n ∧ StrictMono a ∧ T₁ ≤ a 0 ∧
      a (Fin.last n) ≤ T₂ ∧
      ∀ i : Fin n, XiLine (a i.castSucc) * XiLine (a i.succ) < 0) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2 := by
  apply rh_of_high_seating
  intro T₁ T₂ hT₁ hT
  obtain ⟨n, a, hcen, hmono, hlo, hhi, hflip⟩ := h T₁ T₂ hT₁ hT
  have hup := flips_le_onLine_ncard a hmono hlo hhi hflip
  have hle : (onLineBox T₁ T₂).ncard ≤ (stripBox T₁ T₂).ncard :=
    Set.ncard_le_ncard (fun x hx => hx.1) (stripBox_finite T₁ T₂)
  omega

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.rh_of_high_flip_visibility
