import RequestProject.SeatingLedger

/-!
# The bank-side detector: flips of the real line-readout are on-line zeros

The completed readout on the critical line is REAL (`Xi_line_im`, from the
compiled FE-conjugation), so a sign flip between two heights forces an on-line
zero strictly between them (`flip_yields_online_zero`, IVT — no zero location
is an input), and `n` ordered flips force `n` distinct on-line zeros
(`flips_le_onLine_ncard`).  Composing with the seating ledger:

  `rh_of_flip_visibility` — **RH ⟸ the bank readout flips census-many times
  in every box.**

After this file the uncompiled content of the count register is exactly
flip-visibility: `census ≤ flips` — every completion shows its flip.

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

open CriticalLinePhasor.ContourArgument

/-- The line point at ordinate `t`. -/
def linePt (t : ℝ) : ℂ := 1/2 + (t : ℂ) * I

theorem linePt_re (t : ℝ) : (linePt t).re = 1/2 := by
  simp [linePt]

theorem linePt_im (t : ℝ) : (linePt t).im = t := by
  simp [linePt]

theorem linePt_fix (t : ℝ) : 1 - conj (linePt t) = linePt t := by
  apply Complex.ext
  · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, linePt_re]
    norm_num
  · rw [Complex.sub_im, Complex.one_im, Complex.conj_im, linePt_im]
    ring

/-- **The line readout is real**: `Im ξ(½ + it) = 0`. -/
theorem Xi_line_im (t : ℝ) : (ZD.riemannXi (linePt t)).im = 0 := by
  have h := riemannXi_one_sub_conj (linePt t)
  rw [linePt_fix] at h
  have him := congrArg Complex.im h
  simp only [Complex.conj_im] at him
  linarith

/-- The real bank readout on the line. -/
def XiLine (t : ℝ) : ℝ := (ZD.riemannXi (linePt t)).re

theorem XiLine_continuous : Continuous XiLine :=
  Complex.continuous_re.comp (ZD.riemannXi_differentiable.continuous.comp
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)))

theorem XiLine_zero_iff {t : ℝ} :
    XiLine t = 0 ↔ linePt t ∈ ZD.NontrivialZeros := by
  rw [← ZD.riemannXi_eq_zero_iff]
  constructor
  · intro h
    apply Complex.ext
    · exact h
    · exact Xi_line_im t
  · intro h
    unfold XiLine
    rw [h]
    rfl

/-- **A flip is a zero**: a sign change of the real readout forces an on-line
nontrivial zero strictly between the heights.  No zero location is an input. -/
theorem flip_yields_online_zero {a b : ℝ} (hab : a < b)
    (hflip : XiLine a * XiLine b < 0) :
    ∃ γ ∈ Set.Ioo a b, linePt γ ∈ ZD.NontrivialZeros := by
  have hcont : ContinuousOn XiLine (Set.Icc a b) :=
    XiLine_continuous.continuousOn
  rcases mul_neg_iff.mp hflip with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have h0 : (0:ℝ) ∈ Set.Ioo (XiLine b) (XiLine a) := ⟨hb, ha⟩
    obtain ⟨γ, hγmem, hγ⟩ := intermediate_value_Ioo' hab.le hcont h0
    exact ⟨γ, hγmem, XiLine_zero_iff.mp hγ⟩
  · have h0 : (0:ℝ) ∈ Set.Ioo (XiLine a) (XiLine b) := ⟨ha, hb⟩
    obtain ⟨γ, hγmem, hγ⟩ := intermediate_value_Ioo hab.le hcont h0
    exact ⟨γ, hγmem, XiLine_zero_iff.mp hγ⟩

/-- **Ordered flips yield distinct on-line zeros.** -/
theorem flips_le_onLine_ncard {T₁ T₂ : ℝ} {n : ℕ} (a : Fin (n+1) → ℝ)
    (hmono : StrictMono a)
    (hlo : T₁ ≤ a 0) (hhi : a (Fin.last n) ≤ T₂)
    (hflip : ∀ i : Fin n, XiLine (a i.castSucc) * XiLine (a i.succ) < 0) :
    n ≤ (onLineBox T₁ T₂).ncard := by
  have hchoice : ∀ i : Fin n, ∃ γ ∈ Set.Ioo (a i.castSucc) (a i.succ),
      linePt γ ∈ ZD.NontrivialZeros := by
    intro i
    refine flip_yields_online_zero (hmono ?_) (hflip i)
    rw [Fin.lt_def, Fin.coe_castSucc, Fin.val_succ]
    omega
  choose γ hγmem hγzero using hchoice
  have hγmono : StrictMono γ := by
    intro i j hij
    have h1 : γ i < a i.succ := (hγmem i).2
    have h2 : a j.castSucc < γ j := (hγmem j).1
    have hle : a i.succ ≤ a j.castSucc := by
      apply hmono.monotone
      rw [Fin.le_def, Fin.val_succ, Fin.coe_castSucc]
      exact hij
    linarith
  have hmem : ∀ i : Fin n, linePt (γ i) ∈ onLineBox T₁ T₂ := by
    intro i
    have h1 : a 0 ≤ a i.castSucc := hmono.monotone (Fin.zero_le _)
    have h2 : a i.succ ≤ a (Fin.last n) := hmono.monotone (Fin.le_last _)
    have hm1 := (hγmem i).1
    have hm2 := (hγmem i).2
    refine ⟨⟨hγzero i, ?_, ?_⟩, ?_⟩
    · rw [linePt_im]
      linarith
    · rw [linePt_im]
      linarith
    · exact linePt_re _
  have hinj : Function.Injective (fun i : Fin n => linePt (γ i)) := by
    intro i j h
    have him := congrArg Complex.im h
    rw [linePt_im, linePt_im] at him
    exact hγmono.injective him
  have hsub : Set.range (fun i : Fin n => linePt (γ i)) ⊆ onLineBox T₁ T₂ := by
    rintro x ⟨i, rfl⟩
    exact hmem i
  have hfin : (onLineBox T₁ T₂).Finite :=
    (stripBox_finite T₁ T₂).subset (fun x hx => hx.1)
  calc n = (Set.univ : Set (Fin n)).ncard := by
        simp [Set.ncard_univ, Nat.card_eq_fintype_card]
    _ = ((fun i : Fin n => linePt (γ i)) '' Set.univ).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ = (Set.range fun i : Fin n => linePt (γ i)).ncard := by
        rw [Set.image_univ]
    _ ≤ (onLineBox T₁ T₂).ncard := Set.ncard_le_ncard hsub hfin

/-- **RH FROM FLIP VISIBILITY**: if in every box the bank readout flips at
least census-many times, every nontrivial zero is on the critical line. -/
theorem rh_of_flip_visibility
    (h : ∀ T₁ T₂ : ℝ, T₁ < T₂ → ∃ (n : ℕ) (a : Fin (n+1) → ℝ),
      (stripBox T₁ T₂).ncard ≤ n ∧ StrictMono a ∧ T₁ ≤ a 0 ∧
      a (Fin.last n) ≤ T₂ ∧
      ∀ i : Fin n, XiLine (a i.castSucc) * XiLine (a i.succ) < 0) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2 := by
  apply rh_of_seating
  intro T₁ T₂ hT
  obtain ⟨n, a, hcen, hmono, hlo, hhi, hflip⟩ := h T₁ T₂ hT
  have hup := flips_le_onLine_ncard a hmono hlo hhi hflip
  have hle : (onLineBox T₁ T₂).ncard ≤ (stripBox T₁ T₂).ncard :=
    Set.ncard_le_ncard (fun x hx => hx.1) (stripBox_finite T₁ T₂)
  omega

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.flip_yields_online_zero
#print axioms CriticalLinePhasor.SeatingLedger.flips_le_onLine_ncard
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_flip_visibility
