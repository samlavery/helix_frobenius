import RequestProject.ZetaContourArgument

/-!
# The seating ledger: box decomposition, the FE-pair booking, RH from the census

The count-register capstone, compiled.  Per height-box, the strip census splits
as on-line ⊔ off-line; the functional equation pairs every off-line zero with a
distinct mirror **at the same height** (`1 − conj ρ`), so an off-line event
books **at least two** into its box (the integer booking measured on the
Davenport–Heilbronn control, `tmp/c3_dh_control.py`: defect exactly 2, depth-
blind).  Hence census equality per box empties the off-line set, and:

  `rh_of_seating` — **RH ⟸ strip census = on-line census in every box** —

the count-register twin of `rh_of_outer_band` (O108): the same proof, carried
by an integer identity instead of a pointwise sign.

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

open CriticalLinePhasor.ContourArgument

/-- The strip census box: nontrivial zeros with ordinate in `(T₁, T₂]`. -/
def stripBox (T₁ T₂ : ℝ) : Set ℂ :=
  {ρ ∈ ZD.NontrivialZeros | ρ.im ∈ Set.Ioc T₁ T₂}

/-- The on-line part of the box. -/
def onLineBox (T₁ T₂ : ℝ) : Set ℂ :=
  {ρ ∈ stripBox T₁ T₂ | ρ.re = 1/2}

/-- The off-line part of the box. -/
def offLineBox (T₁ T₂ : ℝ) : Set ℂ :=
  {ρ ∈ stripBox T₁ T₂ | ρ.re ≠ 1/2}

theorem stripBox_finite (T₁ T₂ : ℝ) : (stripBox T₁ T₂).Finite := by
  have h := ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite
    (1 + max |T₁| |T₂|)
  apply h.subset
  rintro ρ ⟨hNT, him⟩
  refine ⟨hNT, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre : |ρ.re| ≤ 1 := by
    have h1 := hNT.1
    have h2 := hNT.2.1
    rw [abs_le]
    constructor <;> linarith
  have him' : |ρ.im| ≤ max |T₁| |T₂| := by
    rcases abs_cases ρ.im with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
      exact le_trans him.2 (le_trans (le_abs_self T₂) (le_max_right _ _))
    · rw [he]
      have := him.1
      have : -ρ.im ≤ -T₁ := by linarith
      exact le_trans this (le_trans (neg_le_abs T₁) (le_max_left _ _))
  calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    _ ≤ 1 + max |T₁| |T₂| := by linarith

/-- **The FE mirror**: zeros reflect through the critical line at fixed height. -/
theorem mirror_mem {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    1 - conj ρ ∈ ZD.NontrivialZeros := by
  rw [← ZD.riemannXi_eq_zero_iff, riemannXi_one_sub_conj,
    (ZD.riemannXi_eq_zero_iff ρ).mpr hρ, map_zero]

theorem mirror_im (ρ : ℂ) : (1 - conj ρ).im = ρ.im := by
  simp [Complex.sub_im, Complex.one_im, Complex.conj_im]

theorem mirror_re (ρ : ℂ) : (1 - conj ρ).re = 1 - ρ.re := by
  simp [Complex.sub_re, Complex.one_re, Complex.conj_re]

theorem mirror_ne {ρ : ℂ} (hre : ρ.re ≠ 1/2) : 1 - conj ρ ≠ ρ := by
  intro h
  apply hre
  have := congrArg Complex.re h
  rw [mirror_re] at this
  linarith

theorem mirror_mem_offLineBox {T₁ T₂ : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ offLineBox T₁ T₂) : 1 - conj ρ ∈ offLineBox T₁ T₂ := by
  obtain ⟨⟨hNT, him⟩, hre⟩ := hρ
  refine ⟨⟨mirror_mem hNT, ?_⟩, ?_⟩
  · rw [mirror_im]
    exact him
  · rw [mirror_re]
    intro h
    exact hre (by linarith)

/-- **The integer booking**: an off-line event prices its box at ≥ 2 —
depth-blind, exactly as measured on the DH control. -/
theorem offLineBox_books_two {T₁ T₂ : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ offLineBox T₁ T₂) : 2 ≤ (offLineBox T₁ T₂).ncard := by
  have hfin : (offLineBox T₁ T₂).Finite :=
    (stripBox_finite T₁ T₂).subset (fun x hx => hx.1)
  have hsub : ({ρ, 1 - conj ρ} : Set ℂ) ⊆ offLineBox T₁ T₂ := by
    intro x hx
    rcases hx with rfl | hx
    · exact hρ
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact mirror_mem_offLineBox hρ
  have hpair : ({ρ, 1 - conj ρ} : Set ℂ).ncard = 2 :=
    Set.ncard_pair (mirror_ne hρ.2).symm
  calc (2:ℕ) = ({ρ, 1 - conj ρ} : Set ℂ).ncard := hpair.symm
    _ ≤ (offLineBox T₁ T₂).ncard := Set.ncard_le_ncard hsub hfin

/-- The box decomposition: strip = on-line ⊔ off-line. -/
theorem stripBox_decomp (T₁ T₂ : ℝ) :
    stripBox T₁ T₂ = onLineBox T₁ T₂ ∪ offLineBox T₁ T₂ := by
  ext ρ
  constructor
  · intro h
    by_cases hre : ρ.re = 1/2
    · exact Or.inl ⟨h, hre⟩
    · exact Or.inr ⟨h, hre⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

theorem seating_kills_offline {T₁ T₂ : ℝ}
    (h : (stripBox T₁ T₂).ncard = (onLineBox T₁ T₂).ncard) :
    offLineBox T₁ T₂ = ∅ := by
  have hfin := stripBox_finite T₁ T₂
  have hfin1 : (onLineBox T₁ T₂).Finite := hfin.subset (fun x hx => hx.1)
  have hfin2 : (offLineBox T₁ T₂).Finite := hfin.subset (fun x hx => hx.1)
  have hdisj : Disjoint (onLineBox T₁ T₂) (offLineBox T₁ T₂) := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hre⟩ ⟨_, hre'⟩
    exact hre' hre
  have hcard : (stripBox T₁ T₂).ncard
      = (onLineBox T₁ T₂).ncard + (offLineBox T₁ T₂).ncard := by
    rw [stripBox_decomp]
    exact Set.ncard_union_eq hdisj hfin1 hfin2
  have hzero : (offLineBox T₁ T₂).ncard = 0 := by omega
  exact (Set.ncard_eq_zero hfin2).mp hzero

/-- **RH FROM THE SEATING CENSUS.**  If in every height-box the strip census
equals the on-line census, every nontrivial zero lies on the critical line.
The count-register twin of `rh_of_outer_band`. -/
theorem rh_of_seating
    (h : ∀ T₁ T₂ : ℝ, T₁ < T₂ →
      (stripBox T₁ T₂).ncard = (onLineBox T₁ T₂).ncard) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2 := by
  intro ρ hρ
  by_contra hre
  have hmem : ρ ∈ offLineBox (ρ.im - 1) ρ.im :=
    ⟨⟨hρ, ⟨by linarith, le_refl _⟩⟩, hre⟩
  have hempty := seating_kills_offline
    (h (ρ.im - 1) ρ.im (by linarith))
  rw [hempty] at hmem
  exact hmem

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.offLineBox_books_two
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_seating
