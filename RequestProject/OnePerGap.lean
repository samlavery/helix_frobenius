import RequestProject.HelixHeightIntertwining
import RequestProject.ZetaContourArgument
import RequestProject.XiOrder
import RequestProject.FinitePartSymmetry
import RequestProject.DVPArgumentPrinciple
import RequestProject.DVPChannelBase

/-!
# One zero per station gap ⟹ RH and simplicity ⟹ full intertwining (ledger 600)

The registration operator (HP_PROGRAM §1) has spectrum a strictly increasing station sequence `t`
built from the primes, and the measured law is that the zeros register bijectively: every gap
`(t n, t (n+1)]` holds exactly one zero, counted with multiplicity. This file compiles that law as
the hypothesis `OnePerGap t`, stated on the compiled strip census (`stripZeroFinset`,
`ZD.xiOrderNat`), and proves:

* every zero with positive ordinate is on the line and simple (`online_simple_of_onePerGap`): an
  off-line zero and its mirror `1 − ρ̄` are two zeros at one ordinate, so their gap would count at
  least two; a multiple zero counts at least two by itself;
* hence RH on the whole zero set (`nontrivialZeros_online_of_onePerGap`, via the conjugation
  symmetry of the zero set) and full intertwining of the height correspondence
  (`semiconj_of_onePerGap`, via 597).

This is Track C's "density one per box" leaf with the boxes taken to be the station gaps, and the
count register's form of the residual tail law. The stations themselves — the prime-forced
sequence `ϑ(t_n)/π + 3/2 + Ŝ(t_n) = n` — are the next object.
-/

open Complex Finset

namespace CriticalLinePhasor.ContourArgument

/-- Multiplicity-weighted count of zeros with ordinate in `(a, b]`. -/
noncomputable def bandCountMult (a b : ℝ) : ℕ :=
  ∑ ρ ∈ (stripZeroFinset b).filter (fun ρ => a < ρ.im), ZD.xiOrderNat ρ

theorem mem_stripZeroFinset_iff' {T : ℝ} {ρ : ℂ} :
    ρ ∈ stripZeroFinset T ↔ ρ ∈ ZD.NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  unfold stripZeroFinset
  rw [Set.Finite.mem_toFinset]
  rfl

theorem mem_band_iff {a b : ℝ} {ρ : ℂ} :
    ρ ∈ (stripZeroFinset b).filter (fun ρ => a < ρ.im)
      ↔ ρ ∈ ZD.NontrivialZeros ∧ 0 < ρ.im ∧ a < ρ.im ∧ ρ.im ≤ b := by
  rw [Finset.mem_filter, mem_stripZeroFinset_iff']
  tauto

/-- **One zero per gap**: stations strictly increasing and unbounded, and exactly one zero (with
multiplicity) in every gap `(t n, t (n+1)]`. Zeros at or below `t 0` are outside the gaps. -/
structure OnePerGap (t : ℕ → ℝ) : Prop where
  mono : StrictMono t
  unbounded : Filter.Tendsto t Filter.atTop Filter.atTop
  one : ∀ n, bandCountMult (t n) (t (n + 1)) = 1

/-- Every ordinate above `t 0` lies in some gap `(t n, t (n+1)]`. -/
theorem OnePerGap.exists_gap {t : ℕ → ℝ} (H : OnePerGap t) {y : ℝ} (hy : t 0 < y) :
    ∃ n, t n < y ∧ y ≤ t (n + 1) := by
  classical
  have hex : ∃ n, y ≤ t n := by
    obtain ⟨N, hN⟩ := (Filter.tendsto_atTop.1 H.unbounded y) |>.exists
    exact ⟨N, hN⟩
  let n₀ := Nat.find hex
  have hspec : y ≤ t n₀ := Nat.find_spec hex
  have hn₀ : n₀ ≠ 0 := by
    intro h0
    rw [h0] at hspec
    linarith
  obtain ⟨n, hn⟩ : ∃ n, n₀ = n + 1 := ⟨n₀ - 1, by omega⟩
  refine ⟨n, ?_, by rw [← hn]; exact hspec⟩
  have hmin : ¬ y ≤ t n := Nat.find_min hex (by omega)
  linarith

/-- The mirror of a zero is a zero at the same ordinate, and differs from it off the line. -/
theorem mirror_mem {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    1 - (starRingEnd ℂ) ρ ∈ ZD.NontrivialZeros :=
  (XiChannel.xiZeroReflection ⟨ρ, hρ⟩).2

theorem mirror_im (ρ : ℂ) : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by simp

theorem mirror_ne_of_off {ρ : ℂ} (h : ρ.re ≠ 1 / 2) : 1 - (starRingEnd ℂ) ρ ≠ ρ := by
  intro he
  have := congrArg Complex.re he
  simp at this
  exact h (by linarith)

/-- **Every zero above the first station is on the line and simple.** -/
theorem online_simple_of_onePerGap {t : ℕ → ℝ} (H : OnePerGap t) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (hpos : 0 < ρ.im) (hab : t 0 < ρ.im) :
    ρ.re = 1 / 2 ∧ ZD.xiOrderNat ρ = 1 := by
  classical
  obtain ⟨n, hlo, hhi⟩ := H.exists_gap hab
  have hone := H.one n
  have hmem : ρ ∈ (stripZeroFinset (t (n + 1))).filter (fun ρ => t n < ρ.im) :=
    mem_band_iff.2 ⟨hρ, hpos, hlo, hhi⟩
  have hm := ZD.xiOrderNat_pos_of_mem_NontrivialZeros hρ
  have hsingle : ZD.xiOrderNat ρ ≤ bandCountMult (t n) (t (n + 1)) :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  constructor
  · by_contra hre
    -- the mirror is a second zero in the same gap
    have hmem' : 1 - (starRingEnd ℂ) ρ ∈ (stripZeroFinset (t (n + 1))).filter (fun ρ => t n < ρ.im) :=
      mem_band_iff.2 ⟨mirror_mem hρ, by rw [mirror_im]; exact hpos, by rw [mirror_im]; exact hlo,
        by rw [mirror_im]; exact hhi⟩
    have hm' := ZD.xiOrderNat_pos_of_mem_NontrivialZeros (mirror_mem hρ)
    have hpair : ZD.xiOrderNat ρ + ZD.xiOrderNat (1 - (starRingEnd ℂ) ρ)
        ≤ bandCountMult (t n) (t (n + 1)) := by
      unfold bandCountMult
      rw [← Finset.sum_pair (mirror_ne_of_off hre).symm]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hmem
        · exact hmem'
      · intro _ _ _; exact Nat.zero_le _
    rw [hone] at hpair
    omega
  · rw [hone] at hsingle
    omega

/-- **RH from one zero per gap**, given the range at or below the first station. -/
theorem nontrivialZeros_online_of_onePerGap {t : ℕ → ℝ} (H : OnePerGap t)
    (hlow : ∀ ρ ∈ ZD.NontrivialZeros, 0 < ρ.im → ρ.im ≤ t 0 → ρ.re = 1 / 2) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  have hpos_case : ∀ ρ ∈ ZD.NontrivialZeros, 0 < ρ.im → ρ.re = 1 / 2 := by
    intro ρ hρ hpos
    by_cases hab : t 0 < ρ.im
    · exact (online_simple_of_onePerGap H hρ hpos hab).1
    · exact hlow ρ hρ hpos (not_lt.1 hab)
  intro ρ hρ
  rcases lt_trichotomy 0 ρ.im with hpos | hzero | hneg
  · exact hpos_case ρ hρ hpos
  · exfalso
    exact CriticalLinePhasor.DVP.NontrivialZeros_im_ne_zero hρ hzero.symm
  · have hc := conj_mem_nontrivialZeros hρ
    have hcpos : 0 < ((starRingEnd ℂ) ρ).im := by simp; linarith
    have := hpos_case _ hc hcpos
    simpa using this

/-- **RH from one zero per gap with the first station at or below 58**: the range below is the
compiled ladder (`rh_iff_online_above_58`). -/
theorem nontrivialZeros_online_of_onePerGap_of_le_58 {t : ℕ → ℝ} (H : OnePerGap t)
    (h58 : t 0 ≤ 58) : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  rw [CriticalLinePhasor.DVP.rh_iff_online_above_58]
  intro ρ hρ h58'
  rcases lt_trichotomy 0 ρ.im with hpos | hzero | hneg
  · have hab : t 0 < ρ.im := by
      rw [abs_of_pos hpos] at h58'
      linarith
    exact (online_simple_of_onePerGap H hρ hpos hab).1
  · exfalso
    exact CriticalLinePhasor.DVP.NontrivialZeros_im_ne_zero hρ hzero.symm
  · have hc := conj_mem_nontrivialZeros hρ
    have hcpos : 0 < ((starRingEnd ℂ) ρ).im := by simp; linarith
    have hab : t 0 < ((starRingEnd ℂ) ρ).im := by
      rw [abs_of_neg hneg] at h58'
      simp
      linarith
    have := (online_simple_of_onePerGap H hc hcpos hab).1
    simpa using this

/-- **Full intertwining from one zero per gap** (first station at or below 58). -/
theorem semiconj_of_onePerGap {t : ℕ → ℝ} (H : OnePerGap t) (h58 : t 0 ≤ 58) :
    Function.Semiconj XiChannel.zeroHeightCorrespondence XiChannel.xiZeroLedgerOperator
      (ThreeDFocal.carrierThreeDOperator 1 1) :=
  XiChannel.semiconj_iff_nontrivialZeros_online.2
    (nontrivialZeros_online_of_onePerGap_of_le_58 H h58)

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.online_simple_of_onePerGap
#print axioms CriticalLinePhasor.ContourArgument.nontrivialZeros_online_of_onePerGap
#print axioms CriticalLinePhasor.ContourArgument.nontrivialZeros_online_of_onePerGap_of_le_58
#print axioms CriticalLinePhasor.ContourArgument.semiconj_of_onePerGap
