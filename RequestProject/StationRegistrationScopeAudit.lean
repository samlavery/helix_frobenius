import RequestProject.StationRegistrationIntertwining
import RequestProject.OnePerGap

/-!
# Scope audit for the all-signed natural-number registration

Unfolded object: strictly increasing real stations indexed by naturals;
an injective enumeration of ALL nontrivial zeros; two strict half-gap bounds.
The bounds give a lower bound on every enumerated ordinate. Conjugation gives
an upper bound. The finite strip census then contradicts injectivity from naturals.

Expectation-free decomposition A starts `have hlow : ... := ...` and uses the
finite union of the positive census and its conjugate. Decomposition B starts
`apply Set.infinite_range_of_injective` and compares that range with the same census.
The corrected draft uses `OnePerGap` on positive ordinates, with conjugation applied
after the positive-height argument; it does not instantiate this all-signed record.

Searches: `rg -n -i 'StationRegistration|ord.*bddBelow|no_shared.*ordinate'
RequestProject --glob '*.lean'`; `rg -n 'infinite_range_of_injective|Infinite.*range|
Finite.*range|finite_range' .lake/packages/mathlib/Mathlib/Data/Set/Finite --glob '*.lean'`.
LeanSearch: injective natural-number functions have infinite range.
Loogle: `Set.Infinite, Function.Injective`.
-/

open Complex

namespace CriticalLinePhasor.XiChannel

open ContourArgument

theorem StationRegistration.ordinate_lower_bound {t : ℕ → ℝ}
    (R : StationRegistration t) (ρ : XiZeroIndex) :
    min (R.e 0).val.im (t 0) ≤ ρ.val.im := by
  obtain ⟨n, rfl⟩ := R.surj ρ
  cases n with
  | zero => exact min_le_left _ _
  | succ n =>
      have h := (abs_lt.mp (R.shadowL (n + 1) (by omega))).2
      have h0 : t 0 ≤ t n := R.mono.monotone (Nat.zero_le _)
      have hn : t n < t (n + 1) := R.mono (Nat.lt_succ_self _)
      simp only [Nat.add_sub_cancel] at h
      exact (min_le_right _ _).trans (by linarith)

/-- The original all-signed record has no inhabitants. -/
theorem stationRegistration_not_nonempty (t : ℕ → ℝ) :
    ¬ Nonempty (StationRegistration t) := by
  classical
  rintro ⟨R⟩
  let L : ℝ := min (R.e 0).val.im (t 0)
  let S : Finset ℂ := stripZeroFinset (-L) ∪
    (stripZeroFinset (-L)).image (starRingEnd ℂ)
  have hlow (ρ : XiZeroIndex) : L ≤ ρ.val.im := R.ordinate_lower_bound ρ
  have hupp (ρ : XiZeroIndex) : ρ.val.im ≤ -L := by
    have hc := hlow ⟨(starRingEnd ℂ) ρ.val, conj_mem_nontrivialZeros ρ.property⟩
    simp only [Complex.conj_im] at hc
    linarith
  have hmem (ρ : XiZeroIndex) : ρ.val ∈ S := by
    have hz := DVP.NontrivialZeros_im_ne_zero ρ.property
    rcases lt_or_gt_of_ne hz with hn | hp
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(starRingEnd ℂ) ρ.val, ?_, by simp⟩
      apply mem_stripZeroFinset_iff'.mpr
      refine ⟨conj_mem_nontrivialZeros ρ.property, ?_, ?_⟩
      · simpa using neg_pos.mpr hn
      · simp only [Complex.conj_im]
        linarith [hlow ρ]
    · apply Finset.mem_union_left
      exact mem_stripZeroFinset_iff'.mpr ⟨ρ.property, hp, hupp ρ⟩
  have hinj : Function.Injective (fun n : ℕ => (R.e n).val) :=
    Subtype.val_injective.comp R.injective
  have hfinite : (Set.range (fun n : ℕ => (R.e n).val)).Finite :=
    S.finite_toSet.subset (by rintro _ ⟨n, rfl⟩; exact hmem (R.e n))
  exact Set.infinite_range_of_injective hinj hfinite

end CriticalLinePhasor.XiChannel

#print axioms CriticalLinePhasor.XiChannel.StationRegistration.ordinate_lower_bound
#print axioms CriticalLinePhasor.XiChannel.stationRegistration_not_nonempty
