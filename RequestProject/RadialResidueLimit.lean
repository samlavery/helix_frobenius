import RequestProject.RadialCellBalance

/-!
# The boundary-limit premise is the whole statement (ledger 688)

`radialResidue_zero_of_boundary_limit` consumes `Tendsto (fun n => radialResidue a (c n)) atTop (𝓝 0)` along an
unbounded sequence of good heights.  Because the residue is `−π ∫_a^{c n} N_off`, nonpositive and antitone in the
top height, that limit premise is not a tail estimate: it holds **iff** the residue is `0` at every `n`, **iff** there is
no off-line zero at all.  Compiled here as an `iff`, so the premise cannot be read as weaker than the conclusion.
-/

open Complex MeasureTheory Set Filter Topology
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.ResidueJump
open DoubleCoshProgram

namespace CriticalLinePhasor.DVP

/-- With no off-line zeros the off-line ledger vanishes identically. -/
theorem offLineStripZeroCountMult_eq_zero_of_noOffline (h : NoOfflineZeros) (T : ℝ) :
    offLineStripZeroCountMult T = 0 := by
  unfold offLineStripZeroCountMult
  apply Finset.sum_eq_zero
  intro ρ hρ
  exfalso
  obtain ⟨hmem, hoff⟩ := Finset.mem_filter.mp hρ
  exact hoff (h ρ ((stripZeroWindow_finite T).mem_toFinset.mp hmem).1)

theorem radialResidue_eq_zero_of_noOffline (h : NoOfflineZeros) {a b : ℝ}
    (ha : GoodHeight a) (hb : GoodHeight b) (hab : a ≤ b) : radialResidue a b = 0 := by
  rw [radialResidue_eq_neg_defect ha hb hab]
  have : ∀ t, (offLineStripZeroCountMult t : ℝ) = 0 := fun t => by
    rw [offLineStripZeroCountMult_eq_zero_of_noOffline h t]; simp
  simp [this]

/-- A nonpositive antitone sequence tends to `0` iff it is identically `0`. -/
theorem tendsto_zero_iff_eq_zero_of_antitone_nonpos {u : ℕ → ℝ} (hanti : Antitone u) (hnp : ∀ n, u n ≤ 0) :
    Tendsto u atTop (𝓝 0) ↔ ∀ n, u n = 0 := by
  constructor
  · intro hlim n
    apply le_antisymm (hnp n)
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hanti hm
  · intro h
    have hu : u = fun _ => 0 := funext h
    rw [hu]
    exact tendsto_const_nhds

/-- **The limit premise is the full statement.**  Along an unbounded sequence of good heights above a good `a`,
`radialResidue a (c n) → 0` iff there are no off-line zeros. -/
theorem tendsto_radialResidue_iff_noOffline {a : ℝ} {c : ℕ → ℝ} (ha : GoodHeight a)
    (hc : ∀ n, GoodHeight (c n)) (hmono : Monotone c) (hac : a ≤ c 0) (htop : Tendsto c atTop atTop) :
    Tendsto (fun n => radialResidue a (c n)) atTop (𝓝 0) ↔ NoOfflineZeros := by
  constructor
  · intro hlim
    -- residue zero on every good window ⟹ RadialNoResidue at good windows ⟹ no off-line zero
    intro ρ hρ
    by_contra hoff
    -- reuse the limit door: a good window above the zero has strictly negative residue
    have hzero : ∀ b, GoodHeight b → a ≤ b → radialResidue a b = 0 :=
      fun b hb hab => radialResidue_zero_of_boundary_limit ha hb hab hc htop hlim
    -- normalise to the upper half
    have him_ne : ρ.im ≠ 0 := by
      intro h0
      have hρre : ρ = ((ρ.re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simpa using h0
      obtain ⟨h1, h2, h3⟩ := hρ
      rw [hρre] at h3
      exact zeta_ne_zero_of_real_unit h1 h2 h3
    set ρ' : ℂ := if 0 < ρ.im then ρ else (starRingEnd ℂ) ρ with hρ'def
    have hρ'_mem : ρ' ∈ ZD.NontrivialZeros := by
      rw [hρ'def]
      split_ifs with hh
      · exact hρ
      · obtain ⟨h1, h2, h3⟩ := hρ
        refine ⟨by simpa using h1, by simpa using h2, ?_⟩
        rw [riemannZeta_conj, h3, map_zero]
    have hρ'_im_pos : 0 < ρ'.im := by
      rw [hρ'def]
      split_ifs with hh
      · exact hh
      · simp only [Complex.conj_im]
        rcases lt_trichotomy ρ.im 0 with h1 | h1 | h1
        · linarith
        · exact absurd h1 him_ne
        · exact absurd h1 hh
    have hρ'_re : ρ'.re ≠ 1 / 2 := by
      rw [hρ'def]
      split_ifs with hh
      · exact hoff
      · simpa using hoff
    obtain ⟨b, hb, hgb⟩ := exists_goodHeight_gt (max a ρ'.im + 1)
    have hab : a ≤ b := by linarith [le_max_left a ρ'.im]
    have hN : ∀ t, max a ρ'.im + 1 ≤ t → 1 ≤ offLineStripZeroCountMult t :=
      fun t htt => offLine_count_ge_one hρ'_mem hρ'_re hρ'_im_pos (by linarith [le_max_right a ρ'.im])
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (offline_intervalIntegrable a (max a ρ'.im + 1)) (offline_intervalIntegrable (max a ρ'.im + 1) b)
    have h1 : 0 ≤ ∫ t in a..(max a ρ'.im + 1), (offLineStripZeroCountMult t : ℝ) :=
      intervalIntegral.integral_nonneg (by linarith [le_max_left a ρ'.im]) (fun t _ => Nat.cast_nonneg _)
    have h2 : ∫ t in (max a ρ'.im + 1)..b, (1 : ℝ)
        ≤ ∫ t in (max a ρ'.im + 1)..b, (offLineStripZeroCountMult t : ℝ) :=
      intervalIntegral.integral_mono_on hb.le (by simp) (offline_intervalIntegrable _ _)
        (fun t htm => by exact_mod_cast hN t htm.1)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h2
    have hres := radialResidue_eq_neg_defect ha hgb hab
    rw [hzero b hgb hab] at hres
    have hπ := Real.pi_pos
    have hpos : 0 < ∫ t in a..b, (offLineStripZeroCountMult t : ℝ) := by
      rw [← hsplit]; linarith
    nlinarith
  · intro h
    have hconst : ∀ n, radialResidue a (c n) = 0 :=
      fun n => radialResidue_eq_zero_of_noOffline h ha (hc n) (hac.trans (hmono (Nat.zero_le n)))
    simp only [hconst]
    exact tendsto_const_nhds

/-- Hence the premise of `radialResidue_zero_of_boundary_limit` is equivalent to the Riemann Hypothesis itself. -/
theorem tendsto_radialResidue_iff_RH {a : ℝ} {c : ℕ → ℝ} (ha : GoodHeight a)
    (hc : ∀ n, GoodHeight (c n)) (hmono : Monotone c) (hac : a ≤ c 0) (htop : Tendsto c atTop atTop) :
    Tendsto (fun n => radialResidue a (c n)) atTop (𝓝 0) ↔ RiemannHypothesis := by
  rw [tendsto_radialResidue_iff_noOffline ha hc hmono hac htop]
  constructor
  · exact RiemannHypothesis_of_no_offline
  · intro hRH ρ hρ
    obtain ⟨h0, h1, hz⟩ := hρ
    refine hRH ρ hz ?_ ?_
    · rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp at hre
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro h1'
      rw [h1'] at h1
      simp at h1

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.tendsto_radialResidue_iff_noOffline
#print axioms CriticalLinePhasor.DVP.tendsto_radialResidue_iff_RH
