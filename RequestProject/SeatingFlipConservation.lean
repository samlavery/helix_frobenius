import RequestProject.SeatingOddFlips
import RequestProject.SeatingChain
import RequestProject.SeatingHighFlips

/-!
# Flip–census conservation: the flip supply per box IS the odd on-line census

The T★ package.  The maximal number of consecutive sign changes of the bank
readout in a box is an **attained finite maximum**, exhibited and pinned by two
inequalities — never a supremum:

* **upper** (`flips_le_oddOnLine_ncard`): every admissible flip chain has at
  most odd-on-line-census many flips — a sign change forces an on-line zero of
  ODD ζ-multiplicity strictly inside the flip interval (`flip_yields_odd_zero`,
  by strong induction on the zero count: an even-order zero repels the flip to
  one side, `even_mult_no_flip`);
* **lower** (`exists_odd_census_flip_chain`): a chain achieving exactly the
  odd on-line census exists — every odd-order zero flips (`odd_mult_flips`),
  one uniform window radius serves all of them (`exists_uniform_delta_odd`),
  and the greedy extraction packs the windows (`exists_flip_chain_of_windows`).

Consequence: the high-flip-visibility door is EQUIVALENT to a pure census
inequality (`high_flip_visibility_iff_flip_census`), so the door hypothesis is
exactly the vanishing of the integer defect
`D(box) = (stripBox).ncard − (oddOnLineBox).ncard ≥ 0` above the ladder —
the count-register shadow of the R-normal-form residual (poles of R = the
flip-invisible classes: off-line and even-order on-line).

No `sorry`, no `axiom`.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- The on-line zeros of the readout in an open ordinate window form a finite
set (they embed into the finite `onLineBox`). -/
theorem zerosIoo_finite (x y : ℝ) :
    ({t : ℝ | t ∈ Set.Ioo x y ∧ XiLine t = 0}).Finite := by
  have hfin : (onLineBox x y).Finite :=
    (stripBox_finite x y).subset (fun ρ hρ => hρ.1)
  have hsub : {t : ℝ | t ∈ Set.Ioo x y ∧ XiLine t = 0}
      ⊆ Complex.im '' (onLineBox x y) := by
    rintro t ⟨htI, ht0⟩
    refine ⟨linePt t, ⟨⟨XiLine_zero_iff.mp ht0, ?_, ?_⟩, linePt_re t⟩,
      linePt_im t⟩
    · rw [linePt_im]
      exact htI.1
    · rw [linePt_im]
      exact htI.2.le
  exact (hfin.image _).subset hsub

/-- **Even order repels the flip**: at an on-line zero of even ζ-multiplicity
the readout has the SAME sign on both sides of every sufficiently small
symmetric window, and the zero is isolated in that window.  The exact local
mechanism that makes even-order zeros flip-invisible. -/
theorem even_mult_no_flip {γ : ℝ} (hγ : γ ≠ 0)
    (hmem : linePt γ ∈ ZD.NontrivialZeros)
    (heven : Even (Zeta23.zeroMult (linePt γ))) :
    ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      0 < XiLine (γ - δ) * XiLine (γ + δ) ∧
      ∀ h : ℝ, 0 < |h| → |h| ≤ δ → XiLine (γ + h) ≠ 0 := by
  set m := Zeta23.zeroMult (linePt γ) with hm
  have him : (linePt γ).im ≠ 0 := by
    rw [linePt_im]
    exact hγ
  have hbridge := CriticalLinePhasor.DVP.xi_order_eq_zeta_order him
  have hξne : analyticOrderAt ZD.riemannXi (linePt γ) ≠ ⊤ :=
    ZD.riemannXi_analyticOrderAt_ne_top_everywhere _
  have hζne : analyticOrderAt riemannZeta (linePt γ) ≠ ⊤ := hbridge ▸ hξne
  have hξord : analyticOrderAt ZD.riemannXi (linePt γ) = (m : ℕ∞) := by
    rw [hbridge, hm]
    unfold Zeta23.zeroMult
    exact (ENat.coe_toNat hζne).symm
  have hDiff : Differentiable ℂ ZD.riemannXi := fun z => ZD.riemannXi_differentiable z
  have hA : AnalyticAt ℂ ZD.riemannXi (linePt γ) :=
    hDiff.differentiableOn.analyticAt
      (IsOpen.mem_nhds isOpen_univ (Set.mem_univ _))
  obtain ⟨g, hgA, hg0, hev⟩ := (hA.analyticOrderAt_eq_natCast).mp hξord
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hr, hfac⟩ := hev
  -- the line moves at unit speed toward ρ
  have hline_sub : ∀ h : ℝ, linePt (γ + h) - linePt γ = (h : ℂ) * I := by
    intro h
    unfold linePt
    push_cast
    ring
  have hline_dist : ∀ h : ℝ, dist (linePt (γ + h)) (linePt γ) = |h| := by
    intro h
    rw [dist_eq_norm, hline_sub]
    simp [Complex.norm_mul]
  -- the real unit
  set u : ℝ → ℝ := fun h => (I^m * g (linePt (γ + h))).re with hu
  set v : ℝ → ℝ := fun h => (I^m * g (linePt (γ + h))).im with hv
  have hXi_eq : ∀ h : ℝ, |h| < r → XiLine (γ + h) = h^m * u h := by
    intro h hh
    have hfa := hfac (by rw [hline_dist]; exact hh)
    unfold XiLine
    rw [hfa, hline_sub, smul_eq_mul, mul_pow]
    have hre : (h:ℂ)^m * I^m * g (linePt (γ + h))
        = ((h^m : ℝ) : ℂ) * (I^m * g (linePt (γ + h))) := by
      push_cast
      ring
    rw [hre, Complex.re_ofReal_mul]
  have hXi_im : ∀ h : ℝ, |h| < r → 0 = h^m * v h := by
    intro h hh
    have hfa := hfac (by rw [hline_dist]; exact hh)
    have h0 := Xi_line_im (γ + h)
    rw [hfa, hline_sub, smul_eq_mul, mul_pow] at h0
    have hre : (h:ℂ)^m * I^m * g (linePt (γ + h))
        = ((h^m : ℝ) : ℂ) * (I^m * g (linePt (γ + h))) := by
      push_cast
      ring
    rw [hre] at h0
    rw [← h0, Complex.im_ofReal_mul]
  -- continuity at 0 of the unit and its imaginary part
  have hinner : Continuous (fun h : ℝ => linePt (γ + h)) := by
    unfold linePt
    exact continuous_const.add
      ((Complex.continuous_ofReal.comp
        (continuous_const.add continuous_id)).mul continuous_const)
  have hg_at : ContinuousAt (fun h : ℝ => g (linePt (γ + h))) 0 := by
    have h1 : ContinuousAt (fun h : ℝ => linePt (γ + h)) 0 := hinner.continuousAt
    have h2 : ContinuousAt g ((fun h : ℝ => linePt (γ + h)) 0) := by
      simp only [add_zero]
      exact hgA.continuousAt
    exact ContinuousAt.comp h2 h1
  have hu_at : ContinuousAt u 0 :=
    Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hg_at)
  have hv_at : ContinuousAt v 0 :=
    Complex.continuous_im.continuousAt.comp (continuousAt_const.mul hg_at)
  -- the unit is real at 0: v 0 = 0 by limit uniqueness over the punctured line
  have hv0 : v 0 = 0 := by
    have hev0 : ∀ᶠ h in nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ, v h = 0 := by
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
      refine ⟨r, hr, fun h hh hne => ?_⟩
      have hhr : |h| < r := by
        rw [Real.dist_eq, sub_zero] at hh
        exact hh
      have h0 := hXi_im h hhr
      have hm0 : h ≠ 0 := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hne
      have hpow : h^m ≠ 0 := pow_ne_zero _ hm0
      rcases mul_eq_zero.mp h0.symm with h1 | h1
      · exact absurd h1 hpow
      · exact h1
    have h1 : Filter.Tendsto v (nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ) (nhds (v 0)) :=
      hv_at.continuousWithinAt.tendsto
    have hev0' : v =ᶠ[nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ] fun _ => 0 := hev0
    have h2 : Filter.Tendsto v (nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ) (nhds 0) :=
      Filter.Tendsto.congr' hev0'.symm tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- hence u 0 ≠ 0
  have hu0 : u 0 ≠ 0 := by
    intro h0
    apply hg0
    have hgval : I^m * g (linePt (γ + 0)) = 0 := by
      apply Complex.ext
      · exact h0
      · exact hv0
    rw [show γ + (0:ℝ) = γ from add_zero γ] at hgval
    have hI : (I:ℂ)^m ≠ 0 := pow_ne_zero _ I_ne_zero
    exact (mul_eq_zero.mp hgval).resolve_left hI
  -- the nonvanishing window of the analytic unit (isolation supply)
  have hgval0 : (fun h : ℝ => g (linePt (γ + h))) 0 ≠ 0 := by
    simp only [add_zero]
    exact hg0
  have hgne := hg_at.eventually_ne hgval0
  rw [Metric.eventually_nhds_iff] at hgne
  obtain ⟨r₂, hr₂, hgne'⟩ := hgne
  -- the sign window of the real unit
  obtain ⟨ε₁, hε₁, hus⟩ := Metric.continuousAt_iff.mp hu_at (|u 0|/2)
    (by positivity)
  refine ⟨min (min r r₂) ε₁, lt_min (lt_min hr hr₂) hε₁, fun δ hδ0 hδ => ?_⟩
  have hδr : δ < r :=
    lt_of_lt_of_le hδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδr₂ : δ < r₂ :=
    lt_of_lt_of_le hδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδε : δ < ε₁ := lt_of_lt_of_le hδ (min_le_right _ _)
  constructor
  · -- same sign on both sides
    have hup : |u δ - u 0| < |u 0|/2 := by
      have := hus (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ0]; exact hδε)
      rwa [Real.dist_eq] at this
    have hum : |u (-δ) - u 0| < |u 0|/2 := by
      have := hus (by
        rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hδ0]
        exact hδε : dist (-δ) 0 < ε₁)
      rwa [Real.dist_eq] at this
    have hXp : XiLine (γ + δ) = δ^m * u δ :=
      hXi_eq δ (by rw [abs_of_pos hδ0]; exact hδr)
    have hXm : XiLine (γ - δ) = (-δ)^m * u (-δ) := by
      have := hXi_eq (-δ) (by rw [abs_neg, abs_of_pos hδ0]; exact hδr)
      rw [show γ + -δ = γ - δ by ring] at this
      exact this
    have hnegpow : (-δ)^m = δ^m := heven.neg_pow δ
    have hδm : (0:ℝ) < δ^m := pow_pos hδ0 m
    rw [hXp, hXm, hnegpow]
    -- u(δ), u(−δ) share the sign of u 0
    rcases lt_or_gt_of_ne hu0 with hneg | hpos
    · have h1 : u δ < u 0 / 2 := by
        have := abs_lt.mp hup
        have ha : |u 0| = -(u 0) := abs_of_neg hneg
        rw [ha] at this
        linarith [this.2]
      have h2 : u (-δ) < u 0 / 2 := by
        have := abs_lt.mp hum
        have ha : |u 0| = -(u 0) := abs_of_neg hneg
        rw [ha] at this
        linarith [this.2]
      have hupos : 0 < u δ * u (-δ) := by
        have hd1 : u δ < 0 := by linarith
        have hd2 : u (-δ) < 0 := by linarith
        exact mul_pos_of_neg_of_neg hd1 hd2
      nlinarith [mul_pos hδm hδm, hupos]
    · have h1 : u 0 / 2 < u δ := by
        have := abs_lt.mp hup
        have ha : |u 0| = u 0 := abs_of_pos hpos
        rw [ha] at this
        linarith [this.1]
      have h2 : u 0 / 2 < u (-δ) := by
        have := abs_lt.mp hum
        have ha : |u 0| = u 0 := abs_of_pos hpos
        rw [ha] at this
        linarith [this.1]
      have hupos : 0 < u δ * u (-δ) := by
        have hd1 : 0 < u δ := by linarith
        have hd2 : 0 < u (-δ) := by linarith
        exact mul_pos hd1 hd2
      nlinarith [mul_pos hδm hδm, hupos]
  · -- isolation: no other zero inside the window
    intro h hh0 hhδ
    have hhr : |h| < r := lt_of_le_of_lt hhδ hδr
    have hhr₂ : |h| < r₂ := lt_of_le_of_lt hhδ hδr₂
    have hgn : g (linePt (γ + h)) ≠ 0 :=
      hgne' (by rw [Real.dist_eq, sub_zero]; exact hhr₂)
    intro hzero
    have hxi0 : ZD.riemannXi (linePt (γ + h)) = 0 := by
      apply Complex.ext
      · rw [Complex.zero_re]
        exact hzero
      · rw [Complex.zero_im]
        exact Xi_line_im _
    have hfa := hfac (by rw [hline_dist]; exact hhr)
    rw [hfa, hline_sub, smul_eq_mul] at hxi0
    have hhc : (h : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      intro hc
      rw [hc, abs_zero] at hh0
      exact lt_irrefl 0 hh0
    exact (mul_ne_zero (pow_ne_zero _ (mul_ne_zero hhc I_ne_zero)) hgn) hxi0

/-- **A flip yields an ODD-order zero**: a sign change of the readout forces an
on-line zero of odd ζ-multiplicity strictly between the heights.  Strong
induction on the (finite) zero count of the window: an even-order zero has
same-sign edges and an isolating window, so the flip survives on one side with
strictly fewer zeros. -/
theorem flip_yields_odd_zero {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hflip : XiLine x * XiLine y < 0) :
    ∃ γ ∈ Set.Ioo x y, linePt γ ∈ ZD.NontrivialZeros ∧
      Odd (Zeta23.zeroMult (linePt γ)) := by
  suffices H : ∀ n : ℕ, ∀ x y : ℝ, 0 < x → x < y → XiLine x * XiLine y < 0 →
      ({t : ℝ | t ∈ Set.Ioo x y ∧ XiLine t = 0}).ncard ≤ n →
      ∃ γ ∈ Set.Ioo x y, linePt γ ∈ ZD.NontrivialZeros ∧
        Odd (Zeta23.zeroMult (linePt γ)) by
    exact H (({t : ℝ | t ∈ Set.Ioo x y ∧ XiLine t = 0}).ncard) x y hx hxy
      hflip le_rfl
  intro n
  induction n with
  | zero =>
    intro x y hx hxy hflip hcard
    obtain ⟨γ, hγmem, hγzero⟩ := flip_yields_online_zero hxy hflip
    have hfinB := zerosIoo_finite x y
    have hpos : 0 < ({t : ℝ | t ∈ Set.Ioo x y ∧ XiLine t = 0}).ncard :=
      (Set.ncard_pos hfinB).mpr ⟨γ, hγmem, XiLine_zero_iff.mpr hγzero⟩
    omega
  | succ n ih =>
    intro x y hx hxy hflip hcard
    obtain ⟨γ, hγmem, hγzero⟩ := flip_yields_online_zero hxy hflip
    by_cases hodd : Odd (Zeta23.zeroMult (linePt γ))
    · exact ⟨γ, hγmem, hγzero, hodd⟩
    have heven : Even (Zeta23.zeroMult (linePt γ)) :=
      (Nat.even_or_odd _).resolve_right hodd
    have hγ0 : γ ≠ 0 := (lt_trans hx hγmem.1).ne'
    obtain ⟨ε, hε, hprop⟩ := even_mult_no_flip hγ0 hγzero heven
    set δ : ℝ := min (ε/2) (min ((γ - x)/2) ((y - γ)/2)) with hδdef
    have hxγ : x < γ := hγmem.1
    have hγy : γ < y := hγmem.2
    have hδ0 : 0 < δ :=
      lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδx : δ < γ - x :=
      lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _))
        (by linarith)
    have hδy : δ < y - γ :=
      lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _))
        (by linarith)
    obtain ⟨hposprod, hiso⟩ := hprop δ hδ0 hδε
    have habs : |(-δ)| = δ := by rw [abs_neg]; exact abs_of_pos hδ0
    have habs' : |δ| = δ := abs_of_pos hδ0
    have hQ : XiLine (γ - δ) ≠ 0 := by
      have h := hiso (-δ) (by rw [habs]; exact hδ0) (le_of_eq habs)
      rw [show γ + -δ = γ - δ by ring] at h
      exact h
    have hR : XiLine (γ + δ) ≠ 0 :=
      hiso δ (by rw [habs']; exact hδ0) (le_of_eq habs')
    have hP : XiLine x ≠ 0 := by
      intro h
      rw [h, zero_mul] at hflip
      exact lt_irrefl 0 hflip
    -- the shared census bookkeeping
    have hbig : γ ∈ {t : ℝ | t ∈ Set.Ioo x y ∧ XiLine t = 0} :=
      ⟨hγmem, XiLine_zero_iff.mpr hγzero⟩
    have hfinB := zerosIoo_finite x y
    have hdiff : ({t : ℝ | t ∈ Set.Ioo x y ∧ XiLine t = 0} \ {γ}).ncard
        = ({t : ℝ | t ∈ Set.Ioo x y ∧ XiLine t = 0}).ncard - 1 :=
      Set.ncard_diff_singleton_of_mem hbig
    have hone : 0 < ({t : ℝ | t ∈ Set.Ioo x y ∧ XiLine t = 0}).ncard :=
      (Set.ncard_pos hfinB).mpr ⟨γ, hbig⟩
    have hfinD : ({t : ℝ | t ∈ Set.Ioo x y ∧ XiLine t = 0} \ {γ}).Finite :=
      hfinB.subset Set.diff_subset
    rcases lt_trichotomy (XiLine x * XiLine (γ - δ)) 0 with hPQ | hPQ | hPQ
    · -- the flip survives on the left window
      have hxlt : x < γ - δ := by linarith
      have hsub : {t : ℝ | t ∈ Set.Ioo x (γ - δ) ∧ XiLine t = 0}
          ⊆ {t : ℝ | t ∈ Set.Ioo x y ∧ XiLine t = 0} \ {γ} := by
        rintro t ⟨ht, ht0⟩
        refine ⟨⟨⟨ht.1, by linarith [ht.2]⟩, ht0⟩, ?_⟩
        intro hc
        rw [Set.mem_singleton_iff] at hc
        rw [hc] at ht
        linarith [ht.2]
      have hcard' : ({t : ℝ | t ∈ Set.Ioo x (γ - δ) ∧ XiLine t = 0}).ncard
          ≤ n := by
        have h1 := Set.ncard_le_ncard hsub hfinD
        omega
      obtain ⟨γ', hγ'mem, hγ'zero, hγ'odd⟩ := ih x (γ - δ) hx hxlt hPQ hcard'
      exact ⟨γ', ⟨hγ'mem.1, by linarith [hγ'mem.2]⟩, hγ'zero, hγ'odd⟩
    · exact absurd hPQ (mul_ne_zero hP hQ)
    · -- the flip survives on the right window
      have hRS : XiLine (γ + δ) * XiLine y < 0 := by
        by_contra hc
        push_neg at hc
        have h1 : XiLine x * XiLine y * (XiLine (γ - δ) * XiLine (γ + δ)) < 0 :=
          mul_neg_of_neg_of_pos hflip hposprod
        have h2 : 0 ≤ XiLine x * XiLine (γ - δ) * (XiLine (γ + δ) * XiLine y) :=
          mul_nonneg hPQ.le hc
        have h3 : XiLine x * XiLine y * (XiLine (γ - δ) * XiLine (γ + δ))
            = XiLine x * XiLine (γ - δ) * (XiLine (γ + δ) * XiLine y) := by
          ring
        linarith [h1, h2, h3]
      have hlt : γ + δ < y := by linarith
      have h0' : 0 < γ + δ := by linarith
      have hsub : {t : ℝ | t ∈ Set.Ioo (γ + δ) y ∧ XiLine t = 0}
          ⊆ {t : ℝ | t ∈ Set.Ioo x y ∧ XiLine t = 0} \ {γ} := by
        rintro t ⟨ht, ht0⟩
        refine ⟨⟨⟨by linarith [ht.1], ht.2⟩, ht0⟩, ?_⟩
        intro hc
        rw [Set.mem_singleton_iff] at hc
        rw [hc] at ht
        linarith [ht.1]
      have hcard' : ({t : ℝ | t ∈ Set.Ioo (γ + δ) y ∧ XiLine t = 0}).ncard
          ≤ n := by
        have h1 := Set.ncard_le_ncard hsub hfinD
        omega
      obtain ⟨γ', hγ'mem, hγ'zero, hγ'odd⟩ := ih (γ + δ) y h0' hlt hRS hcard'
      exact ⟨γ', ⟨by linarith [hγ'mem.1], hγ'mem.2⟩, hγ'zero, hγ'odd⟩

/-- The odd-order on-line census of the OPEN window `(T₁, T₂)`: the exact
flip-visible class.  Open because a zero at either edge cannot flip within
the box. -/
def oddOnLineBox (T₁ T₂ : ℝ) : Set ℂ :=
  {ρ | ρ ∈ ZD.NontrivialZeros ∧ ρ.im ∈ Set.Ioo T₁ T₂ ∧ ρ.re = 1/2 ∧
    Odd (Zeta23.zeroMult ρ)}

theorem oddOnLineBox_subset_strip (T₁ T₂ : ℝ) :
    oddOnLineBox T₁ T₂ ⊆ stripBox T₁ T₂ := by
  rintro ρ ⟨hNT, hIoo, _, _⟩
  exact ⟨hNT, hIoo.1, hIoo.2.le⟩

/-- **The defect is nonnegative**: the flip-visible census never exceeds the
strip census — `D(box) = strip − oddOnLine ≥ 0`. -/
theorem oddOnLine_ncard_le_strip (T₁ T₂ : ℝ) :
    (oddOnLineBox T₁ T₂).ncard ≤ (stripBox T₁ T₂).ncard :=
  Set.ncard_le_ncard (oddOnLineBox_subset_strip T₁ T₂) (stripBox_finite T₁ T₂)

/-- **The upper half of the conservation law**: every admissible flip chain in
`[T₁, T₂]` has at most odd-on-line-census many flips. -/
theorem flips_le_oddOnLine_ncard {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) {n : ℕ}
    (a : Fin (n+1) → ℝ) (hmono : StrictMono a)
    (hlo : T₁ ≤ a 0) (hhi : a (Fin.last n) ≤ T₂)
    (hflip : ∀ i : Fin n, XiLine (a i.castSucc) * XiLine (a i.succ) < 0) :
    n ≤ (oddOnLineBox T₁ T₂).ncard := by
  have hchoice : ∀ i : Fin n, ∃ γ ∈ Set.Ioo (a i.castSucc) (a i.succ),
      linePt γ ∈ ZD.NontrivialZeros ∧ Odd (Zeta23.zeroMult (linePt γ)) := by
    intro i
    have hlt : a i.castSucc < a i.succ := by
      apply hmono
      rw [Fin.lt_def, Fin.coe_castSucc, Fin.val_succ]
      omega
    have h0 : 0 < a i.castSucc :=
      lt_of_lt_of_le hT₁ (le_trans hlo (hmono.monotone (Fin.zero_le _)))
    exact flip_yields_odd_zero h0 hlt (hflip i)
  choose γ hγmem hγzero hγodd using hchoice
  have hγmono : StrictMono γ := by
    intro i j hij
    have h1 : γ i < a i.succ := (hγmem i).2
    have h2 : a j.castSucc < γ j := (hγmem j).1
    have hle : a i.succ ≤ a j.castSucc := by
      apply hmono.monotone
      rw [Fin.le_def, Fin.val_succ, Fin.coe_castSucc]
      exact hij
    linarith
  have hmem : ∀ i : Fin n, linePt (γ i) ∈ oddOnLineBox T₁ T₂ := by
    intro i
    have h1 : a 0 ≤ a i.castSucc := hmono.monotone (Fin.zero_le _)
    have h2 : a i.succ ≤ a (Fin.last n) := hmono.monotone (Fin.le_last _)
    have hm1 := (hγmem i).1
    have hm2 := (hγmem i).2
    refine ⟨hγzero i, ⟨?_, ?_⟩, linePt_re _, hγodd i⟩
    · rw [linePt_im]
      linarith
    · rw [linePt_im]
      linarith
  have hinj : Function.Injective (fun i : Fin n => linePt (γ i)) := by
    intro i j h
    have him := congrArg Complex.im h
    rw [linePt_im, linePt_im] at him
    exact hγmono.injective him
  have hsub : Set.range (fun i : Fin n => linePt (γ i)) ⊆ oddOnLineBox T₁ T₂ := by
    rintro z ⟨i, rfl⟩
    exact hmem i
  have hfin : (oddOnLineBox T₁ T₂).Finite :=
    (stripBox_finite T₁ T₂).subset (oddOnLineBox_subset_strip T₁ T₂)
  calc n = (Set.univ : Set (Fin n)).ncard := by
        simp [Set.ncard_univ, Nat.card_eq_fintype_card]
    _ = ((fun i : Fin n => linePt (γ i)) '' Set.univ).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ = (Set.range fun i : Fin n => linePt (γ i)).ncard := by
        rw [Set.image_univ]
    _ ≤ (oddOnLineBox T₁ T₂).ncard := Set.ncard_le_ncard hsub hfin

/-- Uniform window radius for a sorted list of ODD-order on-line ordinates
inside `(T₁, T₂)`: all windows flip, all windows disjoint, and the hull stays
inside the box on BOTH sides — the right margin is what pins the attained
maximum inside the box. -/
theorem exists_uniform_delta_odd (T₁ T₂ : ℝ) :
    ∀ gs : List ℝ, gs.Chain' (· < ·) →
    (∀ g ∈ gs, T₁ < g ∧ g < T₂ ∧ g ≠ 0 ∧ linePt g ∈ ZD.NontrivialZeros ∧
      Odd (Zeta23.zeroMult (linePt g))) →
    ∃ δstar : ℝ, 0 < δstar ∧ δstar ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < δstar →
      gs.Chain' (fun x y => x + δ < y - δ) ∧
      (∀ g ∈ gs, XiLine (g - δ) * XiLine (g + δ) < 0) ∧
      (∀ g ∈ gs, T₁ ≤ g - δ) ∧
      (∀ g ∈ gs, g + δ ≤ T₂) := by
  intro gs
  induction gs with
  | nil =>
    intro _ _
    exact ⟨1, one_pos, le_refl 1, fun δ _ _ =>
      ⟨List.isChain_nil, fun g hg => absurd hg (List.not_mem_nil),
        fun g hg => absurd hg (List.not_mem_nil),
        fun g hg => absurd hg (List.not_mem_nil)⟩⟩
  | cons g rest ih =>
    intro hchain hmem
    obtain ⟨hT₁g, hgT₂, hgne, hgmem, hgodd⟩ := hmem g List.mem_cons_self
    obtain ⟨εg, hεg, hflipg⟩ := odd_mult_flips hgne hgmem hgodd
    have hchain' : rest.Chain' (· < ·) := hchain.tail
    have hmem' : ∀ x ∈ rest, T₁ < x ∧ x < T₂ ∧ x ≠ 0 ∧
        linePt x ∈ ZD.NontrivialZeros ∧ Odd (Zeta23.zeroMult (linePt x)) :=
      fun x hx => hmem x (List.mem_cons_of_mem g hx)
    obtain ⟨δ₁, hδ₁, hδ₁1, hprop⟩ := ih hchain' hmem'
    rcases hr : rest with _ | ⟨g', rest'⟩
    · -- single element
      refine ⟨min εg (min (g - T₁) (min (T₂ - g) 1)), by
        have h1 : (0:ℝ) < g - T₁ := by linarith
        have h2 : (0:ℝ) < T₂ - g := by linarith
        positivity, ?_, ?_⟩
      · exact le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_right _ _))
      · intro δ hδ0 hδ
        have hδε : δ < εg := lt_of_lt_of_le hδ (min_le_left _ _)
        have hδm : δ < g - T₁ :=
          lt_of_lt_of_le hδ (le_trans (min_le_right _ _) (min_le_left _ _))
        have hδM : δ < T₂ - g :=
          lt_of_lt_of_le hδ (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _)))
        refine ⟨List.isChain_singleton _, ?_, ?_, ?_⟩
        · intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          exact hflipg δ hδ0 hδε
        · intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          linarith
        · intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          linarith
    · -- head gap to g'
      subst hr
      have hgg' : g < g' := (List.isChain_cons_cons.mp hchain).1
      refine ⟨min (min δ₁ εg) (min ((g' - g)/2) (min (g - T₁) (min (T₂ - g) 1))), by
        have h1 : (0:ℝ) < g' - g := by linarith
        have h2 : (0:ℝ) < g - T₁ := by linarith
        have h3 : (0:ℝ) < T₂ - g := by linarith
        positivity, ?_, ?_⟩
      · exact le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _)))
      · intro δ hδ0 hδ
        have hδδ₁ : δ < δ₁ :=
          lt_of_lt_of_le hδ (le_trans (min_le_left _ _) (min_le_left _ _))
        have hδε : δ < εg :=
          lt_of_lt_of_le hδ (le_trans (min_le_left _ _) (min_le_right _ _))
        have hδgap : δ < (g' - g)/2 :=
          lt_of_lt_of_le hδ (le_trans (min_le_right _ _) (min_le_left _ _))
        have hδm : δ < g - T₁ :=
          lt_of_lt_of_le hδ (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _)))
        have hδM : δ < T₂ - g :=
          lt_of_lt_of_le hδ (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _)
              (le_trans (min_le_right _ _) (min_le_left _ _))))
        obtain ⟨hsep', hflip', hmargL', hmargR'⟩ := hprop δ hδ0 hδδ₁
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact List.isChain_cons_cons.mpr ⟨by linarith, hsep'⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hflipg δ hδ0 hδε
          · exact hflip' x hx
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · linarith
          · exact hmargL' x hx
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · linarith
          · exact hmargR' x hx

/-- A `FlipStep`-chain list of pinned length inside `[T₁, T₂]` yields the
`Fin`-chain shape the doors consume. -/
private theorem fin_chain_of_list (T₁ T₂ : ℝ) {l : List ℝ} {m : ℕ}
    (hlen : l.length = m + 1) (hchain : l.Chain' FlipStep)
    (hbound : ∀ x ∈ l, T₁ ≤ x ∧ x ≤ T₂) :
    ∃ a : Fin (m+1) → ℝ, StrictMono a ∧ T₁ ≤ a 0 ∧ a (Fin.last m) ≤ T₂ ∧
      ∀ i : Fin m, XiLine (a i.castSucc) * XiLine (a i.succ) < 0 := by
  set a : Fin (m+1) → ℝ := fun i => l.get (Fin.cast hlen.symm i) with ha
  have hltchain : l.Chain' (· < ·) := hchain.imp (fun _ _ h => h.1)
  have hltpair : l.Pairwise (· < ·) := List.isChain_iff_pairwise.mp hltchain
  have hmono : StrictMono a := by
    intro i j hij
    exact List.pairwise_iff_get.mp hltpair _ _ (by simpa using hij)
  have hmem : ∀ i : Fin (m+1), T₁ ≤ a i ∧ a i ≤ T₂ := by
    intro i
    exact hbound _ (List.get_mem _ _)
  have hflip : ∀ i : Fin m,
      XiLine (a i.castSucc) * XiLine (a i.succ) < 0 := by
    intro i
    have h := List.isChain_iff_getElem.mp hchain i.val (by
      rw [hlen]
      omega)
    exact h.2
  exact ⟨a, hmono, (hmem 0).1, (hmem _).2, hflip⟩

/-- **The lower half of the conservation law, at the exact census**: a strictly
monotone chain of consecutive sign changes of the readout, of length EXACTLY
the odd on-line census, inside `[T₁, T₂]`.  Together with
`flips_le_oddOnLine_ncard` this exhibits the flip supply per box as an attained
finite maximum — the census, not a supremum. -/
theorem exists_odd_census_flip_chain (T₁ T₂ : ℝ) (h0 : 0 < T₁) (hT : T₁ < T₂) :
    ∃ a : Fin ((oddOnLineBox T₁ T₂).ncard + 1) → ℝ,
      StrictMono a ∧ T₁ ≤ a 0 ∧ a (Fin.last ((oddOnLineBox T₁ T₂).ncard)) ≤ T₂ ∧
      ∀ i : Fin ((oddOnLineBox T₁ T₂).ncard),
        XiLine (a i.castSucc) * XiLine (a i.succ) < 0 := by
  set S := oddOnLineBox T₁ T₂ with hS
  have hfin : S.Finite :=
    (stripBox_finite T₁ T₂).subset (oddOnLineBox_subset_strip T₁ T₂)
  set ords : Finset ℝ := hfin.toFinset.image Complex.im with hords
  set gs : List ℝ := ords.sort (· ≤ ·) with hgs
  have hmemS : ∀ g ∈ gs, ∃ ρ ∈ S, ρ.im = g := by
    intro g hg
    rw [hgs, Finset.mem_sort] at hg
    rw [hords, Finset.mem_image] at hg
    obtain ⟨ρ, hρ, him⟩ := hg
    exact ⟨ρ, hfin.mem_toFinset.mp hρ, him⟩
  have hfacts : ∀ g ∈ gs, T₁ < g ∧ g < T₂ ∧ g ≠ 0 ∧
      linePt g ∈ ZD.NontrivialZeros ∧ Odd (Zeta23.zeroMult (linePt g)) := by
    intro g hg
    obtain ⟨ρ, hρS, him⟩ := hmemS g hg
    obtain ⟨hNT, hIoo, hre, hoddρ⟩ := hρS
    have hρeq : linePt g = ρ := by
      apply Complex.ext
      · rw [linePt_re, hre]
      · rw [linePt_im, him]
    have h1 : T₁ < g := him ▸ hIoo.1
    have h2 : g < T₂ := him ▸ hIoo.2
    refine ⟨h1, h2, (lt_trans h0 h1).ne', ?_, ?_⟩
    · rw [hρeq]
      exact hNT
    · rw [hρeq]
      exact hoddρ
  have hsorted : gs.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hnodup : gs.Nodup := Finset.sort_nodup _ _
  have hpair : gs.Pairwise (· < ·) :=
    (hsorted.and hnodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hchainlt : gs.Chain' (· < ·) := List.isChain_iff_pairwise.mpr hpair
  have hcount : gs.length = S.ncard := by
    rw [hgs, Finset.length_sort, hords]
    rw [Finset.card_image_of_injOn, ← Set.ncard_eq_toFinset_card _ hfin]
    intro z hz w hw hzw
    have hz' := (hfin.mem_toFinset.mp hz).2.2.1
    have hw' := (hfin.mem_toFinset.mp hw).2.2.1
    apply Complex.ext
    · rw [hz', hw']
    · exact hzw
  rcases eq_or_ne gs [] with hnil | hne
  · -- empty census: the trivial one-point chain attains it
    have hzero : S.ncard = 0 := by
      rw [← hcount, hnil]
      rfl
    refine ⟨fun _ => T₁, ?_, le_refl _, hT.le, ?_⟩
    · intro i j hij
      have : i = j := by omega
      rw [this] at hij
      exact absurd hij (lt_irrefl j)
    · intro i
      exact ((Fin.cast hzero) i).elim0
  · -- pack the windows, then pin the length by the upper bound
    obtain ⟨δs, hδs, hδs1, hδprop⟩ :=
      exists_uniform_delta_odd T₁ T₂ gs hchainlt hfacts
    obtain ⟨hsep, hflips, hmargL, hmargR⟩ := hδprop (δs/2) (by linarith) (by linarith)
    obtain ⟨l, hl, hchain, hlenge, hhull, hlast, _⟩ :=
      exists_flip_chain_of_windows (by linarith : (0:ℝ) < δs/2)
        gs hsep hflips hne
    have hbound : ∀ x ∈ l, T₁ ≤ x ∧ x ≤ T₂ := by
      intro x hx
      have h1 := (hhull x hx).1
      have h2 := (hhull x hx).2
      have h3 := hmargL (gs.head hne) (List.head_mem hne)
      have h4 := hmargR (gs.getLast hne) (List.getLast_mem hne)
      exact ⟨by linarith, by linarith⟩
    set n' : ℕ := l.length - 1 with hn'
    have hlen1 : l.length = n' + 1 := by omega
    obtain ⟨a', hmono', hlo', hhi', hflip'⟩ :=
      fin_chain_of_list T₁ T₂ hlen1 hchain hbound
    have hup : n' ≤ S.ncard :=
      flips_le_oddOnLine_ncard h0 a' hmono' hlo' hhi' hflip'
    have hlow : S.ncard ≤ n' := by
      rw [← hcount]
      omega
    have hlenS : l.length = S.ncard + 1 := by omega
    exact fin_chain_of_list T₁ T₂ hlenS hchain hbound

/-- **T★, the door equivalence**: the high flip-visibility hypothesis is
EQUIVALENT to a pure census inequality — the integer defect
`(stripBox).ncard − (oddOnLineBox).ncard` (nonnegative by
`oddOnLine_ncard_le_strip`) vanishing in every box above the ladder.  The
analytic content of the door is fully discharged by the conservation law;
what remains is one integer equation per box. -/
theorem high_flip_visibility_iff_flip_census :
    (∀ T₁ T₂ : ℝ, 1269/2 ≤ T₁ → T₁ < T₂ → ∃ (n : ℕ) (a : Fin (n+1) → ℝ),
      (stripBox T₁ T₂).ncard ≤ n ∧ StrictMono a ∧ T₁ ≤ a 0 ∧
      a (Fin.last n) ≤ T₂ ∧
      ∀ i : Fin n, XiLine (a i.castSucc) * XiLine (a i.succ) < 0)
    ↔ (∀ T₁ T₂ : ℝ, 1269/2 ≤ T₁ → T₁ < T₂ →
      (stripBox T₁ T₂).ncard ≤ (oddOnLineBox T₁ T₂).ncard) := by
  constructor
  · intro h T₁ T₂ hT₁ hT
    obtain ⟨n, a, hcen, hmono, hlo, hhi, hflip⟩ := h T₁ T₂ hT₁ hT
    have h0 : (0:ℝ) < T₁ := lt_of_lt_of_le (by norm_num) hT₁
    exact le_trans hcen (flips_le_oddOnLine_ncard h0 a hmono hlo hhi hflip)
  · intro h T₁ T₂ hT₁ hT
    have h0 : (0:ℝ) < T₁ := lt_of_lt_of_le (by norm_num) hT₁
    obtain ⟨a, hmono, hlo, hhi, hflip⟩ :=
      exists_odd_census_flip_chain T₁ T₂ h0 hT
    exact ⟨(oddOnLineBox T₁ T₂).ncard, a, h T₁ T₂ hT₁ hT, hmono, hlo, hhi, hflip⟩

/-- **RH from the vanishing defect**: if in every box above the compiled
ladder the strip census is dominated by the odd on-line census, every
nontrivial zero is on the critical line. -/
theorem rh_of_high_flip_census
    (h : ∀ T₁ T₂ : ℝ, 1269/2 ≤ T₁ → T₁ < T₂ →
      (stripBox T₁ T₂).ncard ≤ (oddOnLineBox T₁ T₂).ncard) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2 :=
  rh_of_high_flip_visibility (high_flip_visibility_iff_flip_census.mpr h)

/-- **RH from flip–census conservation in equality form**: the registration
identity per high box — strip census = odd on-line census — forces RH. -/
theorem rh_of_flip_census_conservation
    (h : ∀ T₁ T₂ : ℝ, 1269/2 ≤ T₁ → T₁ < T₂ →
      (stripBox T₁ T₂).ncard = (oddOnLineBox T₁ T₂).ncard) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2 :=
  rh_of_high_flip_census (fun T₁ T₂ h1 h2 => (h T₁ T₂ h1 h2).le)

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.even_mult_no_flip
#print axioms CriticalLinePhasor.SeatingLedger.flip_yields_odd_zero
#print axioms CriticalLinePhasor.SeatingLedger.flips_le_oddOnLine_ncard
#print axioms CriticalLinePhasor.SeatingLedger.exists_uniform_delta_odd
#print axioms CriticalLinePhasor.SeatingLedger.exists_odd_census_flip_chain
#print axioms CriticalLinePhasor.SeatingLedger.high_flip_visibility_iff_flip_census
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_high_flip_census
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_flip_census_conservation
