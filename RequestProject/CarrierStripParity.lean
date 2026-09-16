import RequestProject.CarrierIntervalCount

/-!
# The full strip count's parity is the weld sign bit

`CarrierIntervalCount` closed the ON-LINE half: the parity of the total multiplicity of the events
on the critical line between two non-event ordinates is the readout's sign change.  The remaining
step is bookkeeping rather than zeta theory, and this file does it.

## Why the ordinate variable makes it a rectangle

In the `s` picture the region is a height band inside the critical strip and `Λ` has two poles.  In
the ordinate variable `s = ½+iz` the same region is the **compact rectangle**
`Re z ∈ [a,b]`, `Im z ∈ [-½, ½]` — the first factor is the height band, the second is the closed
critical strip — and `xiEntire` is **entire**, so there is nothing to work around.

* `bounded_strip_zeros_finite` — a nonzero entire function has a discrete zero set, so the compact
  rectangle carries finitely many events, with multiplicity.
* `even_sum_of_involution` — a finite sum of an invariant weight over a set carried to itself by a
  fixed-point-free involution is even.  Elementary, by strong induction on the cardinality.
* `offline_strip_multiplicity_even` — the involution is `z ↦ conj z` (ledger 815: in this variable
  that IS the reflection `s ↦ 1-conj s` fixing the critical line).  Its fixed points are exactly
  the on-line events, so off the line it is fixed-point free, the rectangle is invariant under it,
  and the orders agree — hence the off-line events contribute an even total.
* `full_count_parity_eq_weld_parity` — the composition.  The total multiplicity of ALL events in
  the band, on the line or off it, has the parity of the readout's sign change.

Nothing here assumes RH and nothing assumes simplicity: the on-line half carries multiplicity from
`CarrierIntervalCount`, and the off-line half is even orbitwise whatever the multiplicities are.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.CarrierParity

open scoped Classical

/-! ## Target 1: finiteness in a bounded height band -/

/-- Events are isolated in the ordinate plane. -/
theorem xiEntire_eventually_ne_cx (z : ℂ) :
    ∀ᶠ w in nhdsWithin z {z}ᶜ, xiEntire w ≠ 0 := by
  refine (xiEntire_analyticAt z).eventually_eq_zero_or_eventually_ne_zero.resolve_left ?_
  intro h
  exact xiEntire_analyticOrderAt_ne_top z (analyticOrderAt_eq_top.mpr h)

/-- **Finitely many events in any compact set of ordinates.** -/
theorem xiEntire_zeros_finite_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    {z | z ∈ K ∧ xiEntire z = 0}.Finite := by
  set S : Set ℂ := {z | z ∈ K ∧ xiEntire z = 0} with hS
  have hclosed : IsClosed S := by
    have : S = K ∩ xiEntire ⁻¹' {0} := by ext z; simp [hS, Set.mem_inter_iff]
    rw [this]
    exact hK.isClosed.inter (isClosed_singleton.preimage xiEntire_differentiable.continuous)
  have hcpt : IsCompact S := hK.of_isClosed_subset hclosed (fun z hz => hz.1)
  refine hcpt.finite (isDiscrete_iff_nhdsNE.mpr ?_)
  intro z _
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [xiEntire_eventually_ne_cx z] with w hw
  simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_and]
  exact fun _ => hw

/-- The closed strip band, in the ordinate variable: `Re z` is the height, `Im z ∈ [-½,½ ]` is the
closed critical strip `0 ≤ Re s ≤ 1`. -/
def stripBand (a b : ℝ) : Set ℂ :=
  {z : ℂ | z.re ∈ Set.Icc a b ∧ z.im ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)}

theorem stripBand_isCompact (a b : ℝ) : IsCompact (stripBand a b) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have : stripBand a b
        = Complex.re ⁻¹' Set.Icc a b ∩ Complex.im ⁻¹' Set.Icc (-(1 / 2) : ℝ) (1 / 2) := rfl
    rw [this]
    exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  · refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℂ))
      (r := |a| + |b| + 1)) ?_
    intro z hz
    obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := hz
    have h1 : |z.re| ≤ |a| + |b| := by
      rcases abs_cases z.re with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
        [skip; skip] <;> rcases abs_cases a with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
        rcases abs_cases b with ⟨hb, _⟩ | ⟨hb, _⟩ <;> rw [ha, hb] <;> linarith
    have h2 : |z.im| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ |a| + |b| + 1 := by linarith

/-- **TARGET 1.**  The events in a bounded height band, anywhere in the closed critical strip, are
finitely many — with multiplicity, since each carries a finite order. -/
theorem bounded_strip_zeros_finite (a b : ℝ) :
    {z | z ∈ stripBand a b ∧ xiEntire z = 0}.Finite :=
  xiEntire_zeros_finite_of_isCompact (stripBand_isCompact a b)

/-- The open-height version, matching the on-line count's convention. -/
def stripBandOpen (a b : ℝ) : Set ℂ :=
  {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)}

theorem stripBandOpen_zeros_finite (a b : ℝ) :
    {z | z ∈ stripBandOpen a b ∧ xiEntire z = 0}.Finite :=
  (bounded_strip_zeros_finite a b).subset
    (fun z hz => ⟨⟨Set.Ioo_subset_Icc_self hz.1.1, hz.1.2⟩, hz.2⟩)

/-- **The full count**: total multiplicity of the events in the band, on the line or off it. -/
noncomputable def stripCount (a b : ℝ) : ℕ :=
  ∑ z ∈ (stripBandOpen_zeros_finite a b).toFinset, analyticOrderNatAt xiEntire z

/-! ## Target 2: the off-line events contribute an even total -/

/-- A finite sum of an invariant weight over a set carried to itself by a fixed-point-free
involution is even: the set splits into two-element orbits, each contributing `2·w`. -/
theorem even_sum_of_involution {α : Type*} [DecidableEq α] :
    ∀ (n : ℕ) (s : Finset α) (f : α → α) (w : α → ℕ), s.card = n →
      (∀ x ∈ s, f x ∈ s) → (∀ x ∈ s, f (f x) = x) → (∀ x ∈ s, f x ≠ x) →
      (∀ x ∈ s, w (f x) = w x) → Even (∑ x ∈ s, w x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro s f w hcard hmap hinv hfree hw
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hfx : f x ∈ s := hmap x hx
      have hne : f x ≠ x := hfree x hx
      have hfxe : f x ∈ s.erase x := Finset.mem_erase.mpr ⟨hne, hfx⟩
      set s' := (s.erase x).erase (f x) with hs'
      have hsub : s' ⊆ s := fun y hy =>
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
      have hmem : ∀ y, y ∈ s' ↔ (y ∈ s ∧ y ≠ x ∧ y ≠ f x) := by
        intro y
        simp only [hs', Finset.mem_erase]
        tauto
      -- `s'` is still invariant
      have hmap' : ∀ y ∈ s', f y ∈ s' := by
        intro y hy
        obtain ⟨hy1, hy2, hy3⟩ := (hmem y).mp hy
        refine (hmem _).mpr ⟨hmap y hy1, ?_, ?_⟩
        · intro h; exact hy3 (by rw [← h, hinv y hy1])
        · intro h; exact hy2 (by rw [← hinv y hy1, h, hinv x hx])
      -- the card drops by two
      have hc1 : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
      have hc2 : s'.card = s.card - 2 := by
        rw [hs', Finset.card_erase_of_mem hfxe, hc1]
        omega
      have hge : 2 ≤ s.card := by
        have : ({x, f x} : Finset α) ⊆ s := by
          intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl <;> assumption
        have := Finset.card_le_card this
        rwa [Finset.card_insert_of_notMem (by simpa using (Ne.symm hne)),
          Finset.card_singleton] at this
      have hlt : s.card - 2 < n := by omega
      have hIH := IH (s.card - 2) hlt s' f w hc2
        hmap' (fun y hy => hinv y (hsub hy)) (fun y hy => hfree y (hsub hy))
        (fun y hy => hw y (hsub hy))
      -- peel the orbit
      have e1 : ∑ y ∈ s, w y = w x + ∑ y ∈ s.erase x, w y :=
        (Finset.add_sum_erase s w hx).symm
      have e2 : ∑ y ∈ s.erase x, w y = w (f x) + ∑ y ∈ s', w y :=
        (Finset.add_sum_erase (s.erase x) w hfxe).symm
      rw [e1, e2, hw x hx, ← add_assoc, show w x + w x = 2 * w x from by ring]
      exact (even_two_mul (w x)).add hIH

/-! ## Target 2, concluded: the off-line events contribute an even total -/

/-- The band is invariant under conjugation and conjugation is fixed-point free off the axis. -/
theorem conj_mem_stripBandOpen {a b : ℝ} {z : ℂ} (hz : z ∈ stripBandOpen a b) :
    (starRingEnd ℂ) z ∈ stripBandOpen a b := by
  obtain ⟨hre, hlo, hhi⟩ := hz
  refine ⟨by simpa using hre, ?_, ?_⟩ <;> simp only [Complex.conj_im] <;> linarith

/-- **TARGET 2.**  The off-line events in the band contribute an EVEN total multiplicity: the
involution `z ↦ conj z` carries them to each other, is fixed-point free off the axis, and preserves
the order, so they split into two-element orbits each contributing `2·m`. -/
theorem offline_strip_multiplicity_even (a b : ℝ) :
    Even (∑ z ∈ (stripBandOpen_zeros_finite a b).toFinset.filter (fun z => z.im ≠ 0),
            analyticOrderNatAt xiEntire z) := by
  set F := (stripBandOpen_zeros_finite a b).toFinset.filter (fun z => z.im ≠ 0) with hF
  have hmem : ∀ z, z ∈ F ↔ (z ∈ stripBandOpen a b ∧ xiEntire z = 0 ∧ z.im ≠ 0) := by
    intro z
    simp only [hF, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    tauto
  refine even_sum_of_involution F.card F (starRingEnd ℂ) (analyticOrderNatAt xiEntire) rfl
    ?_ ?_ ?_ ?_
  · intro z hz
    obtain ⟨h1, h2, h3⟩ := (hmem z).mp hz
    refine (hmem _).mpr ⟨conj_mem_stripBandOpen h1, (xiEntire_zero_conj z).mpr h2, ?_⟩
    simpa using h3
  · intro z _; exact Complex.conj_conj z
  · intro z hz; exact (conj_ne_self_iff z).mpr ((hmem z).mp hz).2.2
  · intro z _; exact xiEntire_order_conj z

/-! ## Target 3: the composition -/

/-- The ON-LINE part of the band's event set is the image of the interval's, under `ℝ ↪ ℂ`. -/
theorem online_part_eq_image (a b : ℝ) :
    (stripBandOpen_zeros_finite a b).toFinset.filter (fun z => ¬ z.im ≠ 0)
      = (zeros_finite_Ioo a b).toFinset.image (fun t : ℝ => (t : ℂ)) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    not_not, stripBandOpen]
  constructor
  · rintro ⟨⟨⟨hre, _⟩, h0⟩, him⟩
    have hz : ((z.re : ℝ) : ℂ) = z := Complex.ext rfl (by simpa using him.symm)
    exact ⟨z.re, ⟨hre, by rwa [hz]⟩, hz⟩
  · rintro ⟨t, ⟨ht, h0⟩, rfl⟩
    exact ⟨⟨⟨by simpa using ht, by norm_num⟩, h0⟩, by simp⟩

/-- The on-line part sums to `zeroCount`. -/
theorem online_part_sum (a b : ℝ) :
    ∑ z ∈ (stripBandOpen_zeros_finite a b).toFinset.filter (fun z => ¬ z.im ≠ 0),
      analyticOrderNatAt xiEntire z = zeroCount a b := by
  rw [online_part_eq_image, Finset.sum_image (by
    intro x _ y _ h; simpa using h), zeroCount]

/-- **The band's total splits into the on-line count and an even remainder.** -/
theorem stripCount_split (a b : ℝ) :
    ∃ k : ℕ, stripCount a b = zeroCount a b + 2 * k := by
  obtain ⟨k, hk⟩ := offline_strip_multiplicity_even a b
  refine ⟨k, ?_⟩
  rw [stripCount, ← Finset.sum_filter_add_sum_filter_not
    ((stripBandOpen_zeros_finite a b).toFinset) (fun z => z.im ≠ 0), hk, online_part_sum]
  ring

/-- **TARGET 3 — THE FULL COUNT'S PARITY IS THE WELD SIGN BIT.**  The total multiplicity of ALL
events in the band, on the critical line or off it, has the parity of the readout's sign change.
Nothing here assumes RH and nothing assumes simplicity: the on-line half carries multiplicity from
`CarrierIntervalCount`, and the off-line half is even orbitwise whatever the multiplicities are. -/
theorem full_count_parity_eq_weld_parity {a b : ℝ} (hab : a ≤ b)
    (ha : xiEntire (a : ℂ) ≠ 0) (hb : xiEntire (b : ℂ) ≠ 0) :
    Even (stripCount a b) ↔ 0 < (xiEntire (a : ℂ)).re * (xiEntire (b : ℂ)).re := by
  obtain ⟨k, hk⟩ := stripCount_split a b
  have hswap : Even (stripCount a b) ↔ Even (zeroCount a b) := by
    rw [hk, Nat.even_add]
    exact ⟨fun h => h.mpr ⟨k, by ring⟩, fun h => ⟨fun _ => ⟨k, by ring⟩, fun _ => h⟩⟩
  rw [hswap]
  exact zeroCount_even_iff hab ha hb

/-- `Λ(s) = Γℝ(s)·ζ(s)` at any `s ≠ 0`. -/
theorem completed_eq_gauge_mul_zeta' {s : ℂ} (hs : s ≠ 0) (hpos : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs,
    mul_div_cancel₀ _ (Complex.Gammaℝ_ne_zero_of_re_pos hpos)]

/-! ## The boundary: the band's events are interior, so `stripCount` counts exactly the
nontrivial zeros -/

/-- At `Im z = -1/2` the line point is `s = 1`, where `Λ` has its pole — but the pole-cleared form
gives `xiEntire(-i/2) = 1·0·Λ₀(1) − 1 = −1` outright. -/
theorem xiEntire_at_neg_half_I : xiEntire (-(Complex.I/2)) = -1 := by
  have h1 : (1 : ℂ)/2 + (-(Complex.I/2)) * Complex.I = 1 := by
    rw [show (-(Complex.I/2)) * Complex.I = -(Complex.I*Complex.I)/2 by ring, Complex.I_mul_I]
    ring
  have h2 : (1 : ℂ)/2 - (-(Complex.I/2)) * Complex.I = 0 := by
    rw [show (-(Complex.I/2)) * Complex.I = -(Complex.I*Complex.I)/2 by ring, Complex.I_mul_I]
    ring
  rw [xiEntire, h1, h2]
  ring

/-- **No events on the right edge of the strip** (`Re s = 1`): `ζ(1+it) ≠ 0`, and the one point
where `Λ` has its pole is handled by the entire form. -/
theorem xiEntire_ne_zero_of_im_eq_neg_half {z : ℂ} (h : z.im = -(1/2)) : xiEntire z ≠ 0 := by
  have hre : ((1 : ℂ)/2 + z * Complex.I).re = 1 := by
    simp [Complex.add_re, Complex.mul_re, h]; ring
  by_cases hz : z = -(Complex.I/2)
  · rw [hz, xiEntire_at_neg_half_I]; norm_num
  · have hone : (1 : ℂ)/2 + z * Complex.I ≠ 1 := by
      intro hc
      apply hz
      have him : ((1 : ℂ)/2 + z * Complex.I).im = z.re := by
        simp [Complex.add_im, Complex.mul_im]
      rw [hc] at him
      simp at him
      exact Complex.ext (by simpa using him.symm) (by simpa using h)
    have hzero : (1 : ℂ)/2 + z * Complex.I ≠ 0 := by
      intro hc; rw [hc] at hre; simp at hre
    have hB : ((1 : ℂ)/2 - z * Complex.I) ≠ 0 := by
      intro hc
      have hh : ((1 : ℂ)/2 - z * Complex.I) = 1 - ((1:ℂ)/2 + z*Complex.I) := by ring
      rw [hh, sub_eq_zero] at hc; exact hone hc.symm
    rw [xiEntire_eq_completed hzero hone,
      completed_eq_gauge_mul_zeta' hzero (by rw [hre]; norm_num)]
    exact mul_ne_zero (mul_ne_zero hzero hB)
      (mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hre]; norm_num))
        (riemannZeta_ne_zero_of_one_le_re (by rw [hre])))

/-- **No events on the left edge** (`Re s = 0`), by conjugation from the right edge. -/
theorem xiEntire_ne_zero_of_im_eq_half {z : ℂ} (h : z.im = 1/2) : xiEntire z ≠ 0 := by
  intro h0
  refine xiEntire_ne_zero_of_im_eq_neg_half (z := (starRingEnd ℂ) z) ?_
    ((xiEntire_zero_conj z).mpr h0)
  simp [h]

/-- **THE BOUNDARY LEMMA.**  Every event in the band is INTERIOR: `|Im z| < 1/2`, i.e. the line
point satisfies `0 < Re s < 1`.  So `stripCount` counts exactly the nontrivial zeros of `ζ` in the
open critical strip, with multiplicity — the classical object. -/
theorem stripBand_zeros_interior {a b : ℝ} {z : ℂ} (hz : z ∈ stripBand a b)
    (h0 : xiEntire z = 0) : |z.im| < 1/2 := by
  obtain ⟨_, hlo, hhi⟩ := hz
  rw [abs_lt]
  constructor
  · rcases eq_or_lt_of_le hlo with h | h
    · exact absurd h0 (xiEntire_ne_zero_of_im_eq_neg_half h.symm)
    · exact h
  · rcases eq_or_lt_of_le hhi with h | h
    · exact absurd h0 (xiEntire_ne_zero_of_im_eq_half h)
    · exact h

/-- Read in the `s` chart: the events sit strictly inside the critical strip. -/
theorem stripBand_zeros_in_open_strip {a b : ℝ} {z : ℂ} (hz : z ∈ stripBand a b)
    (h0 : xiEntire z = 0) :
    0 < ((1 : ℂ)/2 + z * Complex.I).re ∧ ((1 : ℂ)/2 + z * Complex.I).re < 1 := by
  have h := stripBand_zeros_interior hz h0
  rw [abs_lt] at h
  have hre : ((1 : ℂ)/2 + z * Complex.I).re = 1/2 - z.im := by
    simp [Complex.add_re, Complex.mul_re]; ring
  rw [hre]; constructor <;> linarith [h.1, h.2]

/-! ## Exactly what the on-line count misses -/

/-- An event has order at least one (complex form). -/
theorem one_le_order_of_zero_cx {z : ℂ} (h0 : xiEntire z = 0) :
    1 ≤ analyticOrderNatAt xiEntire z := by
  rcases Nat.eq_zero_or_pos (analyticOrderNatAt xiEntire z) with h | h
  · exfalso
    obtain ⟨g, _, hg0, hev⟩ :=
      ((xiEntire_analyticAt z).analyticOrderNatAt_eq_iff (xiEntire_analyticOrderAt_ne_top z)).mp h
    have hgz := hev.self_of_nhds
    rw [pow_zero, one_smul] at hgz
    exact hg0 (hgz.symm.trans h0)
  · exact h

/-- The band's total is the on-line count plus the off-line contribution, as an identity. -/
theorem stripCount_eq (a b : ℝ) :
    stripCount a b = zeroCount a b +
      ∑ z ∈ (stripBandOpen_zeros_finite a b).toFinset.filter (fun z => z.im ≠ 0),
        analyticOrderNatAt xiEntire z := by
  rw [stripCount, ← Finset.sum_filter_add_sum_filter_not
    ((stripBandOpen_zeros_finite a b).toFinset) (fun z => z.im ≠ 0), online_part_sum]
  ring

/-- **THE SCOPE STATEMENT, as a theorem.**  The on-line count equals the full strip count for a
band EXACTLY WHEN no event in that band lies off the critical line.  So an index certified by the
on-line chain is the classical index precisely on the bands where this holds — and the compiled
machinery never assumes it. -/
theorem stripCount_eq_zeroCount_iff (a b : ℝ) :
    stripCount a b = zeroCount a b ↔
      ∀ z ∈ stripBandOpen a b, xiEntire z = 0 → z.im = 0 := by
  rw [stripCount_eq]
  constructor
  · intro h z hz h0
    by_contra him
    have hmem : z ∈ (stripBandOpen_zeros_finite a b).toFinset.filter (fun w => w.im ≠ 0) := by
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨⟨hz, h0⟩, him⟩
    have hpos : 0 < ∑ w ∈ (stripBandOpen_zeros_finite a b).toFinset.filter
        (fun w => w.im ≠ 0), analyticOrderNatAt xiEntire w := by
      exact Finset.sum_pos' (fun w _ => Nat.zero_le _) ⟨z, hmem, one_le_order_of_zero_cx h0⟩
    omega
  · intro h
    have : (stripBandOpen_zeros_finite a b).toFinset.filter (fun w => w.im ≠ 0) = ∅ := by
      ext w
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
        Finset.notMem_empty, iff_false, not_and, not_not]
      intro hw
      exact h w hw.1 hw.2
    rw [this, Finset.sum_empty, add_zero]

end CriticalLinePhasor.CarrierParity
