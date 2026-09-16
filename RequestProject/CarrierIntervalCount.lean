import RequestProject.CarrierOffLinePairing

/-!
# From the local sign law to a count over an interval

This is the second and last leaf that ledger 814 named between the compiled parity bit and the
count congruence.  The local law (`weldReadout_sign_flip`) says what happens across ONE event.  The
count needs what happens across an interval containing several, and that is an induction whose two
ingredients are compiled here.

* `zeros_finite` — the events in a compact ordinate interval are finitely many.  From the finiteness
  of the order at every ordinate (`xiEntire_analyticOrderAt_ne_top`, ledger 814), which makes the
  zero set discrete, together with compactness.
* `sign_const_of_no_zeros` — with no event in between, the readout keeps its sign.  Intermediate
  value theorem on the real readout, which is available only because the readout is real, which is
  ledger 813.

These are the base case and the finiteness the induction consumes.  The induction itself is stated
at the end of this file as `interval_sign_parity` and is NOT proved here.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.CarrierParity

/-- The readout is continuous along the ordinate axis. -/
theorem xiEntire_continuous_ofReal :
    Continuous (fun t : ℝ => (xiEntire (t : ℂ)).re) :=
  Complex.continuous_re.comp (xiEntire_differentiable.continuous.comp Complex.continuous_ofReal)

/-- At a real ordinate the readout's real part vanishes exactly when the readout does. -/
theorem xiEntire_re_eq_zero_iff (t : ℝ) : (xiEntire (t : ℂ)).re = 0 ↔ xiEntire (t : ℂ) = 0 := by
  constructor
  · intro h; exact Complex.ext h (xiEntire_im_ofReal t)
  · intro h; rw [h]; simp

/-- Events are isolated along the ordinate axis. -/
theorem xiEntire_eventually_ne (t : ℝ) :
    ∀ᶠ u : ℝ in nhdsWithin t {t}ᶜ, xiEntire (u : ℂ) ≠ 0 := by
  have hdisj := (xiEntire_analyticAt (t : ℂ)).eventually_eq_zero_or_eventually_ne_zero
  have hnot : ¬ (∀ᶠ z in nhds ((t : ℝ) : ℂ), xiEntire z = 0) := by
    intro h
    exact xiEntire_analyticOrderAt_ne_top (t : ℂ) (analyticOrderAt_eq_top.mpr h)
  have hne : ∀ᶠ z in nhdsWithin ((t : ℝ) : ℂ) {((t : ℝ) : ℂ)}ᶜ, xiEntire z ≠ 0 :=
    hdisj.resolve_left hnot
  have hmap : Filter.Tendsto (fun u : ℝ => (u : ℂ)) (nhdsWithin t {t}ᶜ)
      (nhdsWithin ((t : ℝ) : ℂ) {((t : ℝ) : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_inj] using hu
  exact hmap.eventually hne

/-- **The events in a compact ordinate interval are finitely many.** -/
theorem zeros_finite (a b : ℝ) :
    {t : ℝ | t ∈ Set.Icc a b ∧ xiEntire (t : ℂ) = 0}.Finite := by
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc a b ∧ xiEntire (t : ℂ) = 0} with hS
  have hclosed : IsClosed S := by
    have : S = Set.Icc a b ∩ (fun t : ℝ => (xiEntire (t : ℂ)).re) ⁻¹' {0} := by
      ext t
      simp only [hS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, and_congr_right_iff]
      intro _
      exact (xiEntire_re_eq_zero_iff t).symm
    rw [this]
    exact isClosed_Icc.inter (isClosed_singleton.preimage xiEntire_continuous_ofReal)
  have hcpt : IsCompact S := by
    refine (isCompact_Icc (a := a) (b := b)).of_isClosed_subset hclosed ?_
    intro t ht; exact ht.1
  refine hcpt.finite (isDiscrete_iff_nhdsNE.mpr ?_)
  intro t _
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [xiEntire_eventually_ne t] with u hu
  simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_and]
  exact fun _ => hu

/-- **With no event in between, the readout keeps its sign.**  The base case of the induction:
intermediate value theorem on the real readout. -/
theorem sign_const_of_no_zeros {a b : ℝ} (hab : a ≤ b)
    (hnz : ∀ t ∈ Set.Icc a b, xiEntire (t : ℂ) ≠ 0) :
    0 < (xiEntire (a : ℂ)).re * (xiEntire (b : ℂ)).re := by
  set u : ℝ → ℝ := fun t => (xiEntire (t : ℂ)).re with hu
  have hcont : ContinuousOn u (Set.Icc a b) := xiEntire_continuous_ofReal.continuousOn
  have hne : ∀ t ∈ Set.Icc a b, u t ≠ 0 := fun t ht h =>
    hnz t ht ((xiEntire_re_eq_zero_iff t).mp h)
  rcases lt_trichotomy (u a * u b) 0 with hlt | heq | hgt
  · exfalso
    rcases mul_neg_iff.mp hlt with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
    · obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' hab hcont
        (Set.mem_Icc.mpr ⟨hnb.le, hpa.le⟩)
      exact hne t ht hzero
    · obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc hab hcont
        (Set.mem_Icc.mpr ⟨hna.le, hpb.le⟩)
      exact hne t ht hzero
  · exfalso
    rcases mul_eq_zero.mp heq with h | h
    · exact hne a (Set.left_mem_Icc.mpr hab) h
    · exact hne b (Set.right_mem_Icc.mpr hab) h
  · exact hgt

/-- The events in an OPEN ordinate interval. -/
theorem zeros_finite_Ioo (a b : ℝ) :
    {t : ℝ | t ∈ Set.Ioo a b ∧ xiEntire (t : ℂ) = 0}.Finite :=
  (zeros_finite a b).subset (fun _ ht => ⟨Set.Ioo_subset_Icc_self ht.1, ht.2⟩)

/-- **The count**: the total multiplicity of the events strictly between two ordinates. -/
noncomputable def zeroCount (a b : ℝ) : ℕ :=
  ∑ t ∈ (zeros_finite_Ioo a b).toFinset, analyticOrderNatAt xiEntire (t : ℂ)

/-- The count is additive across an ordinate carrying no event. -/
theorem zeroCount_split {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (hc : xiEntire (c : ℂ) ≠ 0) :
    zeroCount a b = zeroCount a c + zeroCount c b := by
  have hfin : (zeros_finite_Ioo a b).toFinset
      = (zeros_finite_Ioo a c).toFinset ∪ (zeros_finite_Ioo c b).toFinset := by
    ext t
    simp only [Set.Finite.mem_toFinset, Finset.mem_union, Set.mem_setOf_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases lt_trichotomy t c with h | h | h
      · exact Or.inl ⟨⟨h1, h⟩, h3⟩
      · exact absurd (h ▸ h3) hc
      · exact Or.inr ⟨⟨h, h2⟩, h3⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨h1, lt_of_lt_of_le h2 hcb⟩, h3⟩
      · exact ⟨⟨lt_of_le_of_lt hac h1, h2⟩, h3⟩
  have hdisj : Disjoint (zeros_finite_Ioo a c).toFinset (zeros_finite_Ioo c b).toFinset := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_Ioo] at ht ht'
    linarith [ht.1.2, ht'.1.1]
  rw [zeroCount, zeroCount, zeroCount, hfin, Finset.sum_union hdisj]

/-- On an interval whose only event is `t₀`, the count is that event's multiplicity. -/
theorem zeroCount_single {c d t₀ : ℝ} (h1 : c < t₀) (h2 : t₀ < d) (hz : xiEntire (t₀ : ℂ) = 0)
    (honly : ∀ t, t ∈ Set.Ioo c d → xiEntire (t : ℂ) = 0 → t = t₀) :
    zeroCount c d = analyticOrderNatAt xiEntire (t₀ : ℂ) := by
  have hfin : (zeros_finite_Ioo c d).toFinset = {t₀} := by
    ext t
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_singleton]
    constructor
    · rintro ⟨hm, h0⟩; exact honly t hm h0
    · rintro rfl; exact ⟨⟨h1, h2⟩, hz⟩
  rw [zeroCount, hfin, Finset.sum_singleton]

/-- An isolating radius around an event: no other event within it, and it stays inside `(a,b)`. -/
theorem exists_isolating_radius {a b t₀ : ℝ} (hat : a < t₀) (htb : t₀ < b) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h < ε ∧ a < t₀ - h ∧ t₀ + h < b ∧
      ∀ t, t ∈ Set.Icc (t₀ - h) (t₀ + h) → xiEntire (t : ℂ) = 0 → t = t₀ := by
  have hev : ∀ᶠ u : ℝ in nhds t₀, u ≠ t₀ → xiEntire (u : ℂ) ≠ 0 := by
    filter_upwards [eventually_nhdsWithin_iff.mp (xiEntire_eventually_ne t₀)] with u hu hne
    exact hu (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hne)
  obtain ⟨δ, hδ, Hδ⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (δ / 2) (min (ε / 2) (min ((t₀ - a) / 2) ((b - t₀) / 2))), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [lt_min_iff]; refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · calc min (δ / 2) (min (ε / 2) (min ((t₀ - a) / 2) ((b - t₀) / 2)))
        ≤ ε / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
      _ < ε := by linarith
  · have : min (δ / 2) (min (ε / 2) (min ((t₀ - a) / 2) ((b - t₀) / 2))) ≤ (t₀ - a) / 2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    linarith
  · have : min (δ / 2) (min (ε / 2) (min ((t₀ - a) / 2) ((b - t₀) / 2))) ≤ (b - t₀) / 2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    linarith
  · intro t ht h0
    by_contra hne
    have hle : min (δ / 2) (min (ε / 2) (min ((t₀ - a) / 2) ((b - t₀) / 2))) ≤ δ / 2 :=
      min_le_left _ _
    obtain ⟨hl, hr⟩ := ht
    have hdist : dist t t₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact Hδ hdist hne h0

/-- **THE INTERVAL COUNT LAW.**  Between two ordinates carrying no event, the readout's two signs
differ by `(-1)` to the total multiplicity of the events strictly between them.  Multiplicity
throughout: no simplicity hypothesis anywhere. -/
theorem interval_sign_parity : ∀ n : ℕ, ∀ a b : ℝ, a ≤ b →
    (zeros_finite_Ioo a b).toFinset.card = n →
    xiEntire (a : ℂ) ≠ 0 → xiEntire (b : ℂ) ≠ 0 →
    0 < (-1 : ℝ) ^ (zeroCount a b) * ((xiEntire (a : ℂ)).re * (xiEntire (b : ℂ)).re) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro a b hab hcard ha hb
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- no event strictly between: the readout keeps its sign
      subst hn
      have hempty : (zeros_finite_Ioo a b).toFinset = ∅ := Finset.card_eq_zero.mp hcard
      have hnone : ∀ t ∈ Set.Icc a b, xiEntire (t : ℂ) ≠ 0 := by
        intro t ht h0
        rcases eq_or_lt_of_le ht.1 with rfl | h1
        · exact ha h0
        rcases eq_or_lt_of_le ht.2 with rfl | h2
        · exact hb h0
        have : t ∈ (zeros_finite_Ioo a b).toFinset := by
          simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_Ioo]
          exact ⟨⟨h1, h2⟩, h0⟩
        rw [hempty] at this
        exact absurd this (Finset.notMem_empty t)
      have hzc : zeroCount a b = 0 := by rw [zeroCount, hempty, Finset.sum_empty]
      rw [hzc, pow_zero, one_mul]
      exact sign_const_of_no_zeros hab hnone
    · -- pick an event, isolate it, split, and combine three positives
      have hne : (zeros_finite_Ioo a b).toFinset.Nonempty :=
        Finset.card_pos.mp (by omega)
      obtain ⟨t₀, ht₀⟩ := hne
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_Ioo] at ht₀
      obtain ⟨⟨hat, htb⟩, hz⟩ := ht₀
      obtain ⟨ε, hε, Hloc⟩ := sign_flip_of_order (xiEntire_analyticAt (t₀ : ℂ))
        (xiEntire_analyticOrderAt_ne_top _) xiEntire_im_ofReal
      obtain ⟨h, hh, hhε, hac, hdb, honly⟩ := exists_isolating_radius hat htb ε hε
      set c := t₀ - h with hc
      set d := t₀ + h with hd
      have hcd : c < d := by rw [hc, hd]; linarith
      have hct : c < t₀ := by rw [hc]; linarith
      have htd : t₀ < d := by rw [hd]; linarith
      have hCne : xiEntire (c : ℂ) ≠ 0 := fun h0 => by
        have := honly c (Set.mem_Icc.mpr ⟨le_refl _, by rw [hc, hd]; linarith⟩) h0
        rw [hc] at this; linarith
      have hDne : xiEntire (d : ℂ) ≠ 0 := fun h0 => by
        have := honly d (Set.mem_Icc.mpr ⟨by rw [hc, hd]; linarith, le_refl _⟩) h0
        rw [hd] at this; linarith
      -- the three counts
      have hsplit1 : zeroCount a b = zeroCount a d + zeroCount d b :=
        zeroCount_split (by linarith) (by linarith) hDne
      have hsplit2 : zeroCount a d = zeroCount a c + zeroCount c d :=
        zeroCount_split (by linarith) (by linarith) hCne
      have hmid : zeroCount c d = analyticOrderNatAt xiEntire (t₀ : ℂ) :=
        zeroCount_single hct htd hz
          (fun t ht h0 => honly t (Set.mem_Icc.mpr ⟨le_of_lt ht.1, le_of_lt ht.2⟩) h0)
      -- strictly fewer events on each side
      have hsub1 : (zeros_finite_Ioo a c).toFinset ⊂ (zeros_finite_Ioo a b).toFinset := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨t₀, ?_, ?_⟩
          · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_Ioo]
            exact ⟨⟨hat, htb⟩, hz⟩
          · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_Ioo, not_and]
            intro hm _; linarith [hm.2]
        · intro t ht
          simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_Ioo] at ht ⊢
          exact ⟨⟨ht.1.1, by linarith [ht.1.2]⟩, ht.2⟩
      have hsub2 : (zeros_finite_Ioo d b).toFinset ⊂ (zeros_finite_Ioo a b).toFinset := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨t₀, ?_, ?_⟩
          · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_Ioo]
            exact ⟨⟨hat, htb⟩, hz⟩
          · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_Ioo, not_and]
            intro hm _; linarith [hm.1]
        · intro t ht
          simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_Ioo] at ht ⊢
          exact ⟨⟨by linarith [ht.1.1], ht.1.2⟩, ht.2⟩
      have hc1 := Finset.card_lt_card hsub1
      have hc2 := Finset.card_lt_card hsub2
      rw [hcard] at hc1 hc2
      have H1 := IH _ hc1 a c (by linarith) rfl ha hCne
      have H2 := IH _ hc2 d b (by linarith) rfl hDne hb
      have H3 := Hloc h hh hhε
      rw [xiEntire_re_ofReal, xiEntire_re_ofReal] at H3
      rw [← xiEntire_re_ofReal, ← xiEntire_re_ofReal] at H3
      -- combine
      set A := (xiEntire (a : ℂ)).re
      set B := (xiEntire (b : ℂ)).re
      set C := (xiEntire (c : ℂ)).re
      set D := (xiEntire (d : ℂ)).re
      have hCz : C ≠ 0 := fun h0 => hCne ((xiEntire_re_eq_zero_iff c).mp h0)
      have hDz : D ≠ 0 := fun h0 => hDne ((xiEntire_re_eq_zero_iff d).mp h0)
      have hCC : (0 : ℝ) < C * C :=
        lt_of_le_of_ne (mul_self_nonneg _) (Ne.symm (mul_ne_zero hCz hCz))
      have hDD : (0 : ℝ) < D * D :=
        lt_of_le_of_ne (mul_self_nonneg _) (Ne.symm (mul_ne_zero hDz hDz))
      have hpos : (0 : ℝ) < C * C * (D * D) := mul_pos hCC hDD
      have hprod : 0 < ((-1 : ℝ) ^ (zeroCount a c) * (A * C))
          * ((((-1 : ℝ) ^ (analyticOrderNatAt xiEntire (t₀ : ℂ)) * (C * D)))
            * ((-1 : ℝ) ^ (zeroCount d b) * (D * B))) := mul_pos H1 (mul_pos H3 H2)
      have heq : ((-1 : ℝ) ^ (zeroCount a c) * (A * C))
          * ((((-1 : ℝ) ^ (analyticOrderNatAt xiEntire (t₀ : ℂ)) * (C * D)))
            * ((-1 : ℝ) ^ (zeroCount d b) * (D * B)))
          = (C * C * (D * D)) * ((-1 : ℝ) ^ (zeroCount a b) * (A * B)) := by
        rw [hsplit1, hsplit2, hmid, pow_add, pow_add]
        ring
      rw [heq] at hprod
      exact (mul_pos_iff_of_pos_left hpos).mp hprod

/-- The `n` in `interval_sign_parity` is an artifact of the induction; this is the statement. -/
theorem interval_sign_parity' {a b : ℝ} (hab : a ≤ b)
    (ha : xiEntire (a : ℂ) ≠ 0) (hb : xiEntire (b : ℂ) ≠ 0) :
    0 < (-1 : ℝ) ^ (zeroCount a b) * ((xiEntire (a : ℂ)).re * (xiEntire (b : ℂ)).re) :=
  interval_sign_parity _ a b hab rfl ha hb

/-- The events counted here are exactly the on-line zeros of `ζ`. -/
theorem xiEntire_ofReal_eq_zero_iff (t : ℝ) :
    xiEntire (t : ℂ) = 0 ↔ riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  rw [xiEntire_ofReal t, mul_eq_zero, completed_eq_gauge_mul_zeta t, mul_eq_zero,
    or_iff_right (StOscillation.gauge_ne_zero_on_line t),
    or_iff_right (by exact_mod_cast ne_of_gt (quarter_add_sq_pos t))]

/-- **THE COUNT'S PARITY IS THE READOUT'S SIGN CHANGE.**  The bit the carrier supplies, read at two
ordinates carrying no event, is exactly the parity of the total multiplicity of the events between
them.  No simplicity hypothesis, and no prime data. -/
theorem zeroCount_even_iff {a b : ℝ} (hab : a ≤ b)
    (ha : xiEntire (a : ℂ) ≠ 0) (hb : xiEntire (b : ℂ) ≠ 0) :
    Even (zeroCount a b) ↔ 0 < (xiEntire (a : ℂ)).re * (xiEntire (b : ℂ)).re := by
  have key := interval_sign_parity' hab ha hb
  constructor
  · intro hev
    rwa [hev.neg_one_pow, one_mul] at key
  · intro hp
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at key
    nlinarith [key, hp]

/-- The same law for the carrier readout, at every carrier scale. -/
theorem weldReadout_interval_parity {Δ : ℝ} (hΔ : 0 < Δ) {a b : ℝ} (hab : a ≤ b)
    (ha : xiEntire (a : ℂ) ≠ 0) (hb : xiEntire (b : ℂ) ≠ 0) :
    0 < (-1 : ℝ) ^ (zeroCount a b) * (weldReadout Δ a * weldReadout Δ b) := by
  have key := interval_sign_parity' hab ha hb
  rw [xiEntire_re_ofReal, xiEntire_re_ofReal] at key
  have p1 : 0 < ‖weldFactor Δ a‖ := norm_pos_iff.mpr (weldFactor_ne_zero hΔ _)
  have p2 : 0 < ‖weldFactor Δ b‖ := norm_pos_iff.mpr (weldFactor_ne_zero hΔ _)
  have q1 := quarter_add_sq_pos a
  have q2 := quarter_add_sq_pos b
  have hexpand : weldReadout Δ a * weldReadout Δ b
      = (‖weldFactor Δ a‖ * ‖weldFactor Δ b‖ / ((1 / 4 + a ^ 2) * (1 / 4 + b ^ 2)))
        * (((1 / 4 + a ^ 2) * (completedRiemannZeta (1 / 2 + (a : ℂ) * I)).re)
          * ((1 / 4 + b ^ 2) * (completedRiemannZeta (1 / 2 + (b : ℂ) * I)).re)) := by
    rw [weldReadout, weldReadout]
    field_simp
  rw [hexpand, ← mul_assoc, mul_comm ((-1 : ℝ) ^ _), mul_assoc]
  exact mul_pos (div_pos (mul_pos p1 p2) (mul_pos q1 q2)) key

end CriticalLinePhasor.CarrierParity
