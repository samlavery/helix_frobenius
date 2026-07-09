import RequestProject.CarrierScaleCompensation

/-!
# The log-derivative residue is the jump of S

The closing piece of the carrier-scale story: **residue = jump(S)**.

The mechanism, in the carrier ontology:

  scale-gap accumulation ⟶ `S(t)` ⟶ π-quantized crossing ⟶ `ΔS` ⟶ log-derivative residue.

Three unconditional theorems:

* **§1 Jump transfer.**  In `N(t) = 1 + ϑ(t)/π + S(t)` the base is constant and the clock is
  continuous (`theta_continuous`), so `S − N` is continuous
  (`S_sub_count_continuous`) and the count and `S` have *identical* jumps
  (`count_hasJump_iff_S_hasJump`): every jump of the readout belongs entirely to `S`.

* **§2 Residue = order (source-general).**  For any `f` analytic at `ρ` with finite
  vanishing order `m`, the logarithmic derivative has a simple pole at `ρ` with residue
  exactly `m`: `(s−ρ)·(f′/f)(s) → m` (`logDeriv_residue_eq_order`).  Stated for arbitrary
  analytic `f`, so the sourcewise version `Res_ρ (L_W′/L_W) = ΔS_W` needs no new analysis —
  only each source's counting section.

* **§3–§4 The bridge at ζ.**  `ζ` is analytic at every line point (`zeta_analyticAt_line`),
  is not locally zero anywhere (`zeta_not_eventually_zero`: identity theorem on the
  connected set `ℂ∖{1}` against `ζ(2) = π²/6 ≠ 0`), so events are isolated
  (`event_isolated_line`) and locally finite (`events_finite`).  Hence the count has
  one-sided limits everywhere, jumping by exactly `1` at each event and `0` elsewhere
  (`count_hasJump_event`, `count_hasJump_of_not_event`), and `S` inherits those jumps.

* **§5 The distinct-event headline.**  At a simple event (`analyticOrderAt = 1`),

    `Res_{ρ_γ} (ζ′/ζ) = 1 = ΔS(γ)`  —  `residue_eq_S_jump`,

  with the signed variant for `−ζ′/ζ` (`residue_neg_eq_neg_S_jump`) and the general-order
  dictionary (`residue_and_S_jump_of_order`: residue `= m`, `ΔS = 1` per event).  The jump
  of `S` *detects* events: `S_jump_detects_event`.

* **§6 The multiplicity-weighted ledger — the boxed identity without simplicity.**  Define
  `N_mult(t) = Σ_{0<γ'≤t} ord_{½+iγ'} ζ` (`zeroEventCountMult`, over the finite event set)
  and `S_mult = N_mult − 1 − ϑ/π` (`Smult`).  The clock is continuous, so
  `ΔS_mult(γ) = ΔN_mult(γ) = m_ρ` (`countMult_hasJump_event`, `Smult_hasJump`), and with
  the source-general residue theorem, **for every `γ > 0`, unconditionally**:

    `Res_{ρ_γ} (ζ′/ζ) = m_{ρ_γ} = ΔS_mult(γ)`  —  `residue_eq_Smult_jump`,

  both sides zero off events; the jump reads off the multiplicity
  (`Smult_jump_eq_order`).  The distinct-event ledger `CarrierScale.S` is **unchanged**;
  the two are typed ledgers — `S_event` counts distinct closures, `S_mult` counts spectral
  residue weight (`Smult_sub_S`: they differ by the excess multiplicity, nothing else).
  `S_mult` is the ledger the trace side consumes: spectral counting measures carry
  multiplicity, and `∫ h dS_mult = Σ_ρ h(γ_ρ)·Res_ρ(L′/L) − (clock term)` is the intended
  Stieltjes reading (not formalized here).

## Scope (exact)

Unconditional; axiom footprint `{propext, Classical.choice, Quot.sound}`; no `sorry`.
Two residue notions must not be conflated: for the **log-derivative** (zero/pole
multiplicity) residue the identity `residue = jump` is exact and proven here — against
`S_mult` at every order (§6), against the distinct-event `S` at simple events (§5); for a
**Laurent** residue of the function itself, the ledger controls the discrete order while
the fiber normalization controls the value (the DC example: the pole order of `ζ` at
`s = 1` is `1`, while the residue *value* `1` is `CarrierScale.dcResidue_spec`).
This file does not assume and does not prove RH/GRH.
-/

set_option maxHeartbeats 1000000

open Complex Filter Set Topology

namespace CriticalLinePhasor.ResidueJump

open CriticalLinePhasor CriticalLinePhasor.CarrierScale

/-! ## §0 Jumps -/

/-- `f` has a jump of size `j` at `γ`: both one-sided limits exist and differ by `j`. -/
def HasJump (f : ℝ → ℝ) (γ j : ℝ) : Prop :=
  ∃ l r : ℝ, Tendsto f (𝓝[<] γ) (𝓝 l) ∧ Tendsto f (𝓝[>] γ) (𝓝 r) ∧ r - l = j

/-- Jumps are unique. -/
theorem HasJump.unique {f : ℝ → ℝ} {γ j j' : ℝ}
    (h : HasJump f γ j) (h' : HasJump f γ j') : j = j' := by
  obtain ⟨l, r, hl, hr, hj⟩ := h
  obtain ⟨l', r', hl', hr', hj'⟩ := h'
  have hll : l = l' := tendsto_nhds_unique hl hl'
  have hrr : r = r' := tendsto_nhds_unique hr hr'
  rw [← hj, ← hj', hll, hrr]

/-- Adding a continuous function changes no jump. -/
theorem HasJump.add_continuous {f c : ℝ → ℝ} {γ j : ℝ}
    (hf : HasJump f γ j) (hc : Continuous c) :
    HasJump (fun t => f t + c t) γ j := by
  obtain ⟨l, r, hl, hr, hj⟩ := hf
  refine ⟨l + c γ, r + c γ, ?_, ?_, by linarith⟩
  · exact hl.add ((hc.tendsto γ).mono_left nhdsWithin_le_nhds)
  · exact hr.add ((hc.tendsto γ).mono_left nhdsWithin_le_nhds)

/-- Continuous perturbations preserve the jump structure exactly. -/
theorem hasJump_add_continuous_iff {f c : ℝ → ℝ} (hc : Continuous c) (γ j : ℝ) :
    HasJump (fun t => f t + c t) γ j ↔ HasJump f γ j := by
  constructor
  · intro h
    have h2 := h.add_continuous hc.neg
    have he : (fun t => (f t + c t) + (-c t)) = f := by
      funext t
      ring
    rwa [he] at h2
  · intro h
    exact h.add_continuous hc

/-! ## §1 Jump transfer: every jump of the count belongs to `S` -/

/-- `S` minus the event count is continuous (it is `−1 − ϑ/π`): the base is constant and the
clock is continuous, so the count's discontinuities live entirely in `S`. -/
theorem S_sub_count_continuous :
    Continuous (fun t => CarrierScale.S t - (zeroEventCount t : ℝ)) := by
  have he : (fun t => CarrierScale.S t - (zeroEventCount t : ℝ))
      = fun t => -1 - theta t / Real.pi := by
    funext t
    unfold CarrierScale.S
    ring
  rw [he]
  exact continuous_const.sub (theta_continuous.div_const _)

/-- **Jump transfer**: the count and `S` have exactly the same jumps.  The clock term is
continuous, therefore every jump of the readout comes entirely from `S`. -/
theorem count_hasJump_iff_S_hasJump (γ j : ℝ) :
    HasJump (fun t => (zeroEventCount t : ℝ)) γ j ↔ HasJump CarrierScale.S γ j := by
  have hc : Continuous (fun t => -1 - theta t / Real.pi) :=
    continuous_const.sub (theta_continuous.div_const _)
  have he : CarrierScale.S = fun t => (zeroEventCount t : ℝ) + (-1 - theta t / Real.pi) := by
    funext t
    unfold CarrierScale.S
    ring
  rw [he]
  exact (hasJump_add_continuous_iff hc γ j).symm

/-! ## §2 Residue = order, source-general

For `f` analytic at `ρ` with finite vanishing order `m`, the logarithmic derivative has a
simple pole at `ρ` with residue exactly `m`.  The residue is taken in the same limit form as
the DC residue of the trivial channel (`dcResidue_spec`): `(s−ρ)·(f′/f)(s) → m`. -/

/-- **The log-derivative residue equals the vanishing order** — for any analytic fiber
readout: if `analyticOrderAt f ρ = m < ⊤` then `(s−ρ)·(f′/f)(s) → m` as `s → ρ`. -/
theorem logDeriv_residue_eq_order {f : ℂ → ℂ} {ρ : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f ρ) (hm : analyticOrderAt f ρ = m) :
    Tendsto (fun s => (s - ρ) * logDeriv f s) (𝓝[≠] ρ) (𝓝 (m : ℂ)) := by
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp hm
  have hgan : ∀ᶠ z in 𝓝 ρ, AnalyticAt ℂ g z := hg.eventually_analyticAt
  have hgne : ∀ᶠ z in 𝓝 ρ, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hfg' : ∀ᶠ z in 𝓝 ρ, f z = (z - ρ) ^ m * g z := by
    filter_upwards [hfg] with z hz
    simpa [smul_eq_mul] using hz
  have hderiv : deriv f =ᶠ[𝓝 ρ] deriv fun z => (z - ρ) ^ m * g z :=
    Filter.EventuallyEq.deriv hfg'
  have hd : ∀ᶠ z in 𝓝 ρ, deriv (fun w => (w - ρ) ^ m * g w) z
      = (m : ℂ) * (z - ρ) ^ (m - 1) * g z + (z - ρ) ^ m * deriv g z := by
    filter_upwards [hgan] with z hz
    have h0 : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
    have h1 := h0.pow m
    rw [mul_one] at h1
    exact (h1.mul hz.differentiableAt.hasDerivAt).deriv
  have hgc : ContinuousAt (fun s => deriv g s / g s) ρ :=
    (hg.deriv.continuousAt).div hg.continuousAt hg0
  have hsub : Tendsto (fun s : ℂ => s - ρ) (𝓝 ρ) (𝓝 0) := by
    have h : Tendsto (fun s : ℂ => id s - ρ) (𝓝 ρ) (𝓝 (ρ - ρ)) :=
      (tendsto_id (x := 𝓝 ρ)).sub_const ρ
    simpa using h
  have hprod : Tendsto (fun s => (s - ρ) * (deriv g s / g s)) (𝓝 ρ) (𝓝 0) := by
    have := hsub.mul hgc.tendsto
    simpa using this
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · -- order zero: no pole, residue zero
    have key : (fun s => (s - ρ) * logDeriv f s)
        =ᶠ[𝓝[≠] ρ] fun s => (s - ρ) * (deriv g s / g s) := by
      filter_upwards [hfg'.filter_mono nhdsWithin_le_nhds,
        hderiv.filter_mono nhdsWithin_le_nhds,
        hd.filter_mono nhdsWithin_le_nhds] with s h1 h2 h3
      rw [logDeriv_apply, h2, h3, h1]
      simp
    have hlim : Tendsto (fun s => (s - ρ) * (deriv g s / g s)) (𝓝[≠] ρ) (𝓝 0) :=
      hprod.mono_left nhdsWithin_le_nhds
    have hfin := hlim.congr' key.symm
    simpa using hfin
  · -- positive order: the pole carries the multiplicity
    have key : (fun s => (s - ρ) * logDeriv f s)
        =ᶠ[𝓝[≠] ρ] fun s => (m : ℂ) + (s - ρ) * (deriv g s / g s) := by
      filter_upwards [hfg'.filter_mono nhdsWithin_le_nhds,
        hderiv.filter_mono nhdsWithin_le_nhds,
        hd.filter_mono nhdsWithin_le_nhds,
        hgne.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with s h1 h2 h3 h4 h5
      have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr h5
      have hpow : (s - ρ) ^ m = (s - ρ) * (s - ρ) ^ (m - 1) := by
        conv_lhs => rw [show m = (m - 1) + 1 by omega]
        rw [pow_succ]
        ring
      have hpne : (s - ρ) ^ (m - 1) ≠ 0 := pow_ne_zero _ hsρ
      rw [logDeriv_apply, h2, h3, h1, hpow]
      field_simp
    have hlim : Tendsto (fun s => (m : ℂ) + (s - ρ) * (deriv g s / g s)) (𝓝 ρ)
        (𝓝 ((m : ℂ) + 0)) := tendsto_const_nhds.add hprod
    rw [add_zero] at hlim
    exact (hlim.mono_left nhdsWithin_le_nhds).congr' key.symm

/-! ## §3 ζ at the line: analyticity, no local vanishing, isolation of events -/

lemma line_ne_one (γ : ℝ) : line γ ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [line_re] at this
  norm_num at this

/-- ζ is analytic at every critical-line point (the pole sits off the line). -/
theorem zeta_analyticAt_line (γ : ℝ) : AnalyticAt ℂ riemannZeta (line γ) := by
  have hU : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hd : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds (line_ne_one γ))

/-- ζ is not locally zero anywhere off its pole: identity theorem on the connected set
`ℂ∖{1}` against `ζ(2) = π²/6 ≠ 0`. -/
theorem zeta_not_eventually_zero {z : ℂ} (hz : z ≠ 1) :
    ¬ (∀ᶠ s in 𝓝 z, riemannZeta s = 0) := by
  intro h
  have hU : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have han : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := by
    have hd : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs =>
      (differentiableAt_riemannZeta hs).differentiableWithinAt
    exact hd.analyticOnNhd hU
  have hconn : IsPreconnected {s : ℂ | s ≠ 1} := by
    have hrank : 1 < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      exact_mod_cast Nat.one_lt_two
    have := (isConnected_compl_singleton_of_one_lt_rank hrank (1 : ℂ)).isPreconnected
    convert this using 1
    ext s
    simp [Set.mem_compl_iff]
  have hzero : EqOn riemannZeta 0 {s : ℂ | s ≠ 1} := by
    refine han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz ?_
    filter_upwards [h] with s hs
    simpa using hs
  have h2 : riemannZeta 2 = 0 := hzero (by norm_num : (2 : ℂ) ∈ {s : ℂ | s ≠ 1})
  rw [riemannZeta_two] at h2
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rcases div_eq_zero_iff.mp h2 with h3 | h3
  · exact hπ ((pow_eq_zero_iff two_ne_zero).mp h3)
  · norm_num at h3

/-- **Events are isolated in ℂ**: near a line point, ζ has no other zeros. -/
theorem event_isolated (γ : ℝ) : ∀ᶠ s in 𝓝[≠] (line γ), riemannZeta s ≠ 0 :=
  (zeta_analyticAt_line γ).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (zeta_not_eventually_zero (line_ne_one γ))

lemma line_injective : Function.Injective line := by
  intro a b h
  have := congrArg Complex.im h
  simpa [line, lineC] using this

/-- **Events are isolated on the line**: near any ordinate, no other ordinate is an event. -/
theorem event_isolated_line (γ : ℝ) :
    ∀ᶠ γ' in 𝓝[≠] γ, riemannZeta (line γ') ≠ 0 := by
  have hmap : Tendsto line (𝓝[≠] γ) (𝓝[≠] (line γ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuous_line.tendsto γ).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with γ' hγ'
    exact fun hEq => hγ' (line_injective hEq)
  exact hmap.eventually (event_isolated γ)

/-! ## §4 Local finiteness and the count's jumps -/

/-- The event set below any height is finite: an infinite set would have an accumulation
point in the compact interval, contradicting isolation. -/
theorem events_finite (t : ℝ) :
    {γ' : ℝ | γ' ∈ Set.Ioc 0 t ∧ riemannZeta (line γ') = 0}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨γ₀, -, hacc⟩ := hinf.exists_accPt_of_subset_isCompact
    (isCompact_Icc (a := (0 : ℝ)) (b := t)) (fun x hx => ⟨hx.1.1.le, hx.1.2⟩)
  have hfreq : ∃ᶠ γ' in 𝓝[≠] γ₀, riemannZeta (line γ') = 0 := by
    have h := accPt_iff_frequently_nhdsNE.mp hacc
    exact h.mono fun γ' hγ' => hγ'.2
  obtain ⟨γ', h1, h2⟩ := (hfreq.and_eventually (event_isolated_line γ₀)).exists
  exact h2 h1

/-- The interval of isolation: around any ordinate there is a punctured interval free of
events. -/
lemma exists_event_free_interval (γ : ℝ) :
    ∃ ε > 0, ∀ γ' : ℝ, |γ' - γ| < ε → γ' ≠ γ → riemannZeta (line γ') ≠ 0 := by
  have h := event_isolated_line γ
  rw [eventually_nhdsWithin_iff] at h
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  exact ⟨ε, hε, fun γ' hd hne => hball (by simpa [Real.dist_eq] using hd) hne⟩

/-- `Ioo a b` is a right-neighborhood of `a`. -/
lemma Ioo_mem_nhdsGT' {a b : ℝ} (h : a < b) : Set.Ioo a b ∈ 𝓝[>] a := by
  rw [← Set.Ioi_inter_Iio]
  exact Filter.inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h))

/-- The count is constant on any interval free of events: for `a ≤ b` with no events in
`(a, b]`, the counts at `a` and `b` agree. -/
lemma count_const_of_event_free {a b : ℝ} (hab : a ≤ b)
    (h : ∀ γ' ∈ Set.Ioc a b, riemannZeta (line γ') ≠ 0) :
    zeroEventCount b = zeroEventCount a := by
  unfold zeroEventCount
  congr 1
  ext γ'
  simp only [Set.mem_setOf_eq, Set.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    by_contra hgt
    rw [not_le] at hgt
    exact h γ' ⟨hgt, h2⟩ h3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2.trans hab⟩, h3⟩

/-- **The count jumps by one at each event**: at an event ordinate `γ > 0`, the count has
left limit `#events < γ` and right limit one larger. -/
theorem count_hasJump_event {γ : ℝ} (hγ : 0 < γ) (hev : riemannZeta (line γ) = 0) :
    HasJump (fun t => (zeroEventCount t : ℝ)) γ 1 := by
  obtain ⟨ε₀, hε₀, hfree⟩ := exists_event_free_interval γ
  set ε : ℝ := min ε₀ γ with hεdef
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hεγ : ε ≤ γ := min_le_right _ _
  have hε : 0 < ε := lt_min hε₀ hγ
  -- left side: constant on (γ − ε, γ)
  have hleft : ∀ t ∈ Set.Ioo (γ - ε) γ, zeroEventCount t = zeroEventCount (γ - ε) := by
    intro t ht
    refine count_const_of_event_free ht.1.le fun γ' hγ' hz => ?_
    refine hfree γ' ?_ (ne_of_lt (lt_of_le_of_lt hγ'.2 ht.2)) hz
    rw [abs_lt]
    exact ⟨by linarith [hγ'.1], by linarith [hγ'.2, ht.2]⟩
  -- right side: constant on [γ, γ + ε), equal to the count at γ
  have hright : ∀ t ∈ Set.Ico γ (γ + ε), zeroEventCount t = zeroEventCount γ := by
    intro t ht
    refine count_const_of_event_free ht.1 fun γ' hγ' hz => ?_
    refine hfree γ' ?_ (ne_of_gt hγ'.1) hz
    rw [abs_lt]
    exact ⟨by linarith [hγ'.1], by linarith [hγ'.2, ht.2]⟩
  -- the count at γ is the count at γ − ε plus one (the event at γ itself)
  have hstep : zeroEventCount γ = zeroEventCount (γ - ε) + 1 := by
    unfold zeroEventCount
    have hsplit : {γ' : ℝ | γ' ∈ Set.Ioc 0 γ ∧ riemannZeta (line γ') = 0}
        = insert γ {γ' : ℝ | γ' ∈ Set.Ioc 0 (γ - ε) ∧ riemannZeta (line γ') = 0} := by
      ext γ'
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_insert_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rcases eq_or_ne γ' γ with rfl | hne
        · exact Or.inl rfl
        · right
          refine ⟨⟨h1, ?_⟩, h3⟩
          by_contra hgt
          rw [not_le] at hgt
          refine hfree γ' ?_ hne h3
          rw [abs_lt]
          exact ⟨by linarith, by linarith [lt_of_le_of_ne h2 hne]⟩
      · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨⟨hγ, le_refl _⟩, hev⟩
        · exact ⟨⟨h1, by linarith⟩, h3⟩
    have hγnotin : γ ∉ {γ' : ℝ | γ' ∈ Set.Ioc 0 (γ - ε) ∧ riemannZeta (line γ') = 0} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ioc]
      rintro ⟨⟨-, h2⟩, -⟩
      linarith
    rw [hsplit, Set.ncard_insert_of_notMem hγnotin (events_finite (γ - ε))]
  refine ⟨(zeroEventCount (γ - ε) : ℝ), (zeroEventCount γ : ℝ), ?_, ?_, ?_⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show γ - ε < γ by linarith)] with t ht
    exact_mod_cast (hleft t ht).symm
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT' (show γ < γ + ε by linarith)] with t ht
    exact_mod_cast (hright t ⟨ht.1.le, ht.2⟩).symm
  · rw [hstep]
    push_cast
    ring

/-- **The count is jump-free off events**: at a non-event ordinate the jump is zero. -/
theorem count_hasJump_of_not_event {γ : ℝ}
    (h : ¬ (0 < γ ∧ riemannZeta (line γ) = 0)) :
    HasJump (fun t => (zeroEventCount t : ℝ)) γ 0 := by
  obtain ⟨ε₀, hε₀, hfree⟩ := exists_event_free_interval γ
  rcases le_or_gt γ 0 with hγ0 | hγ0
  · -- γ ≤ 0: the count vanishes on both sides near γ
    have hzero_left : ∀ t : ℝ, t ≤ 0 → zeroEventCount t = 0 := by
      intro t ht
      unfold zeroEventCount
      convert Set.ncard_empty ℝ using 2
      ext γ'
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false, not_and]
      rintro ⟨h1, h2⟩
      exact absurd (h1.trans_le (h2.trans ht)) (lt_irrefl 0)
    refine ⟨0, 0, ?_, ?_, by ring⟩
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (show γ - 1 < γ by linarith)] with t ht
      have h0 : zeroEventCount t = 0 := hzero_left t (le_of_lt (lt_of_lt_of_le ht.2 hγ0))
      exact_mod_cast h0.symm
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT' (show γ < γ + ε₀ by linarith)] with t ht
      have h0 : zeroEventCount t = 0 := by
        unfold zeroEventCount
        convert Set.ncard_empty ℝ using 2
        ext γ'
        simp only [Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false, not_and]
        rintro ⟨h1, h2⟩
        intro hz
        refine hfree γ' ?_ ?_ hz
        · rw [abs_lt]
          exact ⟨by linarith, by linarith [h2.trans_lt ht.2]⟩
        · intro hEq
          rw [hEq] at h1
          linarith
      exact_mod_cast h0.symm
  · -- γ > 0 and no event at γ
    have hev : riemannZeta (line γ) ≠ 0 := fun hz => h ⟨hγ0, hz⟩
    set ε : ℝ := min ε₀ γ with hεdef
    have hεε₀ : ε ≤ ε₀ := min_le_left _ _
    have hε : 0 < ε := lt_min hε₀ hγ0
    have hconst : ∀ t ∈ Set.Ioo (γ - ε) (γ + ε),
        zeroEventCount t = zeroEventCount (γ - ε) := by
      intro t ht
      refine count_const_of_event_free ht.1.le fun γ' hγ' hz => ?_
      rcases eq_or_ne γ' γ with rfl | hne
      · exact hev hz
      · refine hfree γ' ?_ hne hz
        rw [abs_lt]
        exact ⟨by linarith [hγ'.1], by linarith [hγ'.2, ht.2]⟩
    refine ⟨(zeroEventCount (γ - ε) : ℝ), (zeroEventCount (γ - ε) : ℝ), ?_, ?_, by ring⟩
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (show γ - ε < γ by linarith)] with t ht
      exact_mod_cast (hconst t ⟨ht.1, ht.2.trans (by linarith)⟩).symm
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT' (show γ < γ + ε by linarith)] with t ht
      exact_mod_cast (hconst t ⟨by linarith [ht.1], ht.2⟩).symm

/-! ## §5 The headline: residue = jump(S) -/

/-- At an event of order `m ≥ 1`: the log-derivative residue is `m`, and `S` jumps by one
(the event registers once in the distinct-ordinate count).  At simple events the two numbers
coincide — the literal `residue = jump(S)`. -/
theorem residue_and_S_jump_of_order {γ : ℝ} (hγ : 0 < γ) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : analyticOrderAt riemannZeta (line γ) = m) :
    Tendsto (fun s => (s - line γ) * logDeriv riemannZeta s) (𝓝[≠] line γ) (𝓝 (m : ℂ))
      ∧ HasJump CarrierScale.S γ 1 := by
  have hev : riemannZeta (line γ) = 0 := by
    obtain ⟨g, hg, hg0, hfg⟩ := (zeta_analyticAt_line γ).analyticOrderAt_eq_natCast.mp hm
    have hself := hfg.self_of_nhds
    have hz : ((line γ : ℂ) - line γ) ^ m = 0 := by
      rw [sub_self]
      exact zero_pow (by omega)
    rw [hself, hz, zero_smul]
  exact ⟨logDeriv_residue_eq_order (zeta_analyticAt_line γ) hm,
    (count_hasJump_iff_S_hasJump γ 1).mp (count_hasJump_event hγ hev)⟩

/-- **residue = jump(S)** (the boxed identity, simple-event form): at a simple event,
\[
\operatorname{Res}_{\rho_\gamma}\frac{\zeta'}{\zeta} \;=\; 1 \;=\; \Delta S(\gamma).
\]
The scale-gap accumulation `S` jumps exactly where — and by exactly what — the
log-derivative residue registers. -/
theorem residue_eq_S_jump {γ : ℝ} (hγ : 0 < γ)
    (h1 : analyticOrderAt riemannZeta (line γ) = 1) :
    Tendsto (fun s => (s - line γ) * logDeriv riemannZeta s) (𝓝[≠] line γ) (𝓝 1)
      ∧ HasJump CarrierScale.S γ 1 := by
  have h := residue_and_S_jump_of_order hγ (le_refl 1) (by exact_mod_cast h1)
  simpa using h

/-- The signed convention: `Res_{ρ}(−ζ′/ζ) = −ΔS(γ)` at a simple event. -/
theorem residue_neg_eq_neg_S_jump {γ : ℝ} (hγ : 0 < γ)
    (h1 : analyticOrderAt riemannZeta (line γ) = 1) :
    Tendsto (fun s => (s - line γ) * (-logDeriv riemannZeta s)) (𝓝[≠] line γ) (𝓝 (-1))
      ∧ HasJump CarrierScale.S γ 1 := by
  obtain ⟨hres, hjump⟩ := residue_eq_S_jump hγ h1
  refine ⟨?_, hjump⟩
  have := hres.neg
  simpa [neg_mul, mul_neg] using this

/-- **The jump of `S` detects events**: for `γ > 0`, `S` jumps by one at `γ` exactly when
`γ` is an event ordinate.  The multiplicity residues are therefore computable from the
discontinuities of the scale-gap readout. -/
theorem S_jump_detects_event {γ : ℝ} (hγ : 0 < γ) :
    HasJump CarrierScale.S γ 1 ↔ riemannZeta (line γ) = 0 := by
  constructor
  · intro h
    by_contra hz
    have h0 : HasJump CarrierScale.S γ 0 :=
      (count_hasJump_iff_S_hasJump γ 0).mp (count_hasJump_of_not_event fun hc => hz hc.2)
    have := h.unique h0
    norm_num at this
  · intro hev
    exact (count_hasJump_iff_S_hasJump γ 1).mp (count_hasJump_event hγ hev)

/-! ## §6 The multiplicity-weighted ledger `S_mult`

The distinct-event ledger counts closures; the spectral side wants multiplicity.  Define
the multiplicity-weighted native count `N_mult(t) = Σ_{0<γ'≤t} ord_{½+iγ'} ζ` and its
ledger `S_mult = N_mult − 1 − ϑ/π`.  The clock is continuous, so the jump of `S_mult` at
`γ` is exactly the vanishing order, and with the source-general residue theorem the boxed
identity `Res = ΔS_mult` holds at every ordinate — no simplicity hypothesis.  The
distinct-event ledger `CarrierScale.S` is unchanged. -/

/-- The vanishing order of the fiber at the line point of ordinate `γ`, as a natural
number (the order is finite because ζ is nowhere locally zero). -/
noncomputable def eventOrder (γ : ℝ) : ℕ := analyticOrderNatAt riemannZeta (line γ)

/-- The order at a line point is finite. -/
theorem zeta_orderAt_ne_top (γ : ℝ) : analyticOrderAt riemannZeta (line γ) ≠ ⊤ := by
  intro htop
  exact zeta_not_eventually_zero (line_ne_one γ) (analyticOrderAt_eq_top.mp htop)

/-- `eventOrder` is the genuine analytic order. -/
theorem zeta_orderAt_eq_coe (γ : ℝ) :
    analyticOrderAt riemannZeta (line γ) = (eventOrder γ : ℕ∞) :=
  (Nat.cast_analyticOrderNatAt (zeta_orderAt_ne_top γ)).symm

/-- Zero order exactly off events. -/
theorem eventOrder_eq_zero_iff (γ : ℝ) :
    eventOrder γ = 0 ↔ riemannZeta (line γ) ≠ 0 := by
  rw [← (zeta_analyticAt_line γ).analyticOrderAt_eq_zero, zeta_orderAt_eq_coe γ]
  exact_mod_cast Iff.rfl

/-- **The multiplicity-weighted native count**: the total vanishing order through height
`t`, `N_mult(t) = Σ_{0<γ'≤t} ord_{½+iγ'} ζ`, summed over the (finite) event set. -/
noncomputable def zeroEventCountMult (t : ℝ) : ℕ :=
  ∑ γ' ∈ (events_finite t).toFinset, eventOrder γ'

/-- Event-free windows do not change the event set. -/
lemma events_eq_of_event_free {a b : ℝ} (hab : a ≤ b)
    (h : ∀ γ' ∈ Set.Ioc a b, riemannZeta (line γ') ≠ 0) :
    {γ' : ℝ | γ' ∈ Set.Ioc 0 b ∧ riemannZeta (line γ') = 0}
      = {γ' : ℝ | γ' ∈ Set.Ioc 0 a ∧ riemannZeta (line γ') = 0} := by
  ext γ'
  simp only [Set.mem_setOf_eq, Set.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    by_contra hgt
    rw [not_le] at hgt
    exact h γ' ⟨hgt, h2⟩ h3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2.trans hab⟩, h3⟩

/-- The weighted count is constant on event-free windows. -/
lemma multCount_const_of_event_free {a b : ℝ} (hab : a ≤ b)
    (h : ∀ γ' ∈ Set.Ioc a b, riemannZeta (line γ') ≠ 0) :
    zeroEventCountMult b = zeroEventCountMult a := by
  unfold zeroEventCountMult
  have hF : (events_finite b).toFinset = (events_finite a).toFinset :=
    Set.Finite.toFinset_inj.mpr (events_eq_of_event_free hab h)
  rw [hF]

/-- The generic jump builder: one-sided constancy plus a single step. -/
lemma hasJump_of_locally_step {F : ℝ → ℕ} {γ : ℝ} {w : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hleft : ∀ t ∈ Set.Ioo (γ - ε) γ, F t = F (γ - ε))
    (hright : ∀ t ∈ Set.Ico γ (γ + ε), F t = F γ)
    (hstep : F γ = F (γ - ε) + w) :
    HasJump (fun t => (F t : ℝ)) γ w := by
  refine ⟨(F (γ - ε) : ℝ), (F γ : ℝ), ?_, ?_, ?_⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show γ - ε < γ by linarith)] with t ht
    exact_mod_cast (hleft t ht).symm
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT' (show γ < γ + ε by linarith)] with t ht
    exact_mod_cast (hright t ⟨ht.1.le, ht.2⟩).symm
  · rw [hstep]
    push_cast
    ring

/-- **The weighted count jumps by the multiplicity** at each event. -/
theorem countMult_hasJump_event {γ : ℝ} (hγ : 0 < γ) (hev : riemannZeta (line γ) = 0) :
    HasJump (fun t => (zeroEventCountMult t : ℝ)) γ (eventOrder γ) := by
  obtain ⟨ε₀, hε₀, hfree⟩ := exists_event_free_interval γ
  set ε : ℝ := min ε₀ γ with hεdef
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hεγ : ε ≤ γ := min_le_right _ _
  have hε : 0 < ε := lt_min hε₀ hγ
  refine hasJump_of_locally_step hε ?_ ?_ ?_
  · intro t ht
    refine multCount_const_of_event_free ht.1.le fun γ' hγ' hz => ?_
    refine hfree γ' ?_ (ne_of_lt (lt_of_le_of_lt hγ'.2 ht.2)) hz
    rw [abs_lt]
    exact ⟨by linarith [hγ'.1], by linarith [hγ'.2, ht.2]⟩
  · intro t ht
    refine multCount_const_of_event_free ht.1 fun γ' hγ' hz => ?_
    refine hfree γ' ?_ (ne_of_gt hγ'.1) hz
    rw [abs_lt]
    exact ⟨by linarith [hγ'.1], by linarith [hγ'.2, ht.2]⟩
  · unfold zeroEventCountMult
    have hsplit : {γ' : ℝ | γ' ∈ Set.Ioc 0 γ ∧ riemannZeta (line γ') = 0}
        = insert γ {γ' : ℝ | γ' ∈ Set.Ioc 0 (γ - ε) ∧ riemannZeta (line γ') = 0} := by
      ext γ'
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_insert_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rcases eq_or_ne γ' γ with rfl | hne
        · exact Or.inl rfl
        · right
          refine ⟨⟨h1, ?_⟩, h3⟩
          by_contra hgt
          rw [not_le] at hgt
          refine hfree γ' ?_ hne h3
          rw [abs_lt]
          exact ⟨by linarith, by linarith [lt_of_le_of_ne h2 hne]⟩
      · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨⟨hγ, le_refl _⟩, hev⟩
        · exact ⟨⟨h1, by linarith⟩, h3⟩
    have hγnotin : γ ∉ {γ' : ℝ | γ' ∈ Set.Ioc 0 (γ - ε) ∧ riemannZeta (line γ') = 0} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ioc]
      rintro ⟨⟨-, h2⟩, -⟩
      linarith
    have hF : (events_finite γ).toFinset
        = insert γ ((events_finite (γ - ε)).toFinset) := by
      ext x
      rw [Set.Finite.mem_toFinset, hsplit, Set.mem_insert_iff, Finset.mem_insert,
        Set.Finite.mem_toFinset]
    rw [hF, Finset.sum_insert (by simpa [Set.Finite.mem_toFinset] using hγnotin)]
    omega

/-- **The weighted count is jump-free off events.** -/
theorem countMult_hasJump_of_not_event {γ : ℝ}
    (h : ¬ (0 < γ ∧ riemannZeta (line γ) = 0)) :
    HasJump (fun t => (zeroEventCountMult t : ℝ)) γ 0 := by
  obtain ⟨ε₀, hε₀, hfree⟩ := exists_event_free_interval γ
  rcases le_or_gt γ 0 with hγ0 | hγ0
  · -- γ ≤ 0: the weighted count vanishes on a neighborhood
    have hzero : ∀ t : ℝ, t < γ + ε₀ → zeroEventCountMult t = 0 := by
      intro t ht
      unfold zeroEventCountMult
      have hE : {γ' : ℝ | γ' ∈ Set.Ioc 0 t ∧ riemannZeta (line γ') = 0} = ∅ := by
        ext γ'
        simp only [Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro h1 h2
        refine hfree γ' ?_ ?_ h2
        · rw [abs_lt]
          exact ⟨by linarith [h1.1], by linarith [h1.2.trans_lt ht]⟩
        · intro hEq
          rw [hEq] at h1
          linarith [h1.1]
      have hF : (events_finite t).toFinset = ∅ := by
        ext x
        rw [Set.Finite.mem_toFinset, hE]
        simp
      rw [hF, Finset.sum_empty]
    have hjump : HasJump (fun t => (zeroEventCountMult t : ℝ)) γ ((0 : ℕ) : ℝ) := by
      refine hasJump_of_locally_step hε₀ ?_ ?_ ?_
      · intro t ht
        rw [hzero t (by linarith [ht.2]), hzero (γ - ε₀) (by linarith)]
      · intro t ht
        rw [hzero t ht.2, hzero γ (by linarith)]
      · rw [hzero γ (by linarith), hzero (γ - ε₀) (by linarith)]
    simpa using hjump
  · -- γ > 0, non-event
    have hev : riemannZeta (line γ) ≠ 0 := fun hz => h ⟨hγ0, hz⟩
    set ε : ℝ := min ε₀ γ with hεdef
    have hεε₀ : ε ≤ ε₀ := min_le_left _ _
    have hε : 0 < ε := lt_min hε₀ hγ0
    have hjump : HasJump (fun t => (zeroEventCountMult t : ℝ)) γ ((0 : ℕ) : ℝ) := by
      refine hasJump_of_locally_step hε ?_ ?_ ?_
      · intro t ht
        refine multCount_const_of_event_free ht.1.le fun γ' hγ' hz => ?_
        refine hfree γ' ?_ (ne_of_lt (lt_of_le_of_lt hγ'.2 ht.2)) hz
        rw [abs_lt]
        exact ⟨by linarith [hγ'.1], by linarith [hγ'.2, ht.2]⟩
      · intro t ht
        refine multCount_const_of_event_free ht.1 fun γ' hγ' hz => ?_
        refine hfree γ' ?_ (ne_of_gt hγ'.1) hz
        rw [abs_lt]
        exact ⟨by linarith [hγ'.1], by linarith [hγ'.2, ht.2]⟩
      · have h0 : zeroEventCountMult γ = zeroEventCountMult (γ - ε) := by
          refine multCount_const_of_event_free (by linarith) fun γ' hγ' hz => ?_
          rcases eq_or_ne γ' γ with rfl | hne
          · exact hev hz
          · refine hfree γ' ?_ hne hz
            rw [abs_lt]
            exact ⟨by linarith [hγ'.1], by linarith [hγ'.2]⟩
        omega
    simpa using hjump

/-- **The multiplicity-weighted compensation ledger** `S_mult(t) = N_mult(t) − 1 − ϑ(t)/π`.
The distinct-event ledger `CarrierScale.S` is unchanged: `S_event` counts distinct
closures; `S_mult` counts spectral residue weight. -/
noncomputable def Smult (t : ℝ) : ℝ :=
  (zeroEventCountMult t : ℝ) - 1 - theta t / Real.pi

/-- The two typed ledgers differ by the excess multiplicity, nothing else. -/
theorem Smult_sub_S (t : ℝ) :
    Smult t - CarrierScale.S t
      = (zeroEventCountMult t : ℝ) - (zeroEventCount t : ℝ) := by
  unfold Smult CarrierScale.S
  ring

/-- Jump transfer for the weighted ledger: the clock is continuous, so `S_mult` and
`N_mult` have identical jumps. -/
theorem countMult_hasJump_iff_Smult_hasJump (γ j : ℝ) :
    HasJump (fun t => (zeroEventCountMult t : ℝ)) γ j ↔ HasJump Smult γ j := by
  have hc : Continuous (fun t => -1 - theta t / Real.pi) :=
    continuous_const.sub (theta_continuous.div_const _)
  have he : Smult = fun t => (zeroEventCountMult t : ℝ) + (-1 - theta t / Real.pi) := by
    funext t
    unfold Smult
    ring
  rw [he]
  exact (hasJump_add_continuous_iff hc γ j).symm

/-- **`S_mult` jumps by exactly the multiplicity at every ordinate** `γ > 0` — zero off
events, `m_ρ` at an order-`m` event.  No simplicity hypothesis. -/
theorem Smult_hasJump (γ : ℝ) (hγ : 0 < γ) : HasJump Smult γ (eventOrder γ) := by
  rcases eq_or_ne (riemannZeta (line γ)) 0 with hev | hev
  · exact (countMult_hasJump_iff_Smult_hasJump γ _).mp (countMult_hasJump_event hγ hev)
  · have h0 : eventOrder γ = 0 := (eventOrder_eq_zero_iff γ).mpr hev
    rw [h0]
    simpa using (countMult_hasJump_iff_Smult_hasJump γ 0).mp
      (countMult_hasJump_of_not_event fun hc => hev hc.2)

/-- The jump of `S_mult` reads off the multiplicity (uniqueness of jumps). -/
theorem Smult_jump_eq_order {γ w : ℝ} (hγ : 0 < γ) (h : HasJump Smult γ w) :
    w = eventOrder γ :=
  h.unique (Smult_hasJump γ hγ)

/-- **residue = jump(S_mult), unconditionally — no simplicity hypothesis** (the boxed
identity): for every `γ > 0`,
\[
\operatorname{Res}_{s=\rho_\gamma}\frac{\zeta'}{\zeta}
\;=\; m_{\rho_\gamma}
\;=\; \Delta S_{\mathrm{mult}}(\gamma),
\]
both sides zero off events.  This is the ledger the spectral/trace side consumes:
counting measures carry multiplicity. -/
theorem residue_eq_Smult_jump (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun s => (s - line γ) * logDeriv riemannZeta s) (𝓝[≠] line γ)
        (𝓝 (eventOrder γ : ℂ))
      ∧ HasJump Smult γ (eventOrder γ) :=
  ⟨logDeriv_residue_eq_order (zeta_analyticAt_line γ) (zeta_orderAt_eq_coe γ),
    Smult_hasJump γ hγ⟩

/-! ## §7 From the ledger to the windowed spectral trace

The chain closes into a trace:

  vanishing ↔ jump ↔ residue ↔ spectral atom ↔ (windowed) resolvent trace.

Over any finite window `(0, T]` everything is exact and unconditional: the atomic sum
`Σ_γ m_γ·h(γ)` is simultaneously the jump readout of `S_mult` (`windowedTrace_eq_jump_sum`),
the residue sum of the logarithmic derivative (`windowedTrace_eq_residue_sum`), and the
matrix trace of the diagonalized `h(D)` on the window's spectral atoms — one axis per unit
of multiplicity, so the atoms carry multiplicity linearly
(`trace_diagonal_eq_windowedTrace`).  The resolvent test function `h_w(γ) = (γ−w)⁻¹` gives
the windowed resolvent trace (`windowedResolventTrace_eq_residue_sum`), and the cumulative
registration decomposition `dN_mult = π⁻¹dϑ + dS_mult` is `countMult_decomposition`.

**The audited remaining arrows** (named, not assumed): identifying the window's diagonal
model with the carrier's retained-mode generator `D_Wᶜ` requires the mode dictionary to
carry multiplicity — the existing dictionary (the bridge `R_W = V_W·Φ_W` and the on-line
real-generator realization) is event-level, witnessing one kernel vector per event, and
does not yet grade the kernel by `m_ρ`; and the `T → ∞` limit of the resolvent trace
requires summability/regularization (the raw sum `Σ m_ρ/(γ_ρ−w)` diverges; the classical
remedies are conjugate pairing or differencing at two resolvent points). -/

/-- Cumulative registration decomposition: `N_mult(t) = 1 + ϑ(t)/π + S_mult(t)` — the
Stieltjes reading `dN_mult = π⁻¹dϑ + dS_mult`. -/
theorem countMult_decomposition (t : ℝ) :
    (zeroEventCountMult t : ℝ) = 1 + theta t / Real.pi + Smult t := by
  unfold Smult
  ring

/-- The event window: the (finite) set of event ordinates in `(0, T]`. -/
noncomputable def eventWindow (T : ℝ) : Finset ℝ := (events_finite T).toFinset

lemma eventWindow_pos {T γ : ℝ} (hγ : γ ∈ eventWindow T) : 0 < γ := by
  have := (events_finite T).mem_toFinset.mp hγ
  exact this.1.1

/-- **The windowed spectral trace**: the multiplicity-weighted atomic sum
`Σ_{γ ∈ window} m_γ·h(γ)` — `Tr h(D)` for the window's spectral atoms. -/
noncomputable def windowedTrace (h : ℝ → ℂ) (T : ℝ) : ℂ :=
  ∑ γ ∈ eventWindow T, (eventOrder γ : ℂ) * h γ

/-- **Windowed trace = jump readout of `S_mult`**: any jump assignment for `S_mult`
computes the trace — the atomic Stieltjes sum `Σ h·ΔS_mult`. -/
theorem windowedTrace_eq_jump_sum (h : ℝ → ℂ) (T : ℝ) (j : ℝ → ℝ)
    (hj : ∀ γ ∈ eventWindow T, HasJump Smult γ (j γ)) :
    windowedTrace h T = ∑ γ ∈ eventWindow T, (j γ : ℂ) * h γ := by
  unfold windowedTrace
  refine Finset.sum_congr rfl fun γ hγ => ?_
  have hjγ : j γ = eventOrder γ :=
    Smult_jump_eq_order (eventWindow_pos hγ) (hj γ hγ)
  rw [hjγ]
  norm_cast

/-- **Windowed trace = residue sum of the logarithmic derivative**: any residue assignment
for `ζ′/ζ` computes the trace — the exact standard shape of a spectral trace written
through the pole residues of a log derivative. -/
theorem windowedTrace_eq_residue_sum (h : ℝ → ℂ) (T : ℝ) (r : ℝ → ℂ)
    (hr : ∀ γ ∈ eventWindow T,
      Tendsto (fun s => (s - line γ) * logDeriv riemannZeta s) (𝓝[≠] line γ) (𝓝 (r γ))) :
    windowedTrace h T = ∑ γ ∈ eventWindow T, r γ * h γ := by
  unfold windowedTrace
  refine Finset.sum_congr rfl fun γ hγ => ?_
  have hres := logDeriv_residue_eq_order (zeta_analyticAt_line γ) (zeta_orderAt_eq_coe γ)
  have hrγ : r γ = (eventOrder γ : ℂ) := tendsto_nhds_unique (hr γ hγ) hres
  rw [hrγ]

/-- The finite diagonal model of the window: one coordinate axis per unit of multiplicity —
the spectral atoms of the window, multiplicity carried linearly. -/
def WindowIndex (T : ℝ) : Type :=
  (γ : {x : ℝ // x ∈ eventWindow T}) × Fin (eventOrder γ.1)

noncomputable instance (T : ℝ) : Fintype (WindowIndex T) := by
  unfold WindowIndex
  infer_instance

open Classical in
/-- **The operator form**: the matrix trace of the diagonalized `h(D)` on the window equals
the windowed spectral trace.  `Tr h(D_T) = Σ_γ m_γ·h(γ)` — with
`windowedTrace_eq_residue_sum`, the spectral trace *is* the residue sum. -/
theorem trace_diagonal_eq_windowedTrace (h : ℝ → ℂ) (T : ℝ) :
    Matrix.trace (Matrix.diagonal fun p : WindowIndex T => h p.1.1)
      = windowedTrace h T := by
  rw [Matrix.trace_diagonal]
  unfold windowedTrace
  rw [show (∑ p : WindowIndex T, h p.1.1)
      = ∑ γ : {x : ℝ // x ∈ eventWindow T}, ∑ _i : Fin (eventOrder γ.1), h γ.1 from
    Fintype.sum_sigma _]
  rw [← Finset.sum_coe_sort (eventWindow T) (fun γ => (eventOrder γ : ℂ) * h γ)]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The windowed resolvent trace** `Tr (D_T − w)⁻¹ = Σ_γ m_γ/(γ−w)`. -/
noncomputable def windowedResolventTrace (w : ℂ) (T : ℝ) : ℂ :=
  windowedTrace (fun γ => ((γ : ℂ) - w)⁻¹) T

/-- **The windowed resolvent trace is the residue sum**:
`Tr (D_T − w)⁻¹ = Σ_γ Res_{ρ_γ}(ζ′/ζ)/(γ−w)` — the native zero-to-resolvent
identification, through the linear object whose atoms carry multiplicity. -/
theorem windowedResolventTrace_eq_residue_sum (w : ℂ) (T : ℝ) (r : ℝ → ℂ)
    (hr : ∀ γ ∈ eventWindow T,
      Tendsto (fun s => (s - line γ) * logDeriv riemannZeta s) (𝓝[≠] line γ) (𝓝 (r γ))) :
    windowedResolventTrace w T = ∑ γ ∈ eventWindow T, r γ * ((γ : ℂ) - w)⁻¹ :=
  windowedTrace_eq_residue_sum _ T r hr

end CriticalLinePhasor.ResidueJump
