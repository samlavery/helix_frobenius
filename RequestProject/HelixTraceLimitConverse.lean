import RequestProject.HelixLedgerPairing
import RequestProject.DifferencedResolvent

/-!
# The RH ⟹ trace-limit converse: the wall certified biconditional

The symmetrized line tower's capstone (`rh_of_symmetrizedLineTower_canonicalTraceLimit`) proves
RH **from** the trace-limit box `hlim`.  This file proves the converse: **under RH the box
holds** — the two-sided window partial sums of the rotated Hadamard ledger converge locally
uniformly off the real axis to the rotated ξ-channel minus its Hadamard constant.  Combined,
`rh_iff_symmetrizedLineTower_traceLimit`: the wall is *exactly* the Riemann Hypothesis — not an
approximation from either side.

The four layers of the assembly:

* **RH extraction** (`re_eq_half_of_riemannHypothesis`): every member of the compiled
  nontrivial-zero set has real part `½` — Mathlib's `RiemannHypothesis` applies because the
  strip membership rules out both the trivial zeros and the point `1`.
* **The RH-index bijection** (`zerosEquiv`): under RH the two-sided event index — one event
  copy per conjugate leg — is *equivalent* to the full nontrivial-zero subtype, by
  `γ ↦ ½+iγ` on the upper leg and `γ ↦ conj(½+iγ)` on the lower.  Surjectivity is where RH
  enters: an off-line zero would inhabit neither leg.  Multiplicities transport by the
  compiled `eventOrder_eq_xiOrderNat` and `xiOrderNat_conj_of_re_half`.
* **The finite-stage identification** (`stage_eq_pairSum`): each symmetrized tower stage *is*
  the finite partial sum of the transported ledger family over the two-sided window finset —
  the compiled `symmetrizedTrace_eq_windowedLedgerSum`, re-indexed.
* **The uniform tail** (`traceLimit_of_rh`): on a compact off the real axis the pairing closed
  form (`norm_pairedLedgerTerm`) bounds every tail term by `8B·m_ρ/‖ρ‖²`, and the compiled
  counting summability (`ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros`) drives the tail
  to zero uniformly — window finsets are monotone and cofinal, so the finite stages converge
  to the full ledger sum.

Register: `traceLimit_of_rh` **assumes RH** (it is the converse direction of a biconditional
and says so in its hypothesis); nothing else in the tree consumes it.  The biconditional
`rh_iff_symmetrizedLineTower_traceLimit` is the certificate that the trace-limit wall neither
overshoots nor undershoots RH.  No circularity: the forward direction is the compiled capstone,
the converse direction never touches the tower's spectral data beyond the compiled ledger.
-/

open Filter Topology Complex

namespace CriticalLinePhasor.CaptureInterfaceAudit

open CriticalLinePhasor.ResidueJump CriticalLinePhasor.HilbertPolya
open CriticalLinePhasor.CarrierScale CriticalLinePhasor.XiChannel
open CriticalLinePhasor.ResolventLimit CriticalLinePhasor.ContourArgument

/-! ## §1 RH extraction and chart basics -/

/-- **RH pins every compiled nontrivial zero to the line**: strip membership excludes the
trivial zeros (negative real part) and the point `1`, so Mathlib's `RiemannHypothesis`
applies directly. -/
theorem re_eq_half_of_riemannHypothesis (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) : ρ.re = 1 / 2 := by
  obtain ⟨h0, h1, hz⟩ := hρ
  refine hRH ρ hz ?_ ?_
  · rintro ⟨n, rfl⟩
    have hre : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
      have : ((-2 : ℂ) * ((n : ℂ) + 1)) = (((-2 * ((n : ℝ) + 1) : ℝ)) : ℂ) := by
        push_cast; ring
      rw [this, Complex.ofReal_re]
    rw [hre] at h0
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · intro h1'
    rw [h1'] at h1
    simp at h1

/-- The line chart's imaginary part is the ordinate. -/
theorem line_im (γ : ℝ) : (line γ).im = γ := by
  unfold line lineC
  simp

/-- On the line the pole parameter is the (real) ordinate. -/
theorem poleParam_of_re_half {ρ : ℂ} (h : ρ.re = 1 / 2) :
    HelixLimit.poleParam ρ = ((ρ.im : ℝ) : ℂ) := by
  unfold HelixLimit.poleParam
  rw [h]
  push_cast
  ring

/-- Under RH the chart image of an off-real point is never a nontrivial zero: its real part is
`½ − Im z ≠ ½`. -/
theorem chart_not_mem_of_offReal (hRH : RiemannHypothesis) {z : ℂ} (hz : z.im ≠ 0) :
    (1 / 2 + Complex.I * z) ∉ ZD.NontrivialZeros := by
  intro hmem
  have h := re_eq_half_of_riemannHypothesis hRH hmem
  have hre : ((1 : ℂ) / 2 + Complex.I * z).re = 1 / 2 - z.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  rw [hre] at h
  exact hz (by linarith)

/-! ## §2 The two-sided window finsets -/

/-- Window membership: an ordinate lies in the height-`T` window iff it is an event of height
at most `T`. -/
theorem mem_eventWindow_iff {T γ : ℝ} :
    γ ∈ eventWindow T ↔ γ ∈ Events ∧ γ ≤ T := by
  rw [eventWindow, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hIoc, hz⟩
    exact ⟨⟨hIoc.1, hz⟩, hIoc.2⟩
  · rintro ⟨⟨h0, hz⟩, hT⟩
    exact ⟨⟨h0, hT⟩, hz⟩

/-- The height-`n` window as a finset of the event subtype. -/
noncomputable def windowFinset (n : ℕ) : Finset {γ : ℝ // γ ∈ Events} :=
  (eventWindow (n : ℝ)).attach.map
    ⟨fun x => ⟨x.1, (mem_eventWindow_iff.mp x.2).1⟩, by
      intro x y h
      have hval := congrArg Subtype.val h
      exact Subtype.ext hval⟩

theorem mem_windowFinset_iff {n : ℕ} {a : {γ : ℝ // γ ∈ Events}} :
    a ∈ windowFinset n ↔ a.1 ∈ eventWindow (n : ℝ) := by
  unfold windowFinset
  simp only [Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and]
  constructor
  · rintro ⟨x, hx⟩
    rw [← hx]
    exact x.2
  · intro ha
    exact ⟨⟨a.1, ha⟩, Subtype.ext rfl⟩

/-- The two-sided window: one copy of the height-`n` window per conjugate leg. -/
noncomputable def pairFinset (n : ℕ) :
    Finset ({γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) :=
  (windowFinset n).disjSum (windowFinset n)

/-- The ordinate of a two-sided index. -/
def ordinate : ({γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) → ℝ :=
  Sum.elim Subtype.val Subtype.val

theorem pairFinset_monotone : Monotone pairFinset := by
  intro n m hnm x hx
  cases x with
  | inl a =>
      rw [pairFinset, Finset.inl_mem_disjSum, mem_windowFinset_iff,
        mem_eventWindow_iff] at hx ⊢
      exact ⟨hx.1, hx.2.trans (Nat.cast_le.mpr hnm)⟩
  | inr b =>
      rw [pairFinset, Finset.inr_mem_disjSum, mem_windowFinset_iff,
        mem_eventWindow_iff] at hx ⊢
      exact ⟨hx.1, hx.2.trans (Nat.cast_le.mpr hnm)⟩

theorem pairFinset_exhausts (x : {γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) :
    ∃ n : ℕ, x ∈ pairFinset n := by
  cases x with
  | inl a =>
      refine ⟨⌈a.1⌉₊, ?_⟩
      rw [pairFinset, Finset.inl_mem_disjSum, mem_windowFinset_iff, mem_eventWindow_iff]
      exact ⟨a.2, Nat.le_ceil a.1⟩
  | inr b =>
      refine ⟨⌈b.1⌉₊, ?_⟩
      rw [pairFinset, Finset.inr_mem_disjSum, mem_windowFinset_iff, mem_eventWindow_iff]
      exact ⟨b.2, Nat.le_ceil b.1⟩

/-- The two-sided windows are cofinal in the finset order — the exhaustion net. -/
theorem tendsto_pairFinset_atTop : Tendsto pairFinset atTop atTop :=
  tendsto_atTop_finset_of_monotone pairFinset_monotone pairFinset_exhausts

/-- An index outside the height-`n` two-sided window has ordinate above `n`. -/
theorem lt_ordinate_of_not_mem_pairFinset {n : ℕ}
    {x : {γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}} (hx : x ∉ pairFinset n) :
    (n : ℝ) < ordinate x := by
  cases x with
  | inl a =>
      by_contra h
      exact hx (by
        rw [pairFinset, Finset.inl_mem_disjSum, mem_windowFinset_iff, mem_eventWindow_iff]
        exact ⟨a.2, not_lt.mp h⟩)
  | inr b =>
      by_contra h
      exact hx (by
        rw [pairFinset, Finset.inr_mem_disjSum, mem_windowFinset_iff, mem_eventWindow_iff]
        exact ⟨b.2, not_lt.mp h⟩)

/-! ## §3 The ledger family and the finite-stage identification -/

/-- The rotated Hadamard ledger's unit term, weighted by multiplicity, at a compiled zero. -/
noncomputable def ledgerTerm (z : ℂ) (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) : ℂ :=
  (ZD.xiOrderNat ρ.val : ℂ) * ((z - HelixLimit.poleParam ρ.val)⁻¹ + Complex.I / ρ.val)

/-- The compiled rotated-ledger identity, phrased on the named family. -/
theorem neg_I_mul_trace_eq_tsum_ledgerTerm (z : ℂ) :
    -Complex.I * xiZeroResolventTrace z = ∑' ρ, ledgerTerm z ρ :=
  neg_I_mul_xiZeroResolventTrace z

/-- The upper-leg value at ordinate `γ`. -/
noncomputable def ledgerTermPos (z : ℂ) (γ : ℝ) : ℂ :=
  (ZD.xiOrderNat (line γ) : ℂ) *
    ((z - HelixLimit.poleParam (line γ))⁻¹ + Complex.I / line γ)

/-- The conjugate-leg value at ordinate `γ`. -/
noncomputable def ledgerTermNeg (z : ℂ) (γ : ℝ) : ℂ :=
  (ZD.xiOrderNat ((starRingEnd ℂ) (line γ)) : ℂ) *
    ((z - HelixLimit.poleParam ((starRingEnd ℂ) (line γ)))⁻¹ +
      Complex.I / (starRingEnd ℂ) (line γ))

/-- The two-sided ledger value on the event index. -/
noncomputable def pairValue (z : ℂ) :
    ({γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) → ℂ :=
  Sum.elim (fun a => ledgerTermPos z a.1) (fun b => ledgerTermNeg z b.1)

/-- **The multiplicity-matched pair factorization**: at any positive ordinate the two leg
values sum to the event order times the windowed-ledger integrand — `eventOrder = xiOrderNat`
on the upper leg (the compiled order bridge) and the conjugate multiplicity law on the lower
leg. -/
theorem pairTerm_factored (z : ℂ) {γ : ℝ} (hγ : 0 < γ) :
    ledgerTermPos z γ + ledgerTermNeg z γ =
      (eventOrder γ : ℂ) *
        (-Complex.I * (Complex.I * (z - HelixLimit.poleParam (line γ))⁻¹ - 1 / line γ) +
          -Complex.I * (Complex.I *
            (z - HelixLimit.poleParam ((starRingEnd ℂ) (line γ)))⁻¹ -
              1 / (starRingEnd ℂ) (line γ))) := by
  rw [← pairedTerm_eq_rotatedLedgerTerms z γ]
  unfold ledgerTermPos ledgerTermNeg
  rw [xiOrderNat_conj_of_re_half (line_re γ), eventOrder_eq_xiOrderNat γ hγ,
    poleParam_line, poleParam_conj_line]
  push_cast
  ring

/-- **Each symmetrized stage is the two-sided window partial sum of the ledger family**: the
compiled `symmetrizedTrace_eq_windowedLedgerSum`, re-indexed over the event-subtype finset. -/
theorem stage_eq_pairSum (n : ℕ) (z : ℂ) :
    normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
        (symmetrizedLineTowerOffsets n) z =
      ∑ x ∈ pairFinset n, pairValue z x := by
  have hsplit := Finset.sum_disjSum (windowFinset n) (windowFinset n) (pairValue z)
  have hp : (∑ a ∈ windowFinset n, pairValue z (Sum.inl a)) =
      ∑ γ ∈ eventWindow (n : ℝ), ledgerTermPos z γ := by
    unfold windowFinset
    rw [Finset.sum_map]
    exact Finset.sum_attach _ (fun γ => ledgerTermPos z γ)
  have hq : (∑ b ∈ windowFinset n, pairValue z (Sum.inr b)) =
      ∑ γ ∈ eventWindow (n : ℝ), ledgerTermNeg z γ := by
    unfold windowFinset
    rw [Finset.sum_map]
    exact Finset.sum_attach _ (fun γ => ledgerTermNeg z γ)
  calc normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
          (symmetrizedLineTowerOffsets n) z
        = windowedTrace (fun γ =>
            -Complex.I * (Complex.I * (z - HelixLimit.poleParam (line γ))⁻¹ - 1 / line γ) +
              -Complex.I * (Complex.I *
                (z - HelixLimit.poleParam ((starRingEnd ℂ) (line γ)))⁻¹ -
                  1 / (starRingEnd ℂ) (line γ))) (n : ℝ) :=
          symmetrizedTrace_eq_windowedLedgerSum n z
    _ = ∑ γ ∈ eventWindow (n : ℝ), (ledgerTermPos z γ + ledgerTermNeg z γ) := by
        unfold windowedTrace
        exact Finset.sum_congr rfl fun γ hγ =>
          (pairTerm_factored z (eventWindow_pos hγ)).symm
    _ = (∑ γ ∈ eventWindow (n : ℝ), ledgerTermPos z γ) +
          ∑ γ ∈ eventWindow (n : ℝ), ledgerTermNeg z γ := Finset.sum_add_distrib
    _ = (∑ a ∈ windowFinset n, pairValue z (Sum.inl a)) +
          ∑ b ∈ windowFinset n, pairValue z (Sum.inr b) := by rw [hp, hq]
    _ = ∑ x ∈ (windowFinset n).disjSum (windowFinset n), pairValue z x := hsplit.symm
    _ = ∑ x ∈ pairFinset n, pairValue z x := rfl

/-! ## §4 The RH-index bijection -/

/-- **The RH-index bijection**: under RH, the two-sided event index is equivalent to the full
nontrivial-zero subtype — `γ ↦ ½+iγ` on the upper leg, its conjugate on the lower.
Surjectivity is exactly where RH enters: an off-line zero would inhabit neither leg. -/
noncomputable def zerosEquiv (hRH : RiemannHypothesis) :
    ({γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) ≃
      {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} :=
  Equiv.ofBijective
    (Sum.elim
      (fun a => ⟨line a.1, line_mem_nontrivialZeros a.2⟩)
      (fun b => ⟨(starRingEnd ℂ) (line b.1),
        conj_mem_nontrivialZeros (line_mem_nontrivialZeros b.2)⟩))
    (by
      constructor
      · intro x y hxy
        have hval := congrArg Subtype.val hxy
        cases x with
        | inl a =>
            cases y with
            | inl a' =>
                simp only [Sum.elim_inl] at hval
                exact congrArg Sum.inl (Subtype.ext (line_injective hval))
            | inr b' =>
                exfalso
                simp only [Sum.elim_inl, Sum.elim_inr] at hval
                have him := congrArg Complex.im hval
                rw [line_im, Complex.conj_im, line_im] at him
                have ha := a.2.1
                have hb := b'.2.1
                linarith
        | inr b =>
            cases y with
            | inl a' =>
                exfalso
                simp only [Sum.elim_inl, Sum.elim_inr] at hval
                have him := congrArg Complex.im hval
                rw [Complex.conj_im, line_im, line_im] at him
                have ha := a'.2.1
                have hb := b.2.1
                linarith
            | inr b' =>
                simp only [Sum.elim_inr] at hval
                have hline : line b.1 = line b'.1 := by
                  have h := congrArg (starRingEnd ℂ) hval
                  simpa using h
                exact congrArg Sum.inr (Subtype.ext (line_injective hline))
      · rintro ⟨ρ, hρ⟩
        have hre := re_eq_half_of_riemannHypothesis hRH hρ
        have him := nontrivialZero_im_ne_zero hρ
        rcases lt_or_gt_of_ne him with hneg | hpos
        · have hline : line (-ρ.im) = (starRingEnd ℂ) ρ := by
            apply Complex.ext
            · rw [line_re, Complex.conj_re, hre]
            · rw [line_im, Complex.conj_im]
          have hmem : (-ρ.im) ∈ Events := by
            refine ⟨neg_pos.mpr hneg, ?_⟩
            rw [hline]
            exact (conj_mem_nontrivialZeros hρ).2.2
          refine ⟨Sum.inr ⟨-ρ.im, hmem⟩, ?_⟩
          apply Subtype.ext
          show (starRingEnd ℂ) (line (-ρ.im)) = ρ
          rw [hline, Complex.conj_conj]
        · have hline : line ρ.im = ρ := by
            apply Complex.ext
            · rw [line_re, hre]
            · rw [line_im]
          have hmem : ρ.im ∈ Events := by
            refine ⟨hpos, ?_⟩
            rw [hline]
            exact hρ.2.2
          refine ⟨Sum.inl ⟨ρ.im, hmem⟩, ?_⟩
          apply Subtype.ext
          show line ρ.im = ρ
          exact hline)

/-- The two-sided ledger value is the transported ledger family. -/
theorem pairValue_eq (hRH : RiemannHypothesis) (z : ℂ)
    (x : {γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) :
    pairValue z x = ledgerTerm z (zerosEquiv hRH x) := by
  cases x <;> rfl

/-- The transported zero's absolute imaginary part is the ordinate. -/
theorem abs_im_zerosEquiv (hRH : RiemannHypothesis)
    (x : {γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) :
    |((zerosEquiv hRH x).val).im| = ordinate x := by
  cases x with
  | inl a =>
      show |(line a.1).im| = a.1
      rw [line_im]
      exact abs_of_pos a.2.1
  | inr b =>
      show |((starRingEnd ℂ) (line b.1)).im| = b.1
      rw [Complex.conj_im, line_im, abs_neg]
      exact abs_of_pos b.2.1

/-! ## §5 The converse: RH forces the trace limit -/

set_option maxHeartbeats 1000000 in
/-- **The trace-limit box holds under RH.**  Given RH and the compiled Hadamard identity's
constant, the symmetrized tower's stages converge locally uniformly off the real axis to the
rotated ξ-channel minus its Hadamard constant: each stage is the two-sided window partial sum
of the transported ledger family (`stage_eq_pairSum`, `zerosEquiv`), and on any compact off
the real axis the pairing closed form bounds the tail by the compiled counting summability,
uniformly.  This is the converse direction of the wall; it assumes RH by design. -/
theorem traceLimit_of_rh (hRH : RiemannHypothesis) {C : ℂ}
    (hC : ∀ z : ℂ, (1 / 2 + Complex.I * z) ∉ ZD.NontrivialZeros →
      xiChannel z = C + xiZeroResolventTrace z) :
    TendstoLocallyUniformlyOn
      (fun n => normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
        (symmetrizedLineTowerOffsets n))
      (fun z => (-Complex.I * xiChannel z) - (-Complex.I * C)) atTop offReal := by
  classical
  -- the counting weight, transported to the two-sided event index
  set W : ({γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) → ℝ := fun x =>
    (ZD.xiOrderNat ((zerosEquiv hRH x).val) : ℝ) / ‖(zerosEquiv hRH x).val‖ ^ 2
    with hWdef
  have hWsum : Summable W :=
    (Equiv.summable_iff (zerosEquiv hRH)).mpr
      ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros
  have hopen : IsOpen offReal := by
    have h : offReal = Complex.im ⁻¹' {(0 : ℝ)}ᶜ := rfl
    rw [h]
    exact isOpen_compl_singleton.preimage Complex.continuous_im
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen]
  intro K hKs hK
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  set R : ℝ := max R₀ 0 with hRdef
  have hR : ∀ z ∈ K, ‖z‖ ≤ R := fun z hz => (hR₀ z hz).trans (le_max_left _ _)
  have hR0 : (0 : ℝ) ≤ R := le_max_right _ _
  set B : ℝ := 1 / 2 + R with hBdef
  have hBpos : (0 : ℝ) < B := by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hthresh : (0 : ℝ) < ε / (8 * B + 1) := by positivity
  have hpartial : Tendsto (fun m : ℕ => ∑ x ∈ pairFinset m, W x) atTop
      (𝓝 (∑' x, W x)) :=
    hWsum.hasSum.comp tendsto_pairFinset_atTop
  have hsub : ∀ m : ℕ, (∑' x : {x // x ∉ pairFinset m}, W x.val) =
      (∑' x, W x) - ∑ x ∈ pairFinset m, W x := by
    intro m
    have hcomp : HasSum (fun x : {x // x ∉ pairFinset m} => W x.val)
        ((∑' x, W x) - ∑ x ∈ pairFinset m, W x) :=
      (Finset.hasSum_compl_iff (pairFinset m)).mpr (by
        have halg : (∑' x, W x) - (∑ x ∈ pairFinset m, W x) +
            ∑ x ∈ pairFinset m, W x = ∑' x, W x := by ring
        rw [halg]
        exact hWsum.hasSum)
    exact hcomp.tsum_eq
  have htail : Tendsto (fun m : ℕ => ∑' x : {x // x ∉ pairFinset m}, W x.val)
      atTop (𝓝 0) := by
    have hconst := hpartial.const_sub (∑' x, W x)
    rw [sub_self] at hconst
    exact hconst.congr fun m => (hsub m).symm
  have hev1 := htail.eventually_lt_const hthresh
  have hev2 : ∀ᶠ n : ℕ in atTop, ⌈2 * R + 1⌉₊ ≤ n := eventually_ge_atTop _
  filter_upwards [hev1, hev2] with n htn hn₀ z hzK
  have him : z.im ≠ 0 := hKs hzK
  have hznot := chart_not_mem_of_offReal hRH him
  have hzR : ‖z‖ ≤ R := hR z hzK
  have hnR : 2 * R + 1 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn₀)
  -- the transported ledger family at this chart point
  set G : ({γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) → ℂ := fun x =>
    ledgerTerm z (zerosEquiv hRH x) with hGdef
  -- the numerator bound
  have hBz : ‖(1 : ℂ) / 2 + Complex.I * z‖ ≤ B := by
    have h1 : ‖(1 : ℂ) / 2 + Complex.I * z‖ ≤ ‖(1 : ℂ) / 2‖ + ‖Complex.I * z‖ :=
      norm_add_le _ _
    have h2 : ‖(1 : ℂ) / 2‖ = 1 / 2 := by simp
    have h3 : ‖Complex.I * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    rw [h2, h3] at h1
    rw [hBdef]
    linarith
  -- the per-term tail bound: closed form + counting weight
  have hbound : ∀ x : {x // x ∉ pairFinset n}, ‖G x.val‖ ≤ 8 * B * W x.val := by
    rintro ⟨x, hx⟩
    show ‖ledgerTerm z (zerosEquiv hRH x)‖ ≤ 8 * B *
      ((ZD.xiOrderNat ((zerosEquiv hRH x).val) : ℝ) / ‖(zerosEquiv hRH x).val‖ ^ 2)
    have hγn : (n : ℝ) < ordinate x := lt_ordinate_of_not_mem_pairFinset hx
    have hγ1 : 1 ≤ ordinate x := by linarith
    have hγR : 2 * R < ordinate x := by linarith
    have hγpos : (0 : ℝ) < ordinate x := by linarith
    have hre : (zerosEquiv hRH x).val.re = 1 / 2 :=
      re_eq_half_of_riemannHypothesis hRH (zerosEquiv hRH x).2
    have himρ : |(zerosEquiv hRH x).val.im| = ordinate x := abs_im_zerosEquiv hRH x
    have hρ0 : (zerosEquiv hRH x).val ≠ 0 := by
      intro h0
      rw [h0] at hre
      norm_num at hre
    have hpp : HelixLimit.poleParam (zerosEquiv hRH x).val =
        (((zerosEquiv hRH x).val.im : ℝ) : ℂ) := poleParam_of_re_half hre
    have hzpp : z ≠ HelixLimit.poleParam (zerosEquiv hRH x).val := by
      intro heq
      apply him
      have h := congrArg Complex.im heq
      rw [hpp, Complex.ofReal_im] at h
      exact h
    have hnorm : ‖ledgerTerm z (zerosEquiv hRH x)‖ =
        (ZD.xiOrderNat (zerosEquiv hRH x).val : ℝ) *
          (‖1 / 2 + Complex.I * z‖ /
            (‖z - HelixLimit.poleParam (zerosEquiv hRH x).val‖ *
              ‖(zerosEquiv hRH x).val‖)) := by
      unfold ledgerTerm
      rw [norm_mul, Complex.norm_natCast,
        norm_pairedLedgerTerm z (zerosEquiv hRH x).val hzpp hρ0]
    have hD : ordinate x / 2 ≤ ‖z - HelixLimit.poleParam (zerosEquiv hRH x).val‖ := by
      have h1 : ‖(((zerosEquiv hRH x).val.im : ℝ) : ℂ)‖ - ‖z‖ ≤
          ‖(((zerosEquiv hRH x).val.im : ℝ) : ℂ) - z‖ := norm_sub_norm_le _ _
      rw [norm_sub_rev] at h1
      have h2 : ‖(((zerosEquiv hRH x).val.im : ℝ) : ℂ)‖ = ordinate x := by
        rw [Complex.norm_real, Real.norm_eq_abs, himρ]
      rw [h2] at h1
      rw [hpp]
      linarith
    have hN1 : ordinate x ≤ ‖(zerosEquiv hRH x).val‖ := by
      have h := Complex.abs_im_le_norm (zerosEquiv hRH x).val
      rwa [himρ] at h
    have hN2 : ‖(zerosEquiv hRH x).val‖ ≤ 2 * ordinate x := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (zerosEquiv hRH x).val
      rw [hre, himρ] at h1
      have h2 : |(1 : ℝ) / 2| = 1 / 2 := by norm_num
      rw [h2] at h1
      linarith
    have hDpos : (0 : ℝ) < ‖z - HelixLimit.poleParam (zerosEquiv hRH x).val‖ := by
      linarith
    have hNpos : (0 : ℝ) < ‖(zerosEquiv hRH x).val‖ := by linarith
    have hkey : ‖1 / 2 + Complex.I * z‖ /
        (‖z - HelixLimit.poleParam (zerosEquiv hRH x).val‖ *
          ‖(zerosEquiv hRH x).val‖) ≤ 8 * B / ‖(zerosEquiv hRH x).val‖ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hBz, hD, hN1, hN2, hγ1, hγpos, hBpos, hDpos, hNpos,
        norm_nonneg ((1 : ℂ) / 2 + Complex.I * z),
        mul_le_mul_of_nonneg_left hN2 (mul_nonneg hBpos.le hNpos.le),
        mul_le_mul_of_nonneg_left hD (mul_nonneg (by positivity : (0:ℝ) ≤ 8 * B)
          hNpos.le)]
    rw [hnorm]
    exact (mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg _)).trans
      (le_of_eq (by ring))
  -- summabilities
  have hWcompl : Summable (fun x : {x // x ∉ pairFinset n} => W x.val) :=
    (Finset.summable_compl_iff _).mpr hWsum
  have hnormsum : Summable (fun x : {x // x ∉ pairFinset n} => ‖G x.val‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (hWcompl.mul_left (8 * B))
  have hcomplsum : Summable (fun x : {x // x ∉ pairFinset n} => G x.val) :=
    hnormsum.of_norm
  have hGsum : Summable G := (Finset.summable_compl_iff (pairFinset n)).mp hcomplsum
  -- the identities: full ledger and finite stage
  have hfull : (-Complex.I * xiChannel z) - (-Complex.I * C) = ∑' x, G x := by
    rw [canonicalTarget_eq_rotatedLedger hC hznot, neg_I_mul_trace_eq_tsum_ledgerTerm]
    exact (Equiv.tsum_eq (zerosEquiv hRH) (ledgerTerm z)).symm
  have hstage : normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
      (symmetrizedLineTowerOffsets n) z = ∑ x ∈ pairFinset n, G x := by
    rw [stage_eq_pairSum]
    exact Finset.sum_congr rfl fun x _ => pairValue_eq hRH z x
  have hGcomp : HasSum (fun x : {x // x ∉ pairFinset n} => G x.val)
      ((∑' x, G x) - ∑ x ∈ pairFinset n, G x) :=
    (Finset.hasSum_compl_iff (pairFinset n)).mpr (by
      have halg : (∑' x, G x) - (∑ x ∈ pairFinset n, G x) +
          ∑ x ∈ pairFinset n, G x = ∑' x, G x := by ring
      rw [halg]
      exact hGsum.hasSum)
  have hdiff : ((-Complex.I * xiChannel z) - (-Complex.I * C)) -
      normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
        (symmetrizedLineTowerOffsets n) z =
      ∑' x : {x // x ∉ pairFinset n}, G x.val := by
    rw [hfull, hstage]
    exact hGcomp.tsum_eq.symm
  -- assemble
  show dist ((-Complex.I * xiChannel z) - (-Complex.I * C))
    (normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
      (symmetrizedLineTowerOffsets n) z) < ε
  rw [dist_eq_norm, hdiff]
  have hfin : 8 * B * (∑' x : {x // x ∉ pairFinset n}, W x.val) < ε := by
    have h8B : (0 : ℝ) < 8 * B := by positivity
    have hden : (0 : ℝ) < 8 * B + 1 := by positivity
    have hstep := mul_lt_mul_of_pos_left htn h8B
    have hle : 8 * B * (ε / (8 * B + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith [hε.le]
    linarith
  calc ‖∑' x : {x // x ∉ pairFinset n}, G x.val‖
      ≤ ∑' x : {x // x ∉ pairFinset n}, ‖G x.val‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' x : {x // x ∉ pairFinset n}, 8 * B * W x.val :=
        hnormsum.tsum_le_tsum hbound (hWcompl.mul_left _)
    _ = 8 * B * ∑' x : {x // x ∉ pairFinset n}, W x.val := tsum_mul_left
    _ < ε := hfin

/-! ## §6 The biconditional certificate -/

/-- **The trace-limit wall is exactly the Riemann Hypothesis.**  There is a Hadamard constant
`C` — the compiled `xiChannel_eq_constant_add_zeroResolventTrace` witness — for which the
symmetrized line tower's canonical trace limit holds *if and only if* RH does.  Forward:
the compiled capstone `rh_of_symmetrizedLineTower_canonicalTraceLimit`.  Converse:
`traceLimit_of_rh` — under RH the two-sided window partial sums exhaust the ledger, locally
uniformly off the real axis.  The wall neither overshoots nor undershoots RH. -/
theorem rh_iff_symmetrizedLineTower_traceLimit :
    ∃ C : ℂ, (RiemannHypothesis ↔
      TendstoLocallyUniformlyOn
        (fun n => normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
          (symmetrizedLineTowerOffsets n))
        (fun z => (-Complex.I * xiChannel z) - (-Complex.I * C)) atTop offReal) := by
  obtain ⟨C, hC⟩ := xiChannel_eq_constant_add_zeroResolventTrace
  exact ⟨C, ⟨fun hRH => traceLimit_of_rh hRH hC,
    fun hlim => rh_of_symmetrizedLineTower_canonicalTraceLimit 1 C hlim⟩⟩

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.re_eq_half_of_riemannHypothesis
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.zerosEquiv
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.stage_eq_pairSum
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.traceLimit_of_rh
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.rh_iff_symmetrizedLineTower_traceLimit
