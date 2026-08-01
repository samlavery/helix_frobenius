import RequestProject.HelixTraceLimitConverse

/-!
# The symmetrized line tower converges unconditionally

Brick 1 of the interior program at the certified trace-limit wall.  The converse
theorem `traceLimit_of_rh` consumes RH in exactly one place — the surjectivity of the
index bijection `zerosEquiv` — while its entire tail machinery (the pairing closed
form, the `8B·m/‖ρ‖²` per-term bound, the compiled counting summability) is RH-free.
This file re-runs that machinery on the **native** two-sided event index, with the
RH-derived facts replaced by definitional ones: the on-line zeros have `re = ½` and
`|im| = ordinate` *by construction* (`line γ = ½ + iγ`).

* `zeroOf` / `zeroOf_mem` / `zeroOfSub_injective` — the genuine zero attached to a
  two-sided event index, its compiled ledger membership on both legs, and the
  injection into the nontrivial-zero subtype (upper and conjugate legs separated by
  the sign of the imaginary part).
* `summable_pairWeight` — the native counting weight is summable: the restriction of
  the compiled full counting summability along the injection.
* `pairValue_norm_le` — the per-term tail bound `‖pairValue z x‖ ≤ 8B·W x`,
  RH-free.
* `onLineLedgerLimit` — the on-line ledger's full two-sided sum: the tower's limit.
* **`symmetrizedLineTower_traceLimit_unconditional`** — the tower's stages converge
  locally uniformly off the real axis to `onLineLedgerLimit`, unconditionally.
* **`traceLimit_box_iff_eqOn`** — the reshape of the certified wall: the trace-limit
  box holds iff the two explicitly constructed functions — `onLineLedgerLimit` and
  the rotated ξ-channel minus its Hadamard constant — agree on the off-real set.
  The box's "converges to the channel" becomes "its existing limit equals the
  channel."

Proven in this file: everything above, unconditionally — no RH, no GRH, no new
axioms.  Not proven in this file: the agreement itself (`Set.EqOn` of the two
functions), which by the compiled biconditional is the certified wall.
-/

open Filter Topology Complex

namespace CriticalLinePhasor.CaptureInterfaceAudit

open CriticalLinePhasor.ResidueJump CriticalLinePhasor.HilbertPolya
open CriticalLinePhasor.CarrierScale CriticalLinePhasor.XiChannel
open CriticalLinePhasor.ResolventLimit CriticalLinePhasor.ContourArgument

/-! ## The native index: genuine zeros on both legs -/

/-- The genuine zero attached to a two-sided event index: `½ + iγ` on the upper leg,
its conjugate on the lower. -/
noncomputable def zeroOf : ({γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) → ℂ :=
  Sum.elim (fun a => line a.1) (fun b => (starRingEnd ℂ) (line b.1))

theorem line_im' (γ : ℝ) : (line γ).im = γ := by
  unfold line lineC
  simp

/-- Both legs are genuine ledger members. -/
theorem zeroOf_mem (x : {γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) :
    zeroOf x ∈ ZD.NontrivialZeros := by
  cases x with
  | inl a =>
      show line a.1 ∈ ZD.NontrivialZeros
      exact ⟨by rw [line_re]; norm_num, by rw [line_re]; norm_num, a.2.2⟩
  | inr b =>
      show (starRingEnd ℂ) (line b.1) ∈ ZD.NontrivialZeros
      exact CriticalLinePhasor.ContourArgument.conj_mem_nontrivialZeros
        ⟨by rw [line_re]; norm_num, by rw [line_re]; norm_num, b.2.2⟩

/-- The index-to-zero map, valued in the nontrivial-zero subtype. -/
noncomputable def zeroOfSub (x : {γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) :
    {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} :=
  ⟨zeroOf x, zeroOf_mem x⟩

/-- The legs inject: distinct ordinates give distinct zeros, and the two legs are
separated by the sign of the imaginary part. -/
theorem zeroOfSub_injective : Function.Injective zeroOfSub := by
  intro x y hxy
  have h : zeroOf x = zeroOf y := congrArg Subtype.val hxy
  cases x with
  | inl a =>
      cases y with
      | inl a' =>
          have him := congrArg Complex.im h
          simp only [zeroOf, Sum.elim_inl, line_im'] at him
          exact congrArg Sum.inl (Subtype.ext him)
      | inr b' =>
          exfalso
          have him := congrArg Complex.im h
          simp only [zeroOf, Sum.elim_inl, Sum.elim_inr, Complex.conj_im,
            line_im'] at him
          linarith [a.2.1, b'.2.1]
  | inr b =>
      cases y with
      | inl a' =>
          exfalso
          have him := congrArg Complex.im h
          simp only [zeroOf, Sum.elim_inl, Sum.elim_inr, Complex.conj_im,
            line_im'] at him
          linarith [b.2.1, a'.2.1]
      | inr b' =>
          have him := congrArg Complex.im h
          simp only [zeroOf, Sum.elim_inr, Complex.conj_im, line_im'] at him
          exact congrArg Sum.inr (Subtype.ext (by linarith))

/-! ## The native weight and its summability -/

/-- The native counting weight on the two-sided event index. -/
noncomputable def pairWeight
    (x : {γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) : ℝ :=
  (ZD.xiOrderNat (zeroOf x) : ℝ) / ‖zeroOf x‖ ^ 2

set_option maxHeartbeats 400000 in
/-- **The native weight is summable, unconditionally**: the restriction of the
compiled full counting summability along the leg injection. -/
theorem summable_pairWeight : Summable pairWeight := by
  have h := ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros.comp_injective
    zeroOfSub_injective
  exact h.congr fun x => rfl

/-! ## Definitional geometry of the native zeros -/

theorem zeroOf_re (x : {γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) :
    (zeroOf x).re = 1 / 2 := by
  cases x with
  | inl a => simp only [zeroOf, Sum.elim_inl]; rw [line_re]
  | inr b => simp only [zeroOf, Sum.elim_inr, Complex.conj_re]; rw [line_re]

theorem absIm_zeroOf (x : {γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) :
    |(zeroOf x).im| = ordinate x := by
  cases x with
  | inl a =>
      simp only [zeroOf, Sum.elim_inl, ordinate, line_im']
      exact abs_of_pos a.2.1
  | inr b =>
      simp only [zeroOf, Sum.elim_inr, ordinate, Complex.conj_im, line_im',
        abs_neg]
      exact abs_of_pos b.2.1

/-- The native pair value is the ledger-term shape at the attached zero. -/
theorem pairValue_eq_ledger_shape (z : ℂ)
    (x : {γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) :
    pairValue z x = (ZD.xiOrderNat (zeroOf x) : ℂ) *
      ((z - HelixLimit.poleParam (zeroOf x))⁻¹ + Complex.I / zeroOf x) := by
  cases x with
  | inl a => rfl
  | inr b => rfl

/-! ## The RH-free per-term tail bound -/

/-- **The per-term tail bound, RH-free**: for `‖z‖ ≤ R` off the real axis and an
index of ordinate above `max 1 (2R)`, the native pair value is bounded by
`8B·pairWeight` with `B = ½ + R`. -/
theorem pairValue_norm_le {z : ℂ} {R : ℝ} (hzR : ‖z‖ ≤ R) (him : z.im ≠ 0)
    (x : {γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events})
    (hγ1 : 1 ≤ ordinate x) (hγR : 2 * R < ordinate x) :
    ‖pairValue z x‖ ≤ 8 * (1 / 2 + R) * pairWeight x := by
  set B : ℝ := 1 / 2 + R with hBdef
  have hR0 : (0 : ℝ) ≤ R := le_trans (norm_nonneg z) hzR
  have hBpos : (0 : ℝ) < B := by rw [hBdef]; positivity
  have hγpos : (0 : ℝ) < ordinate x := lt_of_lt_of_le zero_lt_one hγ1
  have hre : (zeroOf x).re = 1 / 2 := zeroOf_re x
  have himρ : |(zeroOf x).im| = ordinate x := absIm_zeroOf x
  have hρ0 : zeroOf x ≠ 0 := by
    intro h0
    rw [h0] at hre
    norm_num at hre
  have hpp : HelixLimit.poleParam (zeroOf x) = (((zeroOf x).im : ℝ) : ℂ) :=
    poleParam_of_re_half hre
  have hzpp : z ≠ HelixLimit.poleParam (zeroOf x) := by
    intro heq
    apply him
    have h := congrArg Complex.im heq
    rw [hpp, Complex.ofReal_im] at h
    exact h
  have hBz : ‖(1 : ℂ) / 2 + Complex.I * z‖ ≤ B := by
    have h1 : ‖(1 : ℂ) / 2 + Complex.I * z‖ ≤ ‖(1 : ℂ) / 2‖ + ‖Complex.I * z‖ :=
      norm_add_le _ _
    have h2 : ‖(1 : ℂ) / 2‖ = 1 / 2 := by simp
    have h3 : ‖Complex.I * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    rw [h2, h3] at h1
    rw [hBdef]
    linarith
  have hnorm : ‖pairValue z x‖ =
      (ZD.xiOrderNat (zeroOf x) : ℝ) *
        (‖1 / 2 + Complex.I * z‖ /
          (‖z - HelixLimit.poleParam (zeroOf x)‖ * ‖zeroOf x‖)) := by
    rw [pairValue_eq_ledger_shape, norm_mul, Complex.norm_natCast,
      norm_pairedLedgerTerm z (zeroOf x) hzpp hρ0]
  have hD : ordinate x / 2 ≤ ‖z - HelixLimit.poleParam (zeroOf x)‖ := by
    have h1 : ‖(((zeroOf x).im : ℝ) : ℂ)‖ - ‖z‖ ≤
        ‖(((zeroOf x).im : ℝ) : ℂ) - z‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at h1
    have h2 : ‖(((zeroOf x).im : ℝ) : ℂ)‖ = ordinate x := by
      rw [Complex.norm_real, Real.norm_eq_abs, himρ]
    rw [h2] at h1
    rw [hpp]
    linarith
  have hN1 : ordinate x ≤ ‖zeroOf x‖ := by
    have h := Complex.abs_im_le_norm (zeroOf x)
    rwa [himρ] at h
  have hN2 : ‖zeroOf x‖ ≤ 2 * ordinate x := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (zeroOf x)
    rw [hre, himρ] at h1
    have h2 : |(1 : ℝ) / 2| = 1 / 2 := by norm_num
    rw [h2] at h1
    linarith
  have hDpos : (0 : ℝ) < ‖z - HelixLimit.poleParam (zeroOf x)‖ := by linarith
  have hNpos : (0 : ℝ) < ‖zeroOf x‖ := by linarith
  have hkey : ‖1 / 2 + Complex.I * z‖ /
      (‖z - HelixLimit.poleParam (zeroOf x)‖ * ‖zeroOf x‖) ≤
        8 * B / ‖zeroOf x‖ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hBz, hD, hN1, hN2, hγ1, hγpos, hBpos, hDpos, hNpos,
      norm_nonneg ((1 : ℂ) / 2 + Complex.I * z),
      mul_le_mul_of_nonneg_left hN2 (mul_nonneg hBpos.le hNpos.le),
      mul_le_mul_of_nonneg_left hD (mul_nonneg (by positivity : (0:ℝ) ≤ 8 * B)
        hNpos.le)]
  rw [hnorm]
  calc (ZD.xiOrderNat (zeroOf x) : ℝ) *
      (‖1 / 2 + Complex.I * z‖ /
        (‖z - HelixLimit.poleParam (zeroOf x)‖ * ‖zeroOf x‖))
      ≤ (ZD.xiOrderNat (zeroOf x) : ℝ) * (8 * B / ‖zeroOf x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg _)
    _ = 8 * B * pairWeight x := by unfold pairWeight; ring

/-! ## The unconditional limit -/

/-- The on-line ledger's full two-sided sum: the tower's unconditional limit. -/
noncomputable def onLineLedgerLimit (z : ℂ) : ℂ := ∑' x, pairValue z x

/-- **The symmetrized line tower converges unconditionally**: its stages tend
locally uniformly off the real axis to the on-line ledger sum.  No RH, no GRH —
the tail is driven by the native counting summability alone. -/
theorem symmetrizedLineTower_traceLimit_unconditional :
    TendstoLocallyUniformlyOn
      (fun n => normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
        (symmetrizedLineTowerOffsets n))
      onLineLedgerLimit atTop offReal := by
  classical
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
  have hpartial : Tendsto (fun m : ℕ => ∑ x ∈ pairFinset m, pairWeight x) atTop
      (𝓝 (∑' x, pairWeight x)) :=
    summable_pairWeight.hasSum.comp tendsto_pairFinset_atTop
  have hsub : ∀ m : ℕ, (∑' x : {x // x ∉ pairFinset m}, pairWeight x.val) =
      (∑' x, pairWeight x) - ∑ x ∈ pairFinset m, pairWeight x := by
    intro m
    have hcomp : HasSum (fun x : {x // x ∉ pairFinset m} => pairWeight x.val)
        ((∑' x, pairWeight x) - ∑ x ∈ pairFinset m, pairWeight x) :=
      (Finset.hasSum_compl_iff (pairFinset m)).mpr (by
        have halg : (∑' x, pairWeight x) - (∑ x ∈ pairFinset m, pairWeight x) +
            ∑ x ∈ pairFinset m, pairWeight x = ∑' x, pairWeight x := by ring
        rw [halg]
        exact summable_pairWeight.hasSum)
    exact hcomp.tsum_eq
  have htail : Tendsto
      (fun m : ℕ => ∑' x : {x // x ∉ pairFinset m}, pairWeight x.val)
      atTop (𝓝 0) := by
    have hconst := hpartial.const_sub (∑' x, pairWeight x)
    rw [sub_self] at hconst
    exact hconst.congr fun m => (hsub m).symm
  have hev1 := htail.eventually_lt_const hthresh
  have hev2 : ∀ᶠ n : ℕ in atTop, ⌈2 * R + 1⌉₊ ≤ n := eventually_ge_atTop _
  filter_upwards [hev1, hev2] with n htn hn₀ z hzK
  have him : z.im ≠ 0 := hKs hzK
  have hzR : ‖z‖ ≤ R := hR z hzK
  have hnR : 2 * R + 1 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn₀)
  -- the per-term tail bound at this chart point
  have hbound : ∀ x : {x // x ∉ pairFinset n},
      ‖pairValue z x.val‖ ≤ 8 * B * pairWeight x.val := by
    rintro ⟨x, hx⟩
    have hγn : (n : ℝ) < ordinate x := lt_ordinate_of_not_mem_pairFinset hx
    have hγ1 : 1 ≤ ordinate x := by linarith
    have hγR : 2 * R < ordinate x := by linarith
    exact pairValue_norm_le hzR him x hγ1 hγR
  -- summabilities
  have hWcompl : Summable (fun x : {x // x ∉ pairFinset n} => pairWeight x.val) :=
    (Finset.summable_compl_iff _).mpr summable_pairWeight
  have hnormsum : Summable
      (fun x : {x // x ∉ pairFinset n} => ‖pairValue z x.val‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
      (hWcompl.mul_left (8 * B))
  have hcomplsum : Summable
      (fun x : {x // x ∉ pairFinset n} => pairValue z x.val) :=
    hnormsum.of_norm
  have hFsum : Summable (pairValue z) :=
    (Finset.summable_compl_iff (pairFinset n)).mp hcomplsum
  -- stage and limit identities
  have hstage : normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
      (symmetrizedLineTowerOffsets n) z = ∑ x ∈ pairFinset n, pairValue z x :=
    stage_eq_pairSum n z
  have hFcomp : HasSum (fun x : {x // x ∉ pairFinset n} => pairValue z x.val)
      ((∑' x, pairValue z x) - ∑ x ∈ pairFinset n, pairValue z x) :=
    (Finset.hasSum_compl_iff (pairFinset n)).mpr (by
      have halg : (∑' x, pairValue z x) - (∑ x ∈ pairFinset n, pairValue z x) +
          ∑ x ∈ pairFinset n, pairValue z x = ∑' x, pairValue z x := by ring
      rw [halg]
      exact hFsum.hasSum)
  -- assemble
  rw [dist_eq_norm, hstage]
  have hdiff : onLineLedgerLimit z - ∑ x ∈ pairFinset n, pairValue z x =
      ∑' x : {x // x ∉ pairFinset n}, pairValue z x.val := hFcomp.tsum_eq.symm
  rw [hdiff]
  have htsum_nonneg : (0 : ℝ) ≤ ∑' x : {x // x ∉ pairFinset n}, pairWeight x.val :=
    tsum_nonneg fun x => div_nonneg (Nat.cast_nonneg _) (by positivity)
  calc ‖∑' x : {x // x ∉ pairFinset n}, pairValue z x.val‖
      ≤ ∑' x : {x // x ∉ pairFinset n}, ‖pairValue z x.val‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' x : {x // x ∉ pairFinset n}, 8 * B * pairWeight x.val :=
        hnormsum.tsum_le_tsum hbound (hWcompl.mul_left _)
    _ = 8 * B * ∑' x : {x // x ∉ pairFinset n}, pairWeight x.val := tsum_mul_left
    _ ≤ (8 * B + 1) * ∑' x : {x // x ∉ pairFinset n}, pairWeight x.val := by
        nlinarith [htsum_nonneg, hBpos]
    _ < ε := by
        have h1 : (8 * B + 1) * (∑' x : {x // x ∉ pairFinset n}, pairWeight x.val)
            < (8 * B + 1) * (ε / (8 * B + 1)) :=
          mul_lt_mul_of_pos_left htn (by positivity)
        have h2 : (8 * B + 1) * (ε / (8 * B + 1)) = ε := by
          field_simp
        linarith

/-! ## The reshape of the certified wall -/

/-- **The certified box becomes function agreement**: the trace-limit box holds iff
the two explicitly constructed functions — the unconditional tower limit and the
rotated ξ-channel minus its Hadamard constant — agree on the off-real set. -/
theorem traceLimit_box_iff_eqOn (C : ℂ) :
    TendstoLocallyUniformlyOn
      (fun n => normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
        (symmetrizedLineTowerOffsets n))
      (fun z => (-Complex.I * xiChannel z) - (-Complex.I * C)) atTop offReal ↔
    Set.EqOn onLineLedgerLimit
      (fun z => (-Complex.I * xiChannel z) - (-Complex.I * C)) offReal := by
  have hopen : IsOpen offReal := by
    have h : offReal = Complex.im ⁻¹' {(0 : ℝ)}ᶜ := rfl
    rw [h]
    exact isOpen_compl_singleton.preimage Complex.continuous_im
  constructor
  · intro hbox z hz
    have h1 : Tendsto (fun n => normalizedSpectrumTrace
        (symmetrizedLineTowerSpectrum n) (symmetrizedLineTowerOffsets n) z)
        atTop (𝓝 (onLineLedgerLimit z)) := by
      have := (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).mp
        symmetrizedLineTower_traceLimit_unconditional {z}
        (Set.singleton_subset_iff.mpr hz) isCompact_singleton
      exact (tendstoUniformlyOn_singleton_iff_tendsto).mp this
    have h2 : Tendsto (fun n => normalizedSpectrumTrace
        (symmetrizedLineTowerSpectrum n) (symmetrizedLineTowerOffsets n) z)
        atTop (𝓝 ((-Complex.I * xiChannel z) - (-Complex.I * C))) := by
      have := (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).mp
        hbox {z} (Set.singleton_subset_iff.mpr hz) isCompact_singleton
      exact (tendstoUniformlyOn_singleton_iff_tendsto).mp this
    exact tendsto_nhds_unique h1 h2
  · intro heq
    have hbase := symmetrizedLineTower_traceLimit_unconditional
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen] at hbase ⊢
    intro K hKs hK
    have hKlim := hbase K hKs hK
    rw [Metric.tendstoUniformlyOn_iff] at hKlim ⊢
    intro ε hε
    filter_upwards [hKlim ε hε] with n hn z hzK
    have hz : z ∈ offReal := hKs hzK
    have hzz : onLineLedgerLimit z =
        (-Complex.I * xiChannel z) - (-Complex.I * C) := heq hz
    rw [← hzz]
    exact hn z hzK

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.summable_pairWeight
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.pairValue_norm_le
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.symmetrizedLineTower_traceLimit_unconditional
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.traceLimit_box_iff_eqOn
