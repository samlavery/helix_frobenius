import RequestProject.HelixTowerUnconditionalConvergence

/-!
# The channel decomposition: target minus tower limit = the off-line packets

Brick 2 of the interior program.  Brick 1 proved the symmetrized tower converges
unconditionally to `onLineLedgerLimit` and reshaped the certified wall into the
agreement of two explicit functions.  This file computes their difference exactly:
on the off-real set, away from the chart images of zeros,

  `(−i·ξchannel − (−i·C))  −  onLineLedgerLimit  =  offLinePacketSum`,

the sum of the ledger terms of the **off-line** zeros alone — an unconditional
Hadamard rearrangement.  The wall's two sides differ by exactly the off-line
packets; the box holds where and only where those packets vanish.

* `ledgerTerm_norm_le_of_im_large` — the general RH-free tail bound: any nontrivial
  zero of large imaginary part has ledger term bounded by `8B·m/‖ρ‖²` (off-line
  zeros included — the pole parameter's real part is the ordinate).
* `summable_ledgerTerm` — the full ledger family is summable at every chart point,
  unconditionally: finitely many zeros in any ball (compiled), the compiled
  counting summability beyond.
* `pairIndexEquivOnLine` — the native two-sided event index is equivalent to the
  on-line members of the ledger (surjectivity is unconditional: an on-line zero has
  `|im| ≥ 2` and lands on a leg by the sign of its ordinate).
* **`channel_decomposition`** — the exact difference identity.
* **`offLinePackets_vanish_of_box`** — under the certified box, the off-line packet
  sum vanishes at every admissible chart point.

Proven in this file: everything above, unconditionally.
-/

open Filter Topology Complex

namespace CriticalLinePhasor.CaptureInterfaceAudit

open CriticalLinePhasor.ResidueJump CriticalLinePhasor.HilbertPolya
open CriticalLinePhasor.CarrierScale CriticalLinePhasor.XiChannel
open CriticalLinePhasor.ResolventLimit CriticalLinePhasor.ContourArgument

/-! ## The general RH-free tail bound -/

/-- **The general ledger tail bound, RH-free**: for any nontrivial zero — off-line
included — of imaginary part above `max 1 (2‖z‖)`, the ledger term is bounded by
`8(½+‖z‖)` times the counting weight.  The pole parameter's real part is the
ordinate, so distance from any fixed chart point grows with the ordinate. -/
theorem ledgerTerm_norm_le_of_im_large (z : ℂ)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (h1 : 1 ≤ |ρ.val.im|) (hR : 2 * ‖z‖ < |ρ.val.im|) :
    ‖ledgerTerm z ρ‖ ≤ 8 * (1 / 2 + ‖z‖) *
      ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
  set B : ℝ := 1 / 2 + ‖z‖ with hBdef
  have hBpos : (0 : ℝ) < B := by positivity
  have hrepos : 0 < ρ.val.re := ρ.2.1
  have hrelt : ρ.val.re < 1 := ρ.2.2.1
  have hρ0 : ρ.val ≠ 0 := by
    intro h0
    rw [h0] at hrepos
    simp at hrepos
  -- the pole parameter's real part is the ordinate
  have hppre : (HelixLimit.poleParam ρ.val).re = ρ.val.im := by
    unfold HelixLimit.poleParam
    simp
  have hppnorm : |ρ.val.im| ≤ ‖HelixLimit.poleParam ρ.val‖ := by
    rw [← hppre]
    exact Complex.abs_re_le_norm _
  have hD : |ρ.val.im| / 2 ≤ ‖z - HelixLimit.poleParam ρ.val‖ := by
    have h1' : ‖HelixLimit.poleParam ρ.val‖ - ‖z‖ ≤
        ‖HelixLimit.poleParam ρ.val - z‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at h1'
    linarith [hppnorm]
  have hDpos : (0 : ℝ) < ‖z - HelixLimit.poleParam ρ.val‖ := by
    have : (0 : ℝ) < |ρ.val.im| / 2 := by linarith
    linarith
  have hzpp : z ≠ HelixLimit.poleParam ρ.val := by
    intro heq
    rw [heq, sub_self, norm_zero] at hDpos
    exact lt_irrefl 0 hDpos
  have hN1 : |ρ.val.im| ≤ ‖ρ.val‖ := Complex.abs_im_le_norm _
  have hN2 : ‖ρ.val‖ ≤ 2 * |ρ.val.im| := by
    have h1' := Complex.norm_le_abs_re_add_abs_im ρ.val
    have h2 : |ρ.val.re| ≤ 1 := by
      rw [abs_of_pos hrepos]
      linarith
    linarith
  have hNpos : (0 : ℝ) < ‖ρ.val‖ := by linarith
  have hBz : ‖(1 : ℂ) / 2 + Complex.I * z‖ ≤ B := by
    have ha : ‖(1 : ℂ) / 2 + Complex.I * z‖ ≤ ‖(1 : ℂ) / 2‖ + ‖Complex.I * z‖ :=
      norm_add_le _ _
    have hb : ‖(1 : ℂ) / 2‖ = 1 / 2 := by simp
    have hc : ‖Complex.I * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    rw [hb, hc] at ha
    rw [hBdef]
    linarith
  have hnorm : ‖ledgerTerm z ρ‖ =
      (ZD.xiOrderNat ρ.val : ℝ) *
        (‖1 / 2 + Complex.I * z‖ /
          (‖z - HelixLimit.poleParam ρ.val‖ * ‖ρ.val‖)) := by
    unfold ledgerTerm
    rw [norm_mul, Complex.norm_natCast, norm_pairedLedgerTerm z ρ.val hzpp hρ0]
  have hkey : ‖1 / 2 + Complex.I * z‖ /
      (‖z - HelixLimit.poleParam ρ.val‖ * ‖ρ.val‖) ≤ 8 * B / ‖ρ.val‖ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hBz, hD, hN1, hN2, h1, hBpos, hDpos, hNpos,
      norm_nonneg ((1 : ℂ) / 2 + Complex.I * z),
      mul_le_mul_of_nonneg_left hN2 (mul_nonneg hBpos.le hNpos.le),
      mul_le_mul_of_nonneg_left hD (mul_nonneg (by positivity : (0:ℝ) ≤ 8 * B)
        hNpos.le)]
  rw [hnorm]
  calc (ZD.xiOrderNat ρ.val : ℝ) *
      (‖1 / 2 + Complex.I * z‖ /
        (‖z - HelixLimit.poleParam ρ.val‖ * ‖ρ.val‖))
      ≤ (ZD.xiOrderNat ρ.val : ℝ) * (8 * B / ‖ρ.val‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg _)
    _ = 8 * B * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by ring

/-! ## Unconditional summability of the full ledger family -/

/-- **The full ledger family is summable at every chart point, unconditionally**:
finitely many zeros inhabit any ball (compiled), and the compiled counting
summability bounds the tail. -/
theorem summable_ledgerTerm (z : ℂ) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} => ledgerTerm z ρ) := by
  classical
  set F : Set {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} :=
    {ρ | |ρ.val.im| ≤ 2 * ‖z‖ + 1} with hFdef
  have hFfin : F.Finite := by
    have hball := ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (2 * ‖z‖ + 2)
    have hsub : Subtype.val '' F ⊆ ZD.NontrivialZeros ∩
        Metric.closedBall (0 : ℂ) (2 * ‖z‖ + 2) := by
      rintro w ⟨ρ, hρF, rfl⟩
      refine ⟨ρ.2, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 := Complex.norm_le_abs_re_add_abs_im ρ.val
      have h2 : |ρ.val.re| ≤ 1 := by
        rw [abs_of_pos ρ.2.1]
        linarith [ρ.2.2.1]
      have h3 : |ρ.val.im| ≤ 2 * ‖z‖ + 1 := hρF
      linarith
    have himg : (Subtype.val '' F).Finite := hball.subset hsub
    exact Set.Finite.of_finite_image himg (Set.injOn_of_injective Subtype.val_injective)
  rw [← hFfin.summable_compl_iff]
  have hbound : ∀ ρ : ↥Fᶜ, ‖ledgerTerm z ρ.val‖ ≤
      8 * (1 / 2 + ‖z‖) * ((ZD.xiOrderNat ρ.val.val : ℝ) / ‖ρ.val.val‖ ^ 2) := by
    rintro ⟨ρ, hρ⟩
    have him : 2 * ‖z‖ + 1 < |ρ.val.im| := by
      by_contra h
      push_neg at h
      exact hρ h
    exact ledgerTerm_norm_le_of_im_large z ρ
      (by linarith [norm_nonneg z]) (by linarith)
  have hWsub : Summable (fun ρ : ↥Fᶜ =>
      8 * (1 / 2 + ‖z‖) * ((ZD.xiOrderNat ρ.val.val : ℝ) / ‖ρ.val.val‖ ^ 2)) := by
    apply Summable.mul_left
    exact (ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros.comp_injective
      Subtype.val_injective)
  exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hWsub).of_norm

/-! ## The on-line members are exactly the native index -/

/-- The on-line members of the ledger. -/
def onLineSet : Set {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := {ρ | ρ.val.re = 1 / 2}

/-- **The native two-sided event index is equivalent to the on-line ledger members**
— unconditionally: an on-line zero has `|im| ≥ 2` (compiled), so it lands on the
upper or conjugate leg by the sign of its ordinate. -/
noncomputable def pairIndexEquivOnLine :
    ({γ : ℝ // γ ∈ Events} ⊕ {γ : ℝ // γ ∈ Events}) ≃ ↥onLineSet := by
  refine Equiv.ofBijective
    (fun x => ⟨zeroOfSub x, zeroOf_re x⟩) ⟨?_, ?_⟩
  · intro x y hxy
    exact zeroOfSub_injective (congrArg Subtype.val hxy)
  · rintro ⟨⟨ρ, hρ⟩, hre⟩
    have hre' : ρ.re = 1 / 2 := hre
    have htriv : ∀ n : ℕ, ρ ≠ -2 * ((n : ℂ) + 1) := by
      intro n h
      have hr := congrArg Complex.re h
      rw [hre'] at hr
      have : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
        push_cast
        simp
      rw [this] at hr
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have him2 : 2 ≤ |ρ.im| :=
      riemannZeta_nontrivial_zero_im_ge_two hρ.2.2 htriv
    by_cases hpos : 0 < ρ.im
    · -- upper leg
      have hev : ρ.im ∈ Events := by
        refine ⟨hpos, ?_⟩
        have : line ρ.im = ρ := by
          apply Complex.ext
          · rw [line_re, hre']
          · rw [line_im']
        rw [this]
        exact hρ.2.2
      refine ⟨Sum.inl ⟨ρ.im, hev⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      show line ρ.im = ρ
      apply Complex.ext
      · rw [line_re, hre']
      · rw [line_im']
    · -- conjugate leg
      push_neg at hpos
      have himneg : ρ.im < 0 := by
        rcases lt_or_eq_of_le hpos with h | h
        · exact h
        · exfalso
          rw [h] at him2
          norm_num at him2
      have hconjmem : (starRingEnd ℂ) ρ ∈ ZD.NontrivialZeros :=
        CriticalLinePhasor.ContourArgument.conj_mem_nontrivialZeros hρ
      have hev : -ρ.im ∈ Events := by
        refine ⟨by linarith, ?_⟩
        have : line (-ρ.im) = (starRingEnd ℂ) ρ := by
          apply Complex.ext
          · rw [line_re, Complex.conj_re, hre']
          · rw [line_im', Complex.conj_im]
        rw [this]
        exact hconjmem.2.2
      refine ⟨Sum.inr ⟨-ρ.im, hev⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      show (starRingEnd ℂ) (line (-ρ.im)) = ρ
      apply Complex.ext
      · rw [Complex.conj_re, line_re, hre']
      · rw [Complex.conj_im, line_im']
        ring

/-- The tower's unconditional limit is the on-line ledger sum, in ledger form. -/
theorem onLineLedgerLimit_eq_tsum_onLine (z : ℂ) :
    onLineLedgerLimit z = ∑' ρ : ↥onLineSet, ledgerTerm z ρ.val := by
  unfold onLineLedgerLimit
  rw [← Equiv.tsum_eq pairIndexEquivOnLine
    (fun ρ : ↥onLineSet => ledgerTerm z ρ.val)]
  exact tsum_congr fun x => by
    show pairValue z x = ledgerTerm z (zeroOfSub x)
    rw [pairValue_eq_ledger_shape]
    rfl

/-! ## The decomposition -/

/-- The off-line packet sum: the ledger terms of the off-line zeros alone. -/
noncomputable def offLinePacketSum (z : ℂ) : ℂ :=
  ∑' ρ : ↥onLineSetᶜ, ledgerTerm z ρ.val

/-- **The channel decomposition** — brick 2, unconditional: on the off-real set,
away from the chart images of zeros, the certified target minus the tower's
unconditional limit is exactly the off-line packet sum. -/
theorem channel_decomposition {C : ℂ}
    (hC : ∀ z : ℂ, (1 / 2 + Complex.I * z) ∉ ZD.NontrivialZeros →
      xiChannel z = C + xiZeroResolventTrace z)
    {z : ℂ} (hznot : (1 / 2 + Complex.I * z) ∉ ZD.NontrivialZeros) :
    (-Complex.I * xiChannel z) - (-Complex.I * C) =
      onLineLedgerLimit z + offLinePacketSum z := by
  rw [canonicalTarget_eq_rotatedLedger hC hznot,
    neg_I_mul_trace_eq_tsum_ledgerTerm,
    onLineLedgerLimit_eq_tsum_onLine]
  unfold offLinePacketSum
  exact ((summable_ledgerTerm z).tsum_subtype_add_tsum_subtype_compl onLineSet).symm

/-- **Under the certified box, the off-line packets vanish** at every admissible
chart point: the box gives function agreement (brick 1), and the decomposition
identifies the discrepancy with the off-line packet sum. -/
theorem offLinePackets_vanish_of_box {C : ℂ}
    (hC : ∀ z : ℂ, (1 / 2 + Complex.I * z) ∉ ZD.NontrivialZeros →
      xiChannel z = C + xiZeroResolventTrace z)
    (hbox : TendstoLocallyUniformlyOn
      (fun n => normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
        (symmetrizedLineTowerOffsets n))
      (fun z => (-Complex.I * xiChannel z) - (-Complex.I * C)) atTop offReal)
    {z : ℂ} (him : z.im ≠ 0)
    (hznot : (1 / 2 + Complex.I * z) ∉ ZD.NontrivialZeros) :
    offLinePacketSum z = 0 := by
  have heq := (traceLimit_box_iff_eqOn C).mp hbox
  have hz : z ∈ offReal := him
  have h1 : onLineLedgerLimit z =
      (-Complex.I * xiChannel z) - (-Complex.I * C) := heq hz
  have h2 := channel_decomposition hC hznot
  rw [← h1] at h2
  have h3 : onLineLedgerLimit z + offLinePacketSum z =
      onLineLedgerLimit z + 0 := by
    rw [add_zero]
    exact h2.symm
  exact add_left_cancel h3

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.ledgerTerm_norm_le_of_im_large
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.summable_ledgerTerm
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.channel_decomposition
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.offLinePackets_vanish_of_box
