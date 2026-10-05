import RequestProject.HelixLedgerPairing
import RequestProject.DifferencedResolvent

/-!
# The symmetrized line tower's finite stages, on the two-sided event index

The symmetrized line tower's capstone (`rh_of_symmetrizedLineTower_canonicalTraceLimit`) puts
every zero on the line **from** the trace-limit box `hlim`.  This file compiles the finite-stage
bookkeeping that the tower's convergence runs on:

* **The two-sided window finsets** (`windowFinset`, `pairFinset`): one event copy per conjugate
  leg, monotone and cofinal (`pairFinset_monotone`, `tendsto_pairFinset_atTop`), with every
  index outside the `n`-th finset of ordinate above `n` (`lt_ordinate_of_not_mem_pairFinset`).
* **The finite-stage identification** (`stage_eq_pairSum`): each symmetrized tower stage *is*
  the finite partial sum of the ledger family over the two-sided window finset — the compiled
  `symmetrizedTrace_eq_windowedLedgerSum`, re-indexed.

The unconditional convergence of the stages is `HelixTowerUnconditionalConvergence.lean`.
-/

open Filter Topology Complex

namespace CriticalLinePhasor.CaptureInterfaceAudit

open CriticalLinePhasor.ResidueJump CriticalLinePhasor.HilbertPolya
open CriticalLinePhasor.CarrierScale CriticalLinePhasor.XiChannel
open CriticalLinePhasor.ResolventLimit CriticalLinePhasor.ContourArgument

/-! ## §1 Chart basics -/

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

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.stage_eq_pairSum
