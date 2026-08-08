import RequestProject.HelixChannelDecomposition
import RequestProject.LedgerAssembly

/-!
# The fusion: the S(t) hub and the tower certificate are one wall

Brick 3 of the interior program.  The S(t) thread's residual Prop
(`IntegratedDefectSublinear` — the running integral of the off-line defect ledger is
sublinear) and the GRH companion's certified trace-limit box were two equivalence
webs certifying the same wall through different instruments.  This file fuses them:

* **`integratedDefectSublinear_iff_riemannHypothesis`** — the S(t) hub's residual is
  equivalent to Mathlib's `RiemannHypothesis`.  Forward: sublinearity forces the
  coordinate identity at every good height (the compiled criterion), while an
  off-line zero would make the coordinate defect strictly positive at any good
  height above its ordinate (the compiled strict-positivity theorem, order
  positivity included) — upper-half representative supplied by conjugation.
  Backward: under RH every ledger member has real part `½` (compiled extraction),
  so the off-line census vanishes identically and the integral is literally zero.
* **`integratedDefectSublinear_iff_box`** — composed with the certified
  biconditional: the S(t) residual is equivalent to the trace-limit box.  The five
  faces of the S(t) hub, the coordinate identity, Mathlib's `RiemannHypothesis`,
  and the tower's trace-limit box are now ONE compiled equivalence class — every
  instrument pointed at one wall, machine-checked mutually equivalent.

Proven in this file: both equivalences, unconditionally.
-/

open Filter Topology Complex Asymptotics

namespace CriticalLinePhasor.CaptureInterfaceAudit

open CriticalLinePhasor.ContourArgument
open CriticalLinePhasor.ResidueJump CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.XiChannel CriticalLinePhasor.ResolventLimit

/-- **Sublinear integrated defect forces the Riemann Hypothesis**: the compiled
criterion gives the coordinate identity at every good height, while an off-line
zero would make the defect strictly positive at any good height above its
ordinate. -/
theorem riemannHypothesis_of_integratedDefectSublinear
    (h : IntegratedDefectSublinear) : RiemannHypothesis := by
  intro s hzero htriv hs1
  have htriv' : ∀ n : ℕ, s ≠ -2 * ((n : ℂ) + 1) := fun n hn => htriv ⟨n, hn⟩
  have hbounds := riemannZeta_nontrivial_zero_re_bounds hzero htriv'
  have hmem : s ∈ ZD.NontrivialZeros := ⟨hbounds.1, hbounds.2, hzero⟩
  by_contra hoff
  have him2 : 2 ≤ |s.im| := riemannZeta_nontrivial_zero_im_ge_two hzero htriv'
  -- an upper-half off-line representative, by conjugation if necessary
  obtain ⟨ρ', hρ'mem, hρ'off, hρ'im⟩ :
      ∃ ρ', ρ' ∈ ZD.NontrivialZeros ∧ ρ'.re ≠ 1 / 2 ∧ 0 < ρ'.im := by
    by_cases hpos : 0 < s.im
    · exact ⟨s, hmem, hoff, hpos⟩
    · push_neg at hpos
      have himne : s.im ≠ 0 := by
        intro h0
        rw [h0] at him2
        norm_num at him2
      have himneg : s.im < 0 := lt_of_le_of_ne hpos himne
      refine ⟨(starRingEnd ℂ) s,
        CriticalLinePhasor.ContourArgument.conj_mem_nontrivialZeros hmem, ?_, ?_⟩
      · rw [Complex.conj_re]
        exact hoff
      · rw [Complex.conj_im]
        linarith
  obtain ⟨T, hTgt, hT⟩ := exists_goodHeight_gt ρ'.im
  have hρ'strip : ρ' ∈ stripZeroFinset T :=
    (stripZeroWindow_finite T).mem_toFinset.mpr ⟨hρ'mem, hρ'im, le_of_lt hTgt⟩
  have hposdefect :=
    classicalSContour_sub_Smult_pos_of_offCarrier hT hρ'strip hρ'off
  have hid := globalCoordinateIdentification_of_integral_sublinear h T hT
  rw [hid] at hposdefect
  simp at hposdefect

/-- **The Riemann Hypothesis forces sublinearity**: under RH the off-line census
vanishes identically, so the integrated defect is literally the zero function. -/
theorem integratedDefectSublinear_of_riemannHypothesis
    (hRH : RiemannHypothesis) : IntegratedDefectSublinear := by
  have hcount : ∀ t : ℝ, offLineStripZeroCountMult t = 0 := by
    intro t
    classical
    unfold offLineStripZeroCountMult
    apply Finset.sum_eq_zero
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    have hmem := ((stripZeroWindow_finite t).mem_toFinset.mp hρ.1).1
    exact absurd (re_eq_half_of_riemannHypothesis hRH hmem) hρ.2
  have hfun : (fun T => ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ))
      = fun _ => (0 : ℝ) := by
    funext T
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))
      (fun t _ => by rw [hcount t, Nat.cast_zero])]
    simp
  show (fun T => ∫ t in (0:ℝ)..T, (offLineStripZeroCountMult t : ℝ))
      =o[atTop] fun T : ℝ => T
  rw [hfun]
  exact isLittleO_zero _ _

/-- **THE FUSION** — the S(t) hub's residual Prop is Mathlib's `RiemannHypothesis`:
the two certificates certify one wall. -/
theorem integratedDefectSublinear_iff_riemannHypothesis :
    IntegratedDefectSublinear ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_integratedDefectSublinear,
    integratedDefectSublinear_of_riemannHypothesis⟩

/-- **The fused certificate**: the S(t) residual is equivalent to the tower's
trace-limit box.  Every face of both webs — the coordinate identity, kernel
coupling, no radial drift, native certificates, ξ-channel regularity, the
integrated defect, `RiemannHypothesis`, and the trace limit — is now one compiled
equivalence class. -/
theorem integratedDefectSublinear_iff_box :
    ∃ C : ℂ, (IntegratedDefectSublinear ↔
      TendstoLocallyUniformlyOn
        (fun n => normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
          (symmetrizedLineTowerOffsets n))
        (fun z => (-Complex.I * xiChannel z) - (-Complex.I * C)) atTop offReal) := by
  obtain ⟨C, hC⟩ := rh_iff_symmetrizedLineTower_traceLimit
  exact ⟨C, integratedDefectSublinear_iff_riemannHypothesis.trans hC⟩

/-! ## The principle: vanishing cannot happen in 3D off the midpoint axis -/

/-- **The 3D source casts no off-axis singularity — unconditionally.**  The tower's
limit is holomorphic on the whole off-real set: every stage is a real-spectrum
Hermitian trace with all poles on the axis (spectral reality is the whole
mechanism), and holomorphy survives the locally uniform limit.  This is the
compiled chart form of the principle that vanishing cannot happen in 3D off the
midpoint axis: the 3D-sourced side of the wall has no off-axis singularities to
offer. -/
theorem onLineLedgerLimit_differentiableOn :
    DifferentiableOn ℂ onLineLedgerLimit offReal := by
  have hopen : IsOpen offReal := by
    have h : offReal = Complex.im ⁻¹' {(0 : ℝ)}ᶜ := rfl
    rw [h]
    exact isOpen_compl_singleton.preimage Complex.continuous_im
  exact symmetrizedLineTower_traceLimit_unconditional.differentiableOn
    (Filter.Eventually.of_forall fun n =>
      normalizedSpectrumTrace_differentiableOn _ _) hopen

/-- **Under the box, the chart channel is exactly as regular as its 3D source**:
the shadow carries no singularity the source didn't cast. -/
theorem channel_differentiableOn_of_box {C : ℂ}
    (hbox : TendstoLocallyUniformlyOn
      (fun n => normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
        (symmetrizedLineTowerOffsets n))
      (fun z => (-Complex.I * xiChannel z) - (-Complex.I * C)) atTop offReal) :
    DifferentiableOn ℂ
      (fun z => (-Complex.I * xiChannel z) - (-Complex.I * C)) offReal := by
  have heq := (traceLimit_box_iff_eqOn C).mp hbox
  exact onLineLedgerLimit_differentiableOn.congr fun z hz => (heq hz).symm

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.onLineLedgerLimit_differentiableOn
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.channel_differentiableOn_of_box
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.riemannHypothesis_of_integratedDefectSublinear
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.integratedDefectSublinear_of_riemannHypothesis
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.integratedDefectSublinear_iff_riemannHypothesis
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.integratedDefectSublinear_iff_box
