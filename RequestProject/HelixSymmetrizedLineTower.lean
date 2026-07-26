import RequestProject.HelixLineTowerHadamard
import RequestProject.ZetaContourXiReceiverIdentification3D

/-!
# The symmetrized line tower: both half-planes, like compared with like

The line tower indexes the upper-half on-line census, while the compiled Hadamard ledger sums
every nontrivial zero in both half-planes.  This file symmetrizes the tower by the conjugation
involution: each window axis acquires a conjugate partner whose spectral value is the negated
ordinate — the exact pole parameter of the conjugate zero, whose membership in the ledger is
the compiled `conj_mem_nontrivialZeros`.

With the symmetrized spectrum and the canonical Hadamard offsets on both legs, the capstone
`rh_of_symmetrizedLineTower_canonicalTraceLimit` restates the wall with no half-plane
mismatch: the single open box `hlim` now reads — **the two-sided on-line images of the window,
normalized by their canonical counterterms, exhaust the full Hadamard ledger** — so what would
break it is exactly an off-line zero's unmatched contribution, nothing bookkeeping-shaped.
`symmetrizedTrace_eq_pairedSum` displays each stage as the window sum of conjugate-paired
terms.  Nothing here proves `hlim`.  No RH/GRH is assumed anywhere in this file.
-/

open Filter Topology Complex

namespace CriticalLinePhasor.CaptureInterfaceAudit

open CriticalLinePhasor.ResidueJump CriticalLinePhasor.HilbertPolya
open CriticalLinePhasor.CarrierScale CriticalLinePhasor.XiChannel

/-! ## The symmetrized spectrum and offsets -/

/-- The symmetrized line-tower spectrum: each window axis and its conjugate partner, whose
spectral value is the negated ordinate. -/
noncomputable def symmetrizedLineTowerSpectrum (n : ℕ) :
    WindowIndex (n : ℝ) ⊕ WindowIndex (n : ℝ) → ℝ :=
  Sum.elim (lineTowerSpectrum n) (fun p => -(lineTowerSpectrum n p))

/-- The canonical Hadamard offsets on both legs: `I/ρ` on the upper leg, `I/ρ̄` on the
conjugate leg. -/
noncomputable def symmetrizedLineTowerOffsets (n : ℕ) :
    WindowIndex (n : ℝ) ⊕ WindowIndex (n : ℝ) → ℂ :=
  Sum.elim (lineTowerOffsets n)
    (fun p => Complex.I / (starRingEnd ℂ) (line (lineTowerSpectrum n p)))

/-! ## The two legs are genuine ledger members -/

/-- Every upper-leg window point is a nontrivial zero of ζ. -/
theorem lineTower_line_mem_nontrivialZeros (n : ℕ) (p : WindowIndex (n : ℝ)) :
    line (lineTowerSpectrum n p) ∈ ZD.NontrivialZeros :=
  ⟨by rw [line_re]; norm_num, by rw [line_re]; norm_num,
    lineTowerSpectrum_isZeroOrdinate n p⟩

/-- Every conjugate-leg partner is a nontrivial zero of ζ: the compiled conjugation transport
of the upper leg. -/
theorem lineTower_conj_mem_nontrivialZeros (n : ℕ) (p : WindowIndex (n : ℝ)) :
    (starRingEnd ℂ) (line (lineTowerSpectrum n p)) ∈ ZD.NontrivialZeros :=
  CriticalLinePhasor.ContourArgument.conj_mem_nontrivialZeros
    (lineTower_line_mem_nontrivialZeros n p)

/-- The conjugate partner's pole parameter is the negated ordinate — exactly the conjugate
leg's spectral value. -/
theorem poleParam_conj_line (γ : ℝ) :
    HelixLimit.poleParam ((starRingEnd ℂ) (line γ)) = ((-γ : ℝ) : ℂ) := by
  unfold HelixLimit.poleParam line lineC
  apply Complex.ext <;> simp

/-! ## The paired-stage display -/

/-- Each symmetrized stage is the window sum of conjugate-paired normalized terms. -/
theorem symmetrizedTrace_eq_pairedSum (n : ℕ) (z : ℂ) :
    normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
        (symmetrizedLineTowerOffsets n) z =
      ∑ p : WindowIndex (n : ℝ),
        (((z - ((lineTowerSpectrum n p : ℝ) : ℂ))⁻¹ + lineTowerOffsets n p) +
          ((z + ((lineTowerSpectrum n p : ℝ) : ℂ))⁻¹ +
            Complex.I / (starRingEnd ℂ) (line (lineTowerSpectrum n p)))) := by
  unfold normalizedSpectrumTrace symmetrizedLineTowerSpectrum symmetrizedLineTowerOffsets
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Sum.elim_inl, Sum.elim_inr]
  push_cast
  ring

/-! ## The symmetrized capstone -/

/-- **RH from the symmetrized line-tower limit — the wall with no half-plane mismatch.**  If
the two-sided window traces, normalized by the canonical Hadamard offsets on both legs,
converge locally uniformly off the real axis to the rotated ξ-channel minus its Hadamard
constant, Mathlib's `RiemannHypothesis` follows.  Both legs are proven ledger members
(`lineTower_line_mem_nontrivialZeros`, `lineTower_conj_mem_nontrivialZeros`), so the open box
`hlim` compares the ledger's full on-line contribution with the full ledger: what would break
it is exactly an off-line zero's unmatched term. -/
theorem rh_of_symmetrizedLineTower_canonicalTraceLimit
    (χ₁ : DirichletCharacter ℂ 1) (C : ℂ)
    (hlim : TendstoLocallyUniformlyOn
      (fun n => normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
        (symmetrizedLineTowerOffsets n))
      (fun z => (-Complex.I * xiChannel z) - (-Complex.I * C)) atTop offReal) :
    RiemannHypothesis := by
  refine HelixLimit.RH_of_GRH_Trivial_Char χ₁ (fun _ hρ => ?_)
  exact re_half_of_traceLimit symmetrizedLineTowerSpectrum symmetrizedLineTowerOffsets
    (fun z => -Complex.I * xiChannel z) (fun _ => -Complex.I * C)
    (differentiable_const _) hlim
    (resonance_const_mul (neg_ne_zero.mpr Complex.I_ne_zero)
      (xiChannel_resonates (mem_ZD_nontrivialZeros_of_modOne hρ)))

/-! ## The literal ledger identification -/

/-- The upper leg's pole parameter is the ordinate itself. -/
theorem poleParam_line (γ : ℝ) :
    HelixLimit.poleParam (line γ) = ((γ : ℝ) : ℂ) := by
  unfold HelixLimit.poleParam line lineC
  apply Complex.ext <;> simp

/-- A sum over the window's spectral atoms of any function of the ordinate is the
multiplicity-weighted windowed trace. -/
theorem sum_windowIndex_eq_windowedTrace (h : ℝ → ℂ) (T : ℝ) :
    (∑ p : WindowIndex T, h p.1.1) = windowedTrace h T := by
  classical
  rw [← trace_diagonal_eq_windowedTrace, Matrix.trace_diagonal]

/-- **The paired stage term is the rotated ledger's unit term pair**: at ordinate `γ`, the
symmetrized tower's summand equals `−I` times the compiled Hadamard ledger's unit term at
`ρ = line γ` plus `−I` times the unit term at its conjugate. -/
theorem pairedTerm_eq_rotatedLedgerTerms (z : ℂ) (γ : ℝ) :
    (((z - ((γ : ℝ) : ℂ))⁻¹ + Complex.I / line γ) +
      ((z + ((γ : ℝ) : ℂ))⁻¹ + Complex.I / (starRingEnd ℂ) (line γ))) =
      -Complex.I * (Complex.I * (z - HelixLimit.poleParam (line γ))⁻¹ - 1 / line γ) +
        -Complex.I * (Complex.I *
          (z - HelixLimit.poleParam ((starRingEnd ℂ) (line γ)))⁻¹ -
            1 / (starRingEnd ℂ) (line γ)) := by
  rw [poleParam_line, poleParam_conj_line]
  push_cast
  rw [sub_neg_eq_add]
  have h1 : -Complex.I * (Complex.I * (z - (γ : ℂ))⁻¹ - 1 / line γ) =
      (z - (γ : ℂ))⁻¹ + Complex.I / line γ := by
    field_simp
    linear_combination (-(z - (γ : ℂ))⁻¹) * Complex.I_sq
  have h2 : -Complex.I * (Complex.I * (z + (γ : ℂ))⁻¹ -
      1 / (starRingEnd ℂ) (line γ)) =
      (z + (γ : ℂ))⁻¹ + Complex.I / (starRingEnd ℂ) (line γ) := by
    field_simp
    linear_combination (-(z + (γ : ℂ))⁻¹) * Complex.I_sq
  rw [h1, h2]

/-- **Each symmetrized stage is a multiplicity-weighted window partial sum of the rotated
Hadamard ledger.**  The tower's stage at height `n` equals the windowed trace of the
conjugate-paired, `−I`-rotated ledger unit terms — so the open box `hlim` reads literally:
these windowed partial sums of the compiled ledger converge, locally uniformly off the real
axis, to its full two-sided sum. -/
theorem symmetrizedTrace_eq_windowedLedgerSum (n : ℕ) (z : ℂ) :
    normalizedSpectrumTrace (symmetrizedLineTowerSpectrum n)
        (symmetrizedLineTowerOffsets n) z =
      windowedTrace (fun γ =>
        -Complex.I * (Complex.I * (z - HelixLimit.poleParam (line γ))⁻¹ - 1 / line γ) +
          -Complex.I * (Complex.I *
            (z - HelixLimit.poleParam ((starRingEnd ℂ) (line γ)))⁻¹ -
              1 / (starRingEnd ℂ) (line γ))) (n : ℝ) := by
  rw [symmetrizedTrace_eq_pairedSum,
    ← sum_windowIndex_eq_windowedTrace (fun γ =>
      -Complex.I * (Complex.I * (z - HelixLimit.poleParam (line γ))⁻¹ - 1 / line γ) +
        -Complex.I * (Complex.I *
          (z - HelixLimit.poleParam ((starRingEnd ℂ) (line γ)))⁻¹ -
            1 / (starRingEnd ℂ) (line γ))) (n : ℝ)]
  apply Finset.sum_congr rfl
  intro p _
  rw [← pairedTerm_eq_rotatedLedgerTerms z p.1.1]
  rfl

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.poleParam_line
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.sum_windowIndex_eq_windowedTrace
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.pairedTerm_eq_rotatedLedgerTerms
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.symmetrizedTrace_eq_windowedLedgerSum
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.lineTower_line_mem_nontrivialZeros
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.lineTower_conj_mem_nontrivialZeros
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.poleParam_conj_line
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.symmetrizedTrace_eq_pairedSum
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.rh_of_symmetrizedLineTower_canonicalTraceLimit
