import RequestProject.HelixLineTowerCapture
import RequestProject.XiZeroLedgerResolvent3D

/-!
# Pinning the line-tower limit to the compiled Hadamard ledger

`HelixLineTowerCapture` leaves the tower's per-stage offsets `c` and the entire correction `E`
free.  The compiled Hadamard identity (`xiChannel_eq_constant_add_zeroResolventTrace`) pins
both: the ξ-channel is one constant plus the regularized ledger trace
`∑ m_ρ (I·(z − poleParam ρ)⁻¹ − 1/ρ)`.  Rotating by `−I` puts every term in the exact
`normalizedSpectrumTrace` shape `(z − d)⁻¹ + c` with the **canonical offsets** `c_ρ = I/ρ`
(`lineTowerOffsets`), and the entire correction degenerates to the constant `−I·C`.

The capstone `rh_of_lineTower_canonicalTraceLimit`: if the line tower's canonically-normalized
traces converge locally uniformly off the real axis to the rotated ξ-channel minus that
constant, Mathlib's `RiemannHypothesis` follows.  `canonicalTarget_eq_rotatedLedger` then shows
the target is, pointwise off the zero images, exactly `−I` times the compiled ledger trace —
so the one open box `hlim` reads literally: **the on-line window partial sums of the normalized
Hadamard ledger exhaust its full two-sided sum**.  The tower indexes the on-line census with
multiplicity; the full ledger sums every nontrivial zero in both half-planes.  Their agreement
in the limit is the coverage wall — off-line or unmatched terms are precisely what would break
it.  Nothing here proves `hlim`; the resonance (`xiChannel_resonates`), the per-stage off-real
holomorphy, the Weierstrass step, and the mod-one hinge are all compiled.  No RH/GRH is assumed
anywhere in this file.
-/

open Filter Topology Complex

namespace CriticalLinePhasor.CaptureInterfaceAudit

open CriticalLinePhasor.ResidueJump CriticalLinePhasor.HilbertPolya
open CriticalLinePhasor.CarrierScale CriticalLinePhasor.XiChannel

/-! ## Transport lemmas -/

/-- Resonance is preserved by a nonzero scalar rotation of the channel. -/
theorem resonance_const_mul {T : ℂ → ℂ} {a : ℂ} (ha : a ≠ 0) {w : ℂ}
    (hres : ¬ ∃ L, Tendsto T (𝓝[≠] w) (𝓝 L)) :
    ¬ ∃ L, Tendsto (fun z => a * T z) (𝓝[≠] w) (𝓝 L) := by
  rintro ⟨L, hL⟩
  refine hres ⟨a⁻¹ * L, ?_⟩
  refine (hL.const_mul a⁻¹).congr fun z => ?_
  field_simp

/-- The mod-one spectral zeros are the classical nontrivial zeros of ζ. -/
theorem mem_ZD_nontrivialZeros_of_modOne {χ₁ : DirichletCharacter ℂ 1} {ρ : ℂ}
    (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ₁) : ρ ∈ ZD.NontrivialZeros := by
  obtain ⟨h0, h1, hz⟩ := hρ
  refine ⟨h0, h1, ?_⟩
  rwa [DirichletCharacter.LFunction_modOne_eq] at hz

/-! ## The canonical offsets and the rotated ledger -/

/-- **The canonical Hadamard offsets of the line tower**: `c_p = I/ρ_p` at the window zero
`ρ_p = ½ + iγ_p` — the per-axis convergence counterterm the compiled ledger prescribes, read
through the `−I` chart rotation. -/
noncomputable def lineTowerOffsets (n : ℕ) : WindowIndex (n : ℝ) → ℂ :=
  fun p => Complex.I / line p.1.1

/-- **The rotated ledger is a normalized spectrum trace over the full zero set**: `−I` times the
compiled Hadamard trace has every term in the exact `(z − d)⁻¹ + c` shape, with `d` the pole
parameter and `c = I/ρ` — the shape the line tower's stages carry. -/
theorem neg_I_mul_xiZeroResolventTrace (z : ℂ) :
    -Complex.I * xiZeroResolventTrace z =
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((z - HelixLimit.poleParam ρ.val)⁻¹ + Complex.I / ρ.val) := by
  unfold xiZeroResolventTrace
  rw [← tsum_mul_left]
  apply tsum_congr
  intro ρ
  field_simp
  ring_nf
  linear_combination
    (-((ZD.xiOrderNat ρ.val : ℂ) * (z - HelixLimit.poleParam ρ.val)⁻¹)) *
      Complex.I_sq

/-! ## The pinned capstone -/

/-- **RH from the canonically-pinned line-tower limit.**  If the line tower's traces, normalized
by the canonical Hadamard offsets `I/ρ`, converge locally uniformly off the real axis to the
rotated ξ-channel minus its Hadamard constant, then Mathlib's `RiemannHypothesis` holds.  The
resonance is the compiled `xiChannel_resonates`, rotated; the entire correction is the constant
`−I·C`; per-stage holomorphy, Weierstrass, and the mod-one hinge are compiled. -/
theorem rh_of_lineTower_canonicalTraceLimit (χ₁ : DirichletCharacter ℂ 1) (C : ℂ)
    (hlim : TendstoLocallyUniformlyOn
      (fun n => normalizedSpectrumTrace (lineTowerSpectrum n) (lineTowerOffsets n))
      (fun z => (-Complex.I * xiChannel z) - (-Complex.I * C)) atTop offReal) :
    RiemannHypothesis := by
  refine HelixLimit.RH_of_GRH_Trivial_Char χ₁ (fun _ hρ => ?_)
  exact re_half_of_traceLimit lineTowerSpectrum lineTowerOffsets
    (fun z => -Complex.I * xiChannel z) (fun _ => -Complex.I * C)
    (differentiable_const _) hlim
    (resonance_const_mul (neg_ne_zero.mpr Complex.I_ne_zero)
      (xiChannel_resonates (mem_ZD_nontrivialZeros_of_modOne hρ)))

/-- **The target is the rotated compiled ledger, pointwise.**  Off the zero images, the
capstone's limit target equals `−I` times the compiled Hadamard trace — so the single open box
`hlim` reads literally: the on-line window partial sums of the normalized ledger exhaust its
full two-sided sum.  The witness for `hC` is the compiled
`xiChannel_eq_constant_add_zeroResolventTrace`. -/
theorem canonicalTarget_eq_rotatedLedger {C : ℂ}
    (hC : ∀ z : ℂ, (1 / 2 + Complex.I * z) ∉ ZD.NontrivialZeros →
      xiChannel z = C + xiZeroResolventTrace z)
    {z : ℂ} (hz : (1 / 2 + Complex.I * z) ∉ ZD.NontrivialZeros) :
    (-Complex.I * xiChannel z) - (-Complex.I * C) =
      -Complex.I * xiZeroResolventTrace z := by
  rw [hC z hz]
  ring

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.resonance_const_mul
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.mem_ZD_nontrivialZeros_of_modOne
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.neg_I_mul_xiZeroResolventTrace
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.rh_of_lineTower_canonicalTraceLimit
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.canonicalTarget_eq_rotatedLedger
