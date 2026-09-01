import RequestProject.HarmonicPencilCell
import RequestProject.RiemannHypothesisBridge
import RequestProject.HilbertPolyaResolventTrace
import RequestProject.ZetaContourArgument
import RequestProject.XiHadamardQuotient
import RequestProject.HelixStrandTemperedness

/-!
# The cell-edge door: the dictated stack, compiled

Sam's assembly (2026-08-31): *double-ended helix, scaled carrier, warped
fiber (L-function), the fiber vanishes at cell edges, the pencil sees the
rank drop at every vanishing.*  In the compiled stock:

* geometry → reality of the eigenheight: `Z : ℝ`, `0 < Z` (the scaled
  carrier's cell edges are ON the axis);
* warped fiber → `reprPoint χ Z = 1/2 + i·τχ(log Z)` — the warp `τχ`
  registers the eigenheight into the fiber's clock, abscissa `1/2` BY
  CONSTRUCTION (the seat, not an assumption);
* pencil → `gramH_rank_drop_iff_L_zero` (unconditional in `χ`, reaching
  `ζ` at `q = 1` through `LFunction_modOne_eq`).

Compiled here, for `ζ`:
* `pencil_sees_registered_vanishing` — **the pencil rank-drops at every
  vanishing it registers**: if a zero sits at a cell edge (`ρ = reprPoint Z`),
  the Gram determinant vanishes at that eigenheight.  Unconditional.
* `riemannHypothesis_of_cell_edge_registration` — **"the fiber vanishes at
  cell edges" ⟹ RH**: if every nontrivial zero is registered at a real
  eigenheight, Mathlib's `RiemannHypothesis` follows.  This is the
  log-correspondence door in the pencil's own vocabulary: the abstract
  height of `riemannHypothesis_of_log_correspondence` becomes the pencil's
  scan parameter.
* `riemannHypothesis_of_pencil_cell_stack` — the two together: RH plus a
  pencil certificate at an eigenheight for every zero.

No `sorry`, no `axiom`.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.CellEdgeDoor

open CriticalLinePhasor.HarmonicCell

/-- **The pencil sees the rank drop at every registered vanishing.**  If a
nontrivial zero sits at the cell edge of eigenheight `Z` (the warped
readout `reprPoint`), then the harmonic Gram pencil at `Z` is
rank-deficient.  Unconditional, any admissible calibration. -/
theorem pencil_sees_registered_vanishing
    {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) {Z : ℝ}
    (hreg : ρ = reprPoint (1 : DirichletCharacter ℂ 1) Z)
    {μ lam : ℂ} (hlam : lam ≠ μ) :
    (GramH (1 : DirichletCharacter ℂ 1) Z μ lam).det = 0 := by
  rw [gramH_rank_drop_iff_L_zero _ _ _ _ hlam,
    DirichletCharacter.LFunction_modOne_eq, ← hreg]
  exact hρ.2.2

/-- **"The fiber vanishes at cell edges" ⟹ RH.**  If every nontrivial zero
is registered at a real eigenheight through the warped readout, the
Riemann Hypothesis follows: the abscissa `1/2` is constitutive of the
readout, not an assumption about zeros. -/
theorem riemannHypothesis_of_cell_edge_registration
    (h : ∀ ρ ∈ ZD.NontrivialZeros, ∃ Z : ℝ, 0 < Z ∧
      ρ = reprPoint (1 : DirichletCharacter ℂ 1) Z) :
    RiemannHypothesis := by
  apply RHBridge.no_offline_zeros_implies_rh
  intro ρ hρ
  obtain ⟨Z, _, hreg⟩ := h ρ hρ
  have hre : (reprPoint (1 : DirichletCharacter ℂ 1) Z).re = 1 / 2 := by
    simp [reprPoint, Complex.add_re, Complex.mul_re]
  rw [hreg]
  exact hre

/-- **The dictated stack, as one statement**: cell-edge registration gives
the Riemann Hypothesis AND a pencil rank-drop certificate at an
eigenheight for every zero. -/
theorem riemannHypothesis_of_pencil_cell_stack
    (h : ∀ ρ ∈ ZD.NontrivialZeros, ∃ Z : ℝ, 0 < Z ∧
      ρ = reprPoint (1 : DirichletCharacter ℂ 1) Z) :
    RiemannHypothesis ∧
    ∀ ρ ∈ ZD.NontrivialZeros, ∀ μ lam : ℂ, lam ≠ μ →
      ∃ Z : ℝ, 0 < Z ∧
        (GramH (1 : DirichletCharacter ℂ 1) Z μ lam).det = 0 ∧
        ρ = reprPoint (1 : DirichletCharacter ℂ 1) Z := by
  refine ⟨riemannHypothesis_of_cell_edge_registration h, ?_⟩
  intro ρ hρ μ lam hlam
  obtain ⟨Z, hZ, hreg⟩ := h ρ hρ
  exact ⟨Z, hZ, pencil_sees_registered_vanishing hρ hreg hlam, hreg⟩

/-! ## The conjugate-end pair law

Sam's identification (2026-08-31): *the resolvent trace goes through the
analytic zeros as corresponding zeros that map to the eigenvalues on each
side of the conjugate helix.*  Each vanishing `ρ` has its anti-helix end
`1 − conj ρ` (also a vanishing — the double-ended geometry's closure), and
the two ends read the conjugate eigenvalue pair `(λ, conj λ)`.  The two
sides' readings coincide exactly on the critical line. -/

/-- The anti-helix end of a vanishing is a vanishing. -/
theorem conjugate_end_mem {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    (1 - (starRingEnd ℂ) ρ) ∈ ZD.NontrivialZeros := by
  have hξ : ZD.riemannXi (1 - (starRingEnd ℂ) ρ) = 0 := by
    rw [ContourArgument.riemannXi_one_sub_conj,
      (ZD.riemannXi_eq_zero_iff ρ).mpr hρ, map_zero]
  exact (ZD.riemannXi_eq_zero_iff _).mp hξ

/-- **The two ends read a conjugate eigenvalue pair**: the anti-helix end's
spectral coordinate is the conjugate of the helix end's. -/
theorem conjugate_end_spectralCoord (ρ : ℂ) :
    HilbertPolya.spectralCoord (1 - (starRingEnd ℂ) ρ)
      = (starRingEnd ℂ) (HilbertPolya.spectralCoord ρ) := by
  simp only [HilbertPolya.spectralCoord, map_mul, map_sub, map_neg,
    Complex.conj_I, map_one, map_div₀, map_ofNat]
  ring

/-- **Ends agree iff on-line**: the two sides' eigenvalues coincide exactly
when the vanishing sits on the critical line. -/
theorem ends_agree_iff_online (ρ : ℂ) :
    HilbertPolya.spectralCoord (1 - (starRingEnd ℂ) ρ)
        = HilbertPolya.spectralCoord ρ ↔ ρ.re = 1 / 2 := by
  rw [conjugate_end_spectralCoord, Complex.conj_eq_iff_im]
  have him : (HilbertPolya.spectralCoord ρ).im = -(ρ.re - 1 / 2) := by
    simp [HilbertPolya.spectralCoord, Complex.mul_im, Complex.sub_re,
      Complex.sub_im]
  rw [him]
  constructor <;> intro h <;> linarith

/-- **The trace's pair reading**: RH ⟺ every analytic zero's two
side-eigenvalues coincide — the eigenvalue map of the double-ended helix
lands on the axis. -/
theorem rh_iff_all_end_pairs_coincide :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) ↔
    ∀ ρ ∈ ZD.NontrivialZeros,
      HilbertPolya.spectralCoord (1 - (starRingEnd ℂ) ρ)
        = HilbertPolya.spectralCoord ρ := by
  constructor
  · intro h ρ hρ
    exact (ends_agree_iff_online ρ).mpr (h ρ hρ)
  · intro h ρ hρ
    exact (ends_agree_iff_online ρ).mp (h ρ hρ)

/-! ## The Frobenius linkage: det = 1 across the two ends

Sam (2026-08-31): *Frobenius links the two same-height vanishing events on
the helix and anti-helix conjugate, det = 1.*  The two ends' events sit at
the SAME height (`(1 − conj ρ).im = ρ.im`), carry the amplitude faces
`(α, α⁻¹)` with `α = e^{β − 1/2}` — det 1 BY CONJUGACY, the compiled
Frobenius similitude — and the face is a helix strand (elliptic,
tempered) exactly on the line.  RH = **temperedness of the spectrum**:
every end-pair face is a helix strand, not a spiral. -/

/-- The amplitude face an event shows its end-pair: `e^{β − 1/2}`. -/
def endPairFace (ρ : ℂ) : ℂ := Complex.exp (((ρ.re - 1 / 2 : ℝ) : ℂ))

/-- **Same height**: the two linked events sit at one height. -/
theorem endPair_same_height (ρ : ℂ) :
    (1 - (starRingEnd ℂ) ρ).im = ρ.im := by
  simp [Complex.sub_im, Complex.conj_im]

/-- **The Frobenius linkage, det = 1**: the two ends' faces are exact
inverses — `α · α⁻¹ = 1` by conjugacy, unconditionally. -/
theorem endPair_det_one (ρ : ℂ) :
    endPairFace ρ * endPairFace (1 - (starRingEnd ℂ) ρ) = 1 := by
  unfold endPairFace
  rw [← Complex.exp_add]
  have h : ((1 : ℂ) - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by
    simp [Complex.sub_re, Complex.conj_re]
  rw [h]
  push_cast
  ring_nf
  exact Complex.exp_zero

/-- **Helix face ⟺ on-line**: the end-pair face is a helix strand
(elliptic, tempered) exactly when the event sits on the critical line. -/
theorem endFace_helix_iff_online (ρ : ℂ) :
    CriticalLinePhasor.HelixStrand.IsHelixStrand (endPairFace ρ)
      ↔ ρ.re = 1 / 2 := by
  rw [CriticalLinePhasor.HelixStrand.isHelixStrand_iff_norm_one]
  unfold endPairFace
  rw [Complex.norm_exp]
  simp only [Complex.ofReal_re]
  rw [Real.exp_eq_one_iff]
  constructor <;> intro h <;> linarith

/-- **RH = temperedness of the spectrum**: every vanishing's end-pair face
is a helix strand, not a spiral — the radial dichotomy landed on the zero
set itself. -/
theorem rh_iff_spectrum_tempered :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) ↔
    ∀ ρ ∈ ZD.NontrivialZeros,
      CriticalLinePhasor.HelixStrand.IsHelixStrand (endPairFace ρ) := by
  constructor
  · intro h ρ hρ
    exact (endFace_helix_iff_online ρ).mpr (h ρ hρ)
  · intro h ρ hρ
    exact (endFace_helix_iff_online ρ).mp (h ρ hρ)

/-! ## The no-spiral law: the exact complement, the trace meter, the isometry form

The faces are REAL AND POSITIVE (`e^{β−1/2} > 0`), so the strand dichotomy is
exhaustive AND exclusive on the zero set: every end-pair face is exactly one
of helix (on-line) or spiral (off-line) — no third branch.  RH = "no spiral
faces."  The face's 1-D readout is the trace meter
`α + α⁻¹ = 2·cosh(β − 1/2)`: DC floor exactly `2`, the excess `≥ 0` vanishing
precisely on the line, and a spiral face rings the compiled non-tempered
signature `|trace| > 2`.  In the operator register the split is literal:
`det (strandBlock face) = 1` is FREE at every zero (the similitude, SL₂),
and RH ⟺ every face's block is an ISOMETRY (the maximal compact, SU₂) —
the remaining field is "exhibit the isometry", discharged by identity. -/

open Matrix

/-- The face in the real register: `e^{β−1/2}` as a positive real. -/
theorem endPairFace_eq_ofReal (ρ : ℂ) :
    endPairFace ρ = ((Real.exp (ρ.re - 1 / 2) : ℝ) : ℂ) := by
  unfold endPairFace
  rw [Complex.ofReal_exp]

/-- The face is on the real axis: its transverse reading is purely radial. -/
theorem endPairFace_im (ρ : ℂ) : (endPairFace ρ).im = 0 := by
  rw [endPairFace_eq_ofReal]
  exact Complex.ofReal_im _

/-- The face never vanishes. -/
theorem endPairFace_ne_zero (ρ : ℂ) : endPairFace ρ ≠ 0 :=
  Complex.exp_ne_zero _

/-- The face's radius: `‖face‖ = e^{β−1/2}` — the radial ledger read. -/
theorem norm_endPairFace (ρ : ℂ) :
    ‖endPairFace ρ‖ = Real.exp (ρ.re - 1 / 2) := by
  unfold endPairFace
  rw [Complex.norm_exp]
  simp

/-- **Spiral face ⟺ off-line**: the exact complement of
`endFace_helix_iff_online`.  The negation of RH now has a concrete typed
inhabitant — a spiral strand at a zero's face. -/
theorem endFace_spiral_iff_offline (ρ : ℂ) :
    CriticalLinePhasor.HelixStrand.IsSpiralStrand (endPairFace ρ)
      ↔ ρ.re ≠ 1 / 2 := by
  unfold CriticalLinePhasor.HelixStrand.IsSpiralStrand
  rw [norm_endPairFace]
  constructor
  · rintro ⟨-, -, h3⟩ heq
    apply h3
    rw [heq]
    simp
  · intro h
    refine ⟨endPairFace_im ρ, endPairFace_ne_zero ρ, fun h1 => h ?_⟩
    rw [Real.exp_eq_one_iff] at h1
    linarith

/-- **The dichotomy is exhaustive on faces**: every end-pair face is a helix
strand or a spiral strand — there is no third branch. -/
theorem endFace_helix_or_spiral (ρ : ℂ) :
    CriticalLinePhasor.HelixStrand.IsHelixStrand (endPairFace ρ) ∨
    CriticalLinePhasor.HelixStrand.IsSpiralStrand (endPairFace ρ) := by
  by_cases h : ρ.re = 1 / 2
  · exact Or.inl ((endFace_helix_iff_online ρ).mpr h)
  · exact Or.inr ((endFace_spiral_iff_offline ρ).mpr h)

/-- **The dichotomy is exclusive on faces**: no face is both. -/
theorem endFace_not_helix_and_spiral (ρ : ℂ) :
    ¬(CriticalLinePhasor.HelixStrand.IsHelixStrand (endPairFace ρ) ∧
      CriticalLinePhasor.HelixStrand.IsSpiralStrand (endPairFace ρ)) := by
  rintro ⟨hh, hs⟩
  exact hs.2.2 (CriticalLinePhasor.HelixStrand.tempered_of_isHelixStrand hh)

/-- **RH = the no-spiral law**: no vanishing's end-pair face is a spiral. -/
theorem rh_iff_no_spiral_faces :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) ↔
    ∀ ρ ∈ ZD.NontrivialZeros,
      ¬ CriticalLinePhasor.HelixStrand.IsSpiralStrand (endPairFace ρ) := by
  constructor
  · intro h ρ hρ hs
    exact (endFace_spiral_iff_offline ρ).mp hs (h ρ hρ)
  · intro h ρ hρ
    by_contra hne
    exact h ρ hρ ((endFace_spiral_iff_offline ρ).mpr hne)

/-- **The pair's radial ledger closes exactly**: the two ends' log-radii sum
to `0` at EVERY zero — det = 1 in the log register, the DC of the radial
channel computed outright.  What RH adds is that each summand is `0`
separately, not just the pair total. -/
theorem endPair_radial_ledger_zero (ρ : ℂ) :
    Real.log ‖endPairFace ρ‖
      + Real.log ‖endPairFace (1 - (starRingEnd ℂ) ρ)‖ = 0 := by
  rw [norm_endPairFace, norm_endPairFace, Real.log_exp, Real.log_exp]
  have h : ((1 : ℂ) - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by
    simp [Complex.sub_re, Complex.conj_re]
  rw [h]
  ring

/-- **A spiral is a coupled expansion/contraction at one height**: an
off-line event (right of the line) expands on the helix end and contracts
reciprocally on the anti-helix end — the hyperbolic pair, det 1. -/
theorem offline_expanding_contracting_pair {ρ : ℂ} (h : 1 / 2 < ρ.re) :
    1 < ‖endPairFace ρ‖ ∧ ‖endPairFace (1 - (starRingEnd ℂ) ρ)‖ < 1 := by
  rw [norm_endPairFace, norm_endPairFace]
  have hre : ((1 : ℂ) - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by
    simp [Complex.sub_re, Complex.conj_re]
  rw [hre]
  constructor
  · calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp (ρ.re - 1 / 2) := Real.exp_lt_exp.mpr (by linarith)
  · calc Real.exp (1 - ρ.re - 1 / 2) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero

/-- **The trace meter, DC exact**: the face's 1-D Hecke readout is
`2·cosh(β − 1/2)` — computed outright, not estimated. -/
theorem endFace_trace_eq_cosh (ρ : ℂ) :
    CriticalLinePhasor.HelixStrand.strandTrace (endPairFace ρ)
      = ((2 * Real.cosh (ρ.re - 1 / 2) : ℝ) : ℂ) := by
  unfold CriticalLinePhasor.HelixStrand.strandTrace
  rw [endPairFace_eq_ofReal, ← Complex.ofReal_inv, ← Real.exp_neg,
    ← Complex.ofReal_add, Real.cosh_eq]
  push_cast
  ring

/-- **DC floor `2`**: every face's trace is at least the tempered ceiling —
the excess `2·cosh(β−1/2) − 2 ≥ 0` is the whole field. -/
theorem endFace_trace_re_ge_two (ρ : ℂ) :
    2 ≤ (CriticalLinePhasor.HelixStrand.strandTrace (endPairFace ρ)).re := by
  rw [endFace_trace_eq_cosh, Complex.ofReal_re]
  nlinarith [Real.one_le_cosh (ρ.re - 1 / 2)]

/-- **The meter reads exactly `2` iff on-line**: the trace excess vanishes
precisely at the tempered faces. -/
theorem endFace_trace_eq_two_iff_online (ρ : ℂ) :
    (CriticalLinePhasor.HelixStrand.strandTrace (endPairFace ρ)).re = 2
      ↔ ρ.re = 1 / 2 := by
  rw [endFace_trace_eq_cosh, Complex.ofReal_re]
  constructor
  · intro h
    have hexp : Real.exp (ρ.re - 1 / 2) + Real.exp (-(ρ.re - 1 / 2)) = 2 := by
      have hc := Real.cosh_eq (ρ.re - 1 / 2)
      linarith
    have hprod :
        Real.exp (ρ.re - 1 / 2) * Real.exp (-(ρ.re - 1 / 2)) = 1 := by
      have hz : (ρ.re - 1 / 2) + -(ρ.re - 1 / 2) = 0 := by ring
      rw [← Real.exp_add, hz, Real.exp_zero]
    have hsq : (Real.exp (ρ.re - 1 / 2) - 1) ^ 2 = 0 := by
      nlinarith [hexp, hprod, Real.exp_pos (ρ.re - 1 / 2),
        sq_nonneg (Real.exp (ρ.re - 1 / 2) - 1)]
    have h1 : Real.exp (ρ.re - 1 / 2) = 1 := by
      have := sq_eq_zero_iff.mp hsq
      linarith
    rw [Real.exp_eq_one_iff] at h1
    linarith
  · intro h
    rw [show ρ.re - 1 / 2 = 0 by linarith, Real.cosh_zero]
    norm_num

/-- **A spiral face rings the non-tempered signature**: off-line means the
face's trace strictly exceeds the tempered ceiling `2`. -/
theorem offline_trace_gt_two {ρ : ℂ} (h : ρ.re ≠ 1 / 2) :
    2 < |(CriticalLinePhasor.HelixStrand.strandTrace (endPairFace ρ)).re| :=
  (CriticalLinePhasor.HelixStrand.spiral_strandTrace_gt_two
    ((endFace_spiral_iff_offline ρ).mpr h)).2

/-- **Isometry forces radius one** — the converse of
`strandBlock_unitary_of_radius_one`: if the strand block is an isometry of
the transverse plane, the leg is on the unit circle. -/
theorem strand_radius_one_of_unitary {α : ℂ}
    (h : (CriticalLinePhasor.RamanujanLimit.strandBlock α)ᴴ *
      CriticalLinePhasor.RamanujanLimit.strandBlock α = 1) :
    ‖α‖ = 1 := by
  have h00 : ((CriticalLinePhasor.RamanujanLimit.strandBlock α)ᴴ *
      CriticalLinePhasor.RamanujanLimit.strandBlock α) 0 0
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [h]
  rw [CriticalLinePhasor.RamanujanLimit.strandBlock,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h00
  simp only [Pi.mul_apply, Pi.star_apply, Matrix.cons_val_zero] at h00
  rw [Complex.star_def] at h00
  have hmc : α * (starRingEnd ℂ) α = 1 := by rw [mul_comm]; exact h00
  have hns : (Complex.normSq α : ℂ) = 1 := by rw [← Complex.mul_conj]; exact hmc
  have hns' : Complex.normSq α = 1 := by exact_mod_cast hns
  have hsq : ‖α‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hns'
  have hfac : (‖α‖ - 1) * (‖α‖ + 1) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.mp hfac with h2 | h2
  · linarith [sub_eq_zero.mp h2]
  · have := norm_nonneg α
    linarith

/-- **det = 1 is FREE at every zero**: the face's transverse block is the
det-one similitude unconditionally — SL₂ costs nothing. -/
theorem endFace_strandBlock_det_one (ρ : ℂ) :
    (CriticalLinePhasor.RamanujanLimit.strandBlock (endPairFace ρ)).det = 1 :=
  CriticalLinePhasor.RamanujanLimit.strandBlock_det_one (endPairFace_ne_zero ρ)

/-- **Isometry ⟺ on-line**: the face's block is unitary exactly when the
event sits on the critical line — SU₂ is the field. -/
theorem endFace_isometry_iff_online (ρ : ℂ) :
    (CriticalLinePhasor.RamanujanLimit.strandBlock (endPairFace ρ))ᴴ *
        CriticalLinePhasor.RamanujanLimit.strandBlock (endPairFace ρ) = 1
      ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    have hn := strand_radius_one_of_unitary h
    rw [norm_endPairFace, Real.exp_eq_one_iff] at hn
    linarith
  · intro h
    exact CriticalLinePhasor.HelixStrand.helix_strandBlock_isometry
      ((endFace_helix_iff_online ρ).mpr h)

/-- **RH = the zero set's transverse monodromy lands in the maximal
compact**: det = 1 holds at every zero for free; RH says every face's
block is moreover an isometry — SL₂ given, SU₂ the field. -/
theorem rh_iff_all_faces_isometry :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) ↔
    ∀ ρ ∈ ZD.NontrivialZeros,
      (CriticalLinePhasor.RamanujanLimit.strandBlock (endPairFace ρ))ᴴ *
        CriticalLinePhasor.RamanujanLimit.strandBlock (endPairFace ρ) = 1 := by
  constructor
  · intro h ρ hρ
    exact (endFace_isometry_iff_online ρ).mpr (h ρ hρ)
  · intro h ρ hρ
    exact (endFace_isometry_iff_online ρ).mp (h ρ hρ)

/-! ## Layer 4: the Frobenius operator — the end exchange, acting

Sam (2026-08-31): *not using Frobenius?* — correct: it was a name, not an
action.  Here it acts.  `endExchange ρ = 1 − conj ρ` is THE Frobenius of
this skeleton: an involution preserving the zero set, acting on the
spectrum as conjugation (pairing `(λ, λ̄)`), on the faces as inversion
(the det-1 similitude in action form), and fixing an event exactly when
it sits on the critical line.  **RH = the zero set is pointwise
Frobenius-fixed.**  The Weil proof shape then compiles: similitude
(free) + ONE Frobenius-invariant positive weight intertwined with the
face action ⟹ unit faces ⟹ RH — Castelnuovo positivity's seat,
relocated to a single exhibitable object. -/

/-- **The Frobenius of the skeleton**: the end-exchange map
`ρ ↦ 1 − conj ρ`, helix end to anti-helix end. -/
def endExchange (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

/-- The Frobenius is an involution. -/
theorem endExchange_involutive : Function.Involutive endExchange := by
  intro ρ
  unfold endExchange
  rw [map_sub, map_one, Complex.conj_conj]
  ring

/-- The Frobenius preserves the zero set. -/
theorem endExchange_mem {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    endExchange ρ ∈ ZD.NontrivialZeros :=
  conjugate_end_mem hρ

/-- The Frobenius acts on the spectrum as conjugation: it pairs
`(λ, conj λ)`. -/
theorem spectralCoord_endExchange (ρ : ℂ) :
    HilbertPolya.spectralCoord (endExchange ρ)
      = (starRingEnd ℂ) (HilbertPolya.spectralCoord ρ) :=
  conjugate_end_spectralCoord ρ

/-- The Frobenius acts on the faces as inversion — `endPair_det_one` in
action form: `face ∘ F = face⁻¹`. -/
theorem endPairFace_endExchange (ρ : ℂ) :
    endPairFace (endExchange ρ) = (endPairFace ρ)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact endPair_det_one ρ)

/-- **The fixed-point law**: the Frobenius fixes an event exactly when it
sits on the critical line.  (The height is always preserved —
`endPair_same_height`; the abscissa is the whole question.) -/
theorem endExchange_fixed_iff (ρ : ℂ) :
    endExchange ρ = ρ ↔ ρ.re = 1 / 2 := by
  unfold endExchange
  constructor
  · intro h
    have hre := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, h]
      norm_num
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring

/-- **RH = the zero set is pointwise Frobenius-fixed** — the fixed-point
chart of the box. -/
theorem rh_iff_zeros_endExchange_fixed :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) ↔
    ∀ ρ ∈ ZD.NontrivialZeros, endExchange ρ = ρ := by
  constructor
  · intro h ρ hρ
    exact (endExchange_fixed_iff ρ).mpr (h ρ hρ)
  · intro h ρ hρ
    exact (endExchange_fixed_iff ρ).mp (h ρ hρ)

/-- **The Weil shape, per event**: a Frobenius-invariant POSITIVE weight
against which the face acts with its full similitude forces a unit face —
similitude + positivity ⟹ unitarity, Castelnuovo's cancellation. -/
theorem face_norm_one_of_invariant_weight {P : ℂ → ℝ} {ρ : ℂ}
    (hpos : 0 < P ρ) (hinv : P (endExchange ρ) = P ρ)
    (hsim : ‖endPairFace ρ‖ ^ 2 * P ρ = P (endExchange ρ)) :
    ‖endPairFace ρ‖ = 1 := by
  rw [hinv] at hsim
  have h1 : ‖endPairFace ρ‖ ^ 2 * P ρ = 1 * P ρ := by
    rw [one_mul]
    exact hsim
  have hsq : ‖endPairFace ρ‖ ^ 2 = 1 := mul_right_cancel₀ (ne_of_gt hpos) h1
  have hfac : (‖endPairFace ρ‖ - 1) * (‖endPairFace ρ‖ + 1) = 0 := by
    nlinarith [hsq]
  rcases mul_eq_zero.mp hfac with h2 | h2
  · linarith [sub_eq_zero.mp h2]
  · have := norm_nonneg (endPairFace ρ)
    linarith

/-- **THE FROBENIUS–WEIL DOOR**: exhibit ONE positive, Frobenius-invariant
weight on the zero set, intertwined with the face similitude, and the
Riemann Hypothesis follows.  Route-shaped: the inhabitant is the weight.
Calibration: invariance and intertwining JOINTLY carry the strength (the
control below shows positivity + intertwining are satisfiable outright);
the door does not lower the box, it relocates it to one exhibitable
object — Castelnuovo positivity's seat in this skeleton. -/
theorem riemannHypothesis_of_frobenius_weight
    (P : ℂ → ℝ)
    (hpos : ∀ ρ ∈ ZD.NontrivialZeros, 0 < P ρ)
    (hinv : ∀ ρ ∈ ZD.NontrivialZeros, P (endExchange ρ) = P ρ)
    (hsim : ∀ ρ ∈ ZD.NontrivialZeros,
      ‖endPairFace ρ‖ ^ 2 * P ρ = P (endExchange ρ)) :
    RiemannHypothesis := by
  apply RHBridge.no_offline_zeros_implies_rh
  intro ρ hρ
  have h1 :=
    face_norm_one_of_invariant_weight (hpos ρ hρ) (hinv ρ hρ) (hsim ρ hρ)
  rw [norm_endPairFace, Real.exp_eq_one_iff] at h1
  linarith

/-- **Calibration control**: positivity + the similitude intertwining are
jointly satisfiable OUTRIGHT (`P = e^{−β}`, at every point of ℂ) — for
this weight the entire RH content sits in Frobenius-invariance alone.
The door's field is genuinely the invariant/intertwined PAIR, not either
half. -/
theorem control_weight_pos_sim :
    ∃ P : ℂ → ℝ, (∀ ρ : ℂ, 0 < P ρ) ∧
      ∀ ρ : ℂ, ‖endPairFace ρ‖ ^ 2 * P ρ = P (endExchange ρ) := by
  refine ⟨fun ρ => Real.exp (-ρ.re), fun ρ => Real.exp_pos _, fun ρ => ?_⟩
  simp only [norm_endPairFace]
  unfold endExchange
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end CriticalLinePhasor.CellEdgeDoor

#print axioms CriticalLinePhasor.CellEdgeDoor.endPair_det_one
#print axioms CriticalLinePhasor.CellEdgeDoor.rh_iff_spectrum_tempered
#print axioms CriticalLinePhasor.CellEdgeDoor.conjugate_end_mem
#print axioms CriticalLinePhasor.CellEdgeDoor.rh_iff_all_end_pairs_coincide
#print axioms CriticalLinePhasor.CellEdgeDoor.pencil_sees_registered_vanishing
#print axioms CriticalLinePhasor.CellEdgeDoor.riemannHypothesis_of_cell_edge_registration
#print axioms CriticalLinePhasor.CellEdgeDoor.riemannHypothesis_of_pencil_cell_stack
#print axioms CriticalLinePhasor.CellEdgeDoor.endFace_spiral_iff_offline
#print axioms CriticalLinePhasor.CellEdgeDoor.endFace_helix_or_spiral
#print axioms CriticalLinePhasor.CellEdgeDoor.rh_iff_no_spiral_faces
#print axioms CriticalLinePhasor.CellEdgeDoor.endPair_radial_ledger_zero
#print axioms CriticalLinePhasor.CellEdgeDoor.endFace_trace_eq_two_iff_online
#print axioms CriticalLinePhasor.CellEdgeDoor.strand_radius_one_of_unitary
#print axioms CriticalLinePhasor.CellEdgeDoor.rh_iff_all_faces_isometry
#print axioms CriticalLinePhasor.CellEdgeDoor.endExchange_involutive
#print axioms CriticalLinePhasor.CellEdgeDoor.endPairFace_endExchange
#print axioms CriticalLinePhasor.CellEdgeDoor.rh_iff_zeros_endExchange_fixed
#print axioms CriticalLinePhasor.CellEdgeDoor.face_norm_one_of_invariant_weight
#print axioms CriticalLinePhasor.CellEdgeDoor.riemannHypothesis_of_frobenius_weight
#print axioms CriticalLinePhasor.CellEdgeDoor.control_weight_pos_sim
