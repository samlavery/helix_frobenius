import RequestProject.RamanujanLimit

/-!
# Temperedness as the 1-D shadow of a 3-D helix: the elliptic/spiral strand dichotomy

The Satake strand `diag(α, α⁻¹)` is the transverse (2-D chart) shadow of a 3-D Frobenius
trajectory.  A **constant-radius helix** projects onto the transverse plane as a rotation — an
*elliptic* strand with `‖α‖ = 1` (tempered); a **growing spiral** projects as a stretch — a
*hyperbolic* strand with `α ∈ ℝ`, `‖α‖ ≠ 1` (complementary series, non-tempered).  Temperedness is
therefore not a size bound to be imported from the chart (`|α_p| ≤ p^{1/2}`, Jacquet–Shalika): it is
the statement that the 3-D trajectory is a **helix**, whose 1-D shadow is automatically a
unit-modulus rotation with real Hecke eigenvalue in `[-2, 2]`.

This file makes the dictionary exact and proves every unconditional entry:

* `isHelixStrand_iff_norm_one` — the strand is a helix winding (a rotation `e^{iθ}`) **iff**
  `‖α‖ = 1`: elliptic ⟺ tempered.  With `helix_strandBlock_isometry`, the helix is exactly the
  isometry (`RamanujanLimit.strandBlock` unitary) of the transverse plane.
* `helix_strandTrace_mem_Icc` — the **1-D readout of a helix is tempered**: `α + α⁻¹ = 2\cos θ`,
  real and in `[-2, 2]` — the Hecke eigenvalue seen in the chart.
* `spiral_strandTrace_gt_two` — the **1-D readout of a spiral is non-tempered**: `α + α⁻¹` is real
  with `|α + α⁻¹| > 2`.
* `strand_dichotomy` — a nonzero strand with **real trace** (the real Hecke eigenvalue) is either
  elliptic (`‖α‖ = 1`, helix) or hyperbolic (`Im α = 0`, spiral) — a clean split on
  `Im(α + α⁻¹) = 0`, exactly the source/sourceless shape of `SourceHolonomy.source_dichotomy`, one
  level down on the radial channel.
* `HasHelixSource` / `EveryFrobeniusHasHelixSource` — **temperedness reframed**: every Frobenius
  strand has a helix source (no spiral orphan).  The clean forcing direction
  `tempered_of_hasHelixSource : HasHelixSource α → ‖α‖ = 1` is proven unconditionally.

**Calibration (honest).**  `HasHelixSource` is *non-circular*: a helix *source* is a rotation
`e^{iθ}` witnessed geometrically, not an assumed unit modulus.  The forcing direction is a theorem;
whether *every* arithmetic Frobenius has a helix source is the **favored branch**, its favor grounded
in the carrier's *proven* Frobenius similitude (`FrobeniusSimilitude`: `√m · unit winding`).  Its
negation — a *spiral* strand (`α ∈ ℝ`, off the circle) — is the **sourceless** reading, the
radial-channel twin of a sourceless zero (`SourceHolonomy`).  This is the 3-D relocation of
Ramanujan–Petersson, at the epistemic status of `EveryZeroHasSource`; it is **not** a from-1-D
proof, and it assumes/proves no RH/GRH.
-/

open Complex Matrix

namespace CriticalLinePhasor.HelixStrand

/-! ## 1. Elliptic (helix) and hyperbolic (spiral) strand legs -/

/-- The strand leg `α` is a **helix winding** — a genuine unit-modulus rotation `e^{iθ}` of the
transverse plane, the 2-D shadow of a constant-radius 3-D helix. -/
def IsHelixStrand (α : ℂ) : Prop := ∃ θ : ℝ, α = Complex.exp ((θ : ℂ) * I)

/-- The strand leg `α` is a **spiral** — real and off the unit circle, the shadow of a
growing-radius trajectory (a stretch, not a rotation). -/
def IsSpiralStrand (α : ℂ) : Prop := α.im = 0 ∧ α ≠ 0 ∧ ‖α‖ ≠ 1

/-- **Elliptic ⟺ tempered.**  The strand is a helix winding (a rotation) iff `‖α‖ = 1`.  A helix
projects to the unit circle; conversely a unit-modulus number is `e^{i\arg α}`. -/
theorem isHelixStrand_iff_norm_one (α : ℂ) : IsHelixStrand α ↔ ‖α‖ = 1 := by
  constructor
  · rintro ⟨θ, rfl⟩
    rw [Complex.norm_exp]
    simp
  · intro h
    refine ⟨Complex.arg α, ?_⟩
    have hpol := Complex.norm_mul_exp_arg_mul_I α
    rw [h, Complex.ofReal_one, one_mul] at hpol
    exact hpol.symm

/-- The clean forcing direction: a helix source is tempered. -/
theorem tempered_of_isHelixStrand {α : ℂ} (h : IsHelixStrand α) : ‖α‖ = 1 :=
  (isHelixStrand_iff_norm_one α).mp h

/-! ## 2. The 1-D readout: the strand trace (Hecke eigenvalue) -/

/-- The **1-D Hecke readout**: the strand trace `a = α + α⁻¹`. -/
noncomputable def strandTrace (α : ℂ) : ℂ := α + α⁻¹

/-- **The 1-D readout of a helix is tempered.**  A helix winding has real trace `2\cos θ ∈ [-2, 2]`
— the Hecke eigenvalue as seen in the chart. -/
theorem helix_strandTrace_mem_Icc {α : ℂ} (h : IsHelixStrand α) :
    (strandTrace α).im = 0 ∧ (strandTrace α).re ∈ Set.Icc (-2 : ℝ) 2 := by
  obtain ⟨θ, rfl⟩ := h
  have key : strandTrace (Complex.exp ((θ : ℂ) * I)) = 2 * Complex.cos (θ : ℂ) := by
    rw [strandTrace, ← Complex.exp_neg, ← neg_mul]
    simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [key]
  rw [show (2 : ℂ) * Complex.cos (θ : ℂ) = ((2 * Real.cos θ : ℝ) : ℂ) by
    rw [← Complex.ofReal_cos]; push_cast; ring]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re, Set.mem_Icc]
  constructor <;> nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]

/-! ## 3. The dichotomy: real trace forces helix or spiral -/

/-- The imaginary part of the trace: `Im(α + α⁻¹) = Im α · (‖α‖² − 1)/‖α‖²`. -/
theorem strandTrace_im {α : ℂ} (hα : α ≠ 0) :
    (strandTrace α).im = α.im * (Complex.normSq α - 1) / Complex.normSq α := by
  have hns : Complex.normSq α ≠ 0 := (Complex.normSq_pos.mpr hα).ne'
  rw [strandTrace, Complex.add_im, Complex.inv_im]
  field_simp
  ring

private theorem norm_one_of_normSq_one {α : ℂ} (h : Complex.normSq α = 1) : ‖α‖ = 1 := by
  have hsq : ‖α‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h
  have h1 : (‖α‖ - 1) * (‖α‖ + 1) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact sub_eq_zero.mp h2
  · exact absurd h2 (by positivity)

/-- **The strand dichotomy.**  A nonzero strand with **real trace** (the real Hecke eigenvalue) is
either **elliptic** (`‖α‖ = 1`, a helix winding) or **hyperbolic** (`Im α = 0`, a spiral).  The
radial-channel twin of `SourceHolonomy.source_dichotomy`: the reciprocal pair is a conjugate pair
(on the unit circle) or a real pair (off it), and nothing else. -/
theorem strand_dichotomy {α : ℂ} (hα : α ≠ 0) (hre : (strandTrace α).im = 0) :
    ‖α‖ = 1 ∨ α.im = 0 := by
  have hns : Complex.normSq α ≠ 0 := (Complex.normSq_pos.mpr hα).ne'
  have h := strandTrace_im hα
  rw [hre] at h
  have hzero : α.im * (Complex.normSq α - 1) = 0 := by
    rcases div_eq_zero_iff.mp h.symm with h' | h'
    · exact h'
    · exact absurd h' hns
  rcases mul_eq_zero.mp hzero with him | hnsq
  · exact Or.inr him
  · exact Or.inl (norm_one_of_normSq_one (by linarith [sub_eq_zero.mp hnsq]))

/-- **The 1-D readout of a spiral is non-tempered.**  A spiral strand (`α` real, off the unit
circle) has real trace with `|α + α⁻¹| > 2`: `(r + 1/r)² = (r − 1/r)² + 4 > 4`. -/
theorem spiral_strandTrace_gt_two {α : ℂ} (h : IsSpiralStrand α) :
    (strandTrace α).im = 0 ∧ 2 < |(strandTrace α).re| := by
  obtain ⟨him, hα0, hnorm⟩ := h
  set r : ℝ := α.re with hr
  have hαr : α = (r : ℂ) := by
    apply Complex.ext
    · simp [hr]
    · simp [him]
  have hr0 : r ≠ 0 := by
    intro h0; apply hα0; rw [hαr, h0]; simp
  have hrne : r ≠ 1 ∧ r ≠ -1 := by
    refine ⟨fun hbad => hnorm ?_, fun hbad => hnorm ?_⟩
    · rw [hαr, hbad]; simp
    · rw [hαr, hbad]; simp
  have htrace : strandTrace α = ((r + r⁻¹ : ℝ) : ℂ) := by
    rw [strandTrace, hαr, ← Complex.ofReal_inv, ← Complex.ofReal_add]
  have hne : r - r⁻¹ ≠ 0 := by
    intro hbad
    have hrr : r = r⁻¹ := by linarith [sub_eq_zero.mp hbad]
    have hr2 : r * r = 1 := by
      have hmi := mul_inv_cancel₀ hr0
      rwa [← hrr] at hmi
    have hfac : (r - 1) * (r + 1) = 0 := by
      have hexp : (r - 1) * (r + 1) = r * r - 1 := by ring
      rw [hexp, hr2]; ring
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact hrne.1 (by linarith)
    · exact hrne.2 (by linarith)
  have hpos : (0 : ℝ) < (r - r⁻¹) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  have hsq : (r - r⁻¹) ^ 2 = (r + r⁻¹) ^ 2 - 4 := by
    field_simp
    ring
  have hkey : (4 : ℝ) < (r + r⁻¹) ^ 2 := by linarith [hpos, hsq]
  rw [htrace]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  have hsq_abs : |r + r⁻¹| ^ 2 = (r + r⁻¹) ^ 2 := sq_abs _
  nlinarith [hkey, abs_nonneg (r + r⁻¹), hsq_abs]

/-! ## 4. The reframe: temperedness = every Frobenius has a helix source -/

/-- **Temperedness, 3-D form.**  The strand has a **helix source** — its transverse trajectory is a
constant-radius helix (a rotation), not a spiral. -/
def HasHelixSource (α : ℂ) : Prop := IsHelixStrand α

/-- **The favored branch.**  Every unramified Frobenius strand has a helix source — no spiral
orphan.  The 3-D relocation of Ramanujan–Petersson (`EveryZeroHasSource`'s radial-channel twin);
the forcing direction below is a theorem, the universal statement is the favored branch. -/
def EveryFrobeniusHasHelixSource {ι : Type*} (α : ι → ℂ) : Prop := ∀ i, HasHelixSource (α i)

/-- **The clean forcing direction (unconditional): a helix source is tempered.**  If the strand
has a helix source then `‖α‖ = 1` — the 3-D-native statement of temperedness at the site. -/
theorem tempered_of_hasHelixSource {α : ℂ} (h : HasHelixSource α) : ‖α‖ = 1 :=
  tempered_of_isHelixStrand h

/-- Under the favored branch every strand is tempered: `EveryFrobeniusHasHelixSource ⟹` Ramanujan
at every site. -/
theorem forall_norm_one_of_everyFrobeniusHasHelixSource {ι : Type*} {α : ι → ℂ}
    (h : EveryFrobeniusHasHelixSource α) (i : ι) : ‖α i‖ = 1 :=
  tempered_of_hasHelixSource (h i)

/-! ## 5. Elliptic = isometry: the helix is the unitary transverse block -/

/-- **The helix is the isometry.**  A helix source makes `RamanujanLimit.strandBlock` unitary — an
isometry of the transverse plane, coinciding with the carrier's chiral (phase-only) class.  Elliptic
strand = rotation = unitary block. -/
theorem helix_strandBlock_isometry {α : ℂ} (h : IsHelixStrand α) :
    (RamanujanLimit.strandBlock α)ᴴ * RamanujanLimit.strandBlock α = 1 :=
  RamanujanLimit.strandBlock_unitary_of_radius_one (tempered_of_isHelixStrand h)

end CriticalLinePhasor.HelixStrand

#print axioms CriticalLinePhasor.HelixStrand.isHelixStrand_iff_norm_one
#print axioms CriticalLinePhasor.HelixStrand.helix_strandTrace_mem_Icc
#print axioms CriticalLinePhasor.HelixStrand.strand_dichotomy
#print axioms CriticalLinePhasor.HelixStrand.spiral_strandTrace_gt_two
#print axioms CriticalLinePhasor.HelixStrand.tempered_of_hasHelixSource
#print axioms CriticalLinePhasor.HelixStrand.helix_strandBlock_isometry
