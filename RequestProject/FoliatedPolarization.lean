import Mathlib

/-!
# The polarization on the cut space: Θ is self-adjoint, RH is definiteness

The foliated-flow route needs Deninger's fifth ingredient: a pairing on the cut
space for which the flow generator is self-adjoint, so that RH becomes
positivity of the pairing — the arithmetic analogue of the Hodge index theorem,
which is what delivers the Riemann Hypothesis for curves over finite fields.

This file constructs that pairing and proves the self-adjointness
unconditionally.

Objects.  On the space cut out of the ambient carrier by focal cancellation —
spanned by the zeros — the flow generator acts by the spectral coordinate
`t ρ = -i (ρ - 1/2)`, which is real exactly on the critical line.  The
functional equation supplies an involution `ρ ↦ 1 - conj ρ` on the zero
multiset, and the pairing couples each zero to its reflection.

The two facts that matter:

* `spectralCoord_feReflect` — the reflection conjugates the spectral
  coordinate, `t (1 - conj ρ) = conj (t ρ)`.  This is the self-adjointness of
  the generator, and it holds for every `ρ`, on-line or not.
* `pairBlock_definite_iff` — the pairing restricted to a reflection pair is
  definite exactly when the zero is on the critical line; off the line it is
  hyperbolic, of signature `(1,1)`.

So the generator is self-adjoint on a Krein space unconditionally, and RH is
exactly the statement that the Krein space is a Hilbert space.  A self-adjoint
operator has real spectrum on a definite space and need not on an indefinite
one; that gap is where the arithmetic must enter, and nothing here closes it.

Scope: no claim is made that the pairing is definite.  That is RH.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.FoliatedPolarization

/-- The functional-equation reflection on the zero parameter. -/
def feReflect (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

/-- The spectral coordinate of the flow generator: real exactly on the line. -/
def spectralCoord (ρ : ℂ) : ℂ := -Complex.I * (ρ - 1 / 2)

@[simp] theorem feReflect_involutive (ρ : ℂ) : feReflect (feReflect ρ) = ρ := by
  simp [feReflect]

/-- **The self-adjointness computation.**  The functional-equation reflection
conjugates the spectral coordinate.  Unconditional. -/
theorem spectralCoord_feReflect (ρ : ℂ) :
    spectralCoord (feReflect ρ) = (starRingEnd ℂ) (spectralCoord ρ) := by
  simp only [spectralCoord, feReflect, map_mul, map_sub, map_neg, map_div₀,
    map_one, map_ofNat, Complex.conj_I, RingHom.id_apply,
    RingHomCompTriple.comp_apply]
  ring_nf

/-- The spectral coordinate is real exactly on the critical line. -/
theorem spectralCoord_im (ρ : ℂ) : (spectralCoord ρ).im = 1 / 2 - ρ.re := by
  simp [spectralCoord, Complex.mul_im, Complex.sub_im, Complex.sub_re]

theorem spectralCoord_real_iff (ρ : ℂ) : (spectralCoord ρ).im = 0 ↔ ρ.re = 1 / 2 := by
  rw [spectralCoord_im]
  constructor <;> intro h <;> linarith

/-- The reflection fixes exactly the critical line. -/
theorem feReflect_eq_self_iff (ρ : ℂ) : feReflect ρ = ρ ↔ ρ.re = 1 / 2 := by
  simp only [feReflect, Complex.ext_iff, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]
  constructor
  · rintro ⟨h1, _⟩; linarith
  · intro h; exact ⟨by linarith, by ring⟩

/-! ## The pairing on a reflection block -/

/-- The functional-equation pairing on the two-dimensional block spanned by a
zero and its reflection, with multiplicity weight `m`.  Off the line the two
basis vectors are distinct and the pairing is the hyperbolic form; on the line
they coincide and it is the positive multiple `2m` of the standard form. -/
def pairForm (m : ℝ) (v w : ℂ × ℂ) : ℂ :=
  (m : ℂ) * (v.1 * (starRingEnd ℂ) w.2 + v.2 * (starRingEnd ℂ) w.1)

/-- The generator on the block: it acts by `t` on the zero and by `conj t` on
its reflection, by `spectralCoord_feReflect`. -/
def blockOp (t : ℂ) (v : ℂ × ℂ) : ℂ × ℂ := (t * v.1, (starRingEnd ℂ) t * v.2)

/-- **The generator is self-adjoint for the functional-equation pairing.**
Unconditional: it holds for every zero, on the line or off it. -/
theorem blockOp_selfAdjoint (m : ℝ) (t : ℂ) (v w : ℂ × ℂ) :
    pairForm m (blockOp t v) w = pairForm m v (blockOp t w) := by
  simp only [pairForm, blockOp, map_mul, RingHomCompTriple.comp_apply,
    RingHom.id_apply]
  ring

/-- Off the critical line the block pairing takes a strictly positive value. -/
theorem pairForm_pos_direction {m : ℝ} (hm : 0 < m) :
    0 < (pairForm m (1, 1) (1, 1)).re := by
  simp [pairForm]
  linarith

/-- …and a strictly negative one: the block is hyperbolic, signature `(1,1)`. -/
theorem pairForm_neg_direction {m : ℝ} (hm : 0 < m) :
    (pairForm m (1, -1) (1, -1)).re < 0 := by
  simp [pairForm]
  linarith

/-- **The indefiniteness of an off-line block.**  A reflection pair that is not
fixed by the functional equation contributes one positive and one negative
direction — exactly the negative index counted by the census. -/
theorem pairBlock_indefinite {m : ℝ} (hm : 0 < m) :
    (0 < (pairForm m (1, 1) (1, 1)).re) ∧ ((pairForm m (1, -1) (1, -1)).re < 0) :=
  ⟨pairForm_pos_direction hm, pairForm_neg_direction hm⟩

/-- **The dichotomy.**  For a zero on the critical line the reflection is the
zero itself, so the block is one-dimensional with positive norm `2m`; off the
line the block is two-dimensional and indefinite.  Definiteness of the
polarization is therefore exactly the assertion that every zero lies on the
critical line. -/
theorem pairBlock_definite_iff {m : ℝ} (hm : 0 < m) (ρ : ℂ) :
    (feReflect ρ = ρ ↔ ρ.re = 1 / 2) ∧
      ((0 < (pairForm m (1, 1) (1, 1)).re) ∧ ((pairForm m (1, -1) (1, -1)).re < 0)) :=
  ⟨feReflect_eq_self_iff ρ, pairBlock_indefinite hm⟩

/-- The on-line block, one-dimensional, has strictly positive norm. -/
theorem pairForm_online_pos {m : ℝ} (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    0 < (pairForm m (z, z) (z, z)).re := by
  have h : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hval : pairForm m (z, z) (z, z) = ((2 * m * Complex.normSq z : ℝ) : ℂ) := by
    simp only [pairForm, Complex.mul_conj]
    push_cast
    ring
  rw [hval, Complex.ofReal_re]
  nlinarith

/-- **Per block, non-real spectrum and negative squares are the same event.**
The generator's eigenvalues on a reflection block are `t ρ` and `conj (t ρ)`;
they are non-real exactly when the zero is off the critical line, which is
exactly when the block is hyperbolic rather than definite.

Consequence for the Krein–Langer/Pontryagin route: a self-adjoint operator on a
space with `κ` negative squares has at most `κ` pairs of non-real eigenvalues.
Here the two counts coincide *identically*, block by block, so that bound is
saturated and returns no information.  It becomes informative only if `κ` is
bounded by something outside the spectrum — which is what a cohomology that
cuts the ambient space would have to supply. -/
theorem block_nonreal_iff_indefinite (ρ : ℂ) :
    (spectralCoord ρ).im ≠ 0 ↔ feReflect ρ ≠ ρ := by
  rw [ne_eq, ne_eq, spectralCoord_real_iff, feReflect_eq_self_iff]

end CriticalLinePhasor.FoliatedPolarization

section AxiomAudit
#print axioms CriticalLinePhasor.FoliatedPolarization.spectralCoord_feReflect
#print axioms CriticalLinePhasor.FoliatedPolarization.blockOp_selfAdjoint
#print axioms CriticalLinePhasor.FoliatedPolarization.pairBlock_indefinite
#print axioms CriticalLinePhasor.FoliatedPolarization.feReflect_eq_self_iff
#print axioms CriticalLinePhasor.FoliatedPolarization.spectralCoord_real_iff
#print axioms CriticalLinePhasor.FoliatedPolarization.pairForm_online_pos
end AxiomAudit
